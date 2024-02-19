use std::collections::HashMap;

use super::{cardinality_constraint, ConfigVars, ProgramSynthesis, SatInstance, SatLiteral};

pub fn truth_table_to_naive_sum_of_products(
  input_count: usize,
  f: impl Fn(&[bool]) -> bool,
) -> Vec<Vec<i32>> {
  let mut sum_of_products = Vec::new();
  for i in 0..2_usize.pow(input_count as u32) {
    let mut product = Vec::new();
    for j in 0..input_count {
      let bit = (i >> j) & 1;
      match bit {
        0 => product.push(-(j as i32 + 1)),
        1 => product.push(j as i32 + 1),
        _ => unreachable!(),
      }
    }
    if f(&product.iter().map(|lit| *lit > 0).collect::<Vec<_>>()) {
      sum_of_products.push(product);
    }
  }
  sum_of_products
}

#[derive(Debug, Clone)]
pub struct SumOfProducts(pub Vec<Vec<i32>>);

impl SumOfProducts {
  fn count_inputs(&self) -> usize {
    self.0
      .iter()
      .map(|product| product.iter().map(|lit| lit.abs()).max().unwrap_or(0))
      .max()
      .unwrap_or(0) as usize
  }
}

pub struct SumOfProductsResourcesSpec {
  pub input_count: usize,
  pub term_limit:  usize,
}

impl ProgramSynthesis for SumOfProducts {
  type ProgramResourcesSpec = SumOfProductsResourcesSpec;
  type ConfigVarsData = Vec<SatLiteral>;

  fn create_configuration_vars(
    instance: &mut SatInstance,
    resources_spec: &Self::ProgramResourcesSpec,
  ) -> ConfigVars<Self::ConfigVarsData> {
    //// NB: We depend on the selection variables starting at 1.
    let config_vars_data = instance.n_fresh(3_usize.pow(resources_spec.input_count as u32));
    // Apply the cardinality constraint.
    cardinality_constraint(instance, &config_vars_data, None, resources_spec.term_limit);
    ConfigVars {
      config_vars_data,
      input_count: resources_spec.input_count,
      output_count: 1,
    }
  }

  fn program_to_bits(
    &self,
    instance: &mut SatInstance,
    false_lit: SatLiteral,
  ) -> ConfigVars<Self::ConfigVarsData> {
    let maximum_input = self.count_inputs();
    let mut vars = vec![false_lit; 3_usize.pow(maximum_input as u32)];
    for product in &self.0 {
      let mut configuration_var_index = 0;
      for lit in product {
        let position = 3_usize.pow(lit.abs() as u32 - 1);
        match *lit > 0 {
          true => configuration_var_index += 1 * position,
          false => configuration_var_index += 2 * position,
        }
      }
      vars[configuration_var_index] = -false_lit;
    }
    ConfigVars {
      config_vars_data: vars,
      input_count:      maximum_input,
      output_count:     1,
    }
  }

  fn decode_program(
    config: &ConfigVars<Self::ConfigVarsData>,
    model: &HashMap<SatLiteral, bool>,
  ) -> Self {
    let mut sum_of_products = Vec::new();
    for (mut i, config_var) in config.config_vars_data.iter().enumerate() {
      let bit = model.get(config_var).copied().unwrap_or(false);
      if !bit {
        continue;
      }
      let mut product = Vec::new();
      for input in 1..=config.input_count as i32 {
        // Note that negation here is reverse of above,
        // because we're no longer building a Horn clause.
        match i % 3 {
          0 => {}
          1 => product.push(input),
          2 => product.push(-input),
          _ => unreachable!(),
        }
        i /= 3;
      }
      sum_of_products.push(product);
    }
    SumOfProducts(sum_of_products)
  }

  fn enumerate_vars_in_config(config_vars: &ConfigVars<Self::ConfigVarsData>) -> Vec<SatLiteral> {
    config_vars.config_vars_data.clone()
  }

  fn evaluate(&self, inputs: &[bool]) -> Vec<bool> {
    for product in &self.0 {
      let mut product_result = true;
      for lit in product {
        let input = inputs[lit.abs() as usize - 1];
        match *lit > 0 {
          true => product_result &= input,
          false => product_result &= !input,
        }
      }
      if product_result {
        return vec![true];
      }
    }
    vec![false]
  }

  fn build_fpga(
    instance: &mut SatInstance,
    configuration_vars: &ConfigVars<Self::ConfigVarsData>,
    input_vars: &[SatLiteral],
    output_vars: &[SatLiteral],
  ) {
    assert!(configuration_vars.config_vars_data.len() == 3_usize.pow(input_vars.len() as u32));
    assert!(output_vars.len() == 1);
    let mut clause_outputs = vec![];
    for (mut combination, configuration_var) in
      configuration_vars.config_vars_data.iter().enumerate()
    {
      let clause_output = instance.fresh();
      // If we don't pick this clause, then the clause output is low.
      instance.add_clause(vec![*configuration_var, -clause_output]);
      clause_outputs.push(clause_output);
      let mut clause = vec![-*configuration_var, clause_output];
      for input_var in input_vars {
        if let Some(lit) = match combination % 3 {
          // Don't include this term
          0 => None,
          // Include this term positively
          1 => Some(*input_var),
          // Include this term negatively
          2 => Some(-*input_var),
          _ => unreachable!(),
        } {
          // Note the negation due to this being a Horn clause.
          clause.push(-lit);
          // If the referenced literal is false, then the clause output is low.
          instance.add_clause(vec![lit, -clause_output]);
        }
        combination /= 3;
      }
      instance.add_clause(clause);
    }
    // Or together all clause outputs into the output var.
    for clause_output in &clause_outputs {
      // Add clauses to drive output_var high if any clause_output is high.
      instance.add_clause(vec![-*clause_output, output_vars[0]]);
    }
    // Add clause to drive output_var low if all clause_outputs are low.
    clause_outputs.push(-output_vars[0]);
    instance.add_clause(clause_outputs);
  }
}
