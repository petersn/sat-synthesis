use std::{collections::HashSet, io::Write};

// pub mod combinational;
pub mod sat_tables;
// pub mod standard_cells;
pub mod sum_of_products;
pub mod vpternlog;

use std::collections::HashMap;

use splr::{SatSolverIF, SolveIF};
use varisat::ExtendFormula;

use crate::sat_tables::StaticCnf;

#[derive(Debug, Clone, Copy)]
pub enum SatSolver {
  External(&'static [&'static str]),
  Varisat,
  Splr,
}

//pub const DEFAULT_SOLVER: SatSolver = SatSolver::External(&["cryptominisat"]);
pub const DEFAULT_SOLVER: SatSolver = SatSolver::Splr;

pub type SatLiteral = i32;

pub enum SatOutcome {
  SAT(HashMap<SatLiteral, bool>),
  UNSAT,
}

enum SolverState {
  External(&'static [&'static str]),
  Varisat {
    lits:           Vec<varisat::Lit>,
    varisat_solver: varisat::solver::Solver<'static>,
  },
  Splr {
    empty_clause_inserted: bool,
    splr_solver:           splr::Solver,
  },
}

macro_rules! add_varisat_clause {
  ($lits:expr, $varisat_solver:expr, $clause:expr) => {{
    let clause: Vec<_> = $clause
      .iter()
      .map(|lit| match *lit > 0 {
        true => $lits[*lit as usize - 1],
        false => !$lits[(-*lit) as usize - 1],
      })
      .collect();
    $varisat_solver.add_clause(&clause);
  }};
}

pub struct SatInstance {
  contents:     Vec<Vec<SatLiteral>>,
  current_var:  i32,
  solver_state: SolverState,
}

impl Clone for SatInstance {
  fn clone(&self) -> Self {
    Self {
      contents:     self.contents.clone(),
      current_var:  self.current_var,
      solver_state: match &self.solver_state {
        SolverState::External(command) => SolverState::External(command),
        SolverState::Varisat { .. } => {
          let mut varisat_solver = varisat::solver::Solver::new();
          let lits: Vec<_> = (0..self.current_var).map(|_| varisat_solver.new_lit()).collect();
          for clause in &self.contents {
            add_varisat_clause!(lits, varisat_solver, clause);
          }
          SolverState::Varisat {
            lits,
            varisat_solver,
          }
        }
        SolverState::Splr {
          empty_clause_inserted,
          splr_solver,
        } => SolverState::Splr {
          empty_clause_inserted: *empty_clause_inserted,
          splr_solver:           splr_solver.clone(),
        },
      },
    }
  }
}

impl SatInstance {
  pub fn new(sat_solver: SatSolver) -> Self {
    Self {
      contents:     vec![],
      current_var:  0,
      solver_state: match sat_solver {
        SatSolver::External(command) => SolverState::External(command),
        SatSolver::Varisat => SolverState::Varisat {
          lits:           vec![],
          varisat_solver: varisat::solver::Solver::new(),
        },
        SatSolver::Splr => {
          let empty_instance: &[Vec<i32>] = &[];
          SolverState::Splr {
            empty_clause_inserted: false,
            splr_solver:           splr::Solver::try_from((
              splr::Config::default(),
              empty_instance,
            ))
            .unwrap(),
          }
        }
      },
    }
  }

  pub fn fresh(&mut self) -> SatLiteral {
    self.current_var += 1;
    self.current_var
  }

  pub fn n_fresh(&mut self, n: usize) -> Vec<SatLiteral> {
    (0..n).map(|_| self.fresh()).collect()
  }

  pub fn add_clause(&mut self, clause: Vec<SatLiteral>) {
    match &mut self.solver_state {
      SolverState::External(_) => {}
      SolverState::Varisat {
        lits,
        varisat_solver,
      } => {
        while lits.len() < self.current_var as usize {
          lits.push(varisat_solver.new_lit());
        }
        add_varisat_clause!(lits, varisat_solver, &clause);
      }
      SolverState::Splr {
        empty_clause_inserted,
        splr_solver,
      } => {
        while splr_solver.asg.num_vars < self.current_var as usize {
          splr_solver.add_var();
        }
        match splr_solver.add_clause(&clause) {
          Ok(_) => {}
          // For some weird reason splr doesn't like empty clauses, rather than just giving UNSAT.
          Err(splr::SolverError::EmptyClause) => *empty_clause_inserted = true,
          Err(e) => panic!("Unexpected error: {:?}", e),
        }
      }
    }
    self.contents.push(clause);
  }

  pub fn add_precompiled(
    &mut self,
    template: &StaticCnf,
    inputs: &[SatLiteral],
    outputs: &[SatLiteral],
  ) {
    assert_eq!(inputs.len(), template.input_count);
    assert_eq!(outputs.len(), template.output_count);
    let all_bits: Vec<_> = inputs.iter().chain(outputs.iter()).copied().collect();
    for clause in template.cnf {
      let mut new_clause = vec![];
      for &lit in *clause {
        match lit > 0 {
          true => new_clause.push(all_bits[lit as usize - 1]),
          false => new_clause.push(-all_bits[(-lit) as usize - 1]),
        }
      }
      self.add_clause(new_clause);
    }
  }

  fn solve_external(current_var: i32, clauses: &[Vec<SatLiteral>], command: &[&str]) -> SatOutcome {
    // Create a temporary DIMACS file.
    let mut file = tempfile::NamedTempFile::new().expect("Failed to create temporary file");
    writeln!(file, "p cnf {} {}", current_var, clauses.len()).unwrap();
    for clause in clauses {
      for lit in clause {
        write!(file, "{} ", lit).unwrap();
      }
      writeln!(file, "0").unwrap();
    }
    // Invoke SAT solver.
    let output = std::process::Command::new(command[0])
      .args(&command[1..])
      .arg(file.path())
      .output()
      .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    // Parse output.
    let mut model: HashMap<SatLiteral, bool> = HashMap::new();
    let mut s_line = false;
    for line in stdout.lines() {
      if line.trim().is_empty() {
        continue;
      }
      if line.starts_with("c ") || line == "c" {
        continue;
      } else if line.starts_with("s ") {
        assert!(!s_line);
        s_line = true;
        let mut parts = line.split_whitespace();
        parts.next();
        let status = parts.next().unwrap();
        if status == "UNSATISFIABLE" {
          return SatOutcome::UNSAT;
        }
        assert_eq!(status, "SATISFIABLE");
      } else if line.starts_with("v ") {
        let mut parts = line.split_whitespace();
        parts.next();
        for part in parts {
          let lit = part.parse::<SatLiteral>().unwrap();
          model.insert(lit.abs(), lit > 0);
        }
      } else if s_line {
        // Disallow unknown output after the s line.
        eprintln!("stdout: {}", stdout);
        panic!("Unexpected solver output: {}", line);
      }
    }
    if !s_line {
      eprintln!("stdout: {}", stdout);
      panic!("No s line in solver output");
    }
    SatOutcome::SAT(model)
  }

  fn solve_varisat(varisat_solver: &mut varisat::Solver) -> SatOutcome {
    if !varisat_solver.solve().unwrap() {
      return SatOutcome::UNSAT;
    }
    SatOutcome::SAT(
      varisat_solver
        .model()
        .unwrap()
        .iter()
        .map(|lit| (lit.to_dimacs().abs() as i32, lit.is_positive()))
        .collect(),
    )
  }

  fn solve_splr(splr_solver: &mut splr::Solver) -> SatOutcome {
    let outcome = match splr_solver.solve().unwrap() {
      splr::Certificate::SAT(x) =>
        SatOutcome::SAT(x.iter().map(|&lit| (lit.abs(), lit > 0)).collect()),
      splr::Certificate::UNSAT => SatOutcome::UNSAT,
    };
    // FIXME: Should I be calling reset here?
    //splr_solver.reset();
    outcome
  }

  pub fn solve(&mut self) -> SatOutcome {
    match &mut self.solver_state {
      SolverState::External(command) =>
        SatInstance::solve_external(self.current_var, &self.contents, command),
      SolverState::Varisat { varisat_solver, .. } => SatInstance::solve_varisat(varisat_solver),
      SolverState::Splr {
        empty_clause_inserted: true,
        ..
      } => SatOutcome::UNSAT,
      SolverState::Splr { splr_solver, .. } => SatInstance::solve_splr(splr_solver),
    }
  }
}

fn cardinality_constraint(
  instance: &mut SatInstance,
  vars: &[SatLiteral],
  // FIXME: Weights aren't used yet.
  weights: Option<&[usize]>,
  max_count: usize,
) {
  // FIXME: Weights aren't implemented yet.
  assert!(weights.is_none());
  let total_cost_of_all_vars = weights.map(|w| w.iter().sum()).unwrap_or(vars.len());
  if max_count >= total_cost_of_all_vars {
    return;
  }
  if max_count == 0 {
    // Simply set each var to false.
    for var in vars {
      instance.add_clause(vec![-*var]);
    }
    return;
  }
  // at_least_k[(i, k)] is true iff vars[:i] has at least k true literals.
  let mut at_most_k: HashMap<(usize, usize), SatLiteral> = HashMap::new();
  let mut get_var = |instance: &mut SatInstance, i: usize, k: usize| -> SatLiteral {
    *at_most_k.entry((i, k)).or_insert_with(|| instance.fresh())
  };
  let get_weight = |i: usize| weights.map(|w| w[i]).unwrap_or(1);
  for prefix_len in 1..=vars.len() {
    for count in 1..=prefix_len.min(max_count + 1) {
      let here = get_var(instance, prefix_len, count);
      // If we already have `count` true literals at the previous position, we do here too.
      if prefix_len > count {
        let clause = vec![-get_var(instance, prefix_len - 1, count), here];
        instance.add_clause(clause);
      }
      // If we have `count - 1` true literals at the previous position, and
      // the current position is also true, then we have `count` true here.
      if prefix_len == 1 {
        // Simply equate.
        instance.add_clause(vec![-vars[0], here]);
        instance.add_clause(vec![vars[0], -here]);
      } else {
        let clause = match count {
          1 => vec![-vars[prefix_len - 1], here],
          _ => vec![
            -get_var(instance, prefix_len - 1, count - 1),
            -vars[prefix_len - 1],
            here,
          ],
        };
        instance.add_clause(clause);
      }
    }
  }
  // Constrain the final bit to be false.
  let clause = vec![-get_var(instance, vars.len(), max_count + 1)];
  instance.add_clause(clause);
}

fn force_unequal(instance: &mut SatInstance, a: &[SatLiteral], b: &[SatLiteral]) {
  assert!(a.len() == b.len());
  let unequal = instance.n_fresh(a.len());
  for i in 0..a.len() {
    // Add the constraint (a[i] == b[i]) -> !unequal[i]
    instance.add_clause(vec![a[i], b[i], -unequal[i]]);
    instance.add_clause(vec![-a[i], -b[i], -unequal[i]]);
  }
  // Constrain at least one position to be unequal.
  instance.add_clause(unequal);
}

pub struct ConfigVars<ConfigVarsData> {
  pub config_vars_data: ConfigVarsData,
  pub input_count:      usize,
  pub output_count:     usize,
}

pub trait ProgramSynthesis: std::fmt::Debug {
  type ProgramResourcesSpec;
  type ConfigVarsData;

  fn create_configuration_vars(
    instance: &mut SatInstance,
    resources: &Self::ProgramResourcesSpec,
  ) -> ConfigVars<Self::ConfigVarsData>;
  fn program_to_bits(
    &self,
    instance: &mut SatInstance,
    false_lit: SatLiteral,
  ) -> ConfigVars<Self::ConfigVarsData>;
  fn decode_program(
    config: &ConfigVars<Self::ConfigVarsData>,
    model: &HashMap<SatLiteral, bool>,
  ) -> Self;
  fn enumerate_vars_in_config(config_vars: &ConfigVars<Self::ConfigVarsData>) -> Vec<SatLiteral>;
  fn evaluate(&self, inputs: &[bool]) -> Vec<bool>;
  fn build_fpga(
    instance: &mut SatInstance,
    configuration_vars: &ConfigVars<Self::ConfigVarsData>,
    input_vars: &[SatLiteral],
    output_vars: &[SatLiteral],
  );
}

#[derive(Debug, Clone, Copy)]
pub struct CegisSettings {
  pub counter_examples_per_step: usize,
}

pub fn program_search<InputSynth: ProgramSynthesis, OutputSynth: ProgramSynthesis>(
  solver: SatSolver,
  base_program: &InputSynth,
  resources_spec: &OutputSynth::ProgramResourcesSpec,
  log: impl Fn(&str),
) -> Option<OutputSynth> {
  let mut program_search_instance = SatInstance::new(solver);
  let config_vars =
    OutputSynth::create_configuration_vars(&mut program_search_instance, resources_spec);
  // // Constrain cost.
  //OutputSynth::constrain_cost(&mut program_search_instance, &config_vars_data, cost_limit);

  let false_lit = program_search_instance.fresh();
  program_search_instance.add_clause(vec![-false_lit]);
  let bits_to_literals = |bits: &[bool]| -> Vec<SatLiteral> {
    bits
      .iter()
      .map(|bit| match bit {
        true => -false_lit,
        false => false_lit,
      })
      .collect()
  };

  // Construct a template SAT instance to use for counter-example search.
  let mut counter_examples = HashSet::new();
  let mut counter_example_search_template = program_search_instance.clone();
  let counter_example_search_inputs =
    counter_example_search_template.n_fresh(config_vars.input_count);
  {
    // Build the circuitry that computes the original program for testing against.
    let reference_output = counter_example_search_template.n_fresh(config_vars.output_count);
    let test_output = counter_example_search_template.n_fresh(config_vars.output_count);
    let base_program_cfg_vars = base_program.program_to_bits(&mut counter_example_search_template, false_lit);
    InputSynth::build_fpga(
      &mut counter_example_search_template,
      &base_program_cfg_vars,
      &counter_example_search_inputs,
      &reference_output,
    );
    // Build circuitry that tests out the candidate program.
    OutputSynth::build_fpga(
      &mut counter_example_search_template,
      &config_vars,
      &counter_example_search_inputs,
      &test_output,
    );
    // Demand that the outputs disagree (as we're searching for a counter-example).
    force_unequal(&mut counter_example_search_template, &reference_output, &test_output);
  }

  let minimized_program = loop {
    // === Step 1: Search for a program that agrees with the original program on all counter-examples.
    let program_search_model = match program_search_instance.solve() {
      SatOutcome::SAT(model) => model,
      SatOutcome::UNSAT => return None,
    };
    // Take our counter-example search template, and assign the selection
    // variables to configure it to test the program we just found.
    let mut counter_example_search_instance = counter_example_search_template.clone();
    for var in OutputSynth::enumerate_vars_in_config(&config_vars) {
      let bit = program_search_model.get(&var).copied().unwrap_or(false);
      counter_example_search_instance.add_clause(match bit {
        true => vec![var],
        false => vec![-var],
      });
    }

    // InputSynth::fix_configuration(
    //   &mut counter_example_search_instance,
    //   &program_search_model,
    //   &InputSynth::program_to_bits(
    //     &mut counter_example_search_instance,
    //     false_lit,
    //     base_program,
    //   ),
    // );
    // let mut candidate_program = Vec::new();
    // for configuration_var in &configuration_vars {
    //   let bit = program_search_model.get(&configuration_var).copied().unwrap_or(false);
    //   candidate_program.push(bit);
    //   counter_example_search_instance.add_clause(match bit {
    //     true => vec![*configuration_var],
    //     false => vec![-*configuration_var],
    //   });
    // }
    // log(&format!(
    //   "Found candidate program: {:?}",
    //   OutputSynth::bits_to_program(input_vars.len(), &candidate_program),
    // ));

    // === Step 2: Find a counter-example where the candidate program disagrees with the original.
    let counter_example_model = match counter_example_search_instance.solve() {
      SatOutcome::SAT(model) => model,
      // If no counter-example exists, then we have found a minimized program.
      SatOutcome::UNSAT => break OutputSynth::decode_program(&config_vars, &program_search_model),
    };
    let mut counter_example_bits = vec![];
    let mut sat_inputs = vec![];
    // Force the inputs.
    for counter_example_search_input in &counter_example_search_inputs {
      let assignment =
        counter_example_model.get(&counter_example_search_input).copied().unwrap_or(false);
      counter_example_bits.push(assignment);
      sat_inputs.push(match assignment {
        true => -false_lit,
        false => false_lit,
      });
    }
    log(&format!("Found counter-example: {:?}", counter_example_bits));
    if !counter_examples.insert(counter_example_bits.clone()) {
      panic!("Duplicate counter-example: {:?} -- this usually indicates a bug in build_fpga", counter_example_bits);
    }
    let desired_value = InputSynth::evaluate(base_program, &counter_example_bits);
    // Add the counter-example as a constraint on our program search.
    OutputSynth::build_fpga(
      &mut program_search_instance,
      &config_vars,
      &sat_inputs,
      &bits_to_literals(&desired_value),
    );
  };

  for input in 0..1 << config_vars.input_count {
    let bits: Vec<bool> = (0..config_vars.input_count).map(|i| (input >> i) & 1 == 1).collect();
    let sop1_value = InputSynth::evaluate(base_program, &bits);
    let sop2_value = OutputSynth::evaluate(&minimized_program, &bits);
    println!("{}: ref={:?} vs minimized={:?}", input, sop1_value, sop2_value);
    assert_eq!(sop1_value, sop2_value);
  }

  Some(minimized_program)
}

pub fn lookup_table_search<OutputSynth: ProgramSynthesis>(
  solver: SatSolver,
  settings: CegisSettings,
  lut: impl Fn(&[bool]) -> Vec<bool>,
  resources_spec: &OutputSynth::ProgramResourcesSpec,
  log: impl Fn(&str),
) -> Option<OutputSynth> {
  let mut program_search_instance = SatInstance::new(solver);
  let config_vars =
    OutputSynth::create_configuration_vars(&mut program_search_instance, resources_spec);
  //// Constrain cost.
  //OutputSynth::constrain_cost(&mut program_search_instance, &config_vars_data, cost_limit);

  let false_lit = program_search_instance.fresh();
  program_search_instance.add_clause(vec![-false_lit]);
  let bits_to_literals = |bits: &[bool]| -> Vec<SatLiteral> {
    bits
      .iter()
      .map(|bit| match bit {
        true => -false_lit,
        false => false_lit,
      })
      .collect()
  };

  // Construct a template SAT instance to use for counter-example search.
  let mut counter_examples = HashSet::new();
  // let mut counter_example_search_template = program_search_instance.clone();
  // let counter_example_search_inputs =
  //   counter_example_search_template.n_fresh(config_vars.input_count);
  // {
  //   // Build the circuitry that computes the original program for testing against.
  //   let reference_output = counter_example_search_template.n_fresh(config_vars.output_count);
  //   let test_output = counter_example_search_template.n_fresh(config_vars.output_count);
  //   let base_program_cfg_vars = base_program.program_to_bits(&mut counter_example_search_template, false_lit);
  //   InputSynth::build_fpga(
  //     &mut counter_example_search_template,
  //     &base_program_cfg_vars,
  //     &counter_example_search_inputs,
  //     &reference_output,
  //   );
  //   // Build circuitry that tests out the candidate program.
  //   OutputSynth::build_fpga(
  //     &mut counter_example_search_template,
  //     &config_vars,
  //     &counter_example_search_inputs,
  //     &test_output,
  //   );
  //   // Demand that the outputs disagree (as we're searching for a counter-example).
  //   force_unequal(&mut counter_example_search_template, &reference_output, &test_output);
  // }

  let minimized_program = loop {
    // === Step 1: Search for a program that agrees with the original program on all counter-examples.
    let program_search_model = match program_search_instance.solve() {
      SatOutcome::SAT(model) => model,
      SatOutcome::UNSAT => return None,
    };

    // // Take our counter-example search template, and assign the selection
    // // variables to configure it to test the program we just found.
    // let mut counter_example_search_instance = counter_example_search_template.clone();
    // for var in OutputSynth::enumerate_vars_in_config(&config_vars) {
    //   let bit = program_search_model.get(&var).copied().unwrap_or(false);
    //   counter_example_search_instance.add_clause(match bit {
    //     true => vec![var],
    //     false => vec![-var],
    //   });
    // }

    let candidate_program = OutputSynth::decode_program(&config_vars, &program_search_model);
    let mut bits = vec![false; config_vars.input_count];
    // let mut counter_example = None;
    let mut current_counter_examples = Vec::new();
    for i in 0..1 << config_vars.input_count {
      for (j, bit) in bits.iter_mut().enumerate() {
        *bit = (i >> j) & 1 == 1;
      }
      let sop1_value = lut(&bits);
      let sop2_value = OutputSynth::evaluate(&candidate_program, &bits);
      if sop1_value != sop2_value {
        //panic!("Disagreement: {:?} vs {:?}", sop1_value, sop2_value);
        // counter_example = Some(bits.clone());
        // break;
        // counter_example_count += 1;
        current_counter_examples.push(bits.clone());
      }
    }

    if current_counter_examples.is_empty() {
      break candidate_program;
    }

    // InputSynth::fix_configuration(
    //   &mut counter_example_search_instance,
    //   &program_search_model,
    //   &InputSynth::program_to_bits(
    //     &mut counter_example_search_instance,
    //     false_lit,
    //     base_program,
    //   ),
    // );
    // let mut candidate_program = Vec::new();
    // for configuration_var in &configuration_vars {
    //   let bit = program_search_model.get(&configuration_var).copied().unwrap_or(false);
    //   candidate_program.push(bit);
    //   counter_example_search_instance.add_clause(match bit {
    //     true => vec![*configuration_var],
    //     false => vec![-*configuration_var],
    //   });
    // }
    // log(&format!(
    //   "Found candidate program: {:?}",
    //   OutputSynth::bits_to_program(input_vars.len(), &candidate_program),
    // ));

    // // === Step 2: Find a counter-example where the candidate program disagrees with the original.
    // let counter_example_model = match counter_example_search_instance.solve() {
    //   SatOutcome::SAT(model) => model,
    //   // If no counter-example exists, then we have found a minimized program.
    //   SatOutcome::UNSAT => break OutputSynth::decode_program(&config_vars, &program_search_model),
    // };


    // let mut counter_example_bits = vec![];
    // Force the inputs.
    let correct_behavior = (1 << config_vars.input_count) - current_counter_examples.len();
    log(&format!("[{} examples] [correct behavior: {}/{}]",
      counter_examples.len(), correct_behavior, 1 << config_vars.input_count,
    ));
    // let i = rand::random::<usize>() % current_counter_examples.len();
    // let counter_example_bits = &current_counter_examples[i];
    // Shuffle the current counter-examples.
    let mut rng = rand::thread_rng();
    use rand::seq::SliceRandom;
    current_counter_examples.shuffle(&mut rng);
    let c = settings.counter_examples_per_step.min(current_counter_examples.len());
    for counter_example_bits in &current_counter_examples[0..c] {
      if !counter_examples.insert(counter_example_bits.clone()) {
        panic!("Duplicate counter-example: {:?} -- this usually indicates a bug in build_fpga", counter_example_bits);
      }
      let desired_value = lut(&counter_example_bits);
      // Add the counter-example as a constraint on our program search.
      OutputSynth::build_fpga(
        &mut program_search_instance,
        &config_vars,
        &bits_to_literals(&counter_example_bits),
        &bits_to_literals(&desired_value),
      );
    }
  };

  for input in 0..1 << config_vars.input_count {
    let bits: Vec<bool> = (0..config_vars.input_count).map(|i| (input >> i) & 1 == 1).collect();
    let sop1_value = lut(&bits);
    let sop2_value = OutputSynth::evaluate(&minimized_program, &bits);
    println!("{}: ref={:?} vs minimized={:?}", input, sop1_value, sop2_value);
    assert_eq!(sop1_value, sop2_value);
  }

  Some(minimized_program)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::sum_of_products::{SumOfProducts, SumOfProductsResourcesSpec};

  #[test]
  fn test_cardinality_constraint() {
    let mut instance = SatInstance::new(DEFAULT_SOLVER);
    let vars = vec![instance.fresh(), instance.fresh(), instance.fresh()];
    cardinality_constraint(&mut instance, &vars, None, 2);
    assert!(matches!(instance.solve(), SatOutcome::SAT(_)));
    instance.add_clause(vec![vars[2]]);
    assert!(matches!(instance.solve(), SatOutcome::SAT(_)));
    instance.add_clause(vec![vars[0]]);
    assert!(matches!(instance.solve(), SatOutcome::SAT(_)));
    instance.add_clause(vec![vars[1]]);
    assert!(matches!(instance.solve(), SatOutcome::UNSAT));
  }

  #[test]
  fn test_vacuous_cardinality_constraint() {
    let mut instance = SatInstance::new(DEFAULT_SOLVER);
    let vars = vec![instance.fresh(), instance.fresh(), instance.fresh()];
    cardinality_constraint(&mut instance, &vars, None, 5);
    assert!(matches!(instance.solve(), SatOutcome::SAT(_)));
  }

  #[test]
  fn test_minimize() {
    let solver = DEFAULT_SOLVER;
    let sop = SumOfProducts(vec![vec![1], vec![2], vec![1, 2]]);
    for (limit, has_solution) in [(3, true), (2, true), (1, false)] {
      assert_eq!(
        program_search::<SumOfProducts, SumOfProducts>(
          solver,
          &sop,
          &SumOfProductsResourcesSpec {
            input_count: 2,
            term_limit:  limit,
          },
          |_| ()
        )
        .is_some(),
        has_solution,
      );
    }
  }

  #[test]
  fn test_all_solvers() {
    //assert!(program_search(SatSolver::External(&["cryptominisat"]), &[vec![1], vec![-1]], 1).is_some());
    //assert!(program_search(SatSolver::External(&["glucose", "-model"]), &[vec![1], vec![-1]], 1).is_some());
    //assert!(program_search(SatSolver::External(&["kissat"]), &[vec![1], vec![-1]], 1).is_some());
    //assert!(program_search(SatSolver::External(&["cadical"]), &[vec![1], vec![-1]], 1).is_some());
    assert!(program_search::<SumOfProducts, SumOfProducts>(
      SatSolver::Varisat,
      &SumOfProducts(vec![vec![1], vec![-1]]),
      &SumOfProductsResourcesSpec {
        input_count: 1,
        term_limit:  1,
      },
      |_| (),
    )
    .is_some());
    assert!(program_search::<SumOfProducts, SumOfProducts>(
      SatSolver::Splr,
      &SumOfProducts(vec![vec![1], vec![-1]]),
      &SumOfProductsResourcesSpec {
        input_count: 1,
        term_limit:  1,
      },
      |_| ()
    )
    .is_some());
  }
}
