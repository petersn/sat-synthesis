use std::collections::HashMap;

use super::{sat_tables, ConfigVars, ProgramSynthesis, SatInstance, SatLiteral};

#[derive(Debug)]
pub struct VpternlogGate {
  pub lut: [bool; 8],
  pub input_indices: [usize; 3],
}

#[derive(Debug)]
pub struct VpternlogProgram {
  pub input_count: usize,
  pub output_count: usize,
  pub gates: Vec<VpternlogGate>,
  pub final_selection: Vec<usize>,
}

#[derive(Debug)]
pub struct VpternlogResourcesSpec {
  pub input_count: usize,
  pub output_count: usize,
  pub gate_count:  usize,
}

pub struct VpternlogGateConfigVars {
  pub lut: [SatLiteral; 8],
  pub input_indices: [Vec<SatLiteral>; 3],
}

pub struct VpternlogConfigVars {
  pub gates: Vec<VpternlogGateConfigVars>,
  pub final_selection: Vec<Vec<SatLiteral>>,
}

pub fn bits_for_index(options: usize) -> usize {
  options.next_power_of_two().trailing_zeros() as usize
}

impl ProgramSynthesis for VpternlogProgram {
  type ProgramResourcesSpec = VpternlogResourcesSpec;
  type ConfigVarsData = VpternlogConfigVars;

  fn create_configuration_vars(
    instance: &mut SatInstance,
    resources_spec: &Self::ProgramResourcesSpec,
  ) -> ConfigVars<Self::ConfigVarsData> {
    let mut gates = Vec::new();
    let mut wire_count = resources_spec.input_count;
    for _ in 0..resources_spec.gate_count {
      let lut = instance.n_fresh(8);
      let input_indices = [
        instance.n_fresh(bits_for_index(wire_count)),
        instance.n_fresh(bits_for_index(wire_count)),
        instance.n_fresh(bits_for_index(wire_count)),
      ];
      gates.push(VpternlogGateConfigVars {
        lut: lut.try_into().unwrap(),
        input_indices,
      });
      wire_count += 1;
    }
    let final_selection = (0..resources_spec.output_count)
      .map(|_| instance.n_fresh(bits_for_index(wire_count))).collect();
    ConfigVars {
      config_vars_data: VpternlogConfigVars {
        gates,
        final_selection,
      },
      input_count: resources_spec.input_count,
      output_count: resources_spec.output_count,
    }
  }

  fn program_to_bits(
    &self,
    _instance: &mut SatInstance,
    false_lit: SatLiteral,
  ) -> ConfigVars<Self::ConfigVarsData> {
    let bool_to_lit = |b: bool| if b { -false_lit } else { false_lit };
    let number_to_bits = |number: usize, bits: usize| {
      assert!(number < 2usize.pow(bits as u32));
      (0..bits).map(|i| bool_to_lit((number >> i) & 1 == 1)).collect()
    };
    let mut config_vars_data = Vec::new();
    let mut wire_count = self.input_count;
    for gate in &self.gates {
      let mut lut = [0; 8];
      for (i, &b) in gate.lut.iter().enumerate() {
        lut[i] = bool_to_lit(b);
      }
      config_vars_data.push(VpternlogGateConfigVars {
        lut,
        input_indices: [
          number_to_bits(gate.input_indices[0], bits_for_index(wire_count)),
          number_to_bits(gate.input_indices[1], bits_for_index(wire_count)),
          number_to_bits(gate.input_indices[2], bits_for_index(wire_count)),
        ],
      });
      wire_count += 1;
    }
    let final_selection = self.final_selection.iter().map(|&wire_index| {
      number_to_bits(wire_index, bits_for_index(wire_count))
    }).collect();
    ConfigVars {
      config_vars_data: VpternlogConfigVars {
        gates: config_vars_data,
        final_selection,
      },
      input_count: self.input_count,
      output_count: self.output_count,
    }
  }

  fn decode_program(
    config: &ConfigVars<Self::ConfigVarsData>,
    model: &HashMap<SatLiteral, bool>,
  ) -> Self {
    let lit_to_bool = |lit: SatLiteral| model.get(&lit).copied().unwrap();
    let bits_to_number = |bits: &[SatLiteral]| {
      bits.iter()
        .enumerate()
        .map(|(i, &lit)| if lit_to_bool(lit) { 1 << i } else { 0 })
        .sum()
    };
    let mut gates = Vec::new();
    for gate in &config.config_vars_data.gates {
      let mut lut = [false; 8];
      for (i, &lit) in gate.lut.iter().enumerate() {
        lut[i] = lit_to_bool(lit);
      }
      let input_indices = [
        bits_to_number(&gate.input_indices[0]),
        bits_to_number(&gate.input_indices[1]),
        bits_to_number(&gate.input_indices[2]),
      ];
      gates.push(VpternlogGate { lut, input_indices });
    }
    let final_selection = config.config_vars_data.final_selection.iter().map(|bits| {
      bits_to_number(bits)
    }).collect();
    VpternlogProgram {
      input_count: config.input_count,
      output_count: config.output_count,
      gates,
      final_selection,
    }
  }

  fn enumerate_vars_in_config(config_vars: &ConfigVars<Self::ConfigVarsData>) -> Vec<SatLiteral> {
    let mut vars = Vec::new();
    for gate in &config_vars.config_vars_data.gates {
      vars.extend_from_slice(&gate.lut);
      for input_indices in &gate.input_indices {
        vars.extend_from_slice(input_indices);
      }
    }
    for final_selection in &config_vars.config_vars_data.final_selection {
      vars.extend_from_slice(final_selection);
    }
    vars
  }

  fn evaluate(&self, inputs: &[bool]) -> Vec<bool> {
    let mut values = inputs.to_vec();
    for gate in &self.gates {
      let x0 = values[gate.input_indices[0]];
      let x1 = values[gate.input_indices[1]];
      let x2 = values[gate.input_indices[2]];
      let lut_index = (x0 as usize) + 2 * (x1 as usize) + 4 * (x2 as usize);
      values.push(gate.lut[lut_index]);
    }
    (0..self.output_count).map(|i| values[self.final_selection[i]]).collect()
  }

  fn build_fpga(
    instance: &mut SatInstance,
    configuration_vars: &ConfigVars<Self::ConfigVarsData>,
    input_vars: &[SatLiteral],
    output_vars: &[SatLiteral],
  ) {
    assert_eq!(input_vars.len(), configuration_vars.input_count);
    assert_eq!(output_vars.len(), configuration_vars.output_count);
    fn mux(
      instance: &mut SatInstance, address: &[SatLiteral], inputs: &[SatLiteral],
    ) -> SatLiteral {
      let output = instance.fresh();
      let all_inputs: Vec<_> = [address, inputs].concat();
      instance.add_precompiled(&sat_tables::READ_WIRES[inputs.len()], &all_inputs, &[output]);
      output
    }
    let mut wires = input_vars.to_vec();
    for gate in &configuration_vars.config_vars_data.gates {
      let lut_inputs = [
        mux(instance, &gate.input_indices[0], &wires),
        mux(instance, &gate.input_indices[1], &wires),
        mux(instance, &gate.input_indices[2], &wires),
      ];
      let lut_output = mux(instance, &lut_inputs, &gate.lut);
      wires.push(lut_output);
    }
    for i in 0..configuration_vars.output_count {
      let final_bit = mux(instance, &configuration_vars.config_vars_data.final_selection[i], &wires);
      instance.add_clause(vec![final_bit, -output_vars[i]]);
      instance.add_clause(vec![-final_bit, output_vars[i]]);
    }
  }
}
