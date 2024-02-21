use std::collections::HashMap;

use super::{sat_tables, ConfigVars, ProgramSynthesis, SatInstance, SatLiteral};

#[derive(Debug, Clone)]
pub struct VpternlogGate {
  pub lut: [bool; 8],
  pub input_indices: [usize; 3],
}

#[derive(Debug, Clone)]
pub struct VpternlogProgram {
  pub input_count: usize,
  pub output_count: usize,
  pub gates: Vec<VpternlogGate>,
  pub final_selection: Vec<usize>,
}

impl VpternlogProgram {
  pub fn pretty_print(&self) -> String {
    let mut s = String::new();
    let format_index = |index: usize| if index < self.input_count {
      format!("x{}", index)
    } else {
      format!("t{}", index - self.input_count)
    };
    let format_lut = |lut: &[bool; 8]| {
      let value = lut.iter().enumerate().map(|(i, &b)| if b { 1 << i } else { 0 }).sum::<usize>();
      format!("0x{:02x}", value)
    };
    s.push_str(&format!("x0, ... x{} = input bits\n", self.input_count - 1));
    for (i, gate) in self.gates.iter().enumerate() {
      s.push_str(&format!("t{} = vpternlog({}, {}, {}, {})\n", i,
        format_index(gate.input_indices[0]),
        format_index(gate.input_indices[1]),
        format_index(gate.input_indices[2]),
        format_lut(&gate.lut),
      ));
    }
    s.push_str("output:");
    for (i, &final_selection) in self.final_selection.iter().enumerate() {
      if i != 0 {
        s.push_str(" +");
      }
      s.push_str(&format!(" {}*{}", (1 << i), format_index(final_selection)));
    }
    s
  }
}

#[derive(Debug)]
pub struct VpternlogResourcesSpec {
  pub input_count: usize,
  pub output_count: usize,
  pub gate_count:  usize,
  pub break_symmetry_15: bool,
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

pub fn mux(
  instance: &mut SatInstance, false_lit: SatLiteral, address: &[SatLiteral], inputs: &[SatLiteral],
) -> SatLiteral {
  if inputs.len() < sat_tables::READ_WIRES_NO_OOB.len() {
    let output = instance.fresh();
    let all_inputs: Vec<_> = [address, inputs].concat();
    instance.add_precompiled(&sat_tables::READ_WIRES_NO_OOB[inputs.len()], &all_inputs, &[output]);
    output
  } else {
    // Otherwise, we need to use a cascade of multiplexers.
    let sqrt_input_count = (inputs.len() as f64).sqrt() as usize;
    let split_size = sqrt_input_count.next_power_of_two().min(8).min(inputs.len());
    // println!("n: {}, split_size: {}", inputs.len(), split_size);
    assert!(0 < split_size);
    assert!(split_size < inputs.len());
    let (split_addr, remaining_addr) = address.split_at(split_size.ilog2() as usize);
    // Use first few bits of the address to perform the initial muxing.
    let mut chunk_muxes = Vec::new();
    for chunk in inputs.chunks(split_size) {
      let mut chunk = chunk.to_vec();
      while chunk.len() < split_size {
        chunk.push(false_lit);
      }
      let chunk_output = mux(instance, false_lit, &split_addr, &chunk);
      chunk_muxes.push(chunk_output);
    }
    // Use the remaining bits of the address to perform the final muxing.
    mux(instance, false_lit, remaining_addr, &chunk_muxes)
  }
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
    if resources_spec.break_symmetry_15 {
      // We make the first five gates apply to triplets of input bits.
      for gate in 0..5 {
        for i in 0..3 {
          let x = gate * 3 + i;
          for (j, &lit) in gates[gate].input_indices[i].iter().enumerate() {
            if (x >> j) & 1 == 1 {
              instance.add_clause(vec![lit]);
            } else {
              instance.add_clause(vec![-lit]);
            }
          }
        }
      }
      // Force the first five gates to have the same LUT.
      for gate in 1..5 {
        for i in 0..8 {
          instance.add_clause(vec![gates[0].lut[i], -gates[gate].lut[i]]);
          instance.add_clause(vec![-gates[0].lut[i], gates[gate].lut[i]]);
        }
      }
    }
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
      let x0 = values.get(gate.input_indices[0]).copied().unwrap_or(false);
      let x1 = values.get(gate.input_indices[1]).copied().unwrap_or(false);
      let x2 = values.get(gate.input_indices[2]).copied().unwrap_or(false);
      let lut_index = 4 * (x0 as usize) + 2 * (x1 as usize) + (x2 as usize);
      values.push(gate.lut[lut_index]);
    }
    (0..self.output_count).map(|i| values.get(self.final_selection[i]).copied().unwrap_or(false)).collect()
  }

  fn build_fpga(
    instance: &mut SatInstance,
    configuration_vars: &ConfigVars<Self::ConfigVarsData>,
    input_vars: &[SatLiteral],
    output_vars: &[SatLiteral],
  ) {
    assert_eq!(input_vars.len(), configuration_vars.input_count);
    assert_eq!(output_vars.len(), configuration_vars.output_count);
    let false_lit = instance.fresh();
    instance.add_clause(vec![-false_lit]);
    let mut wires = input_vars.to_vec();
    for gate in &configuration_vars.config_vars_data.gates {
      let lut_inputs = [
        mux(instance, false_lit, &gate.input_indices[2], &wires),
        mux(instance, false_lit, &gate.input_indices[1], &wires),
        mux(instance, false_lit, &gate.input_indices[0], &wires),
      ];
      let lut_output = mux(instance, false_lit, &lut_inputs, &gate.lut);
      wires.push(lut_output);
    }
    for i in 0..configuration_vars.output_count {
      let final_bit = mux(instance, false_lit, &configuration_vars.config_vars_data.final_selection[i], &wires);
      instance.add_clause(vec![final_bit, -output_vars[i]]);
      instance.add_clause(vec![-final_bit, output_vars[i]]);
    }
  }
}
