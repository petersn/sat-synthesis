#[path = "src/standard_cells.rs"]
mod standard_cells;

use crate::standard_cells::{CombinationalGateType, BITS_FOR_GATE_TYPE, MAXIMUM_GATE_COST};

fn format_cnf(name: &str, input_count: usize, output_count: usize, cnf: &Vec<Vec<i32>>) -> String {
  let mut output = format!(
    "StaticCnf {{ name: {:?}, input_count: {}, output_count: {}, cnf: &[\n",
    name, input_count, output_count,
  );
  for clause in cnf {
    output.push_str(&format!(
      "    &[{}],\n",
      clause.iter().map(|l| l.to_string()).collect::<Vec<_>>().join(", ")
    ));
  }
  output.push_str("  ] }");
  output
}

pub fn generate() -> String {
  let mut output = String::new();
  output.push_str(
    r#"pub struct StaticCnf {
  pub name: &'static str,
  pub input_count: usize,
  pub output_count: usize,
  pub cnf: &'static [&'static [i32]],
}
"#,
  );

  const READ_WIRES_COUNT: usize = 10;
  output.push_str(&format!("pub static READ_WIRES: [StaticCnf; {}] = [\n", READ_WIRES_COUNT));
  // We now figure out CNF for reading from sets of wires.
  for wire_count in 0..READ_WIRES_COUNT {
    // Add one to wire count, for the constant zero wire.
    let address_bits = (1usize + wire_count).next_power_of_two().trailing_zeros() as usize;
    // The first bit is negation, then address, then the wires we're muxing over.
    let input_bits = 1 + address_bits + wire_count;
    let cnf = autosat::convert_to_cnf(input_bits, 1, |inp| {
      let negation = inp[0];
      let mut address = 0;
      for (i, b) in inp[1..1 + address_bits].iter().enumerate() {
        address |= (*b as usize) << i;
      }
      if address > wire_count {
        // FIXME: Is DontCare or ImpossibleInputs what I want here?
        return autosat::SatOutput::ImpossibleInputs;
      }
      let indexed = match address == 0 {
        true => false,
        false => inp[1 + address_bits + (address - 1)],
      };
      return autosat::SatOutput::Bits(vec![negation ^ indexed]);
    });
    output.push_str(&format!(
      "  // {} wires ({} address lines)\n  {},\n",
      wire_count,
      address_bits,
      format_cnf(&format!("READ_WIRES_{}", wire_count), input_bits, 1, &cnf)
    ));
  }
  output.push_str("];\n");

  let mut add_function =
    |name: &str, input_count: usize, output_count: usize, function: fn(&[bool]) -> Vec<bool>| {
      let cnf = autosat::convert_to_cnf(input_count, output_count, |inp| {
        let out = function(inp);
        autosat::SatOutput::Bits(out)
      });
      output.push_str(&format!(
        "pub static {}: StaticCnf = {};\n",
        name,
        format_cnf(name, input_count, output_count, &cnf)
      ));
    };

  add_function("EVALUATE_LUT", 8 + 3, 1, |inp| {
    let lut = &inp[..8];
    let inputs = &inp[8..];
    let mut address = 0;
    for (i, b) in inputs.iter().enumerate() {
      address |= (*b as usize) << i;
    }
    vec![lut[address]]
  });

  // add_function("EVALUATE_GATE", BITS_FOR_GATE_TYPE + 3, 1, |inp| {
  //   let gate = CombinationalGateType::from_bits(&inp[..BITS_FOR_GATE_TYPE]);
  //   let inputs = &inp[BITS_FOR_GATE_TYPE..];
  //   match gate {
  //     CombinationalGateType::NoGate => vec![false],
  //     CombinationalGateType::And2 => vec![inputs[0] & inputs[1]],
  //     CombinationalGateType::Or2 => vec![inputs[0] | inputs[1]],
  //     CombinationalGateType::Xor2 => vec![inputs[0] ^ inputs[1]],
  //   }
  // });

  // add_function("DECODE_COST", BITS_FOR_GATE_TYPE, MAXIMUM_GATE_COST, |inp| {
  //   let gate = CombinationalGateType::from_bits(inp);
  //   let cost = gate.get_cost();
  //   // Return cost trues, and MAXIMUM_GATE_COST - cost falses.
  //   let mut out = vec![true; cost];
  //   out.resize(MAXIMUM_GATE_COST, false);
  //   out
  // });

  output
}

fn main() {
  let tables_source = generate();
  println!("{}", tables_source);

  let out_dir = std::env::var_os("OUT_DIR").unwrap();
  let dest_path = std::path::Path::new(&out_dir).join("sat_tables_generated.rs");
  std::fs::write(&dest_path, tables_source).unwrap();

  println!("cargo:rerun-if-changed=build.rs");
}
