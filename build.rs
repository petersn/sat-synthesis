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

  const READ_WIRES_COUNT: usize = 2;

  for oob_gives_false in [false, true] {
    let suffix = match oob_gives_false {
      false => "NO_OOB",
      true => "OOB_GIVES_FALSE",
    };
    output.push_str(&format!("pub static READ_WIRES_{}: [StaticCnf; {}] = [\n", suffix, READ_WIRES_COUNT + 1));
    // We now figure out CNF for reading from sets of wires.
    for wire_count in 0..=READ_WIRES_COUNT {
      println!("------------- Generating CNF for reading from {} wires", wire_count);
      let address_bits = wire_count.next_power_of_two().trailing_zeros() as usize;
      let input_bits = address_bits + wire_count;
      let cnf = autosat::convert_to_cnf(input_bits, 1, |inp| {
        let mut address = 0;
        for (i, b) in inp[..address_bits].iter().enumerate() {
          address |= (*b as usize) << i;
        }
        if address >= wire_count {
          if oob_gives_false {
            return autosat::SatOutput::Bits(vec![false]);
          }
          // FIXME: Is DontCare or ImpossibleInputs what I want here?
          return autosat::SatOutput::ImpossibleInputs;
        }
        let result = inp[address_bits + address];
        return autosat::SatOutput::Bits(vec![result]);
      });
      println!("CNF: {:?}", cnf);
      output.push_str(&format!(
        "  // {} wires ({} address lines)\n  {},\n",
        wire_count,
        address_bits,
        format_cnf(&format!("READ_WIRES_{}_{}", suffix, wire_count), input_bits, 1, &cnf)
      ));
    }
    output.push_str("];\n");
  }

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

  add_function("FULL_ADDER", 3, 2, |inp| {
    let a = inp[0];
    let b = inp[1];
    let c = inp[2];
    let s = a ^ b ^ c;
    let c_out = (a & b) | (b & c) | (a & c);
    vec![s, c_out]
  });

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
