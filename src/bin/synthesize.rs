use sat_synthesis::{lookup_table_search, vpternlog::{VpternlogProgram, VpternlogResourcesSpec}, SatSolver};

fn hamming_weight_search(n: usize, gate_count: usize) -> Option<VpternlogProgram> {
  let resources_spec = VpternlogResourcesSpec {
    input_count: n,
    output_count: (n + 1).next_power_of_two().trailing_zeros() as usize,
    gate_count,
  };
  println!("resources_spec: {:#?}", resources_spec);
  lookup_table_search::<VpternlogProgram>(
    SatSolver::External(()),
    |bits| {
      let count_set = bits.iter().filter(|&&b| b).count();
      let output_length = (bits.len() + 1).next_power_of_two().trailing_zeros() as usize;
      (0..output_length).map(|i| count_set & (1 << i) != 0).collect()
    },
    &resources_spec,
    |msg| {
      println!("{}", msg);
    },
  )
}

fn main() {
  let r = hamming_weight_search(5, 5);
  println!("{:#?}", r);
}
