use sat_synthesis::{lookup_table_search, vpternlog::{VpternlogProgram, VpternlogResourcesSpec}, SatSolver};

fn hamming_weight_search(solver: SatSolver, n: usize, gate_count: usize) -> Option<VpternlogProgram> {
  let resources_spec = VpternlogResourcesSpec {
    input_count: n,
    output_count: (n + 1).next_power_of_two().trailing_zeros() as usize,
    gate_count,
  };
  // println!("resources_spec: {:#?}", resources_spec);
  lookup_table_search::<VpternlogProgram>(
    solver,
    // SatSolver::External(&["glucose", "-model"]),
    // SatSolver::Varisat,
    |bits| {
      let count_set = bits.iter().filter(|&&b| b).count();
      let output_length = (bits.len() + 1).next_power_of_two().trailing_zeros() as usize;
      (0..output_length).map(|i| count_set & (1 << i) != 0).collect()
    },
    &resources_spec,
    |msg| {
      println!("[{:?}] {}", solver, msg);
    },
  )
}

fn main() {
  let solver_list = [
    // SatSolver::External(&["glucose", "-model"]),
    SatSolver::External(&["cryptominisat"]),
    // SatSolver::External(&["kissat"]),
    // SatSolver::Varisat,
    // SatSolver::Splr,
  ];
  // Launch a thread for each solver.
  let handles: Vec<_> = solver_list
    .iter()
    .map(|solver| {
      let solver = *solver;
      std::thread::spawn(move || {
        let r = hamming_weight_search(solver, 15, 21);
        println!("Solver: {:?} finished: {:#?}", solver, r);
      })
    })
    .collect();
  // Wait for all threads to finish.
  for handle in handles {
    handle.join().unwrap();
  }
}
