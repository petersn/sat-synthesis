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

  let solver = SatSolver::External(&["cryptominisat"]);

  let mut output_file = std::fs::File::create("best_circuits.txt").unwrap();

  for input_count in 2..=15usize {
    let mut best_program_and_gate_count = None;
    let mut bound_lo = input_count.saturating_sub(1);
    let mut bound_hi = input_count * 2;
    while bound_lo < bound_hi {
      let start_time = std::time::Instant::now();
      let test_value = (bound_lo + bound_hi) / 2;
      println!("\x1b[92mTesting\x1b[0m input_count = {} with gate_count = {}   (lo={}, hi={})", input_count, test_value, bound_lo, bound_hi);
      let r = hamming_weight_search(solver, input_count, test_value);

      match (&r, &best_program_and_gate_count) {
        (Some(program), Some((_, best_gate_count))) if test_value < *best_gate_count => {
          best_program_and_gate_count = Some((program.clone(), test_value));
        }
        (Some(program), None) => {
          best_program_and_gate_count = Some((program.clone(), test_value));
        }
        _ => {}
      }

      let elapsed = start_time.elapsed();
      println!("Solver: {:?} finished in {:?}", solver, elapsed);
      match r {
        Some(program) => {
          println!("\x1b[93mProgram with {} gates:\x1b[0m", test_value);
          println!("{}", program.pretty_print());
          bound_hi = test_value;
        }
        None => {
          println!("\x1b[93mNo solution exists for {} gates.\x1b[0m", test_value);
          bound_lo = test_value + 1;
        }
      }
    }
    println!("\x1b[91mFinal gate count\x1b[0m: input_count = {}, gate_count = {}", input_count, bound_lo);

    if let Some((best_program, best_gate_count)) = best_program_and_gate_count {
      use std::io::Write;
      writeln!(output_file, "===== input_count = {}, gate_count = {} =====", input_count, best_gate_count).unwrap();
      writeln!(output_file, "{}\n", best_program.pretty_print()).unwrap();
      output_file.flush().unwrap();
    }

    // // Launch a thread for each solver.
    // let handles: Vec<_> = solver_list
    //   .iter()
    //   .map(|solver| {
    //     let solver = *solver;
    //     std::thread::spawn(move || {
    //       let start_time = std::time::Instant::now();
    //       // let r = hamming_weight_search(solver, 15, 21);
    //       let r = hamming_weight_search(solver, input_count, gate_count);
    //       let elapsed = start_time.elapsed();
    //       println!("Solver: {:?} finished in {:?}", solver, elapsed);
    //       match r {
    //         Some(program) => {
    //           println!("Program:");
    //           println!("{}", program.pretty_print());
    //         }
    //         None => println!("No solution exists."),
    //       }
    //     })
    //   })
    //   .collect();
    // // Wait for all threads to finish.
    // for handle in handles {
    //   handle.join().unwrap();
    // }
  }
}
