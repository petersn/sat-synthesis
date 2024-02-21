use clap::Parser;
use std::path::PathBuf;
use sat_synthesis::{lookup_table_search, vpternlog::{VpternlogProgram, VpternlogResourcesSpec}, SatSolver, CegisSettings};

fn hamming_weight_search(solver: SatSolver, settings: CegisSettings, n: usize, gate_count: usize) -> Option<VpternlogProgram> {
  let resources_spec = VpternlogResourcesSpec {
    input_count: n,
    output_count: (n + 1).next_power_of_two().trailing_zeros() as usize,
    gate_count,
  };
  // println!("resources_spec: {:#?}", resources_spec);
  lookup_table_search::<VpternlogProgram>(
    solver,
    settings,
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

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Args {
  #[arg(short, long, default_value = "best_circuits.txt")]
  output_file: PathBuf,

  #[arg(short, long, default_value = "10")]
  counter_examples_per_step: usize,
}

fn main() {
  let args: Args = Args::parse();

  let solver = SatSolver::External(&["cryptominisat5"]);
  let settings = CegisSettings {
    counter_examples_per_step: args.counter_examples_per_step,
  };
  let mut output_file = std::fs::File::create(&args.output_file).unwrap();

  for input_count in 2.. {
    let input_count_search_start_time = std::time::Instant::now();
    let mut found_lower = false;
    let mut found_upper = false;
    let mut best_program_and_gate_count = None;
    let mut bound_lo = match input_count {
      1 => 0,
      2 => 1,
      3 => 1,
      _ => 2,
    };
    let mut bound_hi = input_count * 2;
    while bound_lo < bound_hi {
      let start_time = std::time::Instant::now();
      let test_value = (bound_lo + bound_hi) / 2;
      println!("\x1b[92mTesting\x1b[0m input_count = {} with gate_count = {}   (lo={}, hi={})", input_count, test_value, bound_lo, bound_hi);
      let r = hamming_weight_search(solver, settings, input_count, test_value);

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
          found_upper = true;
        }
        None => {
          println!("\x1b[93mNo solution exists for {} gates.\x1b[0m", test_value);
          bound_lo = test_value + 1;
          found_lower = true;
        }
      }
    }
    println!("\x1b[91mFinal gate count\x1b[0m: input_count = {}, gate_count = {}", input_count, bound_lo);

    if let Some((best_program, best_gate_count)) = best_program_and_gate_count {
      let elapsed = input_count_search_start_time.elapsed();
      use std::io::Write;
      writeln!(output_file, "===== input_count = {}, gate_count = {} ===== (found in {:?})", input_count, best_gate_count, elapsed).unwrap();
      writeln!(output_file, "{}\n", best_program.pretty_print()).unwrap();
      output_file.flush().unwrap();
    }

    assert!(found_lower);
    assert!(found_upper);

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
