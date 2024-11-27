use clap::Parser;
use std::path::PathBuf;
use std::sync::Mutex;
use sat_synthesis::{
  lookup_table_search,
  nand::{NandProgram, NandResourcesSpec},
  vpternlog::{VpternlogProgram, VpternlogResourcesSpec},
  CegisSettings,
  SatSolver,
};

fn hamming_weight_search(solver: SatSolver, args: &Args, n: usize, gate_count: usize) -> Option<VpternlogProgram> {
  panic!("Not implemented");
  let resources_spec = VpternlogResourcesSpec {
    input_count: n,
    output_count: (n + 1).next_power_of_two().trailing_zeros() as usize,
    gate_count,
    break_symmetry_15: args.break_symmetry_15,
  };
  // println!("resources_spec: {:#?}", resources_spec);
  lookup_table_search::<VpternlogProgram>(
    solver,
    CegisSettings {
      counter_examples_per_step: args.counter_examples_per_step,
    },
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

fn nand_search(solver: SatSolver, args: &Args, n: usize, gate_count: usize) -> Option<NandProgram> {
  let resources_spec = NandResourcesSpec {
    input_count: n,
    output_count: 1,
    gate_count,
  };
  // println!("resources_spec: {:#?}", resources_spec);
  lookup_table_search::<NandProgram>(
    solver,
    CegisSettings {
      counter_examples_per_step: args.counter_examples_per_step,
    },
    // SatSolver::External(&["glucose", "-model"]),
    // SatSolver::Varisat,
    |bits| {
      let value = bits.iter().enumerate().map(|(i, &b)| if b { 1 << i } else { 0 }).sum::<usize>();
      let r = vec![args.lut & (1 << value) != 0];
      // println!("lut = 0x{:02x}, value = 0x{:02x} (bits = {:?}), r = {:?}", lut, value, bits, r);
      r
      // let count_set = bits.iter().filter(|&&b| b).count();
      // let output_length = (bits.len() + 1).next_power_of_two().trailing_zeros() as usize;
      // (0..output_length).map(|i| count_set & (1 << i) != 0).collect()
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

  #[arg(short, long, default_value = "2")]
  start_size: usize,

  #[arg(short, long)]
  break_symmetry_15: bool,

  #[arg(short, long, default_value = "0")]
  lut: u64,

  #[arg(short, long, default_value = "1")]
  input_count: usize,
}

fn old_main() {
  let args: Args = Args::parse();

  let solver = SatSolver::External(&["cryptominisat5"]);
  let mut output_file = std::fs::File::create(&args.output_file).unwrap();

  // for input_count in args.start_size.. {
  for input_count in [args.input_count] {
    let input_count_search_start_time = std::time::Instant::now();
    // let mut found_lower = false;
    let mut found_upper = false;
    let mut best_program_and_gate_count = None;
    let mut bound_lo = 0;
    let mut bound_hi = 5 + 2 * input_count;
    while bound_lo < bound_hi {
      let start_time = std::time::Instant::now();
      let test_value = (bound_lo + bound_hi) / 2;
      println!("\x1b[92mTesting\x1b[0m input_count = {} with gate_count = {}   (lo={}, hi={})", input_count, test_value, bound_lo, bound_hi);
      let r = nand_search(solver, &args, input_count, test_value);

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
          // found_lower = true;
        }
      }
    }
    println!("\x1b[91mFinal gate count\x1b[0m: input_count = {}, gate_count = {}", input_count, bound_lo);

    if let Some((best_program, best_gate_count)) = best_program_and_gate_count {
      let elapsed = input_count_search_start_time.elapsed();
      use std::io::Write;
      writeln!(output_file, "===== input_count = {}, gate_count = {}, lut = {:04x} ===== (found in {:?})", input_count, best_gate_count, args.lut, elapsed).unwrap();
      writeln!(output_file, "{}\n", best_program.pretty_print()).unwrap();
      output_file.flush().unwrap();
    }

    // assert!(found_lower);
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

fn search(lut: u64, output_file_mutex: &Mutex<std::fs::File>) {
  let solver = SatSolver::External(&["cryptominisat5"]);
  let input_count = 4;
  let args = Args {
    output_file: PathBuf::from("this string not used"),
    counter_examples_per_step: usize::MAX,
    start_size: 0,
    break_symmetry_15: false,
    lut,
    input_count,
  };
  let input_count_search_start_time = std::time::Instant::now();
  // let mut found_lower = false;
  let mut found_upper = false;
  let mut best_program_and_gate_count = None;
  let mut bound_lo = 0;
  let mut bound_hi = 12;
  while bound_lo < bound_hi {
    let start_time = std::time::Instant::now();
    let test_value = (bound_lo + bound_hi) / 2;
    println!("\x1b[92mTesting\x1b[0m input_count = {} with gate_count = {}   (lo={}, hi={})", input_count, test_value, bound_lo, bound_hi);
    let r = nand_search(solver, &args, input_count, test_value);

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
        // found_lower = true;
      }
    }
  }
  println!("\x1b[91mFinal gate count\x1b[0m: input_count = {}, gate_count = {}", input_count, bound_lo);

  if let Some((best_program, best_gate_count)) = best_program_and_gate_count {
    let elapsed = input_count_search_start_time.elapsed();
    use std::io::Write;
    let mut output_file = output_file_mutex.lock().unwrap();
    let pretty = best_program.pretty_print();
    let results = serde_json::json!({
      "input_count": input_count,
      "gate_count": best_gate_count,
      "lut": lut,
      "elapsed": elapsed.as_secs_f64(),
      "pretty": pretty,
      "gates": best_program.gates.iter().map(|gate| &gate.input_indices).collect::<Vec<_>>(),
      "final_selection": best_program.final_selection,
      "allow_constant_inputs": sat_synthesis::nand::ALLOW_CONSTANT_INPUTS,
    });
    writeln!(output_file, "JSON: {}", serde_json::to_string(&results).unwrap()).unwrap();
    writeln!(output_file, "===== input_count = {}, gate_count = {}, lut = {:04x} ===== (found in {:?})", input_count, best_gate_count, args.lut, elapsed).unwrap();
    writeln!(output_file, "{}\n", pretty).unwrap();
    output_file.flush().unwrap();
  }

  // assert!(found_lower);
  assert!(found_upper);
}

fn main() {
  use rand::seq::SliceRandom;
  let mut numbers: Vec<u64> = (0..1 << 16).collect();
  numbers.shuffle(&mut rand::thread_rng());
  let numbers: Mutex<Vec<u64>> = Mutex::new(numbers);
  let output_file = Mutex::new(std::fs::File::create("results.txt").unwrap());
  let thread_count = std::thread::available_parallelism().unwrap().get();
  println!("thread_count = {}", thread_count);
  std::thread::scope(|s| {
    for _ in 0..thread_count {
      s.spawn(|| {
        loop {
          let mut numbers = numbers.lock().unwrap();
          if numbers.is_empty() {
            break;
          }
          let n = numbers.pop().unwrap();
          drop(numbers);
          println!("n = {:04x}", n);
          search(n, &output_file);
        }
      });
    }
  });
  println!("Done");
}
