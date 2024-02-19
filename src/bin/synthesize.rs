use sat_synthesis::{program_search, sum_of_products::SumOfProducts, vpternlog::{VpternlogProgram, VpternlogResourcesSpec}, SatSolver};

fn main() {
  let r = program_search::<SumOfProducts, VpternlogProgram>(
    SatSolver::Varisat,
    &SumOfProducts(vec![vec![1], vec![-1]]),
    &VpternlogResourcesSpec {
      input_count: 1,
      output_count: 1,
      gate_count: 1,
    },
    |msg| {
      println!("{}", msg);
    },
  );
  println!("{:#?}", r);
}
