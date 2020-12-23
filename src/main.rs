mod assignment;
mod cnf;
mod input;
mod satsolve;

use cnf::{Clause, Cnf};

fn main() {
    println!(" S A T ");
    let phi = input::read_cnf_interactive();
    println!("Got phi = {:?}", phi);
    println!("Calculating satisfiability....");
    let satisfiable = satsolve::is_satisfiable(&phi);
    println!(
        "phi is {}satisfiable",
        if satisfiable { "" } else { "not " }
    );
}
