mod cnf;
mod input;

use cnf::{Cnf, Clause};

fn main() {
    println!(" S A T ");
    let phi = input::read_cnf_interactive();
    println!("Got {:?}", phi);
}
