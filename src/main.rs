mod cnf;

use cnf::{Cnf, Clause};

fn main() {
    let mut phi = Cnf {
        clauses: vec![Clause::new(), Clause::new()],
    };

    phi.clauses[0].add_positive(2);
    phi.clauses[1].add_positive(4);
    phi.clauses[1].add_positive(5);

    println!("Hello, world!");
    println!("CNF: {:?}", phi);
}
