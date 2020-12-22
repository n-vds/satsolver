use std::io::Write;

use crate::cnf::{Clause, Cnf};

pub fn read_cnf_interactive() -> Cnf {
    println!("New CNF formula:");

    let mut phi = Cnf {
        clauses: Vec::new(),
    };

    'clausesLoop: for i in 1.. {
        print!("  Cls {:02}: ", i);
        std::io::stdout().flush().unwrap();

        let mut line = String::new();
        std::io::stdin().read_line(&mut line).unwrap();
        let line = line.trim();

        if line.is_empty() {
            break;
        }

        let mut clause = Clause::new();

        let literals = line.split_ascii_whitespace().map(|var| var.parse::<i64>());

        for literal in literals {
            match literal {
                Ok(0) => {
                    println!("Error: '0' is not a valid variable!");
                    continue 'clausesLoop;
                },
                Ok(var) if var < 0 => clause.add_negative(-var as u32),
                Ok(var) if var > 0 => clause.add_positive(var as u32),
                Err(_) => {
                    println!("Error: Only input numbers for variables");
                    continue 'clausesLoop;
                },
                _ => unreachable!()
            }
        }

        phi.clauses.push(clause);
    }

    phi
}
