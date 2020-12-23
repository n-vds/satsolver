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
                }
                Ok(var) if var < 0 => clause.add_negative(-var as u32),
                Ok(var) if var > 0 => clause.add_positive(var as u32),
                Err(_) => {
                    println!("Error: Only input numbers for variables");
                    continue 'clausesLoop;
                }
                _ => unreachable!(),
            }
        }

        phi.clauses.push(clause);
    }

    phi
}

pub fn parse_cnf_from_str(input: &str) -> Option<Cnf> {
    let mut cnf = Cnf::new();

    for line_clause in input
        .lines()
        .map(|line| line.trim())
        .filter(|&line| !line.is_empty())
    {
        if line_clause == "false" {
            cnf.clauses.push(Clause::new());
            continue;
        }

        let parts = line_clause
            .split_ascii_whitespace()
            .map(|it| it.trim())
            .filter(|it| !it.is_empty())
            .map(|part| part.parse::<i64>())
            .collect::<Result<Vec<i64>, _>>()
            .ok()?;

        let mut clause = Clause::new();
        for part in parts {
            if part < 0 {
                clause.add_negative(-part as u32);
            } else if part > 0 {
                clause.add_positive(part as u32);
            } else {
                return None;
            }
        }
        cnf.clauses.push(clause);
    }

    Some(cnf)
}

#[cfg(test)]
mod tests {
    use crate::cnf::{Clause, Cnf};

    use super::parse_cnf_from_str;

    #[test]
    fn test_parse_empty_formula() {
        assert_eq!(parse_cnf_from_str(""), Some(Cnf::new()));
        assert_eq!(parse_cnf_from_str("    "), Some(Cnf::new()));
    }

    #[test]
    fn test_parse_empty_clauses() {
        assert_eq!(
            parse_cnf_from_str("false\n"),
            Some(Cnf::new_with(vec![Clause::new()]))
        );
        assert_eq!(
            parse_cnf_from_str("1\nfalse\n2"),
            Some(Cnf::new_with(vec![
                {
                    let mut cls = Clause::new();
                    cls.add_positive(1);
                    cls
                },
                Clause::new(),
                {
                    let mut cls = Clause::new();
                    cls.add_positive(2);
                    cls
                }
            ]))
        );
    }

    #[test]
    fn test_parse() {
        let (mut cls0, mut cls1, mut cls2) = (Clause::new(), Clause::new(), Clause::new());
        cls0.add_positive(1);
        cls0.add_positive(2);
        cls0.add_positive(4);
        cls0.add_negative(3);
        cls0.add_negative(5);
        cls0.add_negative(6);

        cls1.add_negative(7);
        cls1.add_negative(8);
        cls1.add_negative(9);

        cls2.add_positive(10);
        cls2.add_negative(11);
        cls2.add_positive(12);

        assert_eq!(
            parse_cnf_from_str(
                "1 2 -3 4 -5 -6
        -7 -8 -9
        10 -11 12"
            ),
            Some(Cnf::new_with(vec![cls0, cls1, cls2]))
        );
    }
}
