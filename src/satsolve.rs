use crate::{
    assignment::Assignment,
    cnf::{Cnf, Var},
};
#[derive(Debug, PartialEq)]
struct DecisionLevel {
    assignment: Assignment,
    changed_var: Var,
    flipped: bool,
}

pub fn is_satisfiable(cnf: &Cnf) -> bool {
    const FIRST_TRY: bool = false;

    // fast checks
    if cnf.clauses.is_empty() {
        return true;
    }
    if cnf.clauses.iter().any(|cls| cls.is_empty()) {
        return false;
    }

    // solve
    let max = cnf.var_range();

    let mut dec_levels: Vec<DecisionLevel> = Vec::new();

    loop {
        // Check for satisfiability
        if let Some(dl) = dec_levels.last() {
            println!("...Checking {:?}", dl.assignment);
            if cnf.is_satisfied(&dl.assignment) {
                return true;
            }
        }

        // pick a new variable to set
        let var = 1 + dec_levels
            .last()
            .and_then(|dl| dl.assignment.last_assigned())
            .unwrap_or(0);

        // Check if the assignment is complete, i.e. no variable to be set could be found
        if var > max {
            // Assignment complete, therefore backtrack
            let bt_result = backtrack(&mut dec_levels);
            match bt_result {
                BacktrackResult::UnsatisfiableFormula => return false,
                BacktrackResult::ContinueLevel => continue,
            }
        }

        // Assignment incomplete, we found a new variable to set
        let new_assignment = dec_levels
            .last()
            .map(|dl| dl.assignment.with(var, FIRST_TRY))
            .unwrap_or_else(|| Assignment::new_with(var, FIRST_TRY));

        let new_dl = DecisionLevel {
            assignment: new_assignment,
            changed_var: var,
            flipped: false,
        };
        dec_levels.push(new_dl);
    }
}

/// Backtracks the given decision levels,
/// until a new possible assignment is found or every assignment has been tried
fn backtrack(dec_levels: &mut Vec<DecisionLevel>) -> BacktrackResult {
    loop {
        match dec_levels.last_mut() {
            Some(dl) => {
                if !dl.flipped {
                    // This dl has not been flipped yet, so try it out
                    dl.flipped = true;
                    let old_assignment = dl.assignment.get(dl.changed_var).unwrap();
                    dl.assignment.change(dl.changed_var, !old_assignment);
                    return BacktrackResult::ContinueLevel;
                } else {
                    // This dl has already been flipped, backtrack further
                    dec_levels.pop();
                    continue;
                }
            }
            None => {
                // We backtracked beyond all decision-levels
                // this means we tried all assignments
                return BacktrackResult::UnsatisfiableFormula;
            }
        }
    }
}
#[derive(Debug)]
enum BacktrackResult {
    UnsatisfiableFormula,
    ContinueLevel,
}

#[cfg(test)]
mod tests {
    use crate::{cnf::Clause, input::parse_cnf_from_str};

    use super::*;

    #[test]
    fn test_sat_sanity() {
        assert!(is_satisfiable(&Cnf::new()));
        assert!(!is_satisfiable(&parse_cnf_from_str("false").unwrap()));
        assert!(!is_satisfiable(&parse_cnf_from_str("1\nfalse").unwrap()));
        assert!(!is_satisfiable(&parse_cnf_from_str("-1\nfalse").unwrap()));
        assert!(!is_satisfiable(&parse_cnf_from_str("false\n1").unwrap()));
        assert!(!is_satisfiable(&parse_cnf_from_str("false\n-1").unwrap()));
        assert!(is_satisfiable(&parse_cnf_from_str("1").unwrap()));
    }

    #[test]
    fn test_sat_deep_dl() {
        assert!(is_satisfiable(
            &parse_cnf_from_str("1 2 3\n4 5 6\n7 8 9").unwrap()
        ));
        assert!(is_satisfiable(
            &parse_cnf_from_str("-1 -2 -3\n-4 -5 -6\n-7 -8 -9").unwrap()
        ));
        assert!(is_satisfiable(
            &parse_cnf_from_str("-1 -2 -3 4\n1\n2\n3").unwrap()
        ));
        assert!(!is_satisfiable(
            &parse_cnf_from_str("1 2 3\n-1\n-2\n-3").unwrap()
        ));
        assert!(!is_satisfiable(
            &parse_cnf_from_str("-1 2 -3\n1\n-2\n3").unwrap()
        ));
    }

    #[test]
    fn test_backtrack_empty() {
        let mut dls = vec![];
        assert!(matches!(
            backtrack(&mut dls),
            BacktrackResult::UnsatisfiableFormula
        ));
        assert!(dls.is_empty());
    }

    #[test]
    fn test_backtrack_one_completed() {
        let mut dls = vec![DecisionLevel {
            assignment: Assignment::new_with(100, true),
            changed_var: 100,
            flipped: true,
        }];

        assert!(matches!(
            backtrack(&mut dls),
            BacktrackResult::UnsatisfiableFormula
        ));
        assert!(dls.is_empty());
    }

    #[test]
    fn test_backtrack_multiple_completed() {
        let mut dls = vec![
            DecisionLevel {
                assignment: Assignment::new_with(100, true),
                changed_var: 100,
                flipped: true,
            },
            DecisionLevel {
                assignment: Assignment::new_with(10, true),
                changed_var: 10,
                flipped: true,
            },
            DecisionLevel {
                assignment: Assignment::new_with(50, true),
                changed_var: 50,
                flipped: true,
            },
            DecisionLevel {
                assignment: Assignment::new_with(120, true),
                changed_var: 120,
                flipped: true,
            },
        ];

        assert!(matches!(
            backtrack(&mut dls),
            BacktrackResult::UnsatisfiableFormula
        ));

        assert!(dls.is_empty());
    }

    #[test]
    fn test_one_not_flipped() {
        let mut dls = vec![DecisionLevel {
            assignment: Assignment::new_with(100, true),
            changed_var: 100,
            flipped: false,
        }];

        assert!(matches!(
            backtrack(&mut dls),
            BacktrackResult::ContinueLevel
        ));
        assert_eq!(
            dls,
            vec![DecisionLevel {
                assignment: Assignment::new_with(100, false),
                changed_var: 100,
                flipped: true,
            }]
        );
    }

    #[test]
    fn test_multiple_not_flipped() {
        let mut dls = vec![
            DecisionLevel {
                assignment: Assignment::new_with(100, true),
                changed_var: 100,
                flipped: false,
            },
            DecisionLevel {
                assignment: Assignment::new_with(100, true).with(50, false),
                changed_var: 50,
                flipped: false,
            },
            DecisionLevel {
                assignment: Assignment::new_with(100, true)
                    .with(50, false)
                    .with(120, true),
                changed_var: 120,
                flipped: true,
            },
        ];

        assert!(matches!(
            backtrack(&mut dls),
            BacktrackResult::ContinueLevel
        ));
        assert_eq!(
            dls,
            vec![
                DecisionLevel {
                    assignment: Assignment::new_with(100, true),
                    changed_var: 100,
                    flipped: false,
                },
                DecisionLevel {
                    assignment: Assignment::new_with(100, true).with(50, true), // this true now
                    changed_var: 50,
                    flipped: true, // this now flipped
                },
                /* popped off:
                DecisionLevel {
                    assignment: Assignment::new_with(100, true)
                        .with(50, false)
                        .with(120, true),
                    changed_var: 120,
                    flipped: true,
                },*/
            ]
        );
    }
}
