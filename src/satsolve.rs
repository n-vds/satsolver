use std::collections::HashMap;

use crate::{
    assignment::Assignment,
    cnf::{Clause, Cnf, Var},
    watchedliterals::WatchedLiterals,
};
#[derive(Debug, PartialEq)]
struct DecisionLevel {
    assignment: Assignment,
    changed_var: Var,
    flipped: bool,
}

pub struct Stats {
    pub tries: usize,
}

pub fn is_satisfiable(cnf: &Cnf) -> (bool, Stats) {
    const FIRST_TRY: bool = false;

    let mut stats = Stats { tries: 0 };

    // fast checks
    if cnf.clauses.is_empty() {
        return (true, stats);
    }
    if cnf.clauses.iter().any(|cls| cls.is_empty()) {
        return (false, stats);
    }

    // solve
    let max = cnf.highest_var();
    let mut watchedliterals = WatchedLiterals::new(&cnf);
    println!("Watching literals: {:?}", watchedliterals);
    let initial_assignment = match calc_initial_assignment(&watchedliterals) {
        Some(a) => a,
        None => return (false, stats), // unsatisfiable
    };

    println!("---Initial: {:?}", initial_assignment);
    stats.tries += 1;
    if cnf.is_satisfied(&initial_assignment) {
        return (true, stats);
    }

    let mut dec_levels: Vec<DecisionLevel> = Vec::new();

    loop {
        // Check for satisfiability
        if let Some(dl) = dec_levels.last() {
            if check_assignment(&cnf, &dl.assignment, &mut stats) {
                return (true, stats);
            }
        }

        // pick a new variable to set
        // start with 1 + highest from last dl or 0
        let var = {
            let mut var = 1 + dec_levels
                .last()
                .and_then(|dl| dl.assignment.highest_assigned_var())
                .unwrap_or(0);

            // increase picked var while it is already set (due to bcp)
            loop {
                let assigned = dec_levels
                    .last()
                    .map(|dl| &dl.assignment)
                    .unwrap_or(&initial_assignment)
                    .get(var)
                    .is_some();

                if assigned {
                    var += 1;
                } else {
                    break var;
                }
            }
        };

        // Check if the assignment is complete, i.e. no variable to be set could be found
        if var > max {
            // Assignment complete, therefore backtrack
            let bt_result = backtrack(&mut dec_levels);
            match bt_result {
                BacktrackResult::UnsatisfiableFormula => return (false, stats),
                BacktrackResult::ContinueLevel => continue,
            }
        }

        // Assignment incomplete, we found a new variable to set
        let new_assignment = dec_levels
            .last()
            .map(|dl| &dl.assignment)
            .unwrap_or(&initial_assignment)
            .with(var, FIRST_TRY);

        // Propagate vars
        let new_assignment = calc_bool_prop(&cnf, &new_assignment).unwrap_or(new_assignment);
        let new_dl = DecisionLevel {
            assignment: new_assignment,
            changed_var: var,
            flipped: false,
        };
        dec_levels.push(new_dl);
    }
}

#[inline(always)]
fn check_assignment(cnf: &Cnf, a: &Assignment, stats: &mut Stats) -> bool {
    println!("...Checking {:?}", a);
    stats.tries += 1;
    return cnf.is_satisfied(&a);
}

/// Calculates the initial assignment from the watched literal's unit clauses
///
/// @return None, if the formula is unsatisfiable
fn calc_initial_assignment(watchedliterals: &WatchedLiterals) -> Option<Assignment> {
    let mut assignment = Assignment::new();

    for (_cls, lit) in watchedliterals.unit_clauses() {
        match assignment.get(lit.0) {
            Some(val) => {
                if val == lit.1 {
                    // Assignment already done
                    continue;
                } else {
                    // Wrong assignment and this is decision level zero
                    return None;
                }
            }
            None => {
                assignment.change(lit.0, lit.1);
            }
        }
    }

    Some(assignment)
}

///
            }

        }
    }
}

                    }
                        return None;
                    }
                }
            }
        }
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
#[derive(Debug, PartialEq, Eq)]
enum BacktrackResult {
    UnsatisfiableFormula,
    ContinueLevel,
}

#[cfg(test)]
mod tests {
    use crate::input::parse_cnf_from_str;

    use super::*;

    #[test]
    fn test_sat_sanity() {
        assert!(is_satisfiable(&Cnf::new()).0);
        assert!(!is_satisfiable(&parse_cnf_from_str("false").unwrap()).0);
        assert!(!is_satisfiable(&parse_cnf_from_str("1\nfalse").unwrap()).0);
        assert!(!is_satisfiable(&parse_cnf_from_str("-1\nfalse").unwrap()).0);
        assert!(!is_satisfiable(&parse_cnf_from_str("false\n1").unwrap()).0);
        assert!(!is_satisfiable(&parse_cnf_from_str("false\n-1").unwrap()).0);
        assert!(is_satisfiable(&parse_cnf_from_str("1").unwrap()).0);
    }

    #[test]
    fn test_sat_deep_dl() {
        assert!(is_satisfiable(&parse_cnf_from_str("1 2 3\n4 5 6\n7 8 9").unwrap()).0);
        assert!(is_satisfiable(&parse_cnf_from_str("-1 -2 -3\n-4 -5 -6\n-7 -8 -9").unwrap()).0);
        assert!(is_satisfiable(&parse_cnf_from_str("-1 -2 -3 4\n1\n2\n3").unwrap()).0);
        assert!(!is_satisfiable(&parse_cnf_from_str("1 2 3\n-1\n-2\n-3").unwrap()).0);
        assert!(!is_satisfiable(&parse_cnf_from_str("-1 2 -3\n1\n-2\n3").unwrap()).0);
    }

    #[test]
    fn test_sat() {
        assert!(is_satisfiable(&parse_cnf_from_str("1 2 3\n-2 -3\n-3\n-1").unwrap()).0);
        assert!(is_satisfiable(&parse_cnf_from_str("1 2 3 4\n-2 -3\n-3\n-1").unwrap()).0);
        assert!(is_satisfiable(&parse_cnf_from_str("1 2 3\n-2 -3\n-3 2\n-1").unwrap()).0);
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
    fn test_backtrack_one_not_flipped() {
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
    fn test_backtrack_multiple_not_flipped() {
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
