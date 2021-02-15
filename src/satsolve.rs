use std::collections::HashMap;

use crate::{
    assignment::Assignment,
    cnf::{Clause, Cnf, Var},
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

    let initial_assignment = calc_bool_prop(&cnf, &Assignment::new()).unwrap_or_default();
    println!("---Initial: {:?}", initial_assignment);
    stats.tries += 1;
    if cnf.is_satisfied(&initial_assignment) {
        return (true, stats);
    }

    let mut dec_levels: Vec<DecisionLevel> = Vec::new();

    loop {
        // Check for satisfiability
        if let Some(dl) = dec_levels.last() {
            println!("...Checking {:?}", dl.assignment);
            stats.tries += 1;
            if cnf.is_satisfied(&dl.assignment) {
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

/// Calculates the boolean propagation
///
/// Returns a new assignment based on the given one,
/// which contains all assignments known by boolean propagation
/// or None if no variable could be propagated
fn calc_bool_prop(cnf: &Cnf, a: &Assignment) -> Option<Assignment> {
    let mut new_a = None;
    let mut new_assignments = HashMap::new();

    loop {
        for clause in &cnf.clauses {
            if let Some((var, val)) = calc_bool_prop_cls(
                clause, //
                new_a.as_ref().unwrap_or(a),
            ) {
                new_assignments.insert(var, val);
            }
        }

        if !new_assignments.is_empty() {
            let result = new_a
                .as_ref()
                .unwrap_or(a)
                .with_all(new_assignments.iter().map(|(&var, &val)| (var, val)));
            new_assignments.clear();
            new_a = Some(result);
        } else {
            return new_a;
        }
    }
}

fn calc_bool_prop_cls(cls: &Clause, a: &Assignment) -> Option<(Var, bool)> {
    // Check if clause is not satisfied and only one literal is unset
    let mut unassigned = None;

    for (var, val) in cls.literals() {
        match a.get(var) {
            Some(assignment) => {
                // This literal is assigned a value by a
                if val == assignment {
                    // This literal is satisfied, so is this whole clause
                    // There is not anything to be propagated from a satisfied clause
                    return None;
                } else {
                    // This literal is false, so it cannot be propagated
                    // This branch is intentionally left empty
                }
            }
            None => {
                // There is a literal that is not yet assigned a value
                // Check how many of those there are
                match unassigned {
                    None => {
                        // This is the only unassigned variable so far
                        unassigned = Some((var, val));
                    }
                    Some(_) => {
                        // There is already another literal that is unassigned,
                        // so this is the second one. Either one of them
                        // might be true, so there is nothing to propagate
                        return None;
                    }
                }
            }
        }
    }

    unassigned
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
    fn test_prop_cls() {
        let clauses = parse_cnf_from_str("1\n-2\n1 -2 3").unwrap().clauses;
        assert_eq!(
            calc_bool_prop_cls(&clauses[0], &Assignment::new()),
            Some((1, true))
        );
        assert_eq!(
            calc_bool_prop_cls(&clauses[1], &Assignment::new()),
            Some((2, false))
        );
        assert_eq!(calc_bool_prop_cls(&clauses[2], &Assignment::new()), None);
        assert_eq!(
            calc_bool_prop_cls(
                &clauses[2],
                &Assignment::new().with(1, false).with(3, false)
            ),
            Some((2, false))
        );
        assert_eq!(
            calc_bool_prop_cls(
                &clauses[2], //
                &Assignment::new().with(1, false).with(2, true)
            ),
            Some((3, true))
        );
    }

    #[test]
    fn test_prop_cls_no_prop() {
        let clauses = parse_cnf_from_str("1 2\n-2 -1\n1 -2 3").unwrap().clauses;
        assert_eq!(calc_bool_prop_cls(&clauses[0], &Assignment::new()), None);
        assert_eq!(calc_bool_prop_cls(&clauses[1], &Assignment::new()), None);
        assert_eq!(calc_bool_prop_cls(&clauses[2], &Assignment::new()), None);
        assert_eq!(
            calc_bool_prop_cls(&clauses[2], &Assignment::new().with(1, false).with(3, true)),
            None
        );
        assert_eq!(
            calc_bool_prop_cls(
                &clauses[2], //
                &Assignment::new().with(1, false).with(2, false)
            ),
            None
        );
    }

    #[test]
    fn test_prop() {
        assert_eq!(
            calc_bool_prop(&parse_cnf_from_str("1 2 3").unwrap(), &Assignment::new()),
            None
        );
        assert_eq!(
            calc_bool_prop(&parse_cnf_from_str("1\n-2\n3").unwrap(), &Assignment::new()),
            Some(
                Assignment::new() //
                    .with(1, true)
                    .with(2, false)
                    .with(3, true)
            )
        );
        assert_eq!(
            calc_bool_prop(
                &parse_cnf_from_str("1 2 3\n-2 4\n-3\n-4 1 -5").unwrap(),
                &Assignment::new().with(1, false)
            ),
            Some(
                Assignment::new() //
                    .with(1, false)
                    .with(2, true)
                    .with(3, false)
                    .with(4, true)
                    .with(5, false)
            )
        );
        assert_eq!(
            calc_bool_prop(
                &parse_cnf_from_str("1 2 3\n-2 4\n-3\n-4 -1 -5").unwrap(),
                &Assignment::new().with(1, false)
            ),
            Some(
                Assignment::new() //
                    .with(1, false)
                    .with(2, true)
                    .with(3, false)
                    .with(4, true)
            )
        );
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
