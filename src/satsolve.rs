use std::collections::VecDeque;

use crate::{
    assignment::Assignment,
    cnf::{Cnf, LiteralTpl, Var},
    watchedliterals::{UpdateResult, WatchedLiterals},
};
#[derive(Debug, PartialEq)]
struct DecisionLevel {
    assignment: Assignment,
    changed_var: Var,
    next_var_at_least: Var,
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
    let mut watchedliterals = WatchedLiterals::new(&cnf);

    let initial_assignment = {
        // first get clauses with single literals, they have to be true
        let mut assignment = match get_assignment_from_single_clauses(&cnf) {
            Some(a) => a,
            None => return (false, stats), // unsatisfiable
        };
        let assignments_vec = assignment.iter().collect::<Vec<_>>();

        // propagate these
        for new_literal in assignments_vec {
            match propagate_assignment(new_literal, &mut assignment, cnf, &mut watchedliterals) {
                ExecuteAssignmentResult::Unsatisfiable => {
                    // Conflict in DL0
                    return (false, stats);
                }
                ExecuteAssignmentResult::AssignmentDone => {
                    // left intentionally empty
                }
            }
        }

        // after propagation this assignment contains all clauses with a single literal and their propagations
        assignment
    };
    println!("---Initial: {:?}", initial_assignment);

    let max = cnf.highest_var();

    stats.tries += 1;
    if cnf.is_satisfied(&initial_assignment) {
        return (true, stats);
    }

    let mut dec_levels: Vec<DecisionLevel> = Vec::new();

    #[derive(Debug, PartialEq, Eq)]
    enum State {
        CheckCurrentLevel,
        AssignNewVar,
        NewDecLevelWithAssignment(LiteralTpl),
        PropagateAssignment(LiteralTpl),
        Backtrack,
    }
    let mut state = State::CheckCurrentLevel;

    loop {
        match state {
            State::CheckCurrentLevel => {
                // Check for satisfiability
                if let Some(dl) = dec_levels.last() {
                    if check_assignment(&cnf, &dl.assignment, &mut stats) {
                        return (true, stats);
                    }
                }
                state = State::AssignNewVar;
            }

            State::AssignNewVar => {
                // pick a new variable to set
                let var = choose_next_var(max, &dec_levels, &initial_assignment);

                // Check if the assignment is complete, i.e. no variable to be set could be found
                let var = match var {
                    None => {
                        // Assignment complete, therefore backtrack
                        state = State::Backtrack;
                        continue;
                    }
                    Some(var) => var,
                };

                // Assignment incomplete, we found a new variable to set
                state = State::NewDecLevelWithAssignment((var, FIRST_TRY));
            }

            State::Backtrack => {
                print!("Backtracking... ");
                let result = backtrack(&mut dec_levels);
                match result {
                    BacktrackResult::UnsatisfiableFormula => {
                        // Return unsat
                        println!("Unsatisfiable!");
                        return (false, stats);
                    }
                    BacktrackResult::ContinueWith(new_assignment) => {
                        // Backtracking did undo multiple decision levels and the resulting decision level had this assignment
                        // Skip State::ExecAssignment and jump to PropagateAssignment, because the (now) latest
                        // decision level already has the expected assignment set due to the call to backtrack
                        println!("Continuing with dl {}", dec_levels.len() + 1);
                        state = State::PropagateAssignment(new_assignment);
                    }
                }
            }

            State::NewDecLevelWithAssignment(new_assigned_lit) => {
                println!(
                    "Trying to assign new var {:?} = {:?}",
                    new_assigned_lit.0, new_assigned_lit.1
                );
                let new_assignment = dec_levels
                    .last()
                    .map(|dl| &dl.assignment)
                    .unwrap_or(&initial_assignment)
                    .with(new_assigned_lit.0, new_assigned_lit.1);

                let next_var_at_least = {
                    let nval = dec_levels
                        .last()
                        .map(|dl| dl.next_var_at_least)
                        .unwrap_or(0);
                    if new_assigned_lit.0 == nval + 1 {
                        new_assigned_lit.0
                    } else {
                        nval
                    }
                };

                let new_dl = DecisionLevel {
                    assignment: new_assignment,
                    changed_var: new_assigned_lit.0,
                    next_var_at_least,
                    flipped: false,
                };
                dec_levels.push(new_dl);
                state = State::PropagateAssignment(new_assigned_lit);
            }

            State::PropagateAssignment(new_assigned_lit) => {
                print!("Propagating assignment {:?}: ", new_assigned_lit);
                // The current/top decision level already has the assignment set
                // but it needs to be propagated
                debug_assert!(matches!(
                    dec_levels
                        .last()
                        .unwrap()
                        .assignment
                        .get_lit(new_assigned_lit),
                    Some(true)
                ));

                let assignment = &mut dec_levels
                    .last_mut()
                    .expect("Encountered State::PropagateAssignment without decision level")
                    .assignment;

                let result =
                    propagate_assignment(new_assigned_lit, assignment, &cnf, &mut watchedliterals);

                match result {
                    ExecuteAssignmentResult::Unsatisfiable => {
                        // Assignment caused insatisfiability => backtrack
                        println!("Unsatisfiable.");
                        state = State::Backtrack
                    }
                    ExecuteAssignmentResult::AssignmentDone => {
                        println!("Done.");
                        state = State::CheckCurrentLevel;
                    }
                }
            }
        }
    }
}

#[inline(always)]
fn check_assignment(cnf: &Cnf, a: &Assignment, stats: &mut Stats) -> bool {
    let result = cnf.is_satisfied(&a);
    println!("...Checking {:?}: {}", a, result);
    stats.tries += 1;
    result
}

fn choose_next_var(
    max: Var,
    dec_levels: &[DecisionLevel],
    initial_assignment: &Assignment,
) -> Option<Var> {
    // start with 1 + highest from last dl or 0s
    let mut var = 1 + dec_levels
        .last()
        .map(|dl| dl.next_var_at_least)
        .unwrap_or(0);

    let a = dec_levels
        .last()
        .map(|dl| &dl.assignment)
        .unwrap_or(&initial_assignment);

    // increase picked var while it is already set (due to bcp)
    let var = loop {
        let assigned = a.get(var).is_some();

        if assigned {
            var += 1;
        } else {
            break var;
        }
    };

    if var < max {
        Some(var)
    } else {
        None
    }
}

/// Propagates a decision (new_literal) in the given assignment using the watched literals
///
/// The assignment must already contain the new_literal and resulting propagations will mutate it
/// The watched literals are used for propagations and are updated accordingly
///
/// Returns AssignmentDone if the new_literal and all propagations are now reflected in the assignment
/// and watched literals without encountering a conflict
/// Returns Unsatisfiable if the new_literal or resulting propagations caused a conflict. In this case
/// the current decision level should be dropped
fn propagate_assignment(
    new_literal: LiteralTpl,
    assignment: &mut Assignment,
    cnf: &Cnf,
    watchedliterals: &mut WatchedLiterals,
) -> ExecuteAssignmentResult {
    debug_assert!(matches!(assignment.get_lit(new_literal), Some(true)));

    // Vars to propagate
    let mut propagations = VecDeque::new();
    propagations.push_back(new_literal);

    while let Some(prop) = propagations.pop_front() {
        let result = watchedliterals.update(&cnf, assignment, prop);
        match result {
            UpdateResult::Unsatisfiable => {
                // Unsatisfiable
                return ExecuteAssignmentResult::Unsatisfiable;
            }

            UpdateResult::Satisfiable {
                propagations: new_propagations,
            } => {
                // Assignment of propagation successful, store all new propagations
                for (prop_var, prop_val) in new_propagations {
                    propagations.push_back((prop_var, prop_val));
                    assignment.change(prop_var, prop_val);
                }
            }
        }
    }

    // All propagations handled without running into unsatisfiability
    ExecuteAssignmentResult::AssignmentDone
}

#[must_use]
enum ExecuteAssignmentResult {
    Unsatisfiable,
    AssignmentDone,
}

/// Calculates an assignment satisfying all clauses with only a single literal
///
/// @return None, if there are two conflicting clauses with a single literal
fn get_assignment_from_single_clauses(cnf: &Cnf) -> Option<Assignment> {
    let mut assignment = Assignment::new();

    for clause in &cnf.clauses {
        let mut literals = clause.literals();
        match (literals.next(), literals.next()) {
            (Some(lit), None) => {
                // Clause only contains one literal
                match assignment.get_lit(lit) {
                    Some(true) => {
                        // Already satisfying
                    }
                    Some(false) => {
                        // Clause unsat
                        return None;
                    }
                    None => {
                        assignment.change(lit.0, lit.1);
                    }
                }
            }

            _ => {}
        }
    }

    Some(assignment)
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
                    let new_assignment = (dl.changed_var, !old_assignment);
                    dl.assignment.change(new_assignment.0, new_assignment.1);
                    return BacktrackResult::ContinueWith(new_assignment);
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
    ContinueWith(LiteralTpl),
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
            next_var_at_least: 0,
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
                next_var_at_least: 0,
                flipped: true,
            },
            DecisionLevel {
                assignment: Assignment::new_with(10, true),
                changed_var: 10,
                next_var_at_least: 0,
                flipped: true,
            },
            DecisionLevel {
                assignment: Assignment::new_with(50, true),
                changed_var: 50,
                next_var_at_least: 0,
                flipped: true,
            },
            DecisionLevel {
                assignment: Assignment::new_with(120, true),
                changed_var: 120,
                next_var_at_least: 0,
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
            next_var_at_least: 0,
            flipped: false,
        }];

        assert!(matches!(
            backtrack(&mut dls),
            BacktrackResult::ContinueWith((100, false))
        ));
        assert_eq!(
            dls,
            vec![DecisionLevel {
                assignment: Assignment::new_with(100, false),
                changed_var: 100,
                next_var_at_least: 0,
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
                next_var_at_least: 0,
                flipped: false,
            },
            DecisionLevel {
                assignment: Assignment::new_with(100, true).with(50, false),
                changed_var: 50,
                next_var_at_least: 0,
                flipped: false,
            },
            DecisionLevel {
                assignment: Assignment::new_with(100, true)
                    .with(50, false)
                    .with(120, true),
                changed_var: 120,
                next_var_at_least: 0,
                flipped: true,
            },
        ];

        assert!(matches!(
            backtrack(&mut dls),
            BacktrackResult::ContinueWith((50, true))
        ));
        assert_eq!(
            dls,
            vec![
                DecisionLevel {
                    assignment: Assignment::new_with(100, true),
                    changed_var: 100,
                    next_var_at_least: 0,
                    flipped: false,
                },
                DecisionLevel {
                    assignment: Assignment::new_with(100, true).with(50, true), // this true now
                    changed_var: 50,
                    next_var_at_least: 0,
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
