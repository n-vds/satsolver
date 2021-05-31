use std::collections::HashMap;

use crate::{
    assignment::Assignment,
    cnf::{Clause, Cnf, LiteralTpl},
};

use std::fmt::Debug;

pub struct WatchedLiterals {
    /// contains all watched literals indexed by the clause index
    watched_literals: Vec<Option<(LiteralTpl, LiteralTpl)>>,

    /// maps from a literal to all clause indices that watch this literal
    access_map: HashMap<LiteralTpl, Vec<usize>>, // TODO: more efficient data structure than vec
}

#[derive(Debug)]
pub enum UpdateResult {
    Unsatisfiable,
    Satisfiable { propagations: Vec<LiteralTpl> },
}

#[cfg(test)]
impl PartialEq for UpdateResult {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Self::Unsatisfiable => matches!(other, Self::Unsatisfiable),
            Self::Satisfiable { propagations: prp } => match other {
                Self::Satisfiable {
                    propagations: other_prp,
                } => {
                    // TODO: this is terribly slow
                    prp.iter().all(|it| other_prp.contains(it))
                        && other_prp.iter().all(|it| prp.contains(it))
                }
                _ => false,
            },
        }
    }
}

impl WatchedLiterals {
    /// Returns a new WatchedLiterals instance for the specified formula
    pub fn new(cnf: &Cnf) -> Self {
        let mut watched_literals = WatchedLiterals {
            watched_literals: vec![None; cnf.clauses.len()],
            access_map: HashMap::new(),
        };

        for (clause_idx, clause) in cnf.clauses.iter().enumerate() {
            let mut literals = clause.literals();
            match (literals.next(), literals.next()) {
                (Some(lit0), Some(lit1)) => {
                    watched_literals.set_watch(clause_idx, lit0, lit1);
                }
                _ => {
                    // The clause contains less than two literals
                    // So there is nothing to watch here
                }
            }
        }

        watched_literals
    }

    /// Adds the given literal in the given clause to the watched list, without any further updates
    fn set_watch(&mut self, clause_idx: usize, lit0: LiteralTpl, lit1: LiteralTpl) {
        self.watched_literals[clause_idx] = Some((lit0, lit1));

        self.access_map.entry(lit0).or_default().push(clause_idx);
        self.access_map.entry(lit1).or_default().push(clause_idx);
    }

    fn replace_watched_literal(
        &mut self,
        clause_idx: usize,
        old_wl: LiteralTpl,
        new_wl: LiteralTpl,
    ) {
        // Delete old_wl in access map
        match self.access_map.get_mut(&old_wl) {
            Some(clause_indices) => {
                let position = clause_indices
                    .iter()
                    .position(|&ci| ci == clause_idx)
                    .expect("Cannot remove clause from list which does not contain it");

                clause_indices.swap_remove(position);
            }
            None => {
                unreachable!("Cannot remove watched literal without access map entry")
            }
        }

        // Replace watched literal in self.watched_literals
        let wls = self.watched_literals[clause_idx]
            .as_mut()
            .expect("Specified clause index does not contain watched literals");

        if wls.0 == old_wl {
            *wls = (new_wl, wls.1);
        } else if wls.1 == old_wl {
            *wls = (wls.0, new_wl);
        } else {
            unreachable!("Specified clause index does not contain this watched literal");
        }

        // Add new entry to access map
        self.access_map.entry(new_wl).or_default().push(clause_idx);
    }

    pub fn update(
        &mut self,
        cnf: &Cnf,
        assignment: &Assignment,
        new_assignment: LiteralTpl,
    ) -> UpdateResult {
        let (var, val) = new_assignment;

        // Assert the new assignment does in fact contain the new assigned literal
        assert!(matches!(
            assignment.get(var),
            Some(val) if val == val
        ));

        // All learned propagations
        let mut propagations = Vec::new();

        // Find all watched literals made unsatisfying due to the new assignment
        let watched_literal = (var, !val);
        match self.access_map.get_mut(&watched_literal) {
            Some(clauses_vec) => {
                for clause_idx in clauses_vec.clone() {
                    let result = self.check_clause_after_update(
                        clause_idx,
                        &cnf.clauses[clause_idx],
                        assignment,
                        new_assignment,
                        &mut propagations,
                    );

                    match result {
                        CheckClauseAfterUpdateResult::KeepLiteral => {
                            // Keep literal => retain element
                        }
                        CheckClauseAfterUpdateResult::SwapTo(new_wl) => {
                            self.replace_watched_literal(clause_idx, watched_literal, new_wl);
                            // Do not keep literal => do not retain element
                        }
                        CheckClauseAfterUpdateResult::UnsatisfiableClause => {
                            // The clause has become unsatisfiable
                            return UpdateResult::Unsatisfiable;
                        }
                    };
                }

                // No clause has become unsatisfiable, the old watched literal could be replaced
                return UpdateResult::Satisfiable { propagations };
            }
            None => {
                // There is no conflict as there is no clause with the opposite literal
                return UpdateResult::Satisfiable { propagations };
            }
        }
    }

    /// Checks a clause containing a watched literal after it was assigned false
    fn check_clause_after_update(
        &mut self,
        clause_idx: usize,
        clause: &Clause,
        assignment: &Assignment,
        new_assignment: LiteralTpl,
        propagations: &mut Vec<LiteralTpl>,
    ) -> CheckClauseAfterUpdateResult {
        let (wl0, wl1) = self.watched_literals[clause_idx]
            .expect("Cannot update clause not having watched literals");

        let other_wl = if wl0.0 == new_assignment.0 {
            wl1
        } else if wl1.0 == new_assignment.0 {
            wl0
        } else {
            panic!("Old watched literal not contained in watched literal list")
        };

        match Self::find_replacement_literal(clause, assignment, other_wl) {
            FindOtherSuitableLiteral::GivenLiteralSatisfying => {
                // The watched literal one_wl is satisfying, so no changes needed
                CheckClauseAfterUpdateResult::KeepLiteral
            }
            FindOtherSuitableLiteral::OtherLiteralSatisfying(other_lit) => {
                // Another satisfying literal could be found
                // Swap it with this one
                CheckClauseAfterUpdateResult::SwapTo(other_lit)
            }
            FindOtherSuitableLiteral::MultipleUnassigned(other_lit) => {
                // Another unassigned literal was found
                // simply swap for this one
                CheckClauseAfterUpdateResult::SwapTo(other_lit)
            }
            FindOtherSuitableLiteral::UnitClauseWithGiven => {
                // The other_wl has become unit, so propagate it and keep the watched literals as is
                // because other_wl becomes valid
                propagations.push(other_wl);
                CheckClauseAfterUpdateResult::KeepLiteral
            }
            FindOtherSuitableLiteral::UnitClause(other_lit) => {
                // The only unassigned literal was found
                // This is a unit clause, so we can propagate this literal
                // We have to swap the old watched literal (which is false) with this one
                // so it keeps getting watched
                propagations.push(other_lit);
                CheckClauseAfterUpdateResult::SwapTo(other_lit)
            }
            FindOtherSuitableLiteral::UnsatisfiableClause => {
                // The clause was made unsatisfiable, a conflict occurred
                CheckClauseAfterUpdateResult::UnsatisfiableClause
            }
        }
    }

    /// Finds a new literal suitable to be watched in a given clause, acknowledging the second watched literal
    ///
    /// # Arguments
    /// 
    /// * `second_wl` - the other literal that is already watched
    fn find_replacement_literal(
        cls: &Clause,
        assignment: &Assignment,
        second_wl: LiteralTpl,
    ) -> FindOtherSuitableLiteral {
        // First check if second_wl is valid and thus no replacement needed
        if let Some(true) = assignment.get_lit(second_wl) {
            return FindOtherSuitableLiteral::GivenLiteralSatisfying;
        }

        let mut unassigned_literal = None;

        for lit in cls.literals() {
            match assignment.get_lit(lit) {
                Some(true) => {
                    // A satisfying watched literal was found
                    return if lit == second_wl {
                        // This case is already checked in the beginning
                        unreachable!();
                    } else {
                        FindOtherSuitableLiteral::OtherLiteralSatisfying(lit)
                    };
                }

                Some(false) => {
                    // Literal is false, ignore
                    continue;
                }

                None => {
                    // Literal is unassigned

                    match unassigned_literal {
                        Some(stored_lit) => {
                            // Multiple unassigned literals found
                            // Return the one that is not second_wl
                            return if stored_lit == second_wl {
                                FindOtherSuitableLiteral::MultipleUnassigned(lit)
                            } else if lit == second_wl {
                                FindOtherSuitableLiteral::MultipleUnassigned(stored_lit)
                            } else {
                                // second_wl cannot be stored_lit and lit at the same time
                                unreachable!()
                            };
                        }
                        None => {
                            // No other unassigned literal found (yet)
                            unassigned_literal = Some(lit)
                        }
                    }
                }
            }
        }

        // No true literal found and not multiple unassigned
        match unassigned_literal {
            Some(lit) => {
                // One (and only one!) unassigned literal was found
                // Check if this is second_wl
                if lit == second_wl {
                    FindOtherSuitableLiteral::UnitClauseWithGiven
                } else {
                    FindOtherSuitableLiteral::UnitClause(lit)
                }
            }
            None => {
                // No unassigned and no true literal was found
                // This clause is unsatisfiable
                return FindOtherSuitableLiteral::UnsatisfiableClause;
            }
        }
    }
}

impl Debug for WatchedLiterals {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for (literal, watched_in) in self.access_map.iter() {
            write!(
                f,
                "{:+02}: {:?},",
                literal.0 as i64 * if literal.1 { 1 } else { -1 },
                watched_in
            )?;
        }
        write!(f, "}}")?;

        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq)]
enum FindOtherSuitableLiteral {
    /// The given (second) watched literal is already satisfying, so no second watched literal is needed
    GivenLiteralSatisfying,
    /// Another literal (not the given one) was found which satisfies the clause
    OtherLiteralSatisfying(LiteralTpl),
    /// The given literal and (at least) another one are unassigned
    MultipleUnassigned(LiteralTpl),
    /// All literals are false except the given one (second watched literal) which is unassigned, so this clause becomes unit
    UnitClauseWithGiven,
    /// All literals are false except this one which is unassigned, so this clause becomes unit
    UnitClause(LiteralTpl),
    /// All literals are false so this clause has become unsatisfiable
    UnsatisfiableClause,
}

#[derive(Debug, PartialEq, Eq)]
enum CheckClauseAfterUpdateResult {
    KeepLiteral,
    SwapTo(LiteralTpl),
    UnsatisfiableClause,
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::input::parse_cnf_from_str;

    fn two_literal_eq((a0, a1): (LiteralTpl, LiteralTpl), b0: LiteralTpl, b1: LiteralTpl) -> bool {
        (a0 == b0 && a1 == b1) || (a0 == b1 && a1 == b0)
    }

    #[test]
    fn test_watchedliteral_new() {
        let cnf = parse_cnf_from_str("false\n1\n-15\n2 3\n1 -4\n1 2 3\n-4 5 -6").unwrap();
        let wl = WatchedLiterals::new(&cnf);

        // WatchedLiteral#watched_literals
        assert_eq!(&wl.watched_literals[0..3], &[None, None, None]);
        assert!(two_literal_eq(
            wl.watched_literals[3].unwrap(),
            (2, true),
            (3, true)
        ));
        assert!(two_literal_eq(
            wl.watched_literals[4].unwrap(),
            (1, true),
            (4, false)
        ));
        assert!(two_literal_eq(
            wl.watched_literals[5].unwrap(),
            (1, true),
            (2, true)
        ));
        assert!(two_literal_eq(
            wl.watched_literals[6].unwrap(),
            (4, false),
            (5, true)
        ));

        // WatchedLiteral#access_map
        let mut map = HashMap::new();
        map.insert((1, true), vec![4, 5]);
        map.insert((2, true), vec![3, 5]);
        map.insert((3, true), vec![3]);
        map.insert((4, false), vec![4, 6]);
        map.insert((5, true), vec![6]);
        assert_eq!(wl.access_map, map);
    }

    #[test]
    fn test_watchedliteral_replacement() {
        let cnf = parse_cnf_from_str("2 3\n1 -4\n1 2 3\n-4 5 -6").unwrap();

        assert_eq!(
            WatchedLiterals::find_replacement_literal(
                &cnf.clauses[0],
                &Assignment::new().with(2, false),
                (3, true)
            ),
            FindOtherSuitableLiteral::UnitClauseWithGiven
        );

        assert_eq!(
            WatchedLiterals::find_replacement_literal(
                &cnf.clauses[3],
                &Assignment::new().with(4, true).with(6, true),
                (5, true)
            ),
            FindOtherSuitableLiteral::UnitClauseWithGiven
        );

        assert_eq!(
            WatchedLiterals::find_replacement_literal(
                &cnf.clauses[3],
                &Assignment::new().with(4, true).with(6, true),
                (6, false)
            ),
            FindOtherSuitableLiteral::UnitClause((5, true))
        );

        assert_eq!(
            WatchedLiterals::find_replacement_literal(
                &cnf.clauses[3],
                &Assignment::new().with(4, true).with(6, false),
                (6, false)
            ),
            FindOtherSuitableLiteral::GivenLiteralSatisfying
        );

        assert_eq!(
            WatchedLiterals::find_replacement_literal(
                &cnf.clauses[3],
                &Assignment::new().with(4, true).with(6, false),
                (5, true)
            ),
            FindOtherSuitableLiteral::OtherLiteralSatisfying((6, false))
        );

        assert_eq!(
            WatchedLiterals::find_replacement_literal(
                &cnf.clauses[3],
                &Assignment::new().with(6, true),
                (5, true)
            ),
            FindOtherSuitableLiteral::MultipleUnassigned((4, false))
        );

        assert_eq!(
            WatchedLiterals::find_replacement_literal(
                &cnf.clauses[3],
                &Assignment::new().with(4, true).with(5, false).with(6, true),
                (5, true)
            ),
            FindOtherSuitableLiteral::UnsatisfiableClause
        );
    }

    #[test]
    fn test_watchedliteral_checkclauseafterupdate_simple() {
        let cnf = parse_cnf_from_str("2 3\n1 -4\n1 2 3\n-4 5 -6").unwrap();
        let mut wl = WatchedLiterals::new(&cnf);
        let mut propagations = Vec::new();
        let result = wl.check_clause_after_update(
            0,
            &cnf.clauses[0],
            &Assignment::new().with(2, false),
            (2, false),
            &mut propagations,
        );

        // Check correct result, literal is kept, as other (3) is now set to valid
        assert_eq!(result, CheckClauseAfterUpdateResult::KeepLiteral);

        // Test correct propagations
        assert_eq!(propagations, vec![(3, true)]);
    }

    #[test]
    fn test_watchedliteral_update_simple() {
        let cnf = parse_cnf_from_str("2 3").unwrap();
        let mut wl = WatchedLiterals::new(&cnf);
        let result = wl.update(&cnf, &Assignment::new().with(2, false), (2, false));

        assert!(matches!(
        result,
        UpdateResult::Satisfiable {
            propagations 
        } if propagations == vec![(3, true)]));
    }

    #[test]
    fn test_watchedliteral_update_multi() {
        let cnf = parse_cnf_from_str("2 3 -4 5 -6").unwrap();
        let mut wl = WatchedLiterals::new(&cnf);
        let mut assignment = Assignment::new();

        // Watched: 2 3
        assignment.change(5, false);
        let result = wl.update(&cnf, &assignment, (5, false));
        assert_eq!(
            result,
            UpdateResult::Satisfiable {
                propagations: vec![]
            }
        );

        // Watched: 2 3
        assignment.change(3, false);
        let result = wl.update(&cnf, &assignment, (3, false));
        assert_eq!(
            result,
            UpdateResult::Satisfiable {
                propagations: vec![]
            }
        );
        let (lit0, lit1) = wl.watched_literals[0].unwrap();
        assert!([lit0, lit1].contains(&(2, true)));
        assert!([lit0, lit1].contains(&(4, false)) || [lit0, lit1].contains(&(6, false)));
    }

    #[test]
    fn test_watchedliteral_replace() {
        let mut wl = WatchedLiterals::new(&parse_cnf_from_str("1 2 3").unwrap());
        wl.replace_watched_literal(0, (2, true), (3, true));

        assert_eq!(wl.watched_literals, vec![Some(((1, true), (3, true)))]);
        assert_eq!(wl.access_map, {
            let mut map = HashMap::new();
            map.insert((1, true), vec![0]);
            map.insert((2, true), vec![]);
            map.insert((3, true), vec![0]);
            map
        });
    }

    #[test]
    fn test_watchedliterals_prop() {
        let wl = WatchedLiterals::new(&parse_cnf_from_str("1 2 3\n-2 4\n-3\n-4 -1 -5").unwrap());
    }
}
