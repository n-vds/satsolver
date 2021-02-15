use std::collections::HashMap;

use crate::{
    assignment::Assignment,
    cnf::{Clause, Cnf, LiteralTpl},
};

use std::fmt::Debug;

pub struct WatchedLiterals {
    /// contains all watched literals indexed by the clause index
    watched: Vec<WatchedLiteralEntry>,

    /// maps from a literal to all the watched literal entries containing this literal
    access_map: HashMap<LiteralTpl, Vec<usize>>,
}

impl WatchedLiterals {
    pub fn new(cnf: &Cnf) -> Self {
        let watched_entries: Vec<WatchedLiteralEntry> = cnf
            .clauses
            .iter()
            .map(|cls| Self::find_watchedliterals(cls, &Assignment::new()))
            .collect();

        let mut map: HashMap<LiteralTpl, Vec<usize>> = HashMap::new();

        let mut insert = |lit: &LiteralTpl, cls: usize| {
            map.entry(*lit).or_insert(Vec::new()).push(cls);
        };

        for (i, wle) in watched_entries.iter().enumerate() {
            match wle {
                WatchedLiteralEntry::TrueLiteral(lit) => insert(lit, i),
                WatchedLiteralEntry::BothUnassigned(lit0, lit1) => {
                    insert(lit0, i);
                    insert(lit1, i);
                }
                WatchedLiteralEntry::UnitClause(lit) => insert(lit, i),
                WatchedLiteralEntry::ClauseUnsatisfiable => {}
            }
        }

        WatchedLiterals {
            watched: watched_entries,
            access_map: map,
        }
    }

    pub fn is_unsatisfiable(&self) -> impl Iterator<Item = usize> + '_ {
        self.watched
            .iter()
            .enumerate()
            .filter_map(|(i, it)| match it {
                WatchedLiteralEntry::ClauseUnsatisfiable => Some(i),
                _ => None,
            })
    }

    pub fn unit_clauses(&self) -> impl Iterator<Item = (usize, LiteralTpl)> + '_ {
        self.watched
            .iter()
            .enumerate()
            .filter_map(|(i, it)| match it {
                WatchedLiteralEntry::UnitClause(lit) => Some((i, *lit)),
                _ => None,
            })
    }

    pub fn update(&mut self, new_assignment: LiteralTpl) {
        let (var, val) = new_assignment;

        // Check if the opposite literal is conflicting with some clause
        match self.access_map.get(&(var, !val)) {
            Some(vec) => {
                for &idx in vec.iter() {
                    let wle = &self.watched[idx];
                    match wle {
                        WatchedLiteralEntry::TrueLiteral((var, val)) => {
                            assert!(*var == new_assignment.0 && !val == new_assignment.1);

                            // Since this is 
                        }
                        WatchedLiteralEntry::BothUnassigned(_, _) => {}
                        WatchedLiteralEntry::UnitClause(_) => {}
                        WatchedLiteralEntry::ClauseUnsatisfiable => {}
                    }
                }
            }
            None => {
                // There is no conflict as there is no clause with the opposite literal
                return;
            }
        }
    }

    /// Tries to find two literals of the given clause, suitable to being watched literals
    fn find_watchedliterals(cls: &Clause, a: &Assignment) -> WatchedLiteralEntry {
        let literal_count = cls.literals().count();
        if literal_count == 0 {
            return WatchedLiteralEntry::ClauseUnsatisfiable;
        }

        if literal_count == 1 {
            // Special case if there is only one literal in the clause
            let only_literal = cls.literals().next().unwrap();
            return match a.get(only_literal.0) {
                Some(val) if val == only_literal.1 => {
                    WatchedLiteralEntry::TrueLiteral(only_literal)
                }
                Some(_) => WatchedLiteralEntry::ClauseUnsatisfiable,
                None => WatchedLiteralEntry::UnitClause(only_literal),
            };
        }

        // there are at least two literals in this clause
        let mut unassigned_literals = Vec::with_capacity(2);

        for (var, val) in cls.literals() {
            match a.get(var) {
                Some(a_val) if a_val == val => {
                    // This literal is true, as it is assigned its val from the assignment
                    return WatchedLiteralEntry::TrueLiteral((var, val));
                }
                Some(_) => {
                    // This literal is not unassigned, but is false
                    // ignore it
                    continue;
                }
                None => {
                    // This literal is unassigned
                    if unassigned_literals.len() < 2 {
                        unassigned_literals.push((var, val));
                    }
                }
            }
        }

        // This line is only reached, if there is no true literal in the clause
        return match unassigned_literals.as_slice() {
            &[lit0, lit1] => {
                // There are two unassigned literals in this clause
                WatchedLiteralEntry::BothUnassigned(lit0, lit1)
            }
            &[only_lit] => {
                // There is only one unassigned literal in this clause
                WatchedLiteralEntry::UnitClause(only_lit)
            }
            &[] => {
                // There is no unassigned literal and no true one
                // so this clause is unsatisfiable
                WatchedLiteralEntry::ClauseUnsatisfiable
            }
            &[_, _, _, ..] => {
                // More than two unassigned literals
                // this is impossible due to the check in above loop
                unreachable!()
            }
        };
    }
}

impl Debug for WatchedLiterals {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.watched
                .iter()
                .map(|it| format!(
                    "[{}]",
                    match it {
                        WatchedLiteralEntry::ClauseUnsatisfiable => String::from("F"),
                        WatchedLiteralEntry::TrueLiteral(lit) => format!("T{:?}", lit),
                        WatchedLiteralEntry::BothUnassigned(a, b) => format!("{:?}{:?}", a, b),
                        WatchedLiteralEntry::UnitClause(lit) => format!("U{:?}", lit),
                    }
                ))
                .collect::<Vec<_>>()
                .join(", ")
        )?;

        Ok(())
    }
}

#[derive(Debug)]
enum WatchedLiteralEntry {
    TrueLiteral(LiteralTpl),
    BothUnassigned(LiteralTpl, LiteralTpl),
    UnitClause(LiteralTpl),
    ClauseUnsatisfiable,
}

impl PartialEq for WatchedLiteralEntry {
    fn eq(&self, other: &Self) -> bool {
        match self {
            WatchedLiteralEntry::TrueLiteral(literal) => match other {
                WatchedLiteralEntry::TrueLiteral(other_literal) => literal == other_literal,
                _ => false,
            },
            WatchedLiteralEntry::BothUnassigned(lit0, lit1) => match other {
                WatchedLiteralEntry::BothUnassigned(other_lit0, other_lit1) => {
                    (lit0 == other_lit0 && lit1 == other_lit1)
                        || (lit0 == other_lit1 && lit1 == other_lit0)
                }
                _ => false,
            },
            WatchedLiteralEntry::UnitClause(literal) => match other {
                WatchedLiteralEntry::UnitClause(other_literal) => literal == other_literal,
                _ => false,
            },
            WatchedLiteralEntry::ClauseUnsatisfiable => {
                matches!(other, WatchedLiteralEntry::ClauseUnsatisfiable)
            }
        }
    }
}

impl Eq for WatchedLiteralEntry {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::input::parse_cnf_from_str;

    #[test]
    fn test_watchedliteral_eq() {
        assert_eq!(
            WatchedLiteralEntry::ClauseUnsatisfiable,
            WatchedLiteralEntry::ClauseUnsatisfiable
        );
        assert_eq!(
            WatchedLiteralEntry::TrueLiteral((37, true)),
            WatchedLiteralEntry::TrueLiteral((37, true))
        );
        assert_eq!(
            WatchedLiteralEntry::TrueLiteral((37, false)),
            WatchedLiteralEntry::TrueLiteral((37, false))
        );
        assert_eq!(
            WatchedLiteralEntry::UnitClause((42, true)),
            WatchedLiteralEntry::UnitClause((42, true))
        );
        assert_eq!(
            WatchedLiteralEntry::UnitClause((42, false)),
            WatchedLiteralEntry::UnitClause((42, false))
        );
        assert_eq!(
            WatchedLiteralEntry::BothUnassigned((42, true), (52, false)),
            WatchedLiteralEntry::BothUnassigned((42, true), (52, false))
        );
        assert_eq!(
            WatchedLiteralEntry::BothUnassigned((42, false), (52, true)),
            WatchedLiteralEntry::BothUnassigned((42, false), (52, true))
        );
        assert_eq!(
            WatchedLiteralEntry::BothUnassigned((42, false), (52, true)),
            WatchedLiteralEntry::BothUnassigned((52, true), (42, false))
        );
    }

    #[test]
    fn test_watchedliteral_neq() {
        assert_ne!(
            WatchedLiteralEntry::TrueLiteral((37, true)),
            WatchedLiteralEntry::TrueLiteral((37, false))
        );
        assert_ne!(
            WatchedLiteralEntry::TrueLiteral((37, false)),
            WatchedLiteralEntry::TrueLiteral((38, false))
        );
        assert_ne!(
            WatchedLiteralEntry::UnitClause((42, true)),
            WatchedLiteralEntry::UnitClause((42, false))
        );
        assert_ne!(
            WatchedLiteralEntry::UnitClause((42, false)),
            WatchedLiteralEntry::UnitClause((43, false))
        );
        assert_ne!(
            WatchedLiteralEntry::BothUnassigned((42, true), (52, false)),
            WatchedLiteralEntry::BothUnassigned((42, true), (52, true))
        );
        assert_ne!(
            WatchedLiteralEntry::BothUnassigned((42, false), (52, true)),
            WatchedLiteralEntry::BothUnassigned((42, true), (52, true))
        );
        assert_ne!(
            WatchedLiteralEntry::BothUnassigned((42, true), (52, false)),
            WatchedLiteralEntry::BothUnassigned((43, true), (52, false))
        );
        assert_ne!(
            WatchedLiteralEntry::BothUnassigned((42, false), (52, true)),
            WatchedLiteralEntry::BothUnassigned((42, false), (53, true))
        );
        assert_ne!(
            WatchedLiteralEntry::BothUnassigned((42, true), (52, false)),
            WatchedLiteralEntry::BothUnassigned((52, true), (42, false))
        );
    }

    #[test]
    fn test_find_watchedliterals_empty_assignment() {
        let cnf = parse_cnf_from_str("false\n1\n-15\n2 3\n1 -4\n1 2 3\n-4 5 -6")
            .unwrap()
            .clauses;
        let empty_assignment = Assignment::new();

        // Test 0, 1 literals
        assert_eq!(
            WatchedLiterals::find_watchedliterals(&cnf[0], &empty_assignment),
            WatchedLiteralEntry::ClauseUnsatisfiable
        );
        assert_eq!(
            WatchedLiterals::find_watchedliterals(&cnf[1], &empty_assignment),
            WatchedLiteralEntry::UnitClause((1, true))
        );
        assert_eq!(
            WatchedLiterals::find_watchedliterals(&cnf[2], &empty_assignment),
            WatchedLiteralEntry::UnitClause((15, false))
        );

        // Test 2 literals
        assert_eq!(
            WatchedLiterals::find_watchedliterals(&cnf[3], &empty_assignment),
            WatchedLiteralEntry::BothUnassigned((2, true), (3, true))
        );
        assert_eq!(
            WatchedLiterals::find_watchedliterals(&cnf[4], &empty_assignment),
            WatchedLiteralEntry::BothUnassigned((1, true), (4, false))
        );

        // Test more literals
        {
            let result = WatchedLiterals::find_watchedliterals(&cnf[5], &empty_assignment);
            match result {
                WatchedLiteralEntry::BothUnassigned(lit0, lit1) => {
                    let expected = [(1, true), (2, true), (3, true)];
                    assert!(lit0 != lit1);
                    assert!(
                        [lit0, lit1]
                            .iter()
                            .filter(|it| expected.contains(it))
                            .count()
                            == 2
                    );
                }
                _ => assert!(false),
            }
        }

        {
            let result = WatchedLiterals::find_watchedliterals(&cnf[6], &empty_assignment);
            match result {
                WatchedLiteralEntry::BothUnassigned(lit0, lit1) => {
                    let expected = [(4, false), (5, true), (6, false)];
                    assert!(lit0 != lit1);
                    assert!(
                        [lit0, lit1]
                            .iter()
                            .filter(|it| expected.contains(it))
                            .count()
                            == 2
                    );
                }
                _ => assert!(false),
            }
        }
    }

    #[test]
    fn test_find_watchedliterals_with_assignment() {
        let cls = parse_cnf_from_str(
            "2\n2 4 6\n-1 -3 -5
1\n-2\n-1 2 3 4\n-1 2 -3 -4
7\n-7\n-1 7 2\n-1 -7 2
-1 2 7 -3 8\n-7 -8 -1 2 -3",
        )
        .unwrap()
        .clauses;
        let assignment = Assignment::new()
            .with(1, true)
            .with(2, false)
            .with(3, true)
            .with(4, false)
            .with(5, true)
            .with(6, false);

        // Unsatisfiable
        assert_eq!(
            WatchedLiterals::find_watchedliterals(&cls[0], &assignment),
            WatchedLiteralEntry::ClauseUnsatisfiable
        );
        assert_eq!(
            WatchedLiterals::find_watchedliterals(&cls[1], &assignment),
            WatchedLiteralEntry::ClauseUnsatisfiable
        );
        assert_eq!(
            WatchedLiterals::find_watchedliterals(&cls[2], &assignment),
            WatchedLiteralEntry::ClauseUnsatisfiable
        );

        // True
        assert_eq!(
            WatchedLiterals::find_watchedliterals(&cls[3], &assignment),
            WatchedLiteralEntry::TrueLiteral((1, true))
        );
        assert_eq!(
            WatchedLiterals::find_watchedliterals(&cls[4], &assignment),
            WatchedLiteralEntry::TrueLiteral((2, false))
        );
        assert_eq!(
            WatchedLiterals::find_watchedliterals(&cls[5], &assignment),
            WatchedLiteralEntry::TrueLiteral((3, true))
        );
        assert_eq!(
            WatchedLiterals::find_watchedliterals(&cls[6], &assignment),
            WatchedLiteralEntry::TrueLiteral((4, false))
        );

        // Unit clause
        assert_eq!(
            WatchedLiterals::find_watchedliterals(&cls[7], &assignment),
            WatchedLiteralEntry::UnitClause((7, true))
        );
        assert_eq!(
            WatchedLiterals::find_watchedliterals(&cls[8], &assignment),
            WatchedLiteralEntry::UnitClause((7, false))
        );
        assert_eq!(
            WatchedLiterals::find_watchedliterals(&cls[9], &assignment),
            WatchedLiteralEntry::UnitClause((7, true))
        );
        assert_eq!(
            WatchedLiterals::find_watchedliterals(&cls[10], &assignment),
            WatchedLiteralEntry::UnitClause((7, false))
        );

        // Both unassigned
        assert_eq!(
            WatchedLiterals::find_watchedliterals(&cls[11], &assignment),
            WatchedLiteralEntry::BothUnassigned((7, true), (8, true))
        );
        assert_eq!(
            WatchedLiterals::find_watchedliterals(&cls[12], &assignment),
            WatchedLiteralEntry::BothUnassigned((7, false), (8, false))
        );
    }
}
