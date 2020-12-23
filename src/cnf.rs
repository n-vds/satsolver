use std::fmt::Debug;

use crate::assignment::Assignment;

pub type Var = u32;

#[derive(PartialEq)]
pub struct Cnf {
    pub clauses: Vec<Clause>,
}

impl Cnf {
    pub fn new() -> Self {
        Cnf {
            clauses: Vec::new(),
        }
    }

    pub fn new_with(clauses: Vec<Clause>) -> Self {
        Cnf { clauses }
    }

    pub fn var_range(&self) -> Var {
        fn var_range_clause(slc: &[Var]) -> Var {
            slc.iter().fold(0, |cur, var| cur.max(*var))
        }

        self.clauses.iter().fold(0, |cur, clause| {
            cur.max(var_range_clause(&clause.positive))
                .max(var_range_clause(&clause.negative))
        })
    }

    pub fn is_satisfied(&self, assignment: &Assignment) -> bool {
        self.clauses.iter().all(|cls| cls.is_satisfied(assignment))
    }
}

impl Debug for Cnf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.clauses.is_empty() {
            write!(f, "true")?;
            return Ok(());
        }

        let result = self
            .clauses
            .iter()
            .map(|it| format!("{:?}", it))
            .collect::<Vec<String>>()
            .join(" ∧ ");

        write!(f, "{}", result)?;
        Ok(())
    }
}

pub struct Clause {
    positive: Vec<Var>,
    negative: Vec<Var>,
}

impl Clause {
    pub fn new() -> Clause {
        Clause {
            positive: Vec::new(),
            negative: Vec::new(),
        }
    }

    pub fn add_positive(&mut self, var: Var) {
        if !self.positive.contains(&var) {
            if !self.negative.contains(&var) {
                self.positive.push(var);
            } else {
                panic!("Added var both positive and negative!");
            }
        }
    }

    pub fn add_negative(&mut self, var: Var) {
        if !self.negative.contains(&var) {
            if !self.positive.contains(&var) {
                self.negative.push(var);
            } else {
                panic!("Added var both positive and negative!");
            }
        }
    }

    pub fn get(&self, var: Var) -> LiteralInfo {
        if self.positive.contains(&var) {
            LiteralInfo::POSITIVE
        } else if self.negative.contains(&var) {
            LiteralInfo::NEGATIVE
        } else {
            LiteralInfo::NoOcc
        }
    }

    pub fn is_satisfied(&self, assignment: &Assignment) -> bool {
        self.positive
            .iter()
            .any(|&var| matches!(assignment.get(var), Some(true)))
            || self
                .negative
                .iter()
                .any(|&var| matches!(assignment.get(var), Some(false)))
    }

    pub fn is_empty(&self) -> bool {
        self.positive.is_empty() && self.negative.is_empty()
    }
}

impl PartialEq for Clause {
    fn eq(&self, other: &Self) -> bool {
        fn check(literals: &Vec<u32>, other_literals: &Vec<u32>) -> bool {
            literals
                .iter()
                .all(|literal| other_literals.contains(literal))
        }

        check(&self.positive, &other.positive)
            && check(&other.positive, &self.positive)
            && check(&self.negative, &other.negative)
            && check(&other.negative, &self.negative)
    }
}

impl Debug for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.positive.is_empty() && self.negative.is_empty() {
            write!(f, "false")?;
            return Ok(());
        }

        write!(f, "[")?;
        // TODO very inefficient
        let mut all_vars = self.positive.clone();
        all_vars.append(&mut self.negative.clone());
        all_vars.sort();

        let str = all_vars
            .iter()
            .map(|&var| match self.get(var) {
                LiteralInfo::POSITIVE => format!("{:+03}", var),
                LiteralInfo::NEGATIVE => format!("-{:02}", var),
                LiteralInfo::NoOcc => unreachable!(),
            })
            .collect::<Vec<String>>()
            .join(" ∨ ");
        write!(f, "{}", str)?;
        write!(f, "]")?;

        Ok(())
    }
}

pub enum LiteralInfo {
    POSITIVE,
    NEGATIVE,
    NoOcc,
}
