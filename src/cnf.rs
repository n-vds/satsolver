use std::fmt::Debug;

use crate::assignment::Assignment;

pub type Var = u32;

/// A literal is a positive or negated form of a variable
pub type LiteralTpl = (Var, bool);

/// A collection of [clauses] in logical conjunction
/// 
/// [clauses]: Clause
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

    pub fn highest_var(&self) -> Var {
        fn highest_var_in_clause(slc: &[Var]) -> Var {
            slc.iter().fold(0, |cur, var| cur.max(*var))
        }

        self.clauses.iter().fold(0, |cur, clause| {
            cur.max(highest_var_in_clause(&clause.positive))
                .max(highest_var_in_clause(&clause.negative))
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

/// A collection of literals (positive or negative [variables]) in logical disjunction
/// 
/// [variables]: Var
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

    pub fn positives(&self) -> impl Iterator<Item = Var> + '_ {
        self.positive.iter().copied()
    }

    pub fn negatives(&self) -> impl Iterator<Item = Var> + '_ {
        self.negative.iter().copied()
    }

    /// Returns an iterator over all literals in this clause
    pub fn literals(&self) -> impl Iterator<Item = LiteralTpl> + '_ {
        self.positive
            .iter()
            .map(|&it| (it, true))
            .chain(self.negative.iter().map(|&it| (it, false)))
    }

    /// Adds a positive literal to this clause if it is not already present
    /// 
    /// # Panics
    /// 
    /// Panics if the negated literal is already part of this clause
    pub fn add_positive(&mut self, var: Var) {
        if !self.positive.contains(&var) {
            if !self.negative.contains(&var) {
                self.positive.push(var);
            } else {
                panic!("Added var both positive and negative!");
            }
        }
    }

    /// Adds a negative literal to this clause if it is not already present
    /// 
    /// # Panics
    /// 
    /// Panics if the negated literal is already part of this clause
    pub fn add_negative(&mut self, var: Var) {
        if !self.negative.contains(&var) {
            if !self.positive.contains(&var) {
                self.negative.push(var);
            } else {
                panic!("Added var both positive and negative!");
            }
        }
    }

    /// Returns wether the given variable is part of this clause in positive or negative form
    /// 
    /// If the positive literal of the given variable is part of this clause,
    /// returns `Some(true)`, if the negative literal is part of this clause
    /// `Some(false)`.
    /// If neither the positive nor negative literal are part of this clause 
    /// returns `None`.
    pub fn get(&self, var: Var) -> Option<bool> {
        if self.positive.contains(&var) {
            Some(true)
        } else if self.negative.contains(&var) {
            Some(false)
        } else {
            None
        }
    }

    /// Checks wether the given assignment satisfies this clause
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
                Some(true) => format!("{:+03}", var),
                Some(false) => format!("-{:02}", var),
                None => unreachable!(),
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
