use std::collections::HashMap;
use std::fmt::Debug;

use crate::cnf::{LiteralTpl, Var};
#[derive(Clone, PartialEq, Default)]
pub struct Assignment(HashMap<Var, bool>);

impl Assignment {
    pub fn new() -> Assignment {
        Assignment(HashMap::new())
    }

    pub fn new_with(var: Var, val: bool) -> Assignment {
        let mut it = Assignment(HashMap::new());
        it.change(var, val);
        it
    }

    /// Gets the value (true or false) that is assigned to this variable or None if it is unassigned
    pub fn get(&self, var: Var) -> Option<bool> {
        self.0.get(&var).map(|it| *it)
    }

    /// Gets whether this literal is valid, invalid or unassigned
    ///
    /// If the literal is valid (its variable is set to true), this function returns Some(true);
    /// if it is invalid (its variable set to false), this function returns Some(false).
    /// If the literal's variable is unassigned, this function returns None
    pub fn get_lit(&self, lit: LiteralTpl) -> Option<bool> {
        match self.0.get(&lit.0) {
            Some(&val) => Some(val == lit.1),
            None => None,
        }
    }

    /// Checks wether this assignment satisfies the given literal
    pub fn satisfies(&self, lit: LiteralTpl) -> bool {
        self.0.get(&lit.0).map(|&val| val == lit.1).unwrap_or(false)
    }

    pub fn change(&mut self, var: Var, val: bool) {
        self.0.insert(var, val);
    }

    pub fn with(&self, var: Var, val: bool) -> Assignment {
        let mut new = self.clone();
        new.change(var, val);
        new
    }

    pub fn with_all(&self, map: impl Iterator<Item = LiteralTpl>) -> Assignment {
        let mut this = self.clone();
        this.0.extend(map);
        this
    }

    pub fn highest_assigned_var(&self) -> Option<Var> {
        self.0.keys().copied().max()
    }
}

impl Debug for Assignment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let assignment_str = {
            let mut values = self
                .0
                .iter()
                .map(|(&var, &val)| (var, val))
                .collect::<Vec<(u32, bool)>>();

            values.sort_by_key(|&(var, _val)| var);

            values
                .iter()
                .map(|&(var, val)| format!("{:02} => {}", var, if val { 1 } else { 0 }))
                .collect::<Vec<String>>()
                .join("; ")
        };

        write!(f, "α{{{}}}", assignment_str)?;
        Ok(())
    }
}
