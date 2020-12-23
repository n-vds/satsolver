use std::collections::HashMap;
use std::fmt::Debug;

use crate::cnf::Var;
#[derive(Clone, PartialEq)]
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

    pub fn get(&self, var: Var) -> Option<bool> {
        self.0.get(&var).map(|it| *it)
    }

    pub fn change(&mut self, var: Var, val: bool) {
        self.0.insert(var, val);
    }

    pub fn with(&self, var: Var, val: bool) -> Assignment {
        let mut new = self.clone();
        new.change(var, val);
        new
    }

    pub fn last_assigned(&self) -> Option<Var> {
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
