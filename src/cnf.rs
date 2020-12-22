use std::fmt::Debug;

pub type Var = u32;
pub struct Cnf {
    pub clauses: Vec<Clause>,
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
