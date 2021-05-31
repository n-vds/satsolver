use satsolver::assignment::Assignment;
use satsolver::cnf::Var;
use satsolver::cnf::{Clause, Cnf};
use satsolver::satsolve;

#[test]
#[ignore]
fn fuzzy_test_randomly() {
    for _ in 0..10 {
        test_fuzzy_instance();
    }
}

fn test_fuzzy_instance() {
    let cnf = create_rand_cnf();
    println!("Testing clause {:?}", cnf);
    let (result, _stats) = satsolve::is_satisfiable(&cnf);
    let other_result = solve_by_testing_all_combinations(&cnf);

    match (result, other_result) {
        (true, Some(_)) | (false, None) => {}
        (true, None) => assert!(false, "satsolve found a wrong solution"),
        (false, Some(a)) => assert!(false, "satsolve did not find solution {:?}", a),
    }
}

fn create_rand_cnf() -> Cnf {
    let mut cnf = Cnf::new();

    for _ in 0..rand_int(0, 20) {
        let mut clause = Clause::new();

        for _ in 0..rand_int(0, 10) {
            let var = loop {
                let v = rand_int(1, 20) as u32;
                if clause.literals().all(|lit| lit.0 != v) {
                    break v;
                }
            };

            if rand_int(0, 2) == 0 {
                clause.add_negative(var);
            } else {
                clause.add_positive(var);
            }
        }
        cnf.clauses.push(clause);
    }

    cnf
}

fn rand_int(min: u32, max_exclusive: u32) -> u32 {
    // TODO this is so ugly
    let str = format!("{:?}", std::time::Instant::now()); // format: Instant { **.**s }
    let str = str.split('.').nth(1).unwrap();
    let str = str.split('s').next().unwrap();
    let num: u32 = str.parse().expect(&format!("Could not parse {}", str));

    (num % (max_exclusive - min)) + min
}

fn solve_by_testing_all_combinations(cnf: &Cnf) -> Option<Assignment> {
    /// Packs an assignment, the assigned variable and wether it has been flipped
    struct Decision(Assignment, Var, bool);

    let mut stack = Vec::new();
    stack.push(Decision(Assignment::new_with(1, false), 1, false));

    loop {
        let a = &stack.last().unwrap().0;
        let result = cnf.is_satisfied(a);
        if result {
            return Some(a.clone());
        }

        if stack.last().unwrap().1 == cnf.highest_var() {
            // backtrack
            loop {
                let Decision(top_a, top_var, top_flipped) = stack.last_mut().unwrap();
                if !*top_flipped {
                    // Not yet flipped, so flip this
                    top_a.change(*top_var, true);
                    *top_flipped = true;
                    break;
                } else {
                    // Already flipped, pop this decision and continue with the next one
                    stack.pop();

                    if stack.is_empty() {
                        return None;
                    }
                    // else: continue backtrack loop
                }
            }
        } else {
            // Not highest var, choose next one
            let Decision(a, var, _) = stack.last().unwrap();
            let new_decision = Decision(a.with(var + 1, false), var + 1, false);
            stack.push(new_decision);
        }
    }
}
