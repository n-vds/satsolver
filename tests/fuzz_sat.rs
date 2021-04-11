use satsolver::cnf::Cnf;
#[test]
fn test() {
    for _ in 0..100 {
        test_fuzzy();
    }
}

fn test_fuzzy() {
    let phi = create_rand_cnf();
}

fn create_rand_cnf() -> Cnf {}
