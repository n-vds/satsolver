mod assignment;
mod cnf;
mod input;
mod satsolve;

fn main() {
    println!(" S A T ");
    let phi = input::read_cnf_interactive();
    println!("Got phi = {:?}", phi);

    println!("Calculating satisfiability....");
    let (satisfiable, stats) = satsolve::is_satisfiable(&phi);

    let sat_str = if satisfiable {
        "satisfiable"
    } else {
        "not satisfiable"
    };
    println!("phi = {:?}", phi);
    let combinations = 2f64.powi(phi.highest_var() as i32);
    println!(
        "phi is {}, took {} evaluations ({:02.1}% of all combinations)",
        sat_str,
        stats.tries,
        stats.tries as f64 * 100f64 / combinations as f64
    );
}
