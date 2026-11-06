//! Native driver for the SAT-based Numberlink solver used by cspuz-solver2 (web).
//! usage: numlin_sat [--rules off|diag|wedge|g2|diag,wedge,g2] [--full-cover] [--short-only] [--log-encoding] [--max N] URL   (N = max answers to enumerate; default 2 = uniqueness check)
use cspuz_rs_puzzles::puzzles::numlin::{
    NumlinAssumptionSolver,
    deserialize_problem, enumerate_answers_numlin_with_options, NumlinOptions,
};
use std::time::Instant;

use cspuz_rs::solver::Config;

fn main() {
    let mut args = std::env::args().skip(1);
    let mut rnd_freq: Option<f64> = None;
    let mut reduce_db: Option<(i32, i32)> = None;
    let mut no_learn = false;
    let mut stats = false;
    let mut max = 2usize;
    let mut url = None;
    let mut options = NumlinOptions::default();
    while let Some(a) = args.next() {
        if a == "--max" {
            max = args.next().and_then(|v| v.parse().ok()).unwrap_or(2);
        } else if a == "--rules" {
            options.rules = args
                .next()
                .expect("--rules requires off or a comma-separated list of diag,wedge,g2")
                .parse()
                .unwrap_or_else(|e| panic!("{e}"));
        } else if a == "--short-only" {
            options.short_only = true;
        } else if a == "--log-encoding" {
            options.log_encoding = true;
        } else if a == "--full-cover" {
            options.full_cover = true;
        } else if a == "--edges-only" {
            options.edges_only = true;
        } else if a == "--no-learn" {
            no_learn = true;
        } else if a == "--stats" {
            stats = true;
        } else if a == "--rnd-freq" {
            rnd_freq = args.next().and_then(|v| v.parse().ok());
        } else if a == "--reduce-db" {
            let v = args.next().expect("--reduce-db FIRST,INC");
            let mut it = v.split(',').map(|x| x.parse::<i32>().unwrap());
            reduce_db = Some((it.next().unwrap(), it.next().unwrap_or(300)));
        } else {
            url = Some(a);
        }
    }
    if rnd_freq.is_some() || reduce_db.is_some() || no_learn {
        Config::set_default(Config {
            glucose_random_var_freq: rnd_freq,
            glucose_reduce_db: reduce_db,
            glucose_no_learn: if no_learn { Some(true) } else { None },
            ..Config::default()
        });
    }
    let url = url.expect(
        "usage: numlin_sat [--rules off|diag|wedge|g2|diag,wedge,g2] [--full-cover] [--short-only] [--log-encoding] [--max N] URL",
    );
    if options.short_only {
        max = 1;
    }
    let problem = deserialize_problem(&url).expect("failed to decode URL");
    let t = Instant::now();
    let answers = if stats {
        let mut solver = NumlinAssumptionSolver::new(&problem, options);
        let answers = solver.solve_cube(&[], max);
        let (d, p, c) = solver.search_stats();
        println!("decisions: {d}\npropagations: {p}\nconflicts: {c}");
        answers
    } else {
        enumerate_answers_numlin_with_options(&problem, max, &[], options)
    };
    if options.short_only {
        println!(
            "short-circuit: {}",
            if answers.is_empty() { "no" } else { "yes" }
        );
    } else {
        println!("solutions (up to {max}): {}", answers.len());
    }
    println!("elapsed: {:.3?}", t.elapsed());
}
