//! Portfolio-parallel driver for the SAT-based Numberlink solver: every thread solves the same
//! puzzle under a different symmetry transform / random seed, the first finished result wins.
//! usage: numlin_sat_par [--rules off|diag|wedge|g2|diag,wedge,g2] [--full-cover] [--short-only] [--log-encoding] [--threads N] [--max M] [--transforms K,K,...] URL
use cspuz_rs::solver::Config;
use cspuz_rs_puzzles::puzzles::numlin::{
    deserialize_problem, enumerate_answers_numlin_with_options, NumlinOptions,
};
use std::sync::mpsc;
use std::time::Instant;

type Clues = Vec<Vec<Option<i32>>>;

const NAMES: [&str; 8] = [
    "id",
    "rot90",
    "rot180",
    "rot270",
    "flip",
    "flip+rot90",
    "flip+rot180",
    "flip+rot270",
];

fn rotate90(p: &Clues) -> Clues {
    let h = p.len();
    let w = p[0].len();
    let mut out = vec![vec![None; h]; w];
    for y in 0..h {
        for x in 0..w {
            out[x][h - 1 - y] = p[y][x];
        }
    }
    out
}

fn flip(p: &Clues) -> Clues {
    p.iter()
        .map(|row| row.iter().rev().copied().collect())
        .collect()
}

fn transform(p: &Clues, k: usize) -> Clues {
    let mut q = if k >= 4 { flip(p) } else { p.clone() };
    for _ in 0..(k % 4) {
        q = rotate90(&q);
    }
    q
}

fn main() {
    let mut args = std::env::args().skip(1);
    let mut threads = 8usize;
    let mut max = 2usize;
    let mut transforms: Vec<usize> = (0..8).collect();
    let mut seed_base = 0usize;
    let mut url = None;
    let mut options = NumlinOptions::default();
    while let Some(a) = args.next() {
        match a.as_str() {
            "--rules" => {
                options.rules = args
                    .next()
                    .expect("--rules requires off or a comma-separated list of diag,wedge,g2")
                    .parse()
                    .unwrap_or_else(|e| panic!("{e}"))
            }
            "--short-only" => options.short_only = true,
            "--log-encoding" => options.log_encoding = true,
            "--full-cover" => options.full_cover = true,
            "--threads" | "-j" => threads = args.next().and_then(|v| v.parse().ok()).unwrap_or(8),
            "--max" => max = args.next().and_then(|v| v.parse().ok()).unwrap_or(2),
            "--seed" => seed_base = args.next().and_then(|v| v.parse().ok()).unwrap_or(0),
            "--transforms" => {
                transforms = args
                    .next()
                    .map(|v| {
                        v.split(',')
                            .filter_map(|s| s.parse().ok())
                            .filter(|&k: &usize| k < 8)
                            .collect()
                    })
                    .unwrap_or_default();
            }
            _ => url = Some(a),
        }
    }
    let url = url.expect("usage: numlin_sat_par [--rules off|diag|wedge|g2|diag,wedge,g2] [--full-cover] [--short-only] [--log-encoding] [--threads N] [--max M] [--transforms K,..] URL");
    if options.short_only {
        max = 1;
    }
    let problem = deserialize_problem(&url).expect("failed to decode URL");
    assert!(threads > 0 && !transforms.is_empty());
    let started = Instant::now();
    let (tx, rx) = mpsc::channel();
    let mut handles = Vec::new();
    for i in 0..threads {
        let k = transforms[i % transforms.len()];
        let seed_idx = seed_base + i / transforms.len();
        let clues = transform(&problem, k);
        let tx = tx.clone();
        handles.push(std::thread::spawn(move || {
            if seed_idx > 0 {
                // Seeds only matter with randomized initial activities.
                Config::set_default(Config {
                    glucose_random_seed: Some(seed_idx as f64 * 1000.0 + 1.0),
                    glucose_rnd_init_act: true,
                    ..Config::default()
                });
            }
            let t = Instant::now();
            let answers = enumerate_answers_numlin_with_options(&clues, max, &[], options);
            let _ = tx.send((i, k, seed_idx, answers.len(), t.elapsed()));
        }));
    }
    drop(tx);
    if let Ok((i, k, seed_idx, n, el)) = rx.recv() {
        println!(
            "winner: thread {i} transform {} seed_idx {seed_idx}",
            NAMES[k]
        );
        if options.short_only {
            println!("short-circuit: {}", if n > 0 { "yes" } else { "no" });
        } else {
            println!("solutions (up to {max}): {n}");
        }
        println!("thread elapsed: {:.3?}", el);
        println!("elapsed: {:.3?}", started.elapsed());
        println!("threads: {threads}");
        std::process::exit(if n > 0 { 0 } else { 1 });
    }
    eprintln!("no result");
    std::process::exit(2);
}
