//! Row-scan cube generation and the SAT driver's estimate/verification policy.
use rowscan_dfs::{cubes, Puzzle};
pub use rowscan_dfs::{Cube, Options as SolveOptions};
use std::{collections::HashSet, ops::Index};

pub const TRANSFORM_NAMES: [&str; 8] = [
    "id",
    "rot90",
    "rot180",
    "rot270",
    "flip",
    "flip+rot90",
    "flip+rot180",
    "flip+rot270",
];
// CLI/Web use clockwise rotations after reflection; rowscan reflects before transpose.
pub const ROWSCAN_DIRECTIONS: [u8; 8] = [0, 5, 6, 3, 2, 7, 4, 1];

#[derive(Clone)]
pub struct Problem {
    pub puzzle: Puzzle,
    labels: Vec<u16>,
    clues: Vec<Option<i32>>,
}
impl Problem {
    pub fn from_url(url: &str, direction: usize) -> Result<Self, String> {
        if direction >= 8 {
            return Err("transform must be 0..7".into());
        }
        // Preserve the driver's host-agnostic URL input without broadening the
        // standalone library's intentionally strict puzz.link input contract.
        let encoded = url
            .strip_prefix("p?numlin/")
            .or_else(|| url.split_once("/p?numlin/").map(|(_, s)| s))
            .ok_or("expected a puzz.link numlin URL or p?numlin/... path")?;
        let (puzzle, labels) = Puzzle::decode_url(&format!("p?numlin/{encoded}"))?;
        let puzzle = puzzle.transformed(ROWSCAN_DIRECTIONS[direction]);
        let clues = puzzle
            .cells
            .iter()
            .map(|&v| {
                if v == 0 {
                    None
                } else {
                    Some(labels[v as usize - 1] as i32)
                }
            })
            .collect();
        Ok(Self {
            puzzle,
            labels,
            clues,
        })
    }
    pub fn width(&self) -> usize {
        self.puzzle.width
    }
    pub fn height(&self) -> usize {
        self.puzzle.height
    }
    pub fn labels(&self) -> &[u16] {
        &self.labels
    }
}
impl Index<(usize, usize)> for Problem {
    type Output = Option<i32>;
    fn index(&self, (y, x): (usize, usize)) -> &Self::Output {
        &self.clues[y * self.width() + x]
    }
}

pub fn strong_options() -> SolveOptions {
    SolveOptions {
        cut: 5,
        diag_shortcut: true,
        ..SolveOptions::none()
    }
}

pub fn split_cube(
    problem: Problem,
    cube: &Cube,
    minimum: usize,
    options: &SolveOptions,
) -> (Vec<Cube>, usize) {
    let (parts, found) = cubes::split_cube_with_options(&problem.puzzle, cube, minimum, options);
    (parts, found as usize)
}
pub fn estimate_cube_size(
    problem: &Problem,
    cube: &Cube,
    probes: usize,
    seed: u64,
    options: &SolveOptions,
) -> f64 {
    cubes::estimate_cube_size_with_options(&problem.puzzle, cube, probes, seed, options)
}
fn estimate_all(
    problem: &Problem,
    items: &mut [Cube],
    threads: usize,
    probes: usize,
    seed: u64,
    options: &SolveOptions,
) {
    let estimate = |items: &mut [Cube], offset: usize| {
        for (i, cube) in items.iter_mut().enumerate() {
            cube.weight = estimate_cube_size(
                problem,
                cube,
                probes,
                seed ^ ((offset + i) as u64).wrapping_mul(0x2545_f491_4f6c_dd1d),
                options,
            );
        }
    };
    #[cfg(not(target_arch = "wasm32"))]
    if threads > 1 && items.len() > 1 {
        let chunk = items.len().div_ceil(threads);
        std::thread::scope(|scope| {
            for (i, part) in items.chunks_mut(chunk).enumerate() {
                let estimate = &estimate;
                scope.spawn(move || estimate(part, i * chunk));
            }
        });
        return;
    }
    let _ = threads;
    estimate(items, 0);
}

#[allow(clippy::too_many_arguments)]
pub fn generate_cubes_balanced_verify_floor(
    problem: Problem,
    minimum: usize,
    threads: usize,
    slack: f64,
    mean_factor: f64,
    verify_factor: f64,
    verify_min: f64,
    floor: f64,
    probes: usize,
    max_cubes: usize,
    options: &SolveOptions,
) -> (Vec<Cube>, usize) {
    let (initial, found) = if minimum == 0 {
        (
            vec![Cube {
                edges: vec![],
                next: 0,
                weight: 0.0,
            }],
            0,
        )
    } else {
        let split = cubes::generate_cubes(&problem.puzzle, minimum, options, 0);
        (split.cubes, split.solutions_while_splitting as usize)
    };
    balance_cubes(
        &problem,
        initial,
        found,
        threads,
        slack,
        mean_factor,
        verify_factor,
        verify_min,
        floor,
        probes,
        max_cubes,
        options,
    )
}

/// Estimate each new frontier once. Revisit accepted cubes as the total shrinks;
/// the optional mean limit remains anchored to the initial frontier.
#[allow(clippy::too_many_arguments)]
pub fn balance_cubes(
    problem: &Problem,
    mut items: Vec<Cube>,
    mut found: usize,
    threads: usize,
    slack: f64,
    mean_factor: f64,
    verify_factor: f64,
    verify_min: f64,
    floor: f64,
    probes: usize,
    max_cubes: usize,
    options: &SolveOptions,
) -> (Vec<Cube>, usize) {
    const STEP: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut seed = STEP;
    estimate_all(problem, &mut items, threads, probes, seed, options);
    let initial_mean = items.iter().map(|c| c.weight).sum::<f64>() / items.len().max(1) as f64;
    let mut blocked = HashSet::new();
    let mut verified = HashSet::new();
    for pass in 0..7 {
        for _ in 0..201 {
            let total = items.iter().map(|c| c.weight).sum::<f64>();
            let limit = if mean_factor > 0.0 {
                initial_mean * mean_factor
            } else {
                total / (threads.max(1) as f64 * slack)
            };
            let mut kept = Vec::new();
            let mut fresh = Vec::new();
            let count = items.len();
            for parent in items {
                if parent.weight <= limit
                    || count + fresh.len() >= max_cubes
                    || blocked.contains(&parent.edges)
                {
                    kept.push(parent);
                    continue;
                }
                let (parts, extra) = split_cube(problem.clone(), &parent, 2, options);
                if parts.len() == 1 {
                    // Retaining the parent also retains any solutions found by this trial.
                    blocked.insert(parent.edges.clone());
                    kept.push(parent);
                } else {
                    found += extra;
                    fresh.extend(parts);
                }
            }
            let done = fresh.is_empty();
            seed = seed.wrapping_add(STEP);
            estimate_all(problem, &mut fresh, threads, probes, seed, options);
            kept.extend(fresh);
            items = kept;
            if done {
                break;
            }
        }
        if verify_factor <= 0.0 || pass == 6 {
            break;
        }
        let threshold = (verify_min * items.iter().map(|c| c.weight).sum::<f64>()
            / items.len().max(1) as f64)
            .max(floor);
        let mut accepted = Vec::new();
        let mut families = Vec::new();
        let mut children = Vec::new();
        for parent in items {
            if parent.weight >= threshold && !verified.contains(&parent.edges) {
                let (parts, extra) = split_cube(problem.clone(), &parent, 2, options);
                families.push((parent, parts.len(), extra));
                children.extend(parts);
            } else {
                accepted.push(parent);
            }
        }
        seed = seed.wrapping_add(STEP);
        estimate_all(problem, &mut children, threads, probes, seed, options);
        let mut children = children.into_iter();
        let mut changed = false;
        for (mut parent, count, extra) in families {
            let parts: Vec<_> = children.by_ref().take(count).collect();
            let sum = parts.iter().map(|c| c.weight).sum::<f64>();
            let replace = count == 0
                || (count > 1
                    && sum > verify_factor * parent.weight
                    && accepted.len() + count < max_cubes);
            eprintln!(
                "[verify] pass {}: cube est {:.2e} -> {count} children sum {sum:.2e}: {}",
                pass + 1,
                parent.weight,
                if replace { "replaced" } else { "kept" }
            );
            if replace {
                found += extra;
                accepted.extend(parts);
                changed = true;
            } else {
                parent.weight = parent.weight.max(sum);
                verified.insert(parent.edges.clone());
                accepted.push(parent);
            }
        }
        items = accepted;
        if !changed {
            break;
        }
    }
    items.sort_by(|a, b| b.weight.total_cmp(&a.weight));
    (items, found)
}

#[cfg(test)]
mod tests {
    use super::*;
    use cspuz_rs_puzzles::puzzles::numlin::{enumerate_answers_numlin_with_options, NumlinOptions};

    fn count(p: &Problem, cubes: &[Cube]) -> usize {
        let clues: Vec<Vec<_>> = (0..p.height())
            .map(|y| (0..p.width()).map(|x| p[(y, x)]).collect())
            .collect();
        cubes
            .iter()
            .map(|c| {
                enumerate_answers_numlin_with_options(
                    &clues,
                    10,
                    &c.to_fixed_edges(),
                    NumlinOptions::default(),
                )
                .len()
            })
            .sum()
    }

    #[test]
    fn balancing_preserves_completed_answers_and_partition() {
        for url in [
            "https://puzz.link/p?numlin/15/15/z5g2h9l3o3rck1x9jch1h6kazual4gbi4j8ybi6l7g2m8n5h7z",
            "https://puzz.link/p?numlin/15/15/zg5do9-10n73h7l3h5jd4iaj-11q6hbz1k-10veap9ofm-11g6nfp8i1g2eh2ic4ici8gbw",
        ] {
            let p = Problem::from_url(url, 0).unwrap();
            for (minimum, mean, verify) in
                [(0, 0.0, 0.0), (3, 2.0, 0.0), (3, 0.0, 0.1), (3, 0.0, 10.0)]
            {
                let (parts, found) = generate_cubes_balanced_verify_floor(
                    p.clone(),
                    minimum,
                    2,
                    4.0,
                    mean,
                    verify,
                    0.0,
                    0.0,
                    3,
                    512,
                    &SolveOptions::default(),
                );
                assert_eq!(found + count(&p, &parts), 1);
            }
        }
        let p = Problem::from_url("p?numlin/2/2/1h1", 0).unwrap();
        let (parts, found) = generate_cubes_balanced_verify_floor(
            p,
            0,
            2,
            4.0,
            0.0,
            2.0,
            0.0,
            0.0,
            3,
            32,
            &SolveOptions::default(),
        );
        assert!(parts.is_empty());
        assert_eq!(found, 1);
    }

    #[test]
    fn labels_transforms_and_parallel_seed_offsets() {
        let p = Problem::from_url("http://example.test/p?numlin/3/2/-10h-11-10-11", 0).unwrap();
        assert_eq!(p.labels(), &[16, 17]);
        let root = Cube {
            edges: vec![],
            next: 0,
            weight: 0.0,
        };
        assert_eq!(p[(0, 0)], Some(16));
        for k in 0..8 {
            let q = Problem::from_url("http://example.test/p?numlin/3/2/-10h-11-10-11", k).unwrap();
            assert_eq!(q.puzzle, p.puzzle.transformed(ROWSCAN_DIRECTIONS[k]));
        }
        let mut a = vec![root; 7];
        let mut b = a.clone();
        estimate_all(&p, &mut a, 1, 3, 42, &SolveOptions::default());
        estimate_all(&p, &mut b, 4, 3, 42, &SolveOptions::default());
        assert_eq!(a, b);
    }
}
