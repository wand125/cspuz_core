use super::*;

fn problem_for_tests() -> Problem {
    vec![
        vec![None, None, None, None, Some(4), None],
        vec![None, Some(1), Some(4), None, None, None],
        vec![None, None, None, None, Some(2), None],
        vec![None, None, None, None, None, None],
        vec![None, Some(2), None, None, Some(1), Some(3)],
        vec![Some(3), None, None, None, None, None],
    ]
}

#[test]
fn test_numlin_problem() {
    let problem = problem_for_tests();
    let ans = enumerate_answers_numlin(&problem, 3);
    assert_eq!(ans.len(), 1);
    let ans = &ans[0];
    let expected = graph::BoolGridEdgesModel {
        horizontal: util::tests::to_bool_2d([
            [1, 1, 1, 0, 1],
            [0, 0, 0, 1, 0],
            [0, 0, 1, 0, 0],
            [0, 1, 0, 1, 1],
            [1, 0, 1, 1, 0],
            [1, 1, 1, 1, 1],
        ]),
        vertical: util::tests::to_bool_2d([
            [1, 0, 0, 1, 0, 1],
            [1, 1, 1, 0, 1, 1],
            [1, 1, 0, 1, 0, 1],
            [1, 0, 1, 0, 0, 0],
            [0, 0, 0, 0, 0, 1],
        ]),
    };
    assert_eq!(ans, &expected);
}

#[test]
fn test_numlin_serializer() {
    let problem = problem_for_tests();
    let url = "https://puzz.link/p?numlin/6/6/j4h14m2n2h133k";
    util::tests::serializer_test(problem, url, serialize_problem, deserialize_problem);
}

fn answer_flat(answer: &graph::BoolGridEdgesModel) -> Vec<bool> {
    let mut result = vec![];
    let height = answer.horizontal.len();
    let width = answer.horizontal[0].len() + 1;

    for y in 0..height {
        for x in 0..(width - 1) {
            result.push(answer.horizontal[y][x]);
        }
    }
    for y in 0..(height - 1) {
        for x in 0..width {
            result.push(answer.vertical[y][x]);
        }
    }

    result
}

fn run_fuzz(height: usize, width: usize, seed: u64) {
    let problem =
        if let Some(problem) = instance_generator::generate_instance_by_csp(height, width, seed) {
            problem
        } else {
            return;
        };
    let csp_answers = enumerate_answers_numlin(&problem, usize::MAX);
    let with_g2 = enumerate_answers_numlin_with_options(
        &problem,
        usize::MAX,
        &[],
        NumlinOptions {
            rules: "g2".parse().unwrap(),
            ..Default::default()
        },
    );
    let sorted = |answers: &[graph::BoolGridEdgesModel]| {
        let mut flat: Vec<_> = answers.iter().map(answer_flat).collect();
        flat.sort();
        flat
    };
    assert_eq!(
        sorted(&csp_answers),
        sorted(&with_g2),
        "G2: {height}x{width} seed {seed}"
    );
    let no_propagator_answers = enumerate_answers_numlin_impl(&problem, usize::MAX, false, &[]);
    let numlin_answers = no_propagator_answers;

    assert_eq!(csp_answers.len(), numlin_answers.len());

    let mut csp_answers = csp_answers
        .iter()
        .map(|ans| answer_flat(ans))
        .collect::<Vec<_>>();
    csp_answers.sort();

    let mut numlin_answers = numlin_answers
        .iter()
        .map(|ans| answer_flat(ans))
        .collect::<Vec<_>>();
    numlin_answers.sort();

    assert_eq!(csp_answers, numlin_answers);
}

#[test]
fn test_numlin_fuzz_short() {
    for (height, width) in [(7, 8), (8, 7), (8, 8), (9, 9), (10, 10)] {
        let seed_start = height * 10000 + width * 100;
        for seed in 0..10 {
            run_fuzz(height, width, (seed_start + seed) as u64);
        }
    }
}

#[test]
#[ignore]
fn test_numlin_fuzz_long() {
    for (height, width) in [(7, 8), (8, 7), (8, 8), (9, 9), (10, 10)] {
        let seed_start = height * 100000 + width * 1000;
        for seed in 0..1000 {
            run_fuzz(height, width, (seed_start + seed) as u64);
        }
    }
}

fn has_unused_vertex(answer: &graph::BoolGridEdgesModel) -> bool {
    let h = answer.horizontal.len();
    let w = answer.vertical[0].len();
    (0..h).any(|y| {
        (0..w).any(|x| {
            !(y > 0 && answer.vertical[y - 1][x])
                && !(y + 1 < h && answer.vertical[y][x])
                && !(x > 0 && answer.horizontal[y][x - 1])
                && !(x + 1 < w && answer.horizontal[y][x])
        })
    })
}

#[test]
fn test_numlin_rules_generated_equivalence() {
    // Exhaust enumeration rather than inferring nonexistence of unused-cell solutions
    // from a truncated prefix. Include 25 generated boards and 25 pair deletions.
    const MAX: usize = 10_000;
    let mut checked = 0;
    let mut solvable = 0;
    let mut with_unused = 0;
    let mut with_full_cover = 0;
    let mut largest_enumeration = 0;
    for (h, w) in [(5, 6), (6, 5), (7, 8), (8, 7), (10, 10)] {
        let mut generated = 0;
        for seed in 0..100 {
            let Some(problem) = instance_generator::generate_instance_by_csp(h, w, seed) else {
                continue;
            };
            let removed = problem.iter().flatten().copied().flatten().min().unwrap();
            let mut deleted = problem.clone();
            for row in &mut deleted {
                for clue in row {
                    if *clue == Some(removed) {
                        *clue = None;
                    }
                }
            }
            for problem in [problem, deleted] {
                let mut full_cover_baseline = vec![];
                let mut baseline = None;
                for rules in ["off", "diag", "wedge", "diag,wedge", "g2", "diag,wedge,g2"] {
                    let rules: NumlinRules = rules.parse().unwrap();
                    for full_cover in [false, true] {
                        let options = NumlinOptions {
                            rules,
                            full_cover,
                            ..NumlinOptions::default()
                        };
                        let answers =
                            enumerate_answers_numlin_with_options(&problem, MAX + 1, &[], options);
                        assert!(
                            answers.len() <= MAX,
                            "enumeration truncated: {h}x{w}, seed {seed}"
                        );
                        let mut flat: Vec<_> = answers.iter().map(answer_flat).collect();
                        flat.sort();
                        // Exercise the test-only acyclic/straight-shortcut encoding too.
                        let reference = enumerate_answers_numlin_impl_with_options(
                            &problem,
                            MAX + 1,
                            false,
                            &[],
                            options,
                        );
                        assert!(reference.len() <= MAX);
                        let mut reference: Vec<_> = reference.iter().map(answer_flat).collect();
                        reference.sort();
                        assert_eq!(
                            flat, reference,
                            "propagator: {h}x{w} seed {seed}, {rules:?}, full_cover={full_cover}"
                        );
                        largest_enumeration = largest_enumeration.max(answers.len());
                        if full_cover {
                            assert!(answers.iter().all(|a| !has_unused_vertex(a)));
                            if rules == NumlinRules::default() {
                                with_full_cover += usize::from(!answers.is_empty());
                                full_cover_baseline = flat;
                            } else {
                                assert_eq!(
                                    flat, full_cover_baseline,
                                    "{h}x{w} seed {seed}, {rules:?}"
                                );
                            }
                        } else {
                            let signature =
                                (!answers.is_empty(), answers.iter().any(has_unused_vertex));
                            if let Some(expected) = baseline {
                                assert_eq!(signature, expected, "{h}x{w} seed {seed}, {rules:?}");
                            } else {
                                solvable += usize::from(signature.0);
                                with_unused += usize::from(signature.1);
                                baseline = Some(signature);
                            }
                        }
                    }
                }
                checked += 1;
            }
            generated += 1;
            if generated == 5 {
                break;
            }
        }
        assert_eq!(generated, 5);
    }
    assert_eq!(checked, 50);
    assert!(solvable > 0 && with_unused > 0 && with_full_cover > 0);
    eprintln!("50 instances: {solvable} solvable, {with_unused} with unused vertices, {with_full_cover} with full covers; largest enumeration {largest_enumeration}/{MAX}");
}

#[test]
fn test_numlin_wedge_limits() {
    // One clue per table: check first blocking distance and the exclusive bound.
    for (slot, clue) in [(0, (5, 7)), (1, (3, 7)), (2, (7, 3)), (3, (7, 5))] {
        let mut clues = vec![vec![None; 10]; 10];
        clues[clue.0][clue.1] = Some(0);
        assert_eq!(rules::wedge_limits(&clues)[4][4][slot], 4);
        let runs = rules::wedge_runs(&clues);
        assert!(runs.contains(&((4, 4), slot, 2)));
        assert!(runs.contains(&((4, 4), slot, 3)));
        assert!(!runs.contains(&((4, 4), slot, 4)));
        clues[4][4] = Some(1);
        assert_eq!(rules::wedge_limits(&clues)[4][4], [6, 6, 6, 6]);
    }
    // Include the innermost floor(k/2) sample, and an odd first distance.
    for (slot, inner, odd) in [
        (0, (6, 6), (5, 6)),
        (1, (2, 6), (3, 6)),
        (2, (6, 2), (6, 3)),
        (3, (6, 6), (6, 5)),
    ] {
        for (clue, distance) in [(inner, 4), (odd, 3)] {
            let mut clues = vec![vec![None; 10]; 10];
            clues[clue.0][clue.1] = Some(0);
            assert_eq!(rules::wedge_limits(&clues)[4][4][slot], distance);
        }
    }
    // The slot-8 port bug would encounter exterior sentinels and stop early here.
    let clues = vec![vec![None; 3]; 10];
    assert_eq!(rules::wedge_limits(&clues)[0][1], [2, 2, 10, 10]);
    assert_eq!(rules::wedge_limits(&clues)[0][2][3], 10);
    let runs = rules::wedge_runs(&vec![vec![None; 25]; 25]);
    assert_eq!(runs.len(), 26_496);
    assert!(runs.len() < rules::MAX_WEDGE_CLAUSES);
    assert_eq!(
        rules::wedge_runs(&vec![vec![None; 50]; 50]).len(),
        rules::MAX_WEDGE_CLAUSES
    );
}

#[test]
fn test_numlin_rules_parser() {
    assert_eq!(
        "off".parse::<NumlinRules>().unwrap(),
        NumlinRules::default()
    );
    assert_eq!(
        "diag,wedge".parse::<NumlinRules>().unwrap(),
        NumlinRules {
            diag: true,
            wedge: true,
            g2: false
        }
    );
    assert!("diagonal".parse::<NumlinRules>().is_err());
}

#[test]
fn test_numlin_rules_unsatisfiable() {
    // The pairs alternate on the boundary and cannot be joined disjointly.
    let problem = vec![
        vec![None, Some(2), None],
        vec![Some(1), None, Some(1)],
        vec![None, Some(2), None],
    ];
    for rules in ["off", "diag", "wedge", "diag,wedge", "g2", "diag,wedge,g2"] {
        for full_cover in [false, true] {
            assert!(enumerate_answers_numlin_with_options(
                &problem,
                1,
                &[],
                NumlinOptions {
                    rules: rules.parse().unwrap(),
                    full_cover,
                    ..NumlinOptions::default()
                },
            )
            .is_empty());
        }
    }
}

#[test]
fn test_numlin_short_only_and_log_encoding() {
    let mut problems = vec![
        problem_for_tests(),
        vec![vec![Some(1), None, Some(2)], vec![Some(2), None, Some(1)]],
    ];
    for seed in 0..20 {
        if let Some(p) = instance_generator::generate_instance_by_csp(5, 6, seed) {
            problems.push(p);
        }
    }
    let mut yes = false;
    let mut no = false;
    for problem in problems {
        for rules in ["off", "diag,wedge", "g2", "diag,wedge,g2"] {
            for full_cover in [false, true] {
                let base = NumlinOptions {
                    rules: rules.parse().unwrap(),
                    full_cover,
                    ..Default::default()
                };
                let answers = enumerate_answers_numlin_with_options(&problem, 10_001, &[], base);
                assert!(answers.len() < 10_001);
                for log_encoding in [false, true] {
                    let options = NumlinOptions {
                        log_encoding,
                        ..base
                    };
                    let mut expected: Vec<_> = answers.iter().map(answer_flat).collect();
                    expected.sort();
                    let mut actual: Vec<_> =
                        enumerate_answers_numlin_with_options(&problem, 10_001, &[], options)
                            .iter()
                            .map(answer_flat)
                            .collect();
                    actual.sort();
                    assert_eq!(actual, expected);
                    let short = enumerate_answers_numlin_with_options(
                        &problem,
                        2,
                        &[],
                        NumlinOptions {
                            short_only: true,
                            ..options
                        },
                    );
                    let exists = answers.iter().any(has_unused_vertex);
                    assert_eq!(short.len(), usize::from(exists));
                    assert!(short.iter().all(has_unused_vertex));
                    yes |= exists;
                    no |= !exists;
                }
            }
        }
    }
    assert!(yes && no);
}

#[test]
fn test_numlin_fixed_units_root_facts() {
    let problem = vec![vec![Some(1), Some(1)], vec![Some(2), Some(2)]];
    let options = NumlinOptions { full_cover: true, ..Default::default() };
    let base = NumlinAssumptionSolver::new(&problem, options);
    for value in [false, true] {
        let mut units = NumlinAssumptionSolver::with_fixed_units(
            &problem, &[(true, 0, 0, value)], options,
        );
        assert_eq!(units.encoding_fingerprint(), base.encoding_fingerprint());
        assert_eq!(units.solve_cube(&[], 100).len(), usize::from(value));
    }
    // The top-left clue cannot exit to either of its differently numbered
    // neighbors. Other edges may have no SAT mapping when encode exits early.
    let impossible = vec![
        vec![Some(1), Some(2), None, None],
        vec![Some(3), None, None, None],
        vec![None, None, Some(1), Some(2)],
        vec![None, None, Some(3), None],
    ];
    let mut units = NumlinAssumptionSolver::with_fixed_units(
        &impossible, &[(true, 3, 2, true)], NumlinOptions::default(),
    );
    assert!(units.solve_cube(&[], 100).is_empty());
}

#[test]
fn test_numlin_assumption_cubes_and_sharing() {
    for log_encoding in [false, true] {
        for full_cover in [false, true] {
            for short_only in [false, true] {
                let problem = problem_for_tests();
                let options = NumlinOptions {
                    log_encoding,
                    full_cover,
                    short_only,
                    rules: "g2".parse().unwrap(),
                    ..Default::default()
                };
                let mut a = NumlinAssumptionSolver::new(&problem, options);
                let mut b = NumlinAssumptionSolver::new(&problem, options);
                let mut original = NumlinAssumptionSolver::new(&problem, options);
                let mut shared: Vec<Vec<NumlinSatLiteral>> = vec![];
                let cubes = vec![
                    vec![(true, 0, 0, false)],
                    vec![(true, 0, 0, true)],
                    vec![(true, 0, 0, false), (true, 0, 0, true)],
                    vec![],
                ];
                // Repeat and reverse the cubes to exercise backtracking, scoped blockers,
                // contradictory assumptions, and importing after both SAT and UNSAT.
                for fixed in cubes.iter().chain(cubes.iter().rev()) {
                    let reference =
                        enumerate_answers_numlin_with_options(&problem, 100, fixed, options);
                    let actual = a.solve_cube(fixed, 100);
                    let sorted = |answers: &[graph::BoolGridEdgesModel]| {
                        let mut flat: Vec<_> = answers.iter().map(answer_flat).collect();
                        flat.sort();
                        flat
                    };
                    assert_eq!(sorted(&actual), sorted(&reference));
                    let mut units = NumlinAssumptionSolver::with_fixed_units(&problem, &[], options);
                    for clause in &shared { units.add_learnt(clause); }
                    units.add_fixed_units(fixed);
                    assert_eq!(units.encoding_fingerprint(), original.encoding_fingerprint());
                    assert_eq!(sorted(&units.solve_cube(&[], 100)), sorted(&reference));
                    for clause in units.independent_learnts(30, 0) {
                        assert!(original.check_shared_clause(&clause));
                        shared.push(clause);
                    }
                    for clause in a.learnts() {
                        // An exported clause must follow from the original formula alone,
                        // including after private enumeration blockers were used.
                        let negated: Vec<_> = clause.iter().map(|&lit| !lit).collect();
                        assert!(original
                            .solver
                            .solve_encoded_with_assumptions(&negated)
                            .is_none());
                        b.add_learnt(&clause);
                    }
                    assert_eq!(sorted(&b.solve_cube(fixed, 100)), sorted(&reference));
                    for clause in b.learnts() {
                        a.add_learnt(&clause);
                    }
                }
            }
        }
    }
    // Non-unique instances verify complete enumeration and selector isolation.
    for seed in 0..10 {
        let Some(problem) = instance_generator::generate_instance_by_csp(5, 6, seed) else {
            continue;
        };
        let mut solver = NumlinAssumptionSolver::new(&problem, NumlinOptions::default());
        for fixed in [
            vec![],
            vec![(true, 0, 0, true)],
            vec![(true, 0, 0, false)],
            vec![],
        ] {
            let mut expected: Vec<_> = enumerate_answers_numlin(&problem, 1000)
                .iter()
                .filter(|a| fixed.iter().all(|&(_, y, x, v)| a.horizontal[y][x] == v))
                .map(answer_flat)
                .collect();
            expected.sort();
            let mut actual: Vec<_> = solver
                .solve_cube(&fixed, 1000)
                .iter()
                .map(answer_flat)
                .collect();
            actual.sort();
            assert_eq!(actual, expected);
            let mut units = NumlinAssumptionSolver::with_fixed_units(
                &problem,
                &fixed,
                NumlinOptions::default(),
            );
            assert_eq!(units.encoding_fingerprint(), solver.encoding_fingerprint());
            let mut actual: Vec<_> = units.solve_cube(&[], 1000).iter().map(answer_flat).collect();
            actual.sort();
            assert_eq!(actual, expected);
        }
    }
}
