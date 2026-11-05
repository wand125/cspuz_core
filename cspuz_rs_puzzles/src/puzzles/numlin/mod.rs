use crate::util;
use cspuz_rs::graph;
use cspuz_rs::serializer::{
    problem_to_url, url_to_problem, Choice, Combinator, Dict, Grid, HexInt, Optionalize, Spaces,
};
use cspuz_rs::solver::{any, Config, Solver};

mod propagator;
mod rules;

pub use cspuz_core::sat::Lit as NumlinSatLiteral;
pub use rules::NumlinRules;

/// Optional shortening canonicalizations. Existing entry points keep their old behavior.
#[derive(Clone, Copy, Debug, Default)]
pub struct NumlinOptions {
    pub rules: NumlinRules,
    /// Require degree two at every non-clue vertex. Disables the shortening rules.
    pub full_cover: bool,
    /// Require at least one unused non-clue vertex.
    pub short_only: bool,
    /// Enable logarithmic integer encoding when applicable.
    pub log_encoding: bool,
    /// Omit the per-cell clue-id integer variables; connectivity and clue matching are then
    /// enforced by the path propagator alone (the diag rule, which needs the ids, is skipped).
    pub edges_only: bool,
}

pub fn enumerate_answers_numlin(
    clues: &[Vec<Option<i32>>],
    num_max_answers: usize,
) -> Vec<graph::BoolGridEdgesModel> {
    enumerate_answers_numlin_impl(clues, num_max_answers, true, &[])
}

/// Fixed edge: (is_horizontal, y, x, value). Horizontal edges are indexed like
/// `GridEdges::horizontal` (y in 0..h, x in 0..w-1), vertical like `vertical` (y in 0..h-1, x in 0..w).
pub type FixedEdge = (bool, usize, usize, bool);

/// Same as `enumerate_answers_numlin` with some edges pre-assigned (cube-and-conquer).
pub fn enumerate_answers_numlin_fixed(
    clues: &[Vec<Option<i32>>],
    num_max_answers: usize,
    fixed: &[FixedEdge],
) -> Vec<graph::BoolGridEdgesModel> {
    enumerate_answers_numlin_impl(clues, num_max_answers, true, fixed)
}

pub fn enumerate_answers_numlin_impl(
    clues: &[Vec<Option<i32>>],
    num_max_answers: usize,
    use_propagator: bool,
    fixed: &[FixedEdge],
) -> Vec<graph::BoolGridEdgesModel> {
    enumerate_answers_numlin_impl_with_options(
        clues,
        num_max_answers,
        use_propagator,
        fixed,
        NumlinOptions::default(),
    )
}

/// Enumerate with optional canonicalizations and/or full coverage, including fixed edges.
/// Shortening preserves existence on an unrestricted board, but can change counts and
/// satisfiability of an individual fixed-edge cube.
pub fn enumerate_answers_numlin_with_options(
    clues: &[Vec<Option<i32>>],
    num_max_answers: usize,
    fixed: &[FixedEdge],
    options: NumlinOptions,
) -> Vec<graph::BoolGridEdgesModel> {
    enumerate_answers_numlin_impl_with_options(clues, num_max_answers, true, fixed, options)
}

fn enumerate_answers_numlin_impl_with_options(
    clues: &[Vec<Option<i32>>],
    num_max_answers: usize,
    use_propagator: bool,
    fixed: &[FixedEdge],
    options: NumlinOptions,
) -> Vec<graph::BoolGridEdgesModel> {
    let (solver, is_line) = build_model(clues, use_propagator, fixed, options);
    solver
        .answer_iter()
        .take(if options.short_only {
            num_max_answers.min(1)
        } else {
            num_max_answers
        })
        .map(|f| f.get_unwrap(&is_line))
        .collect()
}

fn build_model(
    clues: &[Vec<Option<i32>>],
    use_propagator: bool,
    fixed: &[FixedEdge],
    options: NumlinOptions,
) -> (Solver<'static>, graph::BoolGridEdges) {
    let (h, w) = util::infer_shape(clues);

    let mut solver = if options.log_encoding {
        // `use_log_encoding` is already the default and never selects the log encoding for
        // the small clue-id domains, so the option must force it.
        Solver::with_config(Config {
            use_log_encoding: true,
            force_use_log_encoding: true,
            ..Config::default()
        })
    } else {
        Solver::new()
    };

    let is_line = graph::GridEdges::new(&mut solver, (h - 1, w - 1));
    solver.add_answer_key_bool(&is_line.horizontal);
    solver.add_answer_key_bool(&is_line.vertical);

    for &(horizontal, y, x, value) in fixed {
        let var = if horizontal {
            is_line.horizontal.at((y, x))
        } else {
            is_line.vertical.at((y, x))
        };
        if value {
            solver.add_expr(var.expr());
        } else {
            solver.add_expr(!var.expr());
        }
    }

    for y in 0..h {
        for x in 0..w {
            if clues[y][x].is_some() {
                solver.add_expr(is_line.vertex_neighbors((y, x)).count_true().eq(1));
            } else if options.full_cover {
                solver.add_expr(is_line.vertex_neighbors((y, x)).count_true().eq(2));
            } else {
                solver.add_expr(
                    is_line.vertex_neighbors((y, x)).count_true().eq(0)
                        | is_line.vertex_neighbors((y, x)).count_true().eq(2),
                );
            }
        }
    }

    if options.short_only {
        solver.add_expr(any((0..h)
            .flat_map(|y| (0..w).map(move |x| (y, x)))
            .filter(|&(y, x)| clues[y][x].is_none())
            .map(|v| !is_line.vertex_neighbors(v).any())));
    }

    // forbid trivial detour
    for y in 0..(h - 1) {
        for x in 0..(w - 1) {
            solver.add_expr(is_line.cell_neighbors((y, x)).count_true().le(2));
        }
    }

    // L-shape canonization
    for y in 0..(h - 1) {
        for x in 0..(w - 1) {
            if clues[y + 1][x + 1].is_none() {
                if y == h - 2 || x == w - 2 {
                    solver.add_expr(!(is_line.horizontal.at((y, x)) & is_line.vertical.at((y, x))));
                } else {
                    solver.add_expr(
                        (is_line.horizontal.at((y, x)) & is_line.vertical.at((y, x))).imp(
                            is_line.horizontal.at((y + 1, x + 1))
                                & is_line.vertical.at((y + 1, x + 1)),
                        ),
                    );
                }
            }

            if clues[y + 1][x].is_none() {
                if y == h - 2 || x == 0 {
                    solver.add_expr(
                        !(is_line.horizontal.at((y, x)) & is_line.vertical.at((y, x + 1))),
                    );
                } else {
                    solver.add_expr(
                        (is_line.horizontal.at((y, x)) & is_line.vertical.at((y, x + 1))).imp(
                            is_line.horizontal.at((y + 1, x - 1)) & is_line.vertical.at((y + 1, x)),
                        ),
                    );
                }
            }
        }
    }

    let mut max_clue = 0;
    for y in 0..h {
        for x in 0..w {
            if let Some(n) = clues[y][x] {
                max_clue = max_clue.max(n);
            }
        }
    }

    let cell_clue_id = (!options.edges_only).then(|| solver.int_var_2d((h, w), 0, max_clue));
    if let Some(cell_clue_id) = &cell_clue_id {
        for y in 0..h {
            for x in 0..w {
                if let Some(n) = clues[y][x] {
                    solver.add_expr(cell_clue_id.at((y, x)).eq(n));
                }
            }
        }

        solver.add_expr(
            is_line.horizontal.imp(
                cell_clue_id
                    .slice((.., 1..))
                    .eq(cell_clue_id.slice((.., ..(w - 1)))),
            ),
        );
        solver.add_expr(
            is_line.vertical.imp(
                cell_clue_id
                    .slice((1.., ..))
                    .eq(cell_clue_id.slice((..(h - 1), ..))),
            ),
        );

        if !options.full_cover && options.rules.diag {
            rules::add_diag(&mut solver, &is_line, cell_clue_id, h, w);
        }
    }
    if !options.full_cover && options.rules.wedge {
        rules::add_wedge(&mut solver, &is_line, clues);
    }
    assert!(use_propagator || !options.edges_only, "edges_only requires the path propagator");

    if use_propagator {
        let mut values = vec![];
        for y in 0..h {
            for x in 0..(w - 1) {
                values.push(is_line.horizontal.at((y, x)).expr());
            }
        }
        for y in 0..(h - 1) {
            for x in 0..w {
                values.push(is_line.vertical.at((y, x)).expr());
            }
        }
        for y in 0..h {
            for x in 0..w {
                values.push(is_line.vertex_neighbors((y, x)).any());
            }
        }

        if options.rules.g2 {
            solver.add_custom_constraint(
                Box::new(propagator::PlanarityPropagator::new(h, w, clues)),
                values.clone(),
            );
        }
        solver.add_custom_constraint(
            Box::new(propagator::PathPropagator::new(h, w, clues)),
            values,
        );
    } else {
        #[cfg(test)]
        {
            let cell_clue_id = cell_clue_id.as_ref().unwrap();
            // acyclic
            let mut graph = graph::Graph::new((h - 1) * (w - 1) + 1);
            let outside = (h - 1) * (w - 1);
            let mut indicator = vec![];

            for y in 0..h {
                for x in 0..(w - 1) {
                    let v1 = if y == 0 {
                        outside
                    } else {
                        (y - 1) * (w - 1) + x
                    };
                    let v2 = if y == h - 1 { outside } else { y * (w - 1) + x };
                    graph.add_edge(v1, v2);
                    indicator.push(!is_line.horizontal.at((y, x)));
                }
            }
            for y in 0..(h - 1) {
                for x in 0..w {
                    let v1 = if x == 0 {
                        outside
                    } else {
                        y * (w - 1) + (x - 1)
                    };
                    let v2 = if x == w - 1 { outside } else { y * (w - 1) + x };
                    graph.add_edge(v1, v2);
                    indicator.push(!is_line.vertical.at((y, x)));
                }
            }
            let is_active = vec![cspuz_rs::solver::TRUE; graph.n_vertices()];
            graph::active_vertices_connected_via_active_edges(
                &mut solver,
                &is_active,
                &indicator,
                &graph,
            );

            // no detour
            let is_passed = &solver.bool_var_2d((h, w));
            for y in 0..h {
                for x in 0..w {
                    solver.add_expr(
                        is_passed
                            .at((y, x))
                            .iff(is_line.vertex_neighbors((y, x)).any()),
                    );
                }
            }
            for y in 0..h {
                for x in 0..(w - 1) {
                    solver.add_expr(
                        (!is_line.horizontal.at((y, x))
                            & is_passed.at((y, x))
                            & is_passed.at((y, x + 1)))
                        .imp(cell_clue_id.at((y, x)).ne(cell_clue_id.at((y, x + 1)))),
                    );
                }
                for x1 in 0..(w - 2) {
                    for x2 in (x1 + 2)..w {
                        solver.add_expr(
                            (is_passed.at((y, x1))
                                & is_passed.at((y, x2))
                                & !(is_passed.slice_fixed_y((y, (x1 + 1)..x2)).any()))
                            .imp(cell_clue_id.at((y, x1)).ne(cell_clue_id.at((y, x2)))),
                        );
                    }
                }
            }
            for x in 0..w {
                for y in 0..(h - 1) {
                    solver.add_expr(
                        (!is_line.vertical.at((y, x))
                            & is_passed.at((y, x))
                            & is_passed.at((y + 1, x)))
                        .imp(cell_clue_id.at((y, x)).ne(cell_clue_id.at((y + 1, x)))),
                    );
                }
                for y1 in 0..(h - 2) {
                    for y2 in (y1 + 2)..h {
                        solver.add_expr(
                            (is_passed.at((y1, x))
                                & is_passed.at((y2, x))
                                & !(is_passed.slice_fixed_x(((y1 + 1)..y2, x)).any()))
                            .imp(cell_clue_id.at((y1, x)).ne(cell_clue_id.at((y2, x)))),
                        );
                    }
                }
            }
        }

        #[cfg(not(test))]
        {
            panic!("use_propagator must be true in non-test code");
        }
    }

    (solver, is_line)
}

pub use cspuz_core::backend::glucose::InterruptHandle;

/// A single encoded board, reused for independent fixed-edge cubes.
/// Enumeration blockers use private selectors and cannot affect subsequent cubes.
pub struct NumlinAssumptionSolver {
    solver: Solver<'static>,
    lines: graph::BoolGridEdges,
    feasible: bool,
    base_vars: usize,
    fingerprint: u64,
    short_only: bool,
    dependency_tagged: bool,
}

impl NumlinAssumptionSolver {
    pub fn new(clues: &[Vec<Option<i32>>], options: NumlinOptions) -> Self {
        Self::with_fixed(clues, &[], options)
    }

    /// A solver with `fixed` edges baked into the encoding as unit constraints (level-0
    /// propagation and simplification apply to them). Learned clauses from such a solver must
    /// not be shared with solvers that have different fixed edges.
    pub fn with_fixed(clues: &[Vec<Option<i32>>], fixed: &[FixedEdge], options: NumlinOptions) -> Self {
        let (mut solver, lines) = build_model(clues, true, fixed, options);
        let feasible = solver.encode();
        let base_vars = solver.glucose().num_var() as usize;
        let fingerprint = solver.glucose().encoding_fingerprint();
        Self {
            solver,
            lines,
            feasible,
            base_vars,
            fingerprint,
            short_only: options.short_only,
            dependency_tagged: false,
        }
    }

    /// Original CNF signature, before private enumeration variables are introduced.
    pub fn encoding_fingerprint(&self) -> u64 {
        self.fingerprint
    }

    /// Encode the common board first, then fix cube edges at SAT level zero.
    /// The saved fingerprint describes the common encoding, before the cube units.
    pub fn with_fixed_units(
        clues: &[Vec<Option<i32>>],
        fixed: &[FixedEdge],
        options: NumlinOptions,
    ) -> Self {
        let mut solver = Self::new(clues, options);
        solver.solver.glucose().track_dependencies();
        solver.dependency_tagged = true;
        solver.add_fixed_units(fixed);
        solver
    }

    pub fn add_fixed_units(&mut self, fixed: &[FixedEdge]) {
        assert!(self.dependency_tagged, "cube units require dependency tracking");
        // An inconsistent CSP can stop encode() before literal maps exist.
        if !self.feasible {
            return;
        }
        for &(horizontal, y, x, value) in fixed {
            let var = if horizontal {
                self.lines.horizontal.at((y, x))
            } else {
                self.lines.vertical.at((y, x))
            };
            match self.solver.encoded_bool_literal(var) {
                Ok(lit) => {
                    self.feasible &= self.solver.glucose().add_cube_unit(if value { lit } else { !lit });
                }
                Err(constant) => self.feasible &= constant == value,
            }
        }
    }

    pub fn solve_cube(
        &mut self,
        fixed: &[FixedEdge],
        max: usize,
    ) -> Vec<graph::BoolGridEdgesModel> {
        self.solve_cube_limited(fixed, max, None)
            .expect("unexpected resource limit without a budget")
    }

    /// Solve a cube with at most `budget` conflicts in total; `None` when the budget runs out
    /// before the enumeration is complete (any answers found so far are discarded, so the
    /// caller can split the cube and solve the parts afresh).
    pub fn solve_cube_limited(
        &mut self,
        fixed: &[FixedEdge],
        max: usize,
        budget: Option<u64>,
    ) -> Option<Vec<graph::BoolGridEdgesModel>> {
        if !self.feasible {
            return Some(vec![]);
        }
        let mut assumptions = vec![];
        for &(horizontal, y, x, value) in fixed {
            let var = if horizontal {
                self.lines.horizontal.at((y, x))
            } else {
                self.lines.vertical.at((y, x))
            };
            match self.solver.encoded_bool_literal(var) {
                Ok(lit) => assumptions.push(if value { lit } else { !lit }),
                Err(constant) if constant != value => return Some(vec![]),
                Err(_) => (),
            }
        }
        let selector = self.solver.glucose().new_var().as_lit(false);
        assumptions.push(selector);
        match budget {
            Some(b) => self.solver.glucose().set_conf_budget(b as i64),
            None => self.solver.glucose().budget_off(),
        }
        self.solver.glucose().clear_interrupt();
        let mut answers = vec![];
        let mut exhausted = false;
        for _ in 0..if self.short_only { max.min(1) } else { max } {
            let model = match self.solver.solve_encoded_with_assumptions_limited(&assumptions) {
                Some(Some(model)) => model,
                Some(None) => break,
                None => {
                    exhausted = true;
                    break;
                }
            };
            let answer = model.get(&self.lines);
            let mut blocker = vec![!selector];
            for (grid, values) in [
                (&self.lines.horizontal, &answer.horizontal),
                (&self.lines.vertical, &answer.vertical),
            ] {
                for y in 0..values.len() {
                    for x in 0..values[y].len() {
                        if let Ok(lit) = self.solver.encoded_bool_literal(grid.at((y, x))) {
                            blocker.push(if values[y][x] { !lit } else { lit });
                        }
                    }
                }
            }
            answers.push(answer);
            self.solver.glucose().add_clause(&blocker);
        }
        // Disable private enumeration clauses; learned clauses containing the selector
        // remain valid locally. Such clauses must never enter the shared pool.
        self.solver.glucose().add_clause(&[!selector]);
        self.solver.glucose().budget_off();
        if exhausted {
            None
        } else {
            Some(answers)
        }
    }

    /// Glucose search statistics so far: (decisions, propagations, conflicts).
    pub fn search_stats(&mut self) -> (u64, u64, u64) {
        let g = self.solver.glucose();
        (g.stats_decisions(), g.stats_propagations(), g.stats_conflicts())
    }

    /// Handle to abort the running `solve_cube_limited` from another thread (it returns `None`).
    pub fn interrupt_handle(&mut self) -> cspuz_core::backend::glucose::InterruptHandle {
        self.solver.glucose().interrupt_handle()
    }

    /// Export only original-encoding literals. Private enumeration selectors are excluded.
    pub fn learnts(&mut self) -> Vec<Vec<cspuz_core::sat::Lit>> {
        if self.dependency_tagged {
            return self.independent_learnts(8, 0);
        }
        let backend = self.solver.glucose();
        let mut result = vec![];
        for i in 0..backend.num_learnts() {
            let mut clause = vec![];
            backend.get_learnt(i, &mut clause);
            if clause.len() <= 8 && clause.iter().all(|l| l.var().index() < self.base_vars) {
                clause.sort_unstable();
                result.push(clause);
            }
        }
        result
    }

    pub fn independent_learnts(&mut self, max_size: usize, max_lbd: u32) -> Vec<Vec<NumlinSatLiteral>> {
        assert!(self.dependency_tagged);
        self.solver.glucose().independent_learnts(max_size, max_lbd).into_iter()
            .filter(|clause| clause.iter().all(|l| l.var().index() < self.base_vars))
            .map(|mut clause| { clause.sort_unstable(); clause })
            .collect()
    }

    /// Counts at learn time, before deletion, size/LBD caps and selector filtering.
    pub fn dependency_learnt_counts(&mut self) -> (u64, u64) {
        self.solver.glucose().dependency_learnt_counts()
    }

    /// Debug oracle: call on a separate common model, with no cube units.
    pub fn check_shared_clause(&mut self, clause: &[NumlinSatLiteral]) -> bool {
        assert!(clause.iter().all(|l| l.var().index() < self.base_vars));
        if !self.feasible { return true; }
        let negated: Vec<_> = clause.iter().map(|&lit| !lit).collect();
        self.solver.glucose().solve_with_assumptions_limited(&negated) == Some(false)
    }

    /// Clauses must come from an identical original encoding (same clues and options).
    pub fn add_learnt(&mut self, clause: &[cspuz_core::sat::Lit]) {
        assert!(clause.iter().all(|l| l.var().index() < self.base_vars));
        self.solver.glucose().add_learnt(clause);
    }
}

type Problem = Vec<Vec<Option<i32>>>;

fn combinator() -> impl Combinator<Problem> {
    Grid::new(Choice::new(vec![
        Box::new(Optionalize::new(HexInt)),
        Box::new(Spaces::new(None, 'g')),
        Box::new(Dict::new(Some(-1), ".")),
    ]))
}

pub fn serialize_problem(problem: &Problem) -> Option<String> {
    problem_to_url(combinator(), "numlin", problem.clone())
}

pub fn deserialize_problem(url: &str) -> Option<Problem> {
    url_to_problem(combinator(), &["numlin"], url)
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod instance_generator;
