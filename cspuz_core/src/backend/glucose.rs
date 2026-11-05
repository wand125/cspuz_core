use std::ffi::{c_void, CString};
use std::ops::Drop;
use std::os::raw::c_char;

use crate::propagators::graph_division::{GraphDivision, GraphDivisionOptions};
use crate::propagators::order_encoding_linear;
use crate::sat::{
    CustomPropagator, GraphDivisionMode, Lit, OrderEncodingLinearMode, SolverManipulator, Var,
};

#[repr(C)]
struct Opaque {
    _private: [u8; 0],
}

extern "C-unwind" {
    fn Glucose_CreateSolver() -> *mut Opaque;
    fn Glucose_DestroySolver(solver: *mut Opaque);
    fn Glucose_NewVar(solver: *mut Opaque) -> i32;
    fn Glucose_NewNamedVar(solver: *mut Opaque, name: *const c_char) -> i32;
    fn Glucose_AddClause(solver: *mut Opaque, lits: *const Lit, n_lits: i32) -> i32;
    fn Glucose_Solve(solver: *mut Opaque) -> i32;
    fn Glucose_SolveWithAssumptions(solver: *mut Opaque, lits: *const Lit, n: i32) -> i32;
    fn Glucose_EncodingFingerprint(solver: *mut Opaque) -> u64;
    fn Glucose_NumLearnts(solver: *mut Opaque) -> i32;
    fn Glucose_GetLearnt(solver: *mut Opaque, i: i32, out: *mut Lit) -> i32;
    fn Glucose_AddLearnt(solver: *mut Opaque, lits: *const Lit, n: i32) -> i32;
    fn Glucose_TrackDependencies(solver: *mut Opaque);
    fn Glucose_AddCubeUnit(solver: *mut Opaque, lit: Lit) -> i32;
    fn Glucose_GetIndependentLearnt(solver: *mut Opaque, i: i32, out: *mut Lit, max_size: i32, max_lbd: u32) -> i32;
    fn Glucose_DependencyLearntCount(solver: *mut Opaque, independent: i32) -> u64;
    fn Glucose_NumVar(solver: *mut Opaque) -> i32;
    fn Glucose_GetModelValueVar(solver: *mut Opaque, var: i32) -> i32;
    fn Glucose_SetPolarity(solver: *mut Opaque, var: i32, polarity: i32);
    fn Glucose_AddOrderEncodingLinear(
        solver: *mut Opaque,
        n_terms: i32,
        domain_size: *const i32,
        lits: *const Lit,
        domain: *const i32,
        coefs: *const i32,
        constant: i32,
    ) -> i32;
    fn Glucose_AddActiveVerticesConnected(
        solver: *mut Opaque,
        n_vertices: i32,
        lits: *const Lit,
        n_edges: i32,
        edges: *const i32,
    ) -> i32;
    fn Glucose_AddDirectEncodingExtensionSupports(
        solver: *mut Opaque,
        n_vars: i32,
        domain_size: *const i32,
        lits: *const Lit,
        n_supports: i32,
        supports: *const i32,
    ) -> i32;
    fn Glucose_AddGraphDivision(
        solver: *mut Opaque,
        n_vertices: i32,
        dom_sizes: *const i32,
        domains: *const i32,
        dom_lits: *const Lit,
        n_edges: i32,
        edges: *const i32,
        edge_lits: *const Lit,
    ) -> i32;
    fn Glucose_SolverStats_decisions(solver: *mut Opaque) -> u64;
    fn Glucose_SolverStats_propagations(solver: *mut Opaque) -> u64;
    fn Glucose_SolverStats_conflicts(solver: *mut Opaque) -> u64;
    fn Glucose_Set_random_seed(solver: *mut Opaque, random_seed: f64);
    fn Glucose_Set_rnd_init_act(solver: *mut Opaque, rnd_init_act: i32);
    fn Glucose_Set_random_var_freq(solver: *mut Opaque, freq: f64);
    fn Glucose_Set_reduce_db(solver: *mut Opaque, first: i32, inc: i32);
    fn Glucose_Set_no_learn(solver: *mut Opaque, value: i32);
    fn Glucose_SetConfBudget(solver: *mut Opaque, budget: i64);
    fn Glucose_BudgetOff(solver: *mut Opaque);
    fn Glucose_Interrupt(solver: *mut Opaque);
    fn Glucose_ClearInterrupt(solver: *mut Opaque);
    fn Glucose_Set_dump_analysis_info(solver: *mut Opaque, value: i32);
}

/// See `Solver::interrupt_handle`. Only sets glucose's `asynch_interrupt` flag.
#[derive(Clone, Copy)]
pub struct InterruptHandle {
    ptr: usize,
}

impl InterruptHandle {
    pub fn interrupt(&self) {
        unsafe { Glucose_Interrupt(self.ptr as *mut Opaque) }
    }
}

pub struct Solver {
    ptr: *mut Opaque,

    // We have to pass pointers to `dyn CustomPropagator` to the C++ code.
    // Since Box<dyn ...> uses a fat pointer and its representation is not specified,
    // we deliberately use `Box<Box<dyn ...>>` to make it a thin pointer.
    // https://doc.rust-lang.org/reference/type-layout.html#r-layout.pointer.unsized
    #[allow(clippy::vec_box)]
    custom_constraints: Vec<Box<Box<dyn CustomPropagator<GlucoseSolverManipulator>>>>,
}

const NUM_VAR_MAX: i32 = 0x3fffffff;

// The native bridge uses signed 32-bit offsets into flattened arrays.
fn checked_total_len(lengths: impl IntoIterator<Item = usize>) -> usize {
    lengths.into_iter().fold(0usize, |total, len| {
        let total = total.checked_add(len).expect("array length overflow");
        assert!(
            total <= i32::MAX as usize,
            "array exceeds native index range"
        );
        total
    })
}

impl Solver {
    pub fn new() -> Solver {
        let ptr = unsafe { Glucose_CreateSolver() };
        assert!(!ptr.is_null());
        Solver {
            ptr,
            custom_constraints: vec![],
        }
    }

    pub fn new_var(&mut self) -> Var {
        assert!(self.num_var() <= NUM_VAR_MAX);
        let var_id = unsafe { Glucose_NewVar(self.ptr) };
        assert!((0..=NUM_VAR_MAX).contains(&var_id));
        Var(var_id)
    }

    pub fn new_named_var(&mut self, name: &str) -> Var {
        assert!(self.num_var() <= NUM_VAR_MAX);
        let c_string = CString::new(name).unwrap();
        let var_id = unsafe { Glucose_NewNamedVar(self.ptr, c_string.as_ptr()) };
        assert!((0..=NUM_VAR_MAX).contains(&var_id));
        Var(var_id)
    }

    pub fn num_var(&self) -> i32 {
        unsafe { Glucose_NumVar(self.ptr) }
    }

    pub fn all_vars(&self) -> Vec<Var> {
        (0..self.num_var()).map(Var).collect()
    }

    fn validate_lits<'a>(&self, lits: impl IntoIterator<Item = &'a Lit>) {
        let num_var = self.num_var();
        for &lit in lits {
            assert!(lit.0 >= 0 && lit.var().0 < num_var, "invalid SAT literal");
        }
    }

    pub fn set_polarity(&mut self, var: Var, polarity: bool) {
        assert!(0 <= var.0 && var.0 < self.num_var());
        unsafe { Glucose_SetPolarity(self.ptr, var.0, if polarity { 1 } else { 0 }) }
    }

    pub fn add_clause(&mut self, clause: &[Lit]) -> bool {
        assert!(clause.len() <= i32::MAX as usize);
        self.validate_lits(clause);
        let res = unsafe { Glucose_AddClause(self.ptr, clause.as_ptr(), clause.len() as i32) };
        res != 0
    }

    pub fn add_order_encoding_linear(
        &mut self,
        lits: &[Vec<Lit>],
        domain: &[Vec<i32>],
        coefs: &[i32],
        constant: i32,
        mode: OrderEncodingLinearMode,
    ) -> bool {
        assert!(lits.len() <= i32::MAX as usize);
        assert_eq!(lits.len(), domain.len());
        assert_eq!(lits.len(), coefs.len());

        for i in 0..lits.len() {
            assert!(domain[i].len() <= i32::MAX as usize);
            assert_eq!(lits[i].len() + 1, domain[i].len());
        }

        checked_total_len(domain.iter().map(Vec::len));
        self.validate_lits(lits.iter().flatten());
        for values in domain {
            assert!(
                values.windows(2).all(|w| w[0] < w[1]),
                "domain must be strictly increasing"
            );
        }

        match mode {
            OrderEncodingLinearMode::Cpp => {
                assert!(coefs.iter().all(|&coef| coef != 0), "zero coefficient");
                let n_terms = lits.len() as i32;
                let domain_size = domain.iter().map(|x| x.len() as i32).collect::<Vec<_>>();
                let lits_flat = lits.iter().flatten().copied().collect::<Vec<_>>();
                let domain_flat = domain.iter().flatten().copied().collect::<Vec<_>>();
                let res = unsafe {
                    Glucose_AddOrderEncodingLinear(
                        self.ptr,
                        n_terms,
                        domain_size.as_ptr(),
                        lits_flat.as_ptr(),
                        domain_flat.as_ptr(),
                        coefs.as_ptr(),
                        constant,
                    )
                };
                res != 0
            }
            OrderEncodingLinearMode::Rust | OrderEncodingLinearMode::RustOptimized => {
                let mut terms = vec![];
                for i in 0..lits.len() {
                    terms.push(order_encoding_linear::LinearTerm::new(
                        lits[i].clone(),
                        domain[i].clone(),
                        coefs[i],
                    ));
                }
                let optimized = mode == OrderEncodingLinearMode::RustOptimized;
                self.add_custom_constraint(Box::new(
                    order_encoding_linear::OrderEncodingLinear::new(terms, constant, optimized),
                ))
            }
        }
    }

    pub fn add_active_vertices_connected(
        &mut self,
        lits: &[Lit],
        edges: &[(usize, usize)],
    ) -> bool {
        assert!(lits.len() <= i32::MAX as usize);
        assert!(edges.len() <= (i32::MAX as usize) / 2);
        self.validate_lits(lits);

        let mut edges_flat = vec![];
        for &(u, v) in edges {
            assert!(u < lits.len());
            assert!(v < lits.len());
            edges_flat.push(u as i32);
            edges_flat.push(v as i32);
        }

        let res = unsafe {
            Glucose_AddActiveVerticesConnected(
                self.ptr,
                lits.len() as i32,
                lits.as_ptr(),
                edges.len() as i32,
                edges_flat.as_ptr(),
            )
        };
        res != 0
    }

    pub fn add_direct_encoding_extension_supports(
        &mut self,
        vars: &[Vec<Lit>],
        supports: &[Vec<Option<usize>>],
    ) -> bool {
        assert!(vars.len() <= i32::MAX as usize);
        assert!(supports.len() <= i32::MAX as usize);
        checked_total_len(vars.iter().map(Vec::len));
        assert!(vars
            .len()
            .checked_mul(supports.len())
            .is_some_and(|n| n <= i32::MAX as usize));
        self.validate_lits(vars.iter().flatten());

        let domain_size = vars.iter().map(|v| v.len() as i32).collect::<Vec<_>>();
        let vars_flat = vars.iter().flatten().copied().collect::<Vec<_>>();
        let mut supports_flat = vec![];
        for support in supports {
            assert_eq!(vars.len(), support.len());
            for i in 0..vars.len() {
                if let Some(n) = support[i] {
                    assert!(n < vars[i].len());
                    supports_flat.push(n as i32);
                } else {
                    supports_flat.push(-1);
                }
            }
        }

        let res = unsafe {
            Glucose_AddDirectEncodingExtensionSupports(
                self.ptr,
                vars.len() as i32,
                domain_size.as_ptr(),
                vars_flat.as_ptr(),
                supports.len() as i32,
                supports_flat.as_ptr(),
            )
        };
        res != 0
    }

    pub fn add_graph_division(
        &mut self,
        domains: &[Vec<i32>],
        dom_lits: &[Vec<Lit>],
        edges: &[(usize, usize)],
        edge_lits: &[Lit],
        mode: GraphDivisionMode,
        opts: &GraphDivisionOptions,
    ) -> bool {
        assert!(domains.len() <= i32::MAX as usize);
        assert!(edges.len() <= (i32::MAX as usize) / 2);
        assert_eq!(domains.len(), dom_lits.len());
        assert_eq!(edges.len(), edge_lits.len());
        checked_total_len(domains.iter().map(Vec::len));
        for (domain, lits) in domains.iter().zip(dom_lits) {
            assert_eq!(lits.len(), domain.len().saturating_sub(1));
            assert!(
                domain.windows(2).all(|w| w[0] < w[1]),
                "domain must be strictly increasing"
            );
        }
        self.validate_lits(dom_lits.iter().flatten());
        self.validate_lits(edge_lits);
        for &(u, v) in edges {
            assert!(
                u < domains.len() && v < domains.len(),
                "invalid graph endpoint"
            );
            assert_ne!(u, v, "graph division does not support self-loops");
        }

        if mode == GraphDivisionMode::Rust {
            let vertex_weights = vec![1; domains.len()];
            let constr =
                GraphDivision::new(domains, dom_lits, &vertex_weights, edges, edge_lits, opts);
            return self.add_custom_constraint(Box::new(constr));
        }

        assert!(!opts.require_extra_constraints());

        let mut dom_sizes = vec![];
        let mut dom_lits_flat = vec![];
        let mut domains_flat = vec![];

        for i in 0..domains.len() {
            dom_sizes.push(domains[i].len() as i32);
            if !domains[i].is_empty() {
                assert_eq!(domains[i].len(), dom_lits[i].len() + 1);
                for &v in &domains[i] {
                    domains_flat.push(v);
                }
                for &l in &dom_lits[i] {
                    dom_lits_flat.push(l);
                }
            }
        }

        let mut edges_flat = vec![];
        for &(u, v) in edges {
            edges_flat.push(u as i32);
            edges_flat.push(v as i32);
        }

        let res = unsafe {
            Glucose_AddGraphDivision(
                self.ptr,
                domains.len() as i32,
                dom_sizes.as_ptr(),
                domains_flat.as_ptr(),
                dom_lits_flat.as_ptr(),
                edges.len() as i32,
                edges_flat.as_ptr(),
                edge_lits.as_ptr(),
            )
        };
        res != 0
    }

    pub fn add_custom_constraint(
        &mut self,
        constraint: Box<dyn CustomPropagator<GlucoseSolverManipulator>>,
    ) -> bool {
        self.custom_constraints.push(Box::new(constraint));
        #[allow(clippy::borrowed_box)]
        let c: &Box<dyn CustomPropagator<GlucoseSolverManipulator>> =
            &self.custom_constraints[self.custom_constraints.len() - 1];
        let c = unsafe { std::mem::transmute::<_, *mut c_void>(c) };
        let res = unsafe { Glucose_AddRustExtraConstraint(self.ptr, c) };
        res != 0
    }

    pub fn set_seed(&mut self, seed: f64) {
        unsafe {
            Glucose_Set_random_seed(self.ptr, seed);
        }
    }

    /// Fraction of decisions made on a random variable (0 = pure activity order).
    pub fn set_random_var_freq(&mut self, freq: f64) {
        unsafe { Glucose_Set_random_var_freq(self.ptr, freq) }
    }

    /// Experiment: discard all learnt clauses (backjump + flip as a decision).
    pub fn set_no_learn(&mut self, value: bool) {
        unsafe { Glucose_Set_no_learn(self.ptr, value as i32) }
    }

    /// Learnt database reduction schedule (first, inc); small values keep few learnt clauses.
    pub fn set_reduce_db(&mut self, first: i32, inc: i32) {
        unsafe { Glucose_Set_reduce_db(self.ptr, first, inc) }
    }

    pub fn set_rnd_init_act(&mut self, rnd_init_act: bool) {
        unsafe {
            Glucose_Set_rnd_init_act(self.ptr, if rnd_init_act { 1 } else { 0 });
        }
    }

    pub fn set_dump_analysis_info(&mut self, dump_analysis_info: bool) {
        unsafe { Glucose_Set_dump_analysis_info(self.ptr, if dump_analysis_info { 1 } else { 0 }) }
    }

    pub fn solve(&mut self) -> Option<Model<'_>> {
        if self.solve_without_model() {
            Some(unsafe { self.model() })
        } else {
            None
        }
    }

    pub fn solve_without_model(&mut self) -> bool {
        let res = unsafe { Glucose_Solve(self.ptr) };
        res != 0
    }

    /// Assumptions last for this call only; learned clauses remain in the solver.
    pub fn solve_with_assumptions(&mut self, assumptions: &[Lit]) -> Option<Model<'_>> {
        match self.solve_with_assumptions_limited(assumptions) {
            Some(true) => Some(unsafe { self.model() }),
            Some(false) => None,
            None => panic!("unexpected resource limit in assumption solve"),
        }
    }

    /// Like `solve_with_assumptions`, but returns `None` when the conflict budget set by
    /// `set_conf_budget` runs out before the search finishes. The model is available through
    /// `model()` only after `Some(true)`.
    pub fn solve_with_assumptions_limited(&mut self, assumptions: &[Lit]) -> Option<bool> {
        self.validate_lits(assumptions);
        assert!(assumptions.len() <= i32::MAX as usize);
        let res = unsafe {
            Glucose_SolveWithAssumptions(self.ptr, assumptions.as_ptr(), assumptions.len() as i32)
        };
        match res {
            1 => Some(true),
            0 => Some(false),
            _ => None,
        }
    }

    /// Limit the following assumption solves to `budget` more conflicts in total.
    pub fn set_conf_budget(&mut self, budget: i64) {
        unsafe { Glucose_SetConfBudget(self.ptr, budget) }
    }

    pub fn budget_off(&mut self) {
        unsafe { Glucose_BudgetOff(self.ptr) }
    }

    /// Clear a pending asynchronous interrupt before the next solve.
    pub fn clear_interrupt(&mut self) {
        unsafe { Glucose_ClearInterrupt(self.ptr) }
    }

    /// A handle that can interrupt this solver's current `solve_with_assumptions_limited`
    /// from another thread (the call then returns `None`). The handle must not outlive the solver.
    pub fn interrupt_handle(&mut self) -> InterruptHandle {
        InterruptHandle { ptr: self.ptr as usize }
    }

    /// A guard against sharing raw literal IDs across different encodings.
    /// Call before the first solve, while only the original formula is present.
    pub fn encoding_fingerprint(&self) -> u64 {
        unsafe { Glucose_EncodingFingerprint(self.ptr) }
    }

    pub fn num_learnts(&self) -> usize {
        unsafe { Glucose_NumLearnts(self.ptr) as usize }
    }

    /// Enable tracking before adding any cube units. Existing root facts are global.
    pub fn track_dependencies(&mut self) {
        unsafe { Glucose_TrackDependencies(self.ptr) }
    }

    /// Add a permanent local cube fact after `track_dependencies` was enabled.
    pub fn add_cube_unit(&mut self, lit: Lit) -> bool {
        self.validate_lits(&[lit]);
        unsafe { Glucose_AddCubeUnit(self.ptr, lit) != 0 }
    }

    /// New independent retained clauses and learned units; imports are omitted.
    /// max_lbd=0 disables that cap.
    pub fn independent_learnts(&self, max_size: usize, max_lbd: u32) -> Vec<Vec<Lit>> {
        assert!(max_size <= i32::MAX as usize);
        let mut result = vec![];
        for i in 0..self.num_learnts() {
            let n = unsafe { Glucose_GetIndependentLearnt(self.ptr, i as i32, std::ptr::null_mut(), max_size as i32, max_lbd) };
            if n < 0 { continue; }
            let mut clause = vec![Lit(0); n as usize];
            unsafe { Glucose_GetIndependentLearnt(self.ptr, i as i32, clause.as_mut_ptr(), max_size as i32, max_lbd); }
            result.push(clause);
        }
        result
    }

    /// (All learned clauses, independent learned clauses), counted at creation.
    pub fn dependency_learnt_counts(&self) -> (u64, u64) {
        unsafe { (Glucose_DependencyLearntCount(self.ptr, 0), Glucose_DependencyLearntCount(self.ptr, 1)) }
    }

    /// Indices are valid until the next mutation/solve (Glucose can delete/reorder clauses).
    pub fn get_learnt(&self, i: usize, out: &mut Vec<Lit>) {
        assert!(i < self.num_learnts());
        let n = unsafe { Glucose_GetLearnt(self.ptr, i as i32, std::ptr::null_mut()) };
        assert!(n >= 0);
        out.resize(n as usize, Lit(0));
        unsafe {
            Glucose_GetLearnt(self.ptr, i as i32, out.as_mut_ptr());
        }
    }

    /// Caller must ensure the clause is implied by this solver's formula.
    pub fn add_learnt(&mut self, lits: &[Lit]) -> bool {
        self.validate_lits(lits);
        assert!(lits.len() <= i32::MAX as usize);
        unsafe { Glucose_AddLearnt(self.ptr, lits.as_ptr(), lits.len() as i32) != 0 }
    }

    pub(crate) unsafe fn model(&self) -> Model<'_> {
        Model { solver: self }
    }

    pub fn stats_decisions(&self) -> u64 {
        unsafe { Glucose_SolverStats_decisions(self.ptr) }
    }

    pub fn stats_propagations(&self) -> u64 {
        unsafe { Glucose_SolverStats_propagations(self.ptr) }
    }

    pub fn stats_conflicts(&self) -> u64 {
        unsafe { Glucose_SolverStats_conflicts(self.ptr) }
    }
}

impl Drop for Solver {
    fn drop(&mut self) {
        unsafe {
            Glucose_DestroySolver(self.ptr);
        }
    }
}

const LIT_UNDEF: Lit = Lit(-2);

#[derive(Clone, Copy)]
pub struct Model<'a> {
    solver: &'a Solver,
}

impl Model<'_> {
    pub fn assignment(&self, var: Var) -> bool {
        assert!(0 <= var.0 && var.0 < self.solver.num_var());
        unsafe { Glucose_GetModelValueVar(self.solver.ptr, var.0) != 0 }
    }
}

// Interface for implementing custom constraints in Rust

extern "C-unwind" {
    fn Glucose_AddRustExtraConstraint(solver: *mut Opaque, trait_object: *mut c_void) -> i32;
    fn Glucose_CustomPropagatorCopyReason(reason_vec: *mut c_void, n_lits: i32, lits: *const Lit);
    fn Glucose_SolverValue(solver: *mut Opaque, lit: Lit) -> i32;
    fn Glucose_SolverAddWatch(solver: *mut Opaque, lit: Lit, wrapper_object: *mut c_void);
    fn Glucose_SolverEnqueue(solver: *mut Opaque, lit: Lit, wrapper_object: *mut c_void) -> i32;

    fn Glucose_IsCurrentLevel(solver: *mut Opaque, lit: Lit) -> i32;
}

#[derive(Clone, Copy)]
pub struct GlucoseSolverManipulator {
    ptr: *mut Opaque,
    wrapper_object: Option<*mut c_void>,
}

unsafe impl SolverManipulator for GlucoseSolverManipulator {
    unsafe fn value(&self, lit: Lit) -> Option<bool> {
        let v = Glucose_SolverValue(self.ptr, lit);
        match v {
            0 => Some(true),
            1 => Some(false),
            2 | 3 => None,
            _ => unreachable!(),
        }
    }

    unsafe fn add_watch(&mut self, lit: Lit) {
        assert!(self.wrapper_object.is_some());
        Glucose_SolverAddWatch(self.ptr, lit, self.wrapper_object.unwrap());
    }

    unsafe fn enqueue(&mut self, lit: Lit) -> bool {
        assert!(self.wrapper_object.is_some());
        Glucose_SolverEnqueue(self.ptr, lit, self.wrapper_object.unwrap()) != 0
    }

    unsafe fn is_current_level(&self, lit: Lit) -> bool {
        Glucose_IsCurrentLevel(self.ptr, lit) != 0
    }
}

#[no_mangle]
extern "C-unwind" fn Glucose_CallCustomPropagatorInitialize(
    solver: *mut Opaque,
    wrapper_object: *mut c_void,
    trait_object: *mut c_void,
) -> i32 {
    let trait_object =
        unsafe { &mut *trait_object.cast::<Box<dyn CustomPropagator<GlucoseSolverManipulator>>>() };
    let res = trait_object.initialize(&mut GlucoseSolverManipulator {
        ptr: solver,
        wrapper_object: Some(wrapper_object),
    });
    if res {
        1
    } else {
        0
    }
}

#[no_mangle]
extern "C-unwind" fn Glucose_CallCustomPropagatorPropagate(
    solver: *mut Opaque,
    wrapper_object: *mut c_void,
    trait_object: *mut c_void,
    p: Lit,
    num_pending_propagations: i32,
) -> i32 {
    let trait_object =
        unsafe { &mut *trait_object.cast::<Box<dyn CustomPropagator<GlucoseSolverManipulator>>>() };
    let res = trait_object.propagate(
        &mut GlucoseSolverManipulator {
            ptr: solver,
            wrapper_object: Some(wrapper_object),
        },
        p,
        num_pending_propagations,
    );
    if res {
        1
    } else {
        0
    }
}

#[no_mangle]
extern "C-unwind" fn Glucose_CallCustomPropagatorCalcReason(
    solver: *mut Opaque,
    trait_object: *mut c_void,
    p: Lit,
    extra: Lit,
    out_reason: *mut c_void,
) {
    let trait_object =
        unsafe { &mut *trait_object.cast::<Box<dyn CustomPropagator<GlucoseSolverManipulator>>>() };
    let res = trait_object.calc_reason(
        &mut GlucoseSolverManipulator {
            ptr: solver,
            wrapper_object: None,
        },
        if p != LIT_UNDEF { Some(p) } else { None },
        if extra != LIT_UNDEF {
            Some(extra)
        } else {
            None
        },
    );
    assert!(res.len() <= i32::MAX as usize);
    let num_var = unsafe { Glucose_NumVar(solver) };
    let mut has_current_level = false;
    for &lit in &res {
        assert!(
            lit.0 >= 0 && lit.var().0 < num_var,
            "invalid reason literal"
        );
        assert_eq!(unsafe { Glucose_SolverValue(solver, lit) }, 0);
        if unsafe { Glucose_IsCurrentLevel(solver, lit) } != 0 {
            has_current_level = true;
        }
    }
    assert!(res.is_empty() || has_current_level);

    unsafe {
        Glucose_CustomPropagatorCopyReason(out_reason, res.len() as i32, res.as_ptr());
    }
}

#[no_mangle]
extern "C-unwind" fn Glucose_CallCustomPropagatorUndo(
    solver: *mut Opaque,
    trait_object: *mut c_void,
    p: Lit,
) {
    let trait_object =
        unsafe { &mut *trait_object.cast::<Box<dyn CustomPropagator<GlucoseSolverManipulator>>>() };
    trait_object.undo(
        &mut GlucoseSolverManipulator {
            ptr: solver,
            wrapper_object: None,
        },
        p,
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reject_invalid_literals() {
        for lit in [Lit(-2), Lit(-1), Lit(2), Lit(i32::MAX)] {
            for operation in 0..6 {
                let mut solver = Solver::new();
                solver.new_var();
                let result =
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| match operation {
                        0 => solver.add_clause(&[lit]),
                        1 => solver.add_active_vertices_connected(&[lit], &[]),
                        2 => solver.add_order_encoding_linear(
                            &[vec![lit]],
                            &[vec![0, 1]],
                            &[1],
                            0,
                            OrderEncodingLinearMode::Cpp,
                        ),
                        3 => solver
                            .add_direct_encoding_extension_supports(&[vec![lit]], &[vec![Some(0)]]),
                        4 => solver.add_graph_division(
                            &[vec![1, 2]],
                            &[vec![lit]],
                            &[],
                            &[],
                            GraphDivisionMode::Cpp,
                            &GraphDivisionOptions::default(),
                        ),
                        _ => solver.add_graph_division(
                            &[vec![], vec![]],
                            &[vec![], vec![]],
                            &[(0, 1)],
                            &[lit],
                            GraphDivisionMode::Cpp,
                            &GraphDivisionOptions::default(),
                        ),
                    }));
                assert!(result.is_err(), "operation {operation} accepted {lit:?}");
                assert!(solver.solve().is_some());
            }
        }
    }

    #[test]
    fn test_reject_invalid_graph_structure() {
        for mode in [GraphDivisionMode::Cpp, GraphDivisionMode::Rust] {
            for edge in [(0, 1), (0, usize::MAX), (0, 0)] {
                let mut solver = Solver::new();
                let lit = solver.new_var().as_lit(false);
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    solver.add_graph_division(
                        &[vec![]],
                        &[vec![]],
                        &[edge],
                        &[lit],
                        mode,
                        &GraphDivisionOptions::default(),
                    );
                }));
                assert!(result.is_err());
            }
        }
    }

    #[test]
    #[should_panic(expected = "array exceeds native index range")]
    fn test_reject_flattened_length_overflow() {
        checked_total_len([i32::MAX as usize, 1]);
    }

    #[test]
    #[should_panic(expected = "zero coefficient")]
    fn test_reject_zero_coefficient() {
        Solver::new().add_order_encoding_linear(
            &[vec![]],
            &[vec![1]],
            &[0],
            0,
            OrderEncodingLinearMode::Cpp,
        );
    }

    #[test]
    fn test_solver() {
        let mut solver = Solver::new();
        let x = solver.new_var();
        let y = solver.new_var();

        assert!(solver.add_clause(&[Lit::new(x, false), Lit::new(y, false)]));
        assert!(solver.add_clause(&[Lit::new(x, false), Lit::new(y, true)]));
        assert!(solver.add_clause(&[Lit::new(x, true), Lit::new(y, false)]));
        assert!(solver.add_clause(&[Lit::new(x, true), Lit::new(y, true)]));
        assert!(solver.solve().is_none());
    }

    #[test]
    fn test_solver2() {
        let mut solver = Solver::new();
        let x = solver.new_var();
        let y = solver.new_var();

        assert!(solver.add_clause(&[Lit::new(x, false), Lit::new(y, false)]));
        assert!(solver.add_clause(&[Lit::new(x, false), Lit::new(y, true)]));
        assert!(solver.add_clause(&[Lit::new(x, true), Lit::new(y, true)]));
        {
            match solver.solve() {
                Some(model) => {
                    assert!(model.assignment(x));
                    assert!(!model.assignment(y));
                }
                None => panic!(),
            }
        }
    }

    struct Xor {
        vars: Vec<Var>,
        values: Vec<Option<bool>>,
        parity: bool,
        n_undecided: usize,
    }

    impl Xor {
        fn new(vars: Vec<Var>, parity: bool) -> Xor {
            // This implementation is just for testing.
            // For practical use, we need to add deduplication of literals.
            let size = vars.len();
            Xor {
                vars,
                values: vec![None; size],
                parity,
                n_undecided: size,
            }
        }

        fn var_index(&self, var: Var) -> Option<usize> {
            for i in 0..self.vars.len() {
                if self.vars[i] == var {
                    return Some(i);
                }
            }
            None
        }
    }

    unsafe impl<T: SolverManipulator> CustomPropagator<T> for Xor {
        fn initialize(&mut self, solver: &mut T) -> bool {
            for &var in &self.vars {
                unsafe {
                    solver.add_watch(var.as_lit(false));
                    solver.add_watch(var.as_lit(true));
                }
            }

            for var in self.vars.clone() {
                // TODO: this `clone` is just for silencing the borrow checker
                if let Some(v) = unsafe { solver.value(var.as_lit(false)) } {
                    let lit_sign = var.as_lit(!v);
                    if !self.propagate(solver, lit_sign, 0) {
                        return false;
                    }
                }
            }
            true
        }

        fn propagate(&mut self, solver: &mut T, p: Lit, _num_pending_propagations: i32) -> bool {
            let s = !p.is_negated();
            let v = p.var();

            let idx = self.var_index(v).unwrap();
            assert!(self.values[idx].is_none());
            self.values[idx] = Some(s);
            self.parity ^= s;
            assert_ne!(self.n_undecided, 0);
            self.n_undecided -= 1;

            if self.n_undecided == 0 {
                if self.parity {
                    return false;
                }
            } else if self.n_undecided == 1 {
                for i in 0..self.vars.len() {
                    if self.values[i].is_none() {
                        if !unsafe { solver.enqueue(self.vars[i].as_lit(!self.parity)) } {
                            return false;
                        }
                    }
                }
            }

            true
        }

        fn calc_reason(&mut self, _: &mut T, p: Option<Lit>, extra: Option<Lit>) -> Vec<Lit> {
            let mut ret = vec![];
            for i in 0..self.vars.len() {
                if let Some(v) = self.values[i] {
                    ret.push(self.vars[i].as_lit(!v));
                } else if p.is_none() && extra.is_some() {
                    ret.push(self.vars[i].as_lit(self.parity));
                }
            }
            assert_eq!(if p.is_some() { 1 } else { 0 } + ret.len(), self.vars.len());
            ret
        }

        fn undo(&mut self, _: &mut T, p: Lit) {
            let v = p.var();

            let idx = self.var_index(v).unwrap();
            assert!(self.values[idx] == Some(!p.is_negated()));
            self.parity ^= self.values[idx].unwrap();
            self.values[idx] = None;
            self.n_undecided += 1;
        }
    }

    #[test]
    fn test_custom_constraint_xor1() {
        let mut solver = Solver::new();
        let x = solver.new_var();
        let y = solver.new_var();

        assert!(solver.add_clause(&[Lit::new(x, false), Lit::new(y, true)]));
        assert!(solver.add_custom_constraint(Box::new(Xor::new(vec![x, y], true))));
        let model = solver.solve().unwrap();
        assert!(model.assignment(x));
        assert!(!model.assignment(y));
    }

    #[test]
    fn test_custom_constraint_xor2() {
        let mut solver = Solver::new();
        let mut vars = vec![];
        for _ in 0..10 {
            vars.push(solver.new_var());
        }

        assert!(solver.add_custom_constraint(Box::new(Xor::new(
            vec![vars[0], vars[1], vars[2], vars[3], vars[4]],
            false
        ))));
        assert!(solver.add_custom_constraint(Box::new(Xor::new(
            vec![vars[3], vars[4], vars[5], vars[6], vars[7]],
            true
        ))));
        assert!(solver.add_custom_constraint(Box::new(Xor::new(
            vec![vars[7], vars[8], vars[9], vars[0], vars[1]],
            true
        ))));

        let mut n_assignments = 0;
        loop {
            match solver.solve() {
                Some(model) => {
                    n_assignments += 1;
                    let mut new_clause = vec![];
                    for &v in &vars {
                        new_clause.push(v.as_lit(model.assignment(v)));
                    }
                    solver.add_clause(&new_clause);
                }
                None => break,
            }
        }

        assert_eq!(n_assignments, 128);
    }

    #[test]
    fn test_custom_constraint_xor3() {
        let mut solver = Solver::new();
        let mut vars = vec![];
        for _ in 0..10 {
            vars.push(solver.new_var());
        }

        assert!(solver.add_custom_constraint(Box::new(Xor::new(
            vec![vars[0], vars[1], vars[2], vars[3], vars[4]],
            false
        ))));
        assert!(solver.add_custom_constraint(Box::new(Xor::new(
            vec![vars[3], vars[4], vars[5], vars[6], vars[7]],
            true
        ))));
        assert!(solver.add_custom_constraint(Box::new(Xor::new(
            vec![vars[7], vars[8], vars[9], vars[0], vars[1]],
            true
        ))));
        assert!(solver.add_custom_constraint(Box::new(Xor::new(
            vec![vars[2], vars[5], vars[6], vars[8], vars[9]],
            true
        ))));
        assert!(solver.solve().is_none());
    }
}

#[cfg(test)]
mod incremental_tests {
    use super::*;
    #[test]
    fn root_custom_reasons_are_tagged_after_the_callback_returns() {
        struct Implication { input: Lit, output: Lit, in_callback: bool }
        unsafe impl<T: SolverManipulator> CustomPropagator<T> for Implication {
            fn initialize(&mut self, solver: &mut T) -> bool {
                unsafe { solver.add_watch(self.input); }
                true
            }
            fn propagate(&mut self, solver: &mut T, _: Lit, _: i32) -> bool {
                self.in_callback = true;
                let ok = unsafe { solver.enqueue(self.output) };
                self.in_callback = false;
                ok
            }
            fn calc_reason(&mut self, _: &mut T, _: Option<Lit>, extra: Option<Lit>) -> Vec<Lit> {
                assert!(!self.in_callback, "reentrant Rust callback");
                let mut reason = vec![self.input];
                reason.extend(extra);
                reason
            }
            fn undo(&mut self, _: &mut T, _: Lit) {}
        }
        for dependent in [false, true] {
            let mut solver = Solver::new();
            let c = solver.new_var().as_lit(false);
            let r = solver.new_var().as_lit(false);
            let x = solver.new_var().as_lit(false);
            let y = solver.new_var().as_lit(false);
            let cube = solver.new_var().as_lit(false);
            assert!(solver.add_custom_constraint(Box::new(Implication { input: c, output: r, in_callback: false })));
            assert!(solver.add_clause(&[!r, x, y]));
            assert!(solver.add_clause(&[!r, x, !y]));
            solver.track_dependencies();
            assert!(solver.add_cube_unit(cube));
            if dependent { assert!(solver.add_cube_unit(c)); }
            else { assert!(solver.add_clause(&[c])); }
            assert!(solver.solve_without_model());
            assert_eq!(solver.independent_learnts(30, 0).contains(&vec![x]), !dependent);
            assert!(solver.dependency_learnt_counts().0 > 0);
        }
    }

    #[test]
    fn independent_units_are_exported_and_cube_units_stay_local() {
        let mut solver = Solver::new();
        let x = solver.new_var().as_lit(false);
        let y = solver.new_var().as_lit(false);
        let c = solver.new_var().as_lit(false);
        let z = solver.new_var().as_lit(false);
        let w = solver.new_var().as_lit(false);
        for clause in [vec![x, y], vec![x, !y], vec![!c, z, w], vec![!c, z, !w]] {
            assert!(solver.add_clause(&clause));
        }
        solver.track_dependencies();
        assert!(solver.add_cube_unit(c));
        assert!(solver.solve_without_model());
        let clauses = solver.independent_learnts(30, 0);
        assert!(clauses.contains(&vec![x]), "independent learned unit missing: {clauses:?}");
        assert!(!clauses.contains(&vec![z]));
        let (all, independent) = solver.dependency_learnt_counts();
        assert!(all > independent && independent > 0);
    }

    #[test]
    fn dependency_tagged_exports_follow_the_base_formula() {
        let mut random = 0x8716_42d9u64;
        let mut next = || {
            random ^= random << 13;
            random ^= random >> 7;
            random ^= random << 17;
            random
        };
        let mut exported = 0;
        let mut dependent = 0;
        for _ in 0..100 {
            let mut solver = Solver::new();
            let vars: Vec<_> = (0..10).map(|_| solver.new_var().as_lit(false)).collect();
            let mut formula = vec![];
            for _ in 0..32 {
                let mut clause = vec![];
                while clause.len() < 3 {
                    let r = next();
                    let lit = vars[(r % 10) as usize];
                    if clause.iter().any(|p: &Lit| p.var() == lit.var()) { continue; }
                    clause.push(if r & 16 == 0 { lit } else { !lit });
                }
                solver.add_clause(&clause);
                formula.push(clause);
            }
            solver.track_dependencies();
            solver.add_cube_unit(vars[0]);
            solver.add_cube_unit(!vars[1]);
            solver.solve_without_model();
            let (all, independent) = solver.dependency_learnt_counts();
            dependent += all - independent;
            for clause in solver.independent_learnts(30, 0) {
                exported += 1;
                // Exhaust the original CNF, without the cube units.
                for assignment in 0..1024 {
                    let value = |lit: &Lit| ((assignment >> lit.var().index()) & 1 != 0) != (lit.0 & 1 != 0);
                    if formula.iter().all(|c| c.iter().any(value)) {
                        assert!(clause.iter().any(value), "invalid export {clause:?}");
                    }
                }
            }
        }
        assert!(exported > 0, "must exercise independent exports");
        assert!(dependent > 0, "must exercise cube-dependent learning");
    }

    #[test]
    fn assumptions_are_temporary_and_learnts_can_be_copied() {
        let mut a = Solver::new();
        let x = a.new_var().as_lit(false);
        let y = a.new_var().as_lit(false);
        let z = a.new_var().as_lit(false);
        let formula = vec![
            vec![!x, y, z],
            vec![!x, y, !z],
            vec![!x, !y, z],
            vec![!x, !y, !z],
        ];
        for c in &formula {
            assert!(a.add_clause(c));
        }
        assert!(a.solve_with_assumptions(&[x]).is_none());
        assert!(a.solve_with_assumptions(&[!x]).is_some());
        assert!(a.solve_with_assumptions(&[x, !x]).is_none());
        assert!(a.solve().is_some());
        let mut b = Solver::new();
        for _ in 0..3 {
            b.new_var();
        }
        for c in &formula {
            b.add_clause(c);
        }
        // Explicit non-unit implied clause verifies true learnt allocation and copying.
        assert!(a.add_learnt(&[!x, y]));
        // A root assignment can simplify the clause away. On the fresh solver it cannot.
        assert!(b.add_learnt(&[!x, y]));
        assert!(b.num_learnts() > 0);
        let mut copied = vec![];
        b.get_learnt(b.num_learnts() - 1, &mut copied);
        let mut expected = vec![!x, y];
        expected.sort();
        let mut sorted = copied.clone();
        sorted.sort();
        assert_eq!(sorted, expected);
        assert!(a.add_learnt(&copied));
        assert!(b.solve_with_assumptions(&[x]).is_none());
        assert!(b.solve_with_assumptions(&[!x]).is_some());
        assert!(b.add_learnt(&[!x]));
        assert!(b.solve().is_some());
        assert!(!b.add_learnt(&[]));
        assert!(b.solve().is_none());
    }
}
