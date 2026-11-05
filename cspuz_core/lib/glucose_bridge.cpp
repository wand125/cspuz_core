#include "glucose_bridge.h"

#include "core/Solver.h"
#include "mtl/Sort.h"
#include "constraints/DirectEncodingExtension.h"
#include "constraints/Graph.h"
#include "constraints/GraphDivision.h"
#include "constraints/OrderEncodingLinear.h"

namespace Glucose {

// Access protected clause storage without exposing it in the upstream solver API.
class BridgeSolver : public Solver {
public:
    void setReduceDb(int first, int inc) {
        firstReduceDB = first;
        incReduceDB = inc;
        nbclausesbeforereduce = first;
    }
public:
    uint64_t encodingFingerprint() const {
        uint64_t hash = 14695981039346656037ull;
        auto mix = [&](uint64_t x) { hash ^= x; hash *= 1099511628211ull; };
        mix(nVars()); mix(clauses.size());
        for (int i = 0; i < clauses.size(); ++i) {
            const Clause& c = ca[clauses[i]];
            mix(c.size());
            for (int j = 0; j < c.size(); ++j) mix(toInt(c[j]));
        }
        mix(trail.size());
        for (int i = 0; i < trail.size(); ++i) mix(toInt(trail[i]));
        return hash;
    }
    int numLearnts() const { return learnts.size() + permanentLearnts.size() + independent_units.size(); }
    int copyLearnt(int i, int32_t* out) const {
        if (i < 0 || i >= numLearnts()) return -1;
        if (i >= learnts.size() + permanentLearnts.size()) {
            if (out) out[0] = toInt(independent_units[i - learnts.size() - permanentLearnts.size()]);
            return 1;
        }
        const Clause& c = ca[i < learnts.size() ? learnts[i] : permanentLearnts[i - learnts.size()]];
        if (out) for (int j = 0; j < c.size(); ++j) out[j] = toInt(c[j]);
        return c.size();
    }
    int copyIndependentLearnt(int i, int32_t* out, int maxSize, unsigned maxLbd) const {
        assert(track_dependencies);
        if (i < 0 || i >= numLearnts()) return -1;
        if (i < learnts.size() + permanentLearnts.size()) {
            const Clause& c = ca[i < learnts.size() ? learnts[i] : permanentLearnts[i - learnts.size()]];
            if (c.dependent() || c.getExported() || c.size() > maxSize || (maxLbd && c.lbd() > maxLbd)) return -2;
        } else if (maxSize < 1) return -2;
        return copyLearnt(i, out);
    }
    bool addCubeUnit(Lit p) {
        assert(track_dependencies);
        cancelUntil(0);
        has_cube_units = true;
        if (value(p) == l_Undef) dep[var(p)] = 1;
        return addClause(p);
    }
    bool addLearnt(vec<Lit>& ps) {
        cancelUntil(0);
        if (!ok) return false;
        sort(ps);
        bool dependent = false;
        int j = 0;
        Lit previous = lit_Undef;
        for (int i = 0; i < ps.size(); ++i) {
            if (value(ps[i]) == l_True || ps[i] == ~previous) return true;
            if (track_dependencies && value(ps[i]) == l_False && dep[var(ps[i])]) dependent = true;
            if (value(ps[i]) != l_False && ps[i] != previous) ps[j++] = previous = ps[i];
        }
        ps.shrink(ps.size() - j);
        if (ps.size() < 2) {
            if (track_dependencies && dependent && ps.size() == 1) dep[var(ps[0])] = 1;
            return addClause(ps);
        }
        CRef cr = ca.alloc(ps, true);
        ca[cr].setDependent(dependent);
        ca[cr].setExported(1); // Imported clauses are already present in the shared pool.
        ca[cr].setLBD(ps.size());
        ca[cr].setOneWatched(false);
        learnts.push(cr);
        claBumpActivity(ca[cr]);
        attachClause(cr);
        return true;
    }
};

bool RustExtraConstraint::initialize(Solver& solver) {
    return Glucose_CallCustomPropagatorInitialize(&solver, this, trait_object_) != 0;
}

bool RustExtraConstraint::propagate(Solver& solver, Lit p) {
    solver.registerUndo(var(p), this);
    return Glucose_CallCustomPropagatorPropagate(&solver, this, trait_object_, p.x, num_pending_propagation()) != 0;
}

void RustExtraConstraint::calcReason(Solver& solver, Lit p, Lit extra, vec<Lit>& out_reason) {
    Glucose_CallCustomPropagatorCalcReason(&solver, trait_object_, p.x, extra.x, &out_reason);
}

void RustExtraConstraint::undo(Solver& solver, Lit p) {
    Glucose_CallCustomPropagatorUndo(&solver, trait_object_, p.x);
}

}

extern "C" {

Glucose::Solver* Glucose_CreateSolver() {
    Glucose::Solver* solver = new Glucose::BridgeSolver();
    return solver;
}

void Glucose_DestroySolver(Glucose::Solver* solver) {
    delete solver;
}

int Glucose_NewVar(Glucose::Solver* solver) {
    return solver->newVar();
}

int32_t Glucose_NewNamedVar(Glucose::Solver* solver, const char* name) {
    std::string name_str(name);
    return solver->newNamedVar(name_str);
}

int32_t Glucose_AddClause(Glucose::Solver* solver, int32_t* lits, int32_t n_lits) {
    Glucose::vec<Glucose::Lit> lits_vec;
    for (int i = 0; i < n_lits; ++i) {
        lits_vec.push(Glucose::Lit{lits[i]});
    }
    return solver->addClause(lits_vec);
}

void Glucose_TrackDependencies(Glucose::Solver* solver) { solver->track_dependencies = true; }
int32_t Glucose_AddCubeUnit(Glucose::Solver* solver, int32_t lit) {
    return static_cast<Glucose::BridgeSolver*>(solver)->addCubeUnit(Glucose::Lit{lit});
}
int32_t Glucose_GetIndependentLearnt(Glucose::Solver* solver, int32_t i, int32_t* out, int32_t maxSize, uint32_t maxLbd) {
    return static_cast<Glucose::BridgeSolver*>(solver)->copyIndependentLearnt(i, out, maxSize, maxLbd);
}
uint64_t Glucose_DependencyLearntCount(Glucose::Solver* solver, int32_t independent) {
    return independent ? solver->independent_learnts : solver->dependency_learnts;
}

int32_t Glucose_Solve(Glucose::Solver* solver) {
    return solver->solve();
}

int32_t Glucose_SolveWithAssumptions(Glucose::Solver* solver, const int32_t* lits, int32_t n) {
    Glucose::vec<Glucose::Lit> assumps;
    for (int i = 0; i < n; ++i) assumps.push(Glucose::Lit{lits[i]});
    auto result = solver->solveLimited(assumps);
    return result == l_True ? 1 : result == l_False ? 0 : -1;
}

void Glucose_SetConfBudget(Glucose::Solver* solver, int64_t budget) {
    solver->setConfBudget(budget);
}
void Glucose_BudgetOff(Glucose::Solver* solver) {
    solver->budgetOff();
}
void Glucose_Interrupt(Glucose::Solver* solver) {
    solver->interrupt();
}
void Glucose_ClearInterrupt(Glucose::Solver* solver) {
    solver->clearInterrupt();
}

uint64_t Glucose_EncodingFingerprint(Glucose::Solver* solver) {
    return static_cast<Glucose::BridgeSolver*>(solver)->encodingFingerprint();
}
int32_t Glucose_NumLearnts(Glucose::Solver* solver) {
    return static_cast<Glucose::BridgeSolver*>(solver)->numLearnts();
}
int32_t Glucose_GetLearnt(Glucose::Solver* solver, int32_t i, int32_t* out) {
    return static_cast<Glucose::BridgeSolver*>(solver)->copyLearnt(i, out);
}
int32_t Glucose_AddLearnt(Glucose::Solver* solver, const int32_t* lits, int32_t n) {
    Glucose::vec<Glucose::Lit> clause;
    for (int i = 0; i < n; ++i) clause.push(Glucose::Lit{lits[i]});
    return static_cast<Glucose::BridgeSolver*>(solver)->addLearnt(clause);
}

int32_t Glucose_NumVar(const Glucose::Solver* solver) {
    return solver->nVars();
}

int32_t Glucose_GetModelValueVar(const Glucose::Solver* solver, int32_t var) {
    return solver->modelValue(Glucose::Var(var)) == l_True ? 1 : 0;
}

void Glucose_SetPolarity(Glucose::Solver* solver, int32_t var, int32_t polarity) {
    solver->setPolarity(Glucose::Var(var), polarity != 0);
}

int32_t Glucose_AddOrderEncodingLinear(Glucose::Solver* solver, int32_t n_terms, const int32_t* domain_size, const int32_t* lits, const int32_t* domain, const int32_t* coefs, int32_t constant) {
    std::vector<Glucose::LinearTerm> terms;
    int lits_offset = 0, domain_offset = 0;
    for (int i = 0; i < n_terms; ++i) {
        std::vector<Glucose::Lit> term_lits;
        for (int j = 0; j < domain_size[i] - 1; ++j) {
            term_lits.push_back(Glucose::Lit{lits[lits_offset++]});
        }
        std::vector<int> term_domain;
        for (int j = 0; j < domain_size[i]; ++j) {
            term_domain.push_back(domain[domain_offset++]);
        }
        terms.push_back(Glucose::LinearTerm{ term_lits, term_domain, coefs[i] });
    }
    return solver->addConstraint(std::make_unique<Glucose::OrderEncodingLinear>(std::move(terms), constant)) ? 1 : 0;
}

int32_t Glucose_AddActiveVerticesConnected(Glucose::Solver* solver, int32_t n_vertices, const int32_t* lits, int32_t n_edges, const int32_t* edges) {
    std::vector<Glucose::Lit> g_lits;
    for (int i = 0; i < n_vertices; ++i) {
        g_lits.push_back(Glucose::Lit{lits[i]});
    }
    std::vector<std::pair<int, int>> g_edges;
    for (int i = 0; i < n_edges; ++i) {
        g_edges.push_back({edges[i * 2], edges[i * 2 + 1]});
    }
    return solver->addConstraint(std::make_unique<Glucose::ActiveVerticesConnected>(std::move(g_lits), std::move(g_edges))) ? 1 : 0;
}

#if PUZZLE_SOLVER_MINIMAL
int32_t Glucose_AddDirectEncodingExtensionSupports(Glucose::Solver* solver, int32_t n_vars, const int32_t* domain_size, const int32_t* lits, int32_t n_supports, const int32_t* supports) {
    abort();
}
#else
int32_t Glucose_AddDirectEncodingExtensionSupports(Glucose::Solver* solver, int32_t n_vars, const int32_t* domain_size, const int32_t* lits, int32_t n_supports, const int32_t* supports) {
    std::vector<std::vector<Glucose::Lit>> g_lits;
    int lits_offset = 0;
    for (int i = 0; i < n_vars; ++i) {
        std::vector<Glucose::Lit> var_lits;
        for (int j = 0; j < domain_size[i]; ++j) {
            var_lits.push_back(Glucose::Lit{lits[lits_offset++]});
        }
        g_lits.push_back(var_lits);
    }
    std::vector<std::vector<int>> g_supports;
    for (int i = 0; i < n_supports; ++i) {
        std::vector<int> s;
        for (int j = 0; j < n_vars; ++j) {
            s.push_back(supports[i * n_vars + j]);
        }
        g_supports.push_back(s);
    }
    return solver->addConstraint(std::make_unique<Glucose::DirectEncodingExtensionSupports>(std::move(g_lits), std::move(g_supports)));
}
#endif

int32_t Glucose_AddGraphDivision(Glucose::Solver* solver, int32_t n_vertices, const int32_t* dom_sizes, const int32_t* domains, const int32_t* dom_lits, int32_t n_edges, const int32_t* edges, const int32_t* edge_lits) {
    std::vector<Glucose::OptionalOrderEncoding> vertices;
    int domains_offset = 0;
    int dom_lits_offset = 0;
    for (int i = 0; i < n_vertices; ++i) {
        Glucose::OptionalOrderEncoding ooe;
        if (dom_sizes[i] > 0) {
            for (int j = 0; j < dom_sizes[i]; ++j) {
                ooe.values.push_back(domains[domains_offset++]);
            }
            for (int j = 1; j < dom_sizes[i]; ++j) {
                ooe.lits.push_back(Glucose::Lit{ dom_lits[dom_lits_offset++] });
            }
        }
        vertices.push_back(ooe);
    }

    std::vector<std::pair<int, int>> graph;
    for (int i = 0; i < n_edges; ++i) {
        graph.push_back({edges[i * 2], edges[i * 2 + 1]});
    }

    std::vector<Glucose::Lit> edge_lits_l;
    for (int i = 0; i < n_edges; ++i) {
        edge_lits_l.push_back(Glucose::Lit{ edge_lits[i] });
    }

    return solver->addConstraint(std::make_unique<Glucose::GraphDivision>(vertices, graph, edge_lits_l));
}

uint64_t Glucose_SolverStats_decisions(Glucose::Solver* solver) {
    return solver->decisions;
}

uint64_t Glucose_SolverStats_propagations(Glucose::Solver* solver) {
    return solver->propagations;
}

uint64_t Glucose_SolverStats_conflicts(Glucose::Solver* solver) {
    return solver->conflicts;
}

void Glucose_Set_random_seed(Glucose::Solver* solver, double random_seed) {
    solver->random_seed = random_seed;
}

void Glucose_Set_rnd_init_act(Glucose::Solver* solver, int32_t rnd_init_act) {
    solver->rnd_init_act = rnd_init_act != 0;
}
void Glucose_Set_random_var_freq(Glucose::Solver* solver, double freq) {
    solver->random_var_freq = freq;
}
void Glucose_Set_no_learn(Glucose::Solver* solver, int32_t value) {
    solver->no_learn = value != 0;
}
// Learnt clause database reduction schedule: first reduction after `first` conflicts,
// then every `first + k * inc` conflicts. Small values approximate a DPLL-like solver
// that keeps few learnt clauses.
void Glucose_Set_reduce_db(Glucose::Solver* solver, int32_t first, int32_t inc) {
    static_cast<Glucose::BridgeSolver*>(solver)->setReduceDb(first, inc);
}

void Glucose_Set_dump_analysis_info(Glucose::Solver* solver, int32_t value) {
    solver->dump_analysis_info = value != 0;
}

int32_t Glucose_AddRustExtraConstraint(Glucose::Solver* solver, void* trait_object) {
    return solver->addConstraint(std::make_unique<Glucose::RustExtraConstraint>(trait_object)) ? 1 : 0;
}

void Glucose_CustomPropagatorCopyReason(void* reason_vec, int32_t n_lits, int32_t* lits) {
    Glucose::vec<Glucose::Lit>* v = static_cast<Glucose::vec<Glucose::Lit>*>(reason_vec);
    for (int i = 0; i < n_lits; ++i) {
        v->push(Glucose::Lit{lits[i]});
    }
}

int32_t Glucose_SolverValue(Glucose::Solver* solver, int32_t lit) {
    return Glucose::toInt(solver->value(Glucose::Lit{lit}));
}

void Glucose_SolverAddWatch(Glucose::Solver* solver, int32_t lit, void* wrapper_object) {
    solver->addWatch(Glucose::Lit{lit}, static_cast<Glucose::Constraint*>(wrapper_object));
}

int32_t Glucose_SolverEnqueue(Glucose::Solver* solver, int32_t lit, void* wrapper_object) {
    return solver->enqueue(Glucose::Lit{lit}, static_cast<Glucose::Constraint*>(wrapper_object)) ? 1 : 0;
}

int32_t Glucose_IsCurrentLevel(Glucose::Solver* solver, int32_t lit) {
    return solver->decisionLevel() == solver->level(Glucose::var(Glucose::Lit{lit})) ? 1 : 0;
}

}
