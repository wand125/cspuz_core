# Numberlink fork

This fork of [semiexp/cspuz_core](https://github.com/semiexp/cspuz_core) adds
Numberlink SAT options and pruning rules, fixed-edge and assumption APIs,
Glucose interruption, conflict budgets and learned-clause sharing, three native
drivers, and a C ABI for browser workers.

## Build

Install Rust and a C++17 compiler, and initialize the repository's submodules.
Cube generation is supplied by the MIT-licensed
[rowscan_dfs](https://github.com/wand125/rowscan_dfs) crate, pinned to commit
`34d6d4f22022179586947be8d2b2a94101dc9a88`; Cargo fetches it automatically.

```sh
git submodule update --init --recursive
cargo build --release -p cspuz_solver_backend --bins
cargo test --release -p cspuz_rs_puzzles numlin
cargo test --release -p cspuz_solver_backend
```

The Glucose extensions are stored in `cspuz_core/lib/glucose_extensions/core`.
The build compiles these source/header replacements ahead of the pinned Glucose
submodule's include directory; no submodule edits are required.

## Native drivers

Each driver takes a Numberlink puzzle URL as its final argument. `--max 2`
checks uniqueness; `--max N` caps enumeration at N answers.

```sh
target/release/numlin_sat --max 2 URL
target/release/numlin_sat_par --threads 8 --transforms 0,1,2,3,4,5,6,7 --max 2 URL
target/release/numlin_sat_cube --threads 8 --cubes 64 --max 2 URL
```

`numlin_sat` builds and solves one SAT model. `numlin_sat_par` races models
under rotations, reflections and random seeds; the first finished result wins.
`--transforms K,K,...` restricts its transform portfolio.

`numlin_sat_cube` partitions the row-scan search into fixed-edge cubes, balances
them using Knuth estimates, then schedules SAT workers with idle-worker stealing.
Its defaults are SAT `--rules wedge`, `--cube-rules strong`, `--balance 4` and
100 probes per estimate. `--cubes M` sets a minimum initial frontier size;
balancing and stealing can create additional cubes. `--balance 0` disables
estimate balancing; `--no-steal` disables stealing. `--transform K` selects one
of eight board symmetries. See [the cube method](benchmarks/numlin/CUBES-ROWSCAN_DFS.md).

All drivers accept `--rules off` or a comma-separated subset of `diag,wedge,g2`,
`--full-cover`, `--short-only`, `--log-encoding` and `--edges-only`. Single and
portfolio drivers default to rules off. Full coverage requires every non-clue
cell to have degree two and disables the diagonal/wedge shortening rules.
Short-only asks whether any solution leaves a non-clue cell unused. Diagonal
and wedge rules select canonical paths and can change raw route counts; G2
adds a planarity check. Edges-only omits clue-ID integer variables and skips
the diagonal rule.

Cube enumeration counts the row-scan canonical partitions, including answers
completed while splitting. `--exact-count` also performs unrestricted SAT
enumeration when the cube count is below the answer cap, replacing that count.
Full-cover uses an unrestricted SAT root. Native short-only tests the
canonical partitions; use `--exact-count` to request unrestricted verification.

```sh
target/release/numlin_sat_cube --threads 8 --dump-cubes cubes.json URL
target/release/numlin_sat_cube --threads 8 --cubes-file cubes.json --cube-stats stats.jsonl URL
target/release/numlin_sat_cube --threads 8 --assumptions --budget 10000 --resplit 4 URL
target/release/numlin_sat_cube --threads 8 --share-pool --share-max-size 8 URL
```

External cubes include board dimensions, transform, fixed edges, scan position,
weights and completed-answer count. Assumption mode reuses each worker's model;
conflict budgets permit re-splitting. `--fixed-units` uses a common SAT encoding
with dependency-tagged cube units. `--share-pool` enables this mode and exchanges
only cube-independent learned clauses; it is opt-in. `--check-shared` verifies
exported clauses against a separate base model, and `--verify-cubes` compares
cube answers with fresh models.

### DFS prefilter and partition verification (2026-11-07)

```sh
target/release/numlin_sat_cube --threads 8 --dfs-ratio 300 URL
target/release/numlin_sat_cube --threads 8 --dfs-budget 1000000 --dfs-recurse 2 URL
target/release/numlin_sat_cube --threads 8 --balance-verify 10 --verify-floor 1e6 URL
```

`--dfs-budget STEPS` runs the row-scan DFS (`rowscan_dfs::solve_cube_budget`) on
each cube before its SAT solve; a cube the DFS exhausts with no solution is
closed without SAT, while a cube with solutions still goes to SAT so that the
canonical count comes from one engine. `--dfs-ratio R` sets the budget to
`R x estimate` (`--dfs-min` floors it, `--dfs-budget` caps it). `--dfs-recurse D`
splits a budget-exhausted cube and retries its children up to depth D
(`--dfs-grow F` scales the budget per depth). Measured on 20x20 boards, `--dfs-ratio 300`
cuts wall time by 54-76%; on 25x25 boards where SAT wins it is a loss (+17..+79%),
so the default is off and the choice belongs to the board, not the cube.

`--balance-verify F` now re-estimates a suspicious cube by splitting it into
`--verify-children N` (default 32) parts and summing their estimates, and by the
DFS progress estimate after `--verify-progress-steps B` (default 100000) steps;
either exceeding `F x` the parent replaces it by its children. A depth-0 victim
that has run longer than `--heavy-steal-secs S` (600) or whose children estimate
above it is stolen into `4 x threads` parts (`--heavy-steal-parts`). Stolen
parts queue behind earlier split groups, heaviest first within a group.

## Web backend

`numlin_web.rs` and `numlin_json.rs` expose `numlin_cubes`, `numlin_solve_cube`,
`numlin_split_cube` and `numlin_estimate_cube`, alongside `solve_problem` and
`enumerate_answers_problem`. Inputs use UTF-8 URLs and JSON; replies are JSON
prefixed by a four-byte little-endian byte length. Copy a reply before calling
again, because calls reuse the reply buffer. Browser workers provide concurrency;
cube estimation inside a wasm instance is sequential. Full-cover and short-only
web requests use an unrestricted SAT root.

With the Rust `wasm32-unknown-emscripten` target and Emscripten installed, build
the ES module and wasm bundle from this checkout:

```sh
export CARGO_TARGET_WASM32_UNKNOWN_EMSCRIPTEN_LINKER="$PWD/util/emcc_wrapper"
export CARGO_TARGET_WASM32_UNKNOWN_EMSCRIPTEN_RUSTFLAGS="-Cpanic=abort -Clink-arg=-sMODULARIZE=1 -Clink-arg=-sEXPORT_ES6=1 -Clink-arg=-sALLOW_MEMORY_GROWTH=1 -Clink-arg=-sINITIAL_MEMORY=268435456 -Clink-arg=-sSTACK_SIZE=16777216 -Clink-arg=-sFILESYSTEM=0 -Clink-arg=-sENVIRONMENT=web,worker,node -Clink-arg=-sEXPORTED_RUNTIME_METHODS=HEAPU8 -Clink-arg=-sDEFAULT_TO_CXX=1"
cargo build --release --lib -p cspuz_solver_backend --target wasm32-unknown-emscripten --no-default-features
```

The output is `target/wasm32-unknown-emscripten/release/deps/cspuz_solver_backend.js`
and the corresponding `.wasm`. The linker wrapper retains Rust callback exports
and adds the public C ABI exports.

## Benchmarks and license

See [the benchmark summary](benchmarks/numlin/README.md) for single-solve,
cube-and-conquer and cube-generator replacement measurements.

The upstream [MIT license](LICENSE) and semiexp copyright are retained, together
with the existing Glucose and MiniSat notices. Glucose replacement files retain
their original license headers. The rowscan_dfs dependency is MIT licensed.
