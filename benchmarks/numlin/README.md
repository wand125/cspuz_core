# Numberlink benchmarks

The solver partitions a row-scan canonical search into fixed-edge cubes, estimates
and balances their sizes, then solves the cubes with parallel SAT workers.
Idle workers can split a running cube. SAT rules, encoding, balancing and clause
sharing can be selected independently; see [the fork guide](../../NUMLIN-FORK.md)
for build commands and driver options.

## Three 25×25 magazine puzzles

Historical measurements use eight SAT workers, wedge SAT rules, strong cube
pruning, balance 4 and stealing. Verification uses `--balance-verify 10
--verify-floor 1e6`: large cubes are probed again and replaced if their children's
combined estimate exceeds ten times the parent estimate. The browser reference
is a single-solve measurement, while cube-and-conquer uses native workers.
The table predates the rowscan_dfs replacement below.

| Puzzle | Single solve, browser | Cube-and-conquer wall | Sum of cube times | Generated cubes |
|---|---:|---:|---:|---:|
| g34_nl5 | 1:09:37 | 394.4 s | 3,145 s | 476 |
| pp26_nl27 | 0:48:18 | 1,031.6 s | 8,235 s | 659 |
| g36nl05 | 36:26:57 | 20,798.6 s | 166,262 s | 2,107 |

The sum of cube times measures worker elapsed time, including interrupted work;
it is distinct from operating-system CPU time. Wall time includes generation
and scheduling. The magazine puzzle names and timings identify the measurements.

## Cube-generator replacement

CPU: AMD Ryzen 9 9950X, x86_64 Linux, Rust 1.98.0. Two interleaved repetitions
per board compare the preceding cube generator with rowscan_dfs, using eight
workers and unchanged defaults: minimum 64 cubes, balance 4, 100 estimate probes,
strong cube rules, wedge SAT rules and stealing. Values are means in seconds.
OS CPU is process user + system time, including generation.

| Board | Size | Previous wall | rowscan_dfs wall | Change | Previous OS CPU | rowscan_dfs OS CPU |
|---|---|---:|---:|---:|---:|---:|
| g34_nl5 | 25×25 | 405.961 | 348.236 | -14.22% | 3,209.825 | 2,662.922 |
| p2592 | 20×20 | 29.727 | 22.208 | -25.29% | 219.376 | 155.395 |
| p7933 | 20×20 | 28.756 | 28.244 | -1.78% | 204.928 | 141.818 |
| p10157 | 20×20 | 23.014 | 14.167 | -38.44% | 172.492 | 104.673 |

All 16 runs exited successfully. [results.json](replacement/results.json)
contains each run's wall, user and system time and cube counts;
[build-equivalence.json](replacement/build-equivalence.json) records binary hashes
and identical frontiers across the measured and final builds. The
[method and replacement tables](CUBES-ROWSCAN_DFS.md) include both repetitions.

## Small public boards

The three URLs in [tasks.json](tasks.json) describe 15×15, 14×14 and 15×15
boards. The single-SAT series uses macOS 26.2 arm64 and Rust 1.99.0, one serial
run per configuration, an answer cap of two and a 600-second timeout. All 81
single/transform runs completed with one answer. Driver elapsed time includes
model construction and enumeration; the CSV also records process wall time.

| Task | Size | Single SAT, rules off | Single SAT, diag | Single SAT, diag+wedge |
|---|---|---:|---:|---:|
| 1 | 15×15 | 26.570 ms | 48.104 ms | 65.637 ms |
| 2 | 14×14 | 218.861 ms | 226.542 ms | 217.022 ms |
| 3 | 15×15 | 367.815 ms | 502.857 ms | 377.215 ms |

[Raw timings](timings.csv) include `numlin_sat_par -j 1 --transforms K` for
K = 0 through 7; [metadata](timings.meta.json) records the timestamp, compiler
and binary hashes. The added rules have different costs by board, so they
remain optional for the single and portfolio drivers.

To repeat a selected configuration after building release binaries, set `URL`
to an entry in tasks.json and run:

```sh
target/release/numlin_sat --max 2 --rules off "$URL"
target/release/numlin_sat_par -j 1 --max 2 --transforms 3 --rules diag,wedge "$URL"
target/release/numlin_sat_cube --threads 8 --cubes 64 --max 2 "$URL"
```
