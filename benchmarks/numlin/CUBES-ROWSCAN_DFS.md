# Row-scan cubes

The backend uses the MIT-licensed [rowscan_dfs](https://github.com/wand125/rowscan_dfs)
library for URL decoding, cube generation, re-splitting and Knuth estimates.
`cspuz_solver_backend/src/cubes.rs` implements estimate balancing and verification;
the SAT scheduler, external cube JSON and web worker protocol use this adapter.

A cube records fixed edges, the next row-scan cell and an estimated weight.
Re-splitting resumes from that cell. Answers completed during a split are counted
when their parent is replaced, including when the subtree is exhausted. Accepted
cubes are rechecked as the estimated total shrinks; `--balance-mean` instead
limits against the initial mean. Verification uses deterministic probe seeds.
Native parallel estimates and sequential wasm estimates use the same seed sets.

CLI and web transforms 0 through 7 map to rowscan_dfs directions
**0, 5, 6, 3, 2, 7, 4, 1**. Original numeric clue values are retained separately
from dense row-scan pair IDs. Strong cube rules enable the optional diagonal
shortcut and cut interval 5; off uses the library's base canonical form and cut
interval 25. Its base structural propagation is intrinsic to the search.
Full-cover and short-only web calls use an unrestricted SAT root.

## Replacement measurements

CPU: **AMD Ryzen 9 9950X**, x86_64 Linux, Rust 1.98.0.
Two interleaved repetitions per board: previous generator, rowscan_dfs, previous,
rowscan_dfs. Both drivers use `--threads 8` and unchanged defaults: minimum
64 cubes, balance 4, 100 probes, strong cube rules, wedge SAT rules and stealing.
Wall time includes generation and scheduler shutdown. OS CPU is process user +
system time; runtime cubes include stolen descendants. All 16 runs exited
successfully.

| Board | Driver | Wall r1 / r2 (s) | Mean wall (s) | OS CPU r1 / r2 (s) | Initial cubes | Runtime cubes r1 / r2 |
|---|---|---:|---:|---:|---:|---:|
| g34_nl5 | previous | 408.959 / 402.962 | 405.961 | 3225.706 / 3193.945 | 476 / 476 | 592 / 484 |
| g34_nl5 | rowscan_dfs | 350.234 / 346.239 | 348.236 | 2682.806 / 2643.038 | 126 / 126 | 142 / 142 |
| p2592 | previous | 30.731 / 28.723 | 29.727 | 220.056 / 218.696 | 595 / 595 | 595 / 595 |
| p2592 | rowscan_dfs | 22.201 / 22.215 | 22.208 | 155.403 / 155.388 | 146 / 146 | 146 / 146 |
| p7933 | previous | 28.756 / 28.756 | 28.756 | 204.000 / 205.856 | 556 / 556 | 589 / 589 |
| p7933 | rowscan_dfs | 28.235 / 28.253 | 28.244 | 143.049 / 140.588 | 147 / 147 | 151 / 151 |
| p10157 | previous | 23.051 / 22.976 | 23.014 | 172.131 / 172.854 | 749 / 749 | 749 / 749 |
| p10157 | rowscan_dfs | 14.167 / 14.167 | 14.167 | 104.632 / 104.714 | 126 / 126 | 126 / 126 |

Raw observations are in [results.json](replacement/results.json). The default
frontiers (fixed edges, scan positions, weights and completed-answer counts)
were identical between measured and final builds on all four boards; binary
hashes and those checks are in [build-equivalence.json](replacement/build-equivalence.json).
The final build was used for the p10157 rowscan_dfs samples.

The [benchmark summary](README.md) compares mean wall and OS CPU times and
includes single-solve measurements.
