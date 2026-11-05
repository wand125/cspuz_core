use cspuz_rs::graph::BoolGridEdges;
use cspuz_rs::solver::{all, BoolExpr, IntVarArray2D, Solver};
use std::str::FromStr;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct NumlinRules {
    pub diag: bool,
    pub wedge: bool,
    pub g2: bool,
}

impl FromStr for NumlinRules {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let mut rules = Self::default();
        if value == "off" || value == "none" || value.is_empty() {
            return Ok(rules);
        }
        for name in value.split(',') {
            match name {
                "diag" => rules.diag = true,
                "wedge" => rules.wedge = true,
                "g2" => rules.g2 = true,
                _ => return Err(format!("unknown Numberlink rule: {name}")),
            }
        }
        Ok(rules)
    }
}

type Vertex = (usize, usize);

fn edge(lines: &BoolGridEdges, a: Vertex, b: Vertex) -> BoolExpr {
    if a.0 == b.0 {
        lines.horizontal.at((a.0, a.1.min(b.1))).expr()
    } else {
        lines.vertical.at((a.0.min(b.0), a.1)).expr()
    }
}

pub(super) fn add_diag(
    solver: &mut Solver,
    lines: &BoolGridEdges,
    ids: &IntVarArray2D,
    h: usize,
    w: usize,
) {
    for y in 0..h - 1 {
        for x in 0..w - 1 {
            // Choose each corner as the unused vertex; c is the opposite corner.
            for dy in 0..2 {
                for dx in 0..2 {
                    let u = (y + dy, x + dx);
                    let a = (y + 1 - dy, x + dx);
                    let b = (y + dy, x + 1 - dx);
                    let c = (y + 1 - dy, x + 1 - dx);
                    solver.add_expr(
                        (!lines.vertex_neighbors(u).any()
                            & lines.vertex_neighbors(a).any()
                            & lines.vertex_neighbors(b).any()
                            & ids.at(a).eq(ids.at(b)))
                        .imp(edge(lines, a, c) & edge(lines, c, b)),
                    );
                }
            }
        }
    }
}

// P1 slots [1, 4, 2, 8]: right/below, right/above, down/left, down/right.
// Store distances, rather than the port's stride-128 blocking coordinates.
pub(super) fn wedge_limits(clues: &[Vec<Option<i32>>]) -> Vec<Vec<[usize; 4]>> {
    let h = clues.len();
    let w = clues[0].len();
    let mut limits = vec![vec![[0; 4]; w]; h];
    for y in 0..h {
        for x in 0..w {
            limits[y][x] = [w - x, w - x, h - y, h - y];
            // P1 gives starting clues exterior defaults, without sampling.
            if clues[y][x].is_some() {
                continue;
            }
            for slot in 0..4 {
                'candidate: for k in 2..limits[y][x][slot] {
                    for j in 1..=k / 2 {
                        let (sy, sx) = match slot {
                            0 => (y as isize + j as isize, x + k - j),
                            1 => (y as isize - j as isize, x + k - j),
                            2 => (y as isize + (k - j) as isize, x.wrapping_sub(j)),
                            3 => (y as isize + (k - j) as isize, x + j),
                            _ => unreachable!(),
                        };
                        // Symmetric geometric boundaries: stop sampling at any exterior.
                        // In particular, do NOT reproduce slot 8's x+j <= 128*height bug.
                        if sy < 0 || sy >= h as isize || sx >= w {
                            break;
                        }
                        // Option presence matters: generated instances use clue value zero.
                        if clues[sy as usize][sx].is_some() {
                            limits[y][x][slot] = k;
                            break 'candidate;
                        }
                    }
                }
            }
        }
    }
    limits
}

// On 25x25 even a completely clue-free board has only 26,496 candidate clauses.
// Larger boards get a bounded subset of this optional canonicalization.
pub(super) const MAX_WEDGE_CLAUSES: usize = 50_000;

pub(super) fn wedge_runs(clues: &[Vec<Option<i32>>]) -> Vec<(Vertex, usize, usize)> {
    let h = clues.len();
    let w = clues[0].len();
    let limits = wedge_limits(clues);
    let mut runs = vec![];
    for y in 0..h {
        for x in 0..w {
            for slot in 0..4 {
                if (slot == 0 && y + 1 == h)
                    || (slot == 1 && y == 0)
                    || (slot == 2 && x == 0)
                    || (slot == 3 && x + 1 == w)
                {
                    continue;
                }
                for k in 2..limits[y][x][slot] {
                    runs.push(((y, x), slot, k));
                    if runs.len() == MAX_WEDGE_CLAUSES {
                        return runs;
                    }
                }
            }
        }
    }
    runs
}

pub(super) fn add_wedge(solver: &mut Solver, lines: &BoolGridEdges, clues: &[Vec<Option<i32>>]) {
    for ((y, x), slot, k) in wedge_runs(clues) {
        let c = (y, x);
        let q = if slot < 2 { (y, x + k) } else { (y + k, x) };
        // The port uses opposite(t) for arms in direction t: U->4, D->1,
        // L->2, R->8. Thus the sampled wedge is on the SAME side as both arms.
        let bend = |(y, x): Vertex| match slot {
            0 => (y + 1, x),
            1 => (y - 1, x),
            2 => (y, x - 1),
            3 => (y, x + 1),
            _ => unreachable!(),
        };
        let mut edges = vec![edge(lines, c, bend(c)), edge(lines, q, bend(q))];
        for i in 0..k {
            edges.push(if slot < 2 {
                lines.horizontal.at((y, x + i)).expr()
            } else {
                lines.vertical.at((y + i, x)).expr()
            });
        }
        solver.add_expr(!all(&edges));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fix_path(solver: &mut Solver, lines: &BoolGridEdges, n: usize, path: &[Vertex]) {
        let used = |a, b| path.windows(2).any(|p| p == [a, b] || p == [b, a]);
        for y in 0..n {
            for x in 0..n - 1 {
                solver.add_expr(lines.horizontal.at((y, x)).iff(used((y, x), (y, x + 1))));
                solver.add_expr(lines.vertical.at((x, y)).iff(used((x, y), (x + 1, y))));
            }
        }
    }

    #[test]
    fn test_numlin_diag_orientations_and_ties() {
        for rotation in 0..4 {
            for (path, accepted) in [
                (
                    vec![(1, 2), (0, 2), (0, 1), (0, 0), (1, 0), (2, 0), (2, 1)],
                    false,
                ),
                (vec![(1, 2), (1, 1), (2, 1)], true),
            ] {
                let path: Vec<_> = path
                    .into_iter()
                    .map(|mut p| {
                        for _ in 0..rotation {
                            p = (p.1, 3 - p.0);
                        }
                        p
                    })
                    .collect();
                for same_id in [false, true] {
                    let mut solver = Solver::new();
                    let lines = BoolGridEdges::new(&mut solver, (3, 3));
                    let ids = solver.int_var_2d((4, 4), 0, 15);
                    for y in 0..4 {
                        for x in 0..4 {
                            solver.add_expr(ids.at((y, x)).eq(if same_id {
                                0
                            } else {
                                (y * 4 + x) as i32
                            }));
                        }
                    }
                    add_diag(&mut solver, &lines, &ids, 4, 4);
                    fix_path(&mut solver, &lines, 4, &path);
                    assert_eq!(solver.solve().is_some(), accepted || !same_id);
                }
            }
        }
    }

    #[test]
    fn test_numlin_wedge_bend_sides() {
        for slot in 0..4 {
            let (path, blocker) = match slot {
                0 => (vec![(3, 1), (2, 1), (2, 2), (2, 3), (3, 3)], (3, 2)),
                1 => (vec![(1, 1), (2, 1), (2, 2), (2, 3), (1, 3)], (1, 2)),
                2 => (vec![(1, 1), (1, 2), (2, 2), (3, 2), (3, 1)], (2, 1)),
                3 => (vec![(1, 3), (1, 2), (2, 2), (3, 2), (3, 3)], (2, 3)),
                _ => unreachable!(),
            };
            for blocked in [false, true] {
                let mut clues = vec![vec![None; 5]; 5];
                if blocked {
                    clues[blocker.0][blocker.1] = Some(0);
                }
                let mut solver = Solver::new();
                let lines = BoolGridEdges::new(&mut solver, (4, 4));
                add_wedge(&mut solver, &lines, &clues);
                fix_path(&mut solver, &lines, 5, &path);
                assert_eq!(solver.solve().is_some(), blocked, "slot {slot}");
            }
        }
    }
}
