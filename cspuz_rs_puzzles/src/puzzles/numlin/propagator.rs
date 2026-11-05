use cspuz_core::custom_constraints::SimpleCustomConstraint;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum EdgeState {
    Unknown,
    Line,
    NoLine,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum VertexState {
    Unknown,
    Traversed,
    NotTraversed,
}

pub(super) struct PathPropagator {
    height: usize,
    width: usize,
    clue: Vec<Option<i32>>,

    edges: Vec<(usize, usize)>,
    adjacent: Vec<Vec<(usize, usize)>>,
    edge_state: Vec<EdgeState>,
    vertex_state: Vec<VertexState>,

    // Union-Find structure
    parent: Vec<usize>,
    size: Vec<usize>,
    terminal: Vec<Option<usize>>,

    updates: Vec<Update>,
    conflicts: Vec<Conflict>,

    workspace: std::cell::RefCell<PathWorkspace>,
}

struct Merge {
    child: usize,
    parent: usize,
    old_size: usize,
    old_terminal: Option<usize>,
}

enum Update {
    Edge {
        index: usize,
        merge: Option<Merge>,
        conflict: bool,
    },
    Vertex {
        index: usize,
    },
}

/// The path connecting two vertices `a` and `b`, excluding the edge `cycle_edge` is the reason for the conflict.
struct Conflict {
    a: usize,
    b: usize,
    cycle_edge: Option<usize>,
}

struct PathWorkspace {
    previous: Vec<(usize, usize)>,
    visited: Vec<bool>,
    queue: Vec<usize>,
}

impl PathPropagator {
    pub(super) fn new(height: usize, width: usize, clues: &[Vec<Option<i32>>]) -> PathPropagator {
        let mut edges = vec![];
        let mut adjacent = vec![vec![]; height * width];
        for y in 0..height {
            for x in 0..(width - 1) {
                edges.push((y * width + x, y * width + (x + 1)));
            }
        }
        for y in 0..(height - 1) {
            for x in 0..width {
                edges.push((y * width + x, (y + 1) * width + x));
            }
        }
        for (e, &(a, b)) in edges.iter().enumerate() {
            adjacent[a].push((b, e));
            adjacent[b].push((a, e));
        }
        let edge_state = vec![EdgeState::Unknown; edges.len()];
        let vertex_state = vec![VertexState::Unknown; height * width];
        let mut terminal = vec![None; height * width];
        for y in 0..height {
            for x in 0..width {
                if clues[y][x].is_some() {
                    terminal[y * width + x] = Some(y * width + x);
                }
            }
        }

        let parent = (0..(height * width)).collect();
        let size = vec![1; height * width];

        let workspace = PathWorkspace {
            previous: vec![(0, 0); height * width],
            visited: vec![false; height * width],
            queue: vec![],
        };

        let mut clue = vec![];
        for y in 0..height {
            for x in 0..width {
                clue.push(clues[y][x]);
            }
        }

        PathPropagator {
            height,
            width,
            clue,
            edges,
            adjacent,
            edge_state,
            vertex_state,
            parent,
            size,
            terminal,
            updates: vec![],
            conflicts: vec![],
            workspace: std::cell::RefCell::new(workspace),
        }
    }

    fn root(&self, mut v: usize) -> usize {
        // We don't do path compression here because we want to keep the parent structure intact for backtracking.
        while self.parent[v] != v {
            let p = self.parent[v];
            v = p;
        }
        v
    }
}

impl PathPropagator {
    fn find_path(&self, a: usize, b: usize, exclude: Option<usize>) -> Vec<usize> {
        if a == b {
            return vec![];
        }

        let workspace = &mut self.workspace.borrow_mut();
        for i in 0..workspace.queue.len() {
            let p = workspace.queue[i];
            workspace.visited[p] = false;
        }
        workspace.queue.clear();
        workspace.queue.push(a);
        workspace.visited[a] = true;

        let mut top = 0;
        while top < workspace.queue.len() && !workspace.visited[b] {
            let p = workspace.queue[top];
            top += 1;

            for &(u, e) in &self.adjacent[p] {
                if Some(e) == exclude {
                    continue;
                }
                if self.edge_state[e] == EdgeState::Line && !workspace.visited[u] {
                    workspace.visited[u] = true;
                    workspace.previous[u] = (p, e);
                    workspace.queue.push(u);
                }
            }
        }

        assert!(workspace.visited[b]);

        let mut path = vec![];
        let mut v = b;
        while v != a {
            let (p, e) = workspace.previous[v];
            path.push(e);
            v = p;
        }
        path
    }

    fn shortcut_path(&self, a: usize, b: usize) -> Option<Vec<usize>> {
        let ra = self.root(a);
        let rb = self.root(b);
        if ra == rb {
            return Some(self.find_path(a, b, None));
        }
        let ta = self.terminal[ra]?;
        let tb = self.terminal[rb]?;
        if self.clue[ta] != self.clue[tb] {
            return None;
        }
        let mut reason = self.find_path(a, ta, None);
        reason.extend(self.find_path(tb, b, None));
        Some(reason)
    }

    fn edge_between(&self, a: usize, b: usize) -> usize {
        for &(u, e) in &self.adjacent[a] {
            if u == b {
                return e;
            }
        }
        panic!("No edge between {} and {}", a, b);
    }

    fn find_shortcut(&self, start: usize, end: usize, stride: usize) -> Option<Vec<(usize, bool)>> {
        let mut v = start;
        let mut last = None;

        while v <= end {
            match self.vertex_state[v] {
                VertexState::Unknown => {
                    last = None;
                }
                VertexState::NotTraversed => {}
                VertexState::Traversed => {
                    if let Some(last) = last {
                        let blocker = if v - last == stride {
                            let e = self.edge_between(v, last);
                            if self.edge_state[e] != EdgeState::NoLine {
                                None
                            } else {
                                Some(e)
                            }
                        } else {
                            Some(!0)
                        };

                        if let Some(blocker) = blocker {
                            if let Some(reason) = self.shortcut_path(last, v) {
                                let mut reason =
                                    reason.iter().map(|&e| (e, true)).collect::<Vec<_>>();
                                let mut w = last + stride;
                                while w < v {
                                    reason.push((self.edges.len() + w, false));
                                    w += stride;
                                }
                                if blocker != !0 {
                                    reason.push((blocker, false));
                                }

                                // Needed because this reason is found only when vertex_state is set to Traversed
                                reason.push((self.edges.len() + last, true));
                                reason.push((self.edges.len() + v, true));
                                return Some(reason);
                            }
                        }
                    }
                    last = Some(v);
                }
            }
            v += stride;
        }

        None
    }
}

impl SimpleCustomConstraint for PathPropagator {
    fn initialize_sat(&mut self, num_inputs: usize) {
        assert_eq!(num_inputs, self.edge_state.len() + self.vertex_state.len());
    }

    fn lazy_propagation(&self) -> bool {
        true
    }

    fn notify(&mut self, index: usize, value: bool) {
        if index < self.edges.len() {
            assert_eq!(self.edge_state[index], EdgeState::Unknown);
            self.edge_state[index] = if value {
                EdgeState::Line
            } else {
                EdgeState::NoLine
            };

            let mut merge = None;
            let mut conflict = None;

            if value {
                let (a, b) = self.edges[index];
                let root_a = self.root(a);
                let root_b = self.root(b);

                if root_a == root_b {
                    conflict = Some(Conflict {
                        a,
                        b,
                        cycle_edge: Some(index),
                    });
                } else {
                    if let (Some(ta), Some(tb)) = (self.terminal[root_a], self.terminal[root_b]) {
                        if self.clue[ta] != self.clue[tb] {
                            conflict = Some(Conflict {
                                a: ta,
                                b: tb,
                                cycle_edge: None,
                            });
                        }
                    }

                    let mut root_a = root_a;
                    let mut root_b = root_b;
                    if self.size[root_a] < self.size[root_b] {
                        std::mem::swap(&mut root_a, &mut root_b);
                    }
                    merge = Some(Merge {
                        child: root_b,
                        parent: root_a,
                        old_size: self.size[root_a],
                        old_terminal: self.terminal[root_a],
                    });
                    self.parent[root_b] = root_a;
                    self.size[root_a] += self.size[root_b];
                    if self.terminal[root_a].is_none() {
                        self.terminal[root_a] = self.terminal[root_b];
                    }
                }
            }

            self.updates.push(Update::Edge {
                index,
                merge,
                conflict: conflict.is_some(),
            });
            if let Some(c) = conflict {
                self.conflicts.push(c);
            }
        } else {
            let index = index - self.edges.len();
            assert_eq!(self.vertex_state[index], VertexState::Unknown);
            self.vertex_state[index] = if value {
                VertexState::Traversed
            } else {
                VertexState::NotTraversed
            };
            self.updates.push(Update::Vertex { index });
        }
    }

    fn find_inconsistency(&mut self) -> Option<Vec<(usize, bool)>> {
        if let Some(c) = self.conflicts.first() {
            let path = self.find_path(c.a, c.b, c.cycle_edge);
            let mut reason = vec![];
            for e in path {
                reason.push((e, true));
            }
            if let Some(e) = c.cycle_edge {
                reason.push((e, true));
            }
            return Some(reason);
        }

        for y in 0..self.height {
            if let Some(reason) = self.find_shortcut(y * self.width, (y + 1) * self.width - 1, 1) {
                return Some(reason);
            }
        }
        for x in 0..self.width {
            if let Some(reason) =
                self.find_shortcut(x, x + (self.height - 1) * self.width, self.width)
            {
                return Some(reason);
            }
        }
        None
    }

    fn undo(&mut self) {
        let update = self.updates.pop().unwrap();
        match update {
            Update::Edge {
                index,
                merge,
                conflict,
            } => {
                if conflict {
                    self.conflicts.pop();
                }
                if let Some(m) = merge {
                    self.parent[m.child] = m.child;
                    self.size[m.parent] = m.old_size;
                    self.terminal[m.parent] = m.old_terminal;
                }
                self.edge_state[index] = EdgeState::Unknown;
            }
            Update::Vertex { index } => {
                self.vertex_state[index] = VertexState::Unknown;
            }
        }
    }
}

/// Lazy G2 check. Unlabelled segments remain part of the free area: excluding
/// them could hide a bridge between regions and make the planarity test unsound.
pub(super) struct PlanarityPropagator {
    path: PathPropagator,
}

impl PlanarityPropagator {
    pub(super) fn new(h: usize, w: usize, clues: &[Vec<Option<i32>>]) -> Self {
        Self {
            path: PathPropagator::new(h, w, clues),
        }
    }

    fn crossing(&self) -> bool {
        let p = &self.path;
        if !p.conflicts.is_empty() {
            return false;
        }
        let n = p.height * p.width;
        let pitch = p.width + 2;
        let mut tags = vec![-1i32; (p.height + 2) * pitch];
        let offsets = [0usize.wrapping_sub(pitch), 1, pitch, usize::MAX];
        let index = |v: usize| (v / p.width + 1) * pitch + v % p.width + 1;
        let mut clues_in_root = vec![0; n];
        for v in 0..n {
            if p.clue[v].is_some() {
                clues_in_root[p.root(v)] += 1;
            }
        }
        let mut ends = vec![];
        let mut exits = vec![0u8; n];
        for v in 0..n {
            let r = p.root(v);
            if clues_in_root[r] == 0 {
                if p.vertex_state[v] != VertexState::NotTraversed {
                    tags[index(v)] = 0;
                }
                continue;
            }
            let degree = p.adjacent[v]
                .iter()
                .filter(|&&(_, e)| p.edge_state[e] == EdgeState::Line)
                .count();
            if clues_in_root[r] == 1
                && ((p.clue[v].is_some() && degree == 0) || (p.clue[v].is_none() && degree == 1))
            {
                ends.push(v);
                tags[index(v)] = v as i32 + 1;
                for &(u, e) in &p.adjacent[v] {
                    if p.edge_state[e] == EdgeState::Unknown {
                        let delta = index(u).wrapping_sub(index(v));
                        let d = offsets.iter().position(|&o| o == delta).unwrap();
                        exits[v] |= 1 << d;
                    }
                }
            }
        }
        if ends.len() < 4 {
            return false;
        }
        // Geometric connectivity is deliberately an overapproximation: even a
        // NoLine edge inside the free area does not split that area.
        let mut components = vec![0; tags.len()];
        let mut queue = vec![];
        let mut next_component = 0;
        for v in 0..n {
            let start = index(v);
            if tags[start] != 0 || components[start] != 0 {
                continue;
            }
            next_component += 1;
            components[start] = next_component;
            queue.clear();
            queue.push(start);
            let mut head = 0;
            while head < queue.len() {
                let c = queue[head];
                head += 1;
                for &offset in &offsets {
                    let a = c.wrapping_add(offset);
                    if tags[a] == 0 && components[a] == 0 {
                        components[a] = next_component;
                        queue.push(a);
                    }
                }
            }
        }
        let mut confined = vec![0; n];
        for &v in &ends {
            if exits[v] == 0 {
                continue;
            }
            let mut component = 0;
            for d in 0..4 {
                if exits[v] & (1 << d) == 0 {
                    continue;
                }
                let neighbor = index(v).wrapping_add(offsets[d]);
                let c = components[neighbor];
                if c == 0 || (component != 0 && component != c) {
                    component = 0;
                    break;
                }
                component = c;
            }
            confined[v] = component;
        }
        let value = |v: usize| p.clue[p.terminal[p.root(v)].unwrap()].unwrap();
        let mut pairs = vec![];
        for (i, &a) in ends.iter().enumerate() {
            if confined[a] == 0 {
                continue;
            }
            for &b in &ends[i + 1..] {
                if confined[a] == confined[b]
                    && value(a) == value(b)
                    && p.clue.iter().filter(|&&c| c == Some(value(a))).count() == 2
                {
                    pairs.push((a, b));
                }
            }
        }
        if pairs.len() < 2 {
            return false;
        }
        let mut seen = vec![0u8; n];
        for &end in &ends {
            if confined[end] == 0 {
                continue;
            }
            for direction in 0..4 {
                if exits[end] & !seen[end] & (1 << direction) == 0 {
                    continue;
                }
                let start = index(end).wrapping_add(offsets[direction]);
                let start_d = (direction + 3) & 3;
                let (mut c, mut d) = (start, start_d);
                let mut contacts = vec![];
                let mut masks = vec![0u8; n];
                let mut closed = false;
                // Follow the region boundary with the right-hand rule.
                for _ in 0..=4 * n {
                    let a = c.wrapping_add(offsets[d]);
                    let (occupied, contact_dir);
                    if tags[a] == 0 {
                        let side = (d + 1) & 3;
                        let b = a.wrapping_add(offsets[side ^ 2]);
                        if tags[b] == 0 {
                            contact_dir = d;
                            c = b;
                            d = (d + 3) & 3;
                            occupied = c.wrapping_add(offsets[contact_dir ^ 2]);
                        } else {
                            c = a;
                            contact_dir = side;
                            occupied = b;
                        }
                    } else {
                        d = (d + 1) & 3;
                        contact_dir = (d + 1) & 3;
                        occupied = a;
                    }
                    if tags[occupied] > 0 {
                        let v = tags[occupied] as usize - 1;
                        let bit = 1 << contact_dir;
                        if exits[v] & bit != 0 {
                            contacts.push(v);
                            masks[v] ^= bit;
                            seen[v] |= bit;
                        }
                    }
                    if (c, d) == (start, start_d) {
                        closed = true;
                        break;
                    }
                }
                if !closed {
                    continue;
                }
                let boundary_pairs: Vec<_> = pairs
                    .iter()
                    .copied()
                    .filter(|&(a, b)| masks[a] == exits[a] && masks[b] == exits[b])
                    .collect();
                for (i, &(a, aa)) in boundary_pairs.iter().enumerate() {
                    for &(b, bb) in &boundary_pairs[i + 1..] {
                        if value(a) == value(b) {
                            continue;
                        }
                        let mut order = vec![];
                        for &v in &contacts {
                            if [a, aa, b, bb].contains(&v) && order.last() != Some(&v) {
                                order.push(v);
                            }
                        }
                        if order.len() > 1 && order.first() == order.last() {
                            order.pop();
                        }
                        if order.len() == 4
                            && (0..4).all(|i| value(order[i]) != value(order[(i + 1) % 4]))
                        {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }
}

impl SimpleCustomConstraint for PlanarityPropagator {
    fn initialize_sat(&mut self, inputs: usize) {
        self.path.initialize_sat(inputs);
    }
    fn lazy_propagation(&self) -> bool {
        true
    }
    fn notify(&mut self, index: usize, value: bool) {
        self.path.notify(index, value);
    }
    fn undo(&mut self) {
        self.path.undo();
    }
    fn find_inconsistency(&mut self) -> Option<Vec<(usize, bool)>> {
        if !self.crossing() {
            return None;
        }
        // Conservative certificate: all known edges preserve the four clue paths,
        // every labelled boundary blocker, and every forbidden port exit. False
        // passed literals preserve unused blocking cells. No unlabelled traversed
        // cell was excluded from a region. All entries are currently true literals.
        let mut reason = vec![];
        for (e, &state) in self.path.edge_state.iter().enumerate() {
            match state {
                EdgeState::Line => reason.push((e, true)),
                EdgeState::NoLine => reason.push((e, false)),
                EdgeState::Unknown => (),
            }
        }
        for (v, &state) in self.path.vertex_state.iter().enumerate() {
            if state == VertexState::NotTraversed {
                reason.push((self.path.edges.len() + v, false));
            }
        }
        Some(reason)
    }
}

#[cfg(test)]
mod planarity_tests {
    use super::*;

    fn four_ports(escape: bool, alternating: bool) -> PlanarityPropagator {
        let mut clues = vec![vec![None; 7]; 7];
        for (y, x, v) in [
            (1, 3, 1),
            (3, 5, 2),
            (5, 3, if alternating { 1 } else { 2 }),
            (3, 1, if alternating { 2 } else { 1 }),
        ] {
            clues[y][x] = Some(v);
        }
        let mut p = PlanarityPropagator::new(7, 7, &clues);
        let free = |v: usize| {
            let (y, x) = (v / 7, v % 7);
            clues[y][x].is_some()
                || ((2..=4).contains(&y) && (2..=4).contains(&x))
                || (escape && v == 3)
        };
        for e in 0..p.path.edges.len() {
            let (a, b) = p.path.edges[e];
            if !free(a) || !free(b) {
                p.notify(e, false);
            }
        }
        for v in 0..49 {
            if !free(v) {
                p.notify(p.path.edges.len() + v, false);
            }
        }
        p
    }

    #[test]
    fn test_numlin_g2_boundary_reason_and_undo() {
        let mut p = four_ports(false, true);
        let reason = p.find_inconsistency().expect("alternating confined pairs");
        assert!(!reason.is_empty());
        // The certificate alone reproduces the geometric contradiction.
        let mut replay = PlanarityPropagator::new(
            7,
            7,
            &p.path
                .clue
                .chunks(7)
                .map(|r| r.to_vec())
                .collect::<Vec<_>>(),
        );
        for &(i, v) in &reason {
            replay.notify(i, v);
        }
        assert!(replay.find_inconsistency().is_some());
        for _ in 0..reason.len() {
            replay.undo();
        }
        assert!(replay.find_inconsistency().is_none());
        assert!(
            four_ports(true, true).find_inconsistency().is_none(),
            "escape prevents confinement"
        );
        assert!(
            four_ports(false, false).find_inconsistency().is_none(),
            "nonalternating pairs"
        );
    }
}
