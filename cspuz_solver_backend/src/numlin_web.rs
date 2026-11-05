//! Numberlink C ABI. Each call owns its model; only the length-prefixed reply is shared.
use super::numlin_json::{self as json, Json};
use cspuz_rs_puzzles::puzzles::numlin::{FixedEdge, NumlinAssumptionSolver, NumlinOptions};
use crate::cubes::{estimate_cube_size, generate_cubes_balanced_verify_floor, split_cube, Cube, SolveOptions};
use crate::cubes::{Problem, strong_options};
use std::time::Instant;

struct Options {
    threads: usize, cubes: usize, balance: f64, balance_verify: f64,
    verify_min: f64, verify_floor: f64, score_k: usize, score_factor: f64,
    score_min_total: f64, score_rounds: usize, probes: usize, transform: usize,
    cube: SolveOptions, sat: NumlinOptions,
}
impl Options {
    fn new(v: &Json) -> Result<Self, String> {
        let integer = |key, default, min, max| -> usize { v.get(key).number(default as f64).clamp(min as f64, max as f64) as usize };
        let number = |key, default| -> f64 { v.get(key).number(default).max(0.0) };
        let mut sat = NumlinOptions::default();
        sat.rules = v.get("rules").string("wedge").replace('+', ",").parse().map_err(|e| format!("invalid SAT rules: {e}"))?;
        sat.full_cover = v.get("full_cover").boolean(false);
        sat.short_only = v.get("short_only").boolean(false);
        sat.log_encoding = v.get("log_encoding").boolean(false);
        let cube = match v.get("cube_rules").string("strong") {
            "strong" => strong_options(),
            "off" => SolveOptions::default(),
            _ => return Err("cube_rules must be strong or off".into()),
        };
        Ok(Self {
            threads: integer("threads", 8, 1, 256), cubes: integer("cubes", 64, 0, 32768),
            balance: number("balance", 4.0), balance_verify: number("balance_verify", 10.0),
            verify_min: number("verify_min", 2.0), verify_floor: number("verify_floor", 1e6),
            score_k: integer("score_k", 10, 0, 10000), score_factor: number("score_factor", 30.0),
            score_min_total: number("score_min_total", 1e8), score_rounds: integer("score_rounds", 1, 0, 100),
            probes: integer("probes", 100, 1, 1000000), transform: integer("transform", 0, 0, 7), cube, sat,
        })
    }
}

fn problem(url: &str, opts: &Options) -> Result<Problem, String> {
    Problem::from_url(url, opts.transform)
}
fn cube_json(c: &Cube, id: usize) -> String {
    let edges = c.edges.iter().map(|(y,x,v)| format!("[{y},{x},{v}]")).collect::<Vec<_>>().join(",");
    format!("{{\"id\":{id},\"edges\":[{edges}],\"next\":{},\"est\":{}}}", c.next, c.weight)
}
fn cubes_json(cubes: &[Cube]) -> String {
    cubes.iter().enumerate().map(|(id, c)| cube_json(c, id)).collect::<Vec<_>>().join(",")
}
fn read_cube(v: &Json, p: &Problem) -> Result<Cube, String> {
    let uint = |v: &Json| -> Result<usize, String> {
        let n = v.number(-1.0);
        if n < 0.0 || n.fract() != 0.0 || n > usize::MAX as f64 { return Err("invalid cube coordinate".into()); }
        Ok(n as usize)
    };
    let mut edges = Vec::new();
    for edge in v.get("edges").array()? {
        let a = edge.array()?;
        if a.len() != 3 { return Err("edge must be [y,x,bool]".into()); }
        let y = uint(&a[0])?; let x = uint(&a[1])?;
        if y >= 2*p.height()-1 || x >= 2*p.width()-1 || y%2 == x%2 { return Err("edge outside board or not on an edge".into()); }
        let value = match a[2] { Json::Bool(b) => b, _ => return Err("edge value must be boolean".into()) };
        edges.push((y,x,value));
    }
    let next = uint(v.get("next"))?;
    if next > p.width()*p.height() { return Err("cube next outside board".into()); }
    Ok(Cube { edges, next, weight: v.get("est").number(0.0).max(0.0) })
}
fn sort(cubes: &mut [Cube]) { cubes.sort_by(|a,b| b.weight.total_cmp(&a.weight)); }

// Native --score pass, with the same seeds, max-of-K scores and fixed generation mean.
// Sequential here: Web Workers provide concurrency; a wasm instance has no OS threads.
fn score(p: &Problem, cubes: &mut Vec<Cube>, extra: &mut usize, o: &Options) {
    let total0: f64 = cubes.iter().map(|c| c.weight).sum();
    if o.score_k == 0 || o.balance == 0.0 || total0 < o.score_min_total { return; }
    let score_of = |cs: &[Cube], round: usize| -> Vec<f64> {
        cs.iter().enumerate().map(|(i,c)| (0..o.score_k).map(|k| {
            estimate_cube_size(p, c, o.probes, 7_777_777 + round as u64 * 1_000_003 + k as u64 * 7_919 + i as u64 * 104_729, &o.cube)
        }).fold(0.0f64, f64::max)).collect()
    };
    let mut scores = score_of(cubes, 0);
    let threshold = (o.score_factor * total0 / cubes.len().max(1) as f64).max(o.verify_floor);
    for round in 1..=o.score_rounds {
        let mut keep = Vec::new(); let mut kept_scores = Vec::new(); let mut children = Vec::new();
        for (c, sc) in cubes.drain(..).zip(scores.iter().copied()) {
            if sc >= threshold {
                let (parts, found) = split_cube(p.clone(), &c, 2, &o.cube);
                if parts.len() != 1 { *extra += found; children.extend(parts); continue; }
            }
            keep.push(c); kept_scores.push(sc);
        }
        let no_children = children.is_empty();
        let child_scores = score_of(&children, round);
        for (mut c, sc) in children.into_iter().zip(child_scores) { c.weight = sc; keep.push(c); kept_scores.push(sc); }
        *cubes = keep; scores = kept_scores;
        if no_children { break; }
    }
    for (c, sc) in cubes.iter_mut().zip(scores) { c.weight = sc; }
    sort(cubes);
}
fn generate(url: &str, v: &Json) -> Result<String, String> {
    let start = Instant::now(); let o = Options::new(v)?; let p = problem(url, &o)?;
    let (mut cubes, mut extra) = if o.sat.full_cover || o.sat.short_only {
        (vec![Cube { edges: vec![], next: 0, weight: 0.0 }], 0)
    } else if o.balance > 0.0 {
        // The logical worker count controls the balancing limit. solver.rs forces only
        // the estimator's execution concurrency to one on wasm, preserving native cubes.
        generate_cubes_balanced_verify_floor(p.clone(), o.cubes, o.threads, o.balance, 0.0, o.balance_verify, o.verify_min, o.verify_floor, o.probes, 1<<15, &o.cube)
    } else {
        // Unlike generate_cubes_at(), retain solutions completed by the initial split.
        split_cube(p.clone(), &Cube { edges: vec![], next: 0, weight: 0.0 }, o.cubes, &o.cube)
    };
    if !o.sat.full_cover && !o.sat.short_only { score(&p, &mut cubes, &mut extra, &o); }
    sort(&mut cubes);
    let total: f64 = cubes.iter().map(|c| c.weight).sum();
    // Row-scan splitting can exhaust a solution without leaving a SAT task. Obtain
    // its diagram from the same SAT model, without adding to the answer count.
    let answer = if extra > 0 {
        solve_answers(&p, &Cube { edges: vec![], next: 0, weight: 0.0 }, &o, 1)?.1
    } else { "null".into() };
    Ok(format!("{{\"width\":{},\"height\":{},\"cubes\":[{}],\"extra_solutions\":{extra},\"answer\":{answer},\"total_est\":{total},\"gen_ms\":{}}}", p.width(), p.height(), cubes_json(&cubes), start.elapsed().as_secs_f64()*1000.0))
}
fn solve(url: &str, v: &Json, max: usize) -> Result<String, String> {
    let start = Instant::now(); let o = Options::new(v.get("options"))?; let p = problem(url, &o)?;
    let c = read_cube(v, &p)?;
    let (answers, answer) = solve_answers(&p, &c, &o, max)?;
    Ok(format!("{{\"answers\":{answers},\"answer\":{answer},\"elapsed_ms\":{}}}", start.elapsed().as_secs_f64()*1000.0))
}
fn solve_answers(p: &Problem, c: &Cube, o: &Options, max: usize) -> Result<(usize, String), String> {
    let fixed: Vec<FixedEdge> = c.to_fixed_edges();
    let clues: Vec<Vec<Option<i32>>> = (0..p.height()).map(|y| (0..p.width()).map(|x| p[(y,x)]).collect()).collect();
    let mut solver = NumlinAssumptionSolver::with_fixed(&clues, &fixed, o.sat);
    let models = solver.solve_cube_limited(&[], max, None).ok_or("unexpected solver interruption")?;
    let answers = models.len();
    let answer = models.first().map(|model| {
        let (w, h) = if o.transform % 2 == 1 { (p.height(), p.width()) } else { (p.width(), p.height()) };
        answer_json(&model.horizontal, &model.vertical, w, h, o.transform)
    }).unwrap_or_else(|| "null".into());
    Ok((answers, answer))
}

// Transform original cell coordinates and direction vectors into the SAT model's
// orientation, then read its edges back in the original up/right/down/left order.
fn answer_json(horizontal: &[Vec<bool>], vertical: &[Vec<bool>], w: usize, h: usize, k: usize) -> String {
    let position = |mut x: usize, mut y: usize| {
        let (mut tw, mut th) = (w, h);
        if k >= 4 { x = tw - 1 - x; }
        for _ in 0..k % 4 {
            (x, y) = (th - 1 - y, x);
            std::mem::swap(&mut tw, &mut th);
        }
        (x, y)
    };
    let mut links = vec![0u8; w*h];
    for y in 0..h {
        for x in 0..w {
            let (tx, ty) = position(x, y);
            for (bit, dx, dy) in [(1, 0, -1), (2, 1, 0), (4, 0, 1), (8, -1, 0)] {
                let (nx, ny) = (x as isize + dx, y as isize + dy);
                if nx < 0 || ny < 0 || nx >= w as isize || ny >= h as isize { continue; }
                let (nx, ny) = position(nx as usize, ny as usize);
                let used = if ty == ny { horizontal[ty][tx.min(nx)] } else { vertical[ty.min(ny)][tx] };
                if used { links[y*w+x] |= bit; }
            }
        }
    }
    let empty = links.contains(&0);
    format!("{{\"width\":{w},\"height\":{h},\"links\":{:?},\"has_empty\":{empty}}}", links)
}

fn split(url: &str, v: &Json, min_tasks: usize) -> Result<String, String> {
    let o = Options::new(v.get("options"))?; let p = problem(url, &o)?; let c = read_cube(v, &p)?;
    // Row-scan's completed answers do not distinguish short solutions. Keep this
    // existence-only mode on its unrestricted SAT model instead of miscounting extras.
    if o.sat.short_only || o.sat.full_cover { return Ok(format!("{{\"cubes\":[{}],\"extra_solutions\":0,\"unsplittable\":true}}", cube_json(&c, 0))); }
    let (mut parts, extra) = split_cube(p.clone(), &c, min_tasks.max(2), &o.cube);
    for (i,c) in parts.iter_mut().enumerate() { c.weight = estimate_cube_size(&p, c, o.probes, 7+i as u64, &o.cube); }
    sort(&mut parts);
    let answer = if extra > 0 { solve_answers(&p, &c, &o, 1)?.1 } else { "null".into() };
    Ok(format!("{{\"cubes\":[{}],\"extra_solutions\":{extra},\"answer\":{answer}}}", cubes_json(&parts)))
}
fn estimate(url: &str, v: &Json, probes: usize, seed: u32) -> Result<String, String> {
    let o = Options::new(v.get("options"))?; let p = problem(url, &o)?; let c = read_cube(v, &p)?;
    Ok(format!("{{\"est\":{}}}", estimate_cube_size(&p, &c, probes.max(1), seed as u64, &o.cube)))
}

unsafe fn call(url: *const u8, len: usize, input: *const u8, input_len: usize, f: impl FnOnce(&str, &Json) -> Result<String,String>) -> *const u8 {
    let result = (|| {
        let url = std::str::from_utf8(std::slice::from_raw_parts(url, len)).map_err(|_| "invalid URL UTF-8")?;
        let input = std::str::from_utf8(std::slice::from_raw_parts(input, input_len)).map_err(|_| "invalid JSON UTF-8")?;
        let value = json::parse(input)?;
        f(url, &value)
    })();
    let reply = result.unwrap_or_else(|e| format!("{{\"error\":{}}}", json::quote(&e)));
    super::SHARED_ARRAY.clear();
    super::SHARED_ARRAY.extend_from_slice(&(reply.len() as u32).to_le_bytes());
    super::SHARED_ARRAY.extend_from_slice(reply.as_bytes());
    super::SHARED_ARRAY.as_ptr()
}
#[no_mangle]
pub unsafe extern "C" fn numlin_cubes(url: *const u8, len: usize, opts: *const u8, opts_len: usize) -> *const u8 { call(url, len, opts, opts_len, generate) }
#[no_mangle]
pub unsafe extern "C" fn numlin_solve_cube(url: *const u8, len: usize, cube: *const u8, cube_len: usize, max: usize) -> *const u8 { call(url, len, cube, cube_len, |u,v| solve(u,v,max)) }
#[no_mangle]
pub unsafe extern "C" fn numlin_split_cube(url: *const u8, len: usize, cube: *const u8, cube_len: usize, min_tasks: usize) -> *const u8 { call(url, len, cube, cube_len, |u,v| split(u,v,min_tasks)) }
#[no_mangle]
pub unsafe extern "C" fn numlin_estimate_cube(url: *const u8, len: usize, cube: *const u8, cube_len: usize, probes: usize, seed: u32) -> *const u8 { call(url, len, cube, cube_len, |u,v| estimate(u,v,probes,seed)) }

#[cfg(test)]
mod tests {
    use super::*;
    const URL: &str = "p?numlin/2/2/1h1";
    #[test]
    fn abi_models_and_validation() {
        let v = json::parse(r#"{"edges":[],"next":0,"options":{"rules":"off"}}"#).unwrap();
        let r = json::parse(&solve(URL, &v, 2).unwrap()).unwrap();
        assert_eq!(r.get("answers").number(-1.0), 1.0);
        assert!(generate("p?numlin/2/2/1", &Json::Null).is_err());
        assert!(generate("p?numlin/2/2/1gg2", &Json::Null).is_err());
        let bad = json::parse(r#"{"edges":[[0,0,true]],"next":0}"#).unwrap();
        assert!(solve(URL, &bad, 2).is_err());
    }
    #[test]
    fn split_extras_and_json() {
        let input = json::parse(r#"{"cubes":64,"balance":0}"#).unwrap();
        let result = json::parse(&generate(URL, &input).unwrap()).unwrap();
        assert!(result.get("extra_solutions").number(-1.0) > 0.0);
        validate_answer(URL, &result);
        assert!(json::parse("{bad}").is_err());
        assert_eq!(json::parse(r#""\ud83d\udc08""#).unwrap().string(""), "🐈");
    }
    fn validate_answer(url: &str, r: &Json) {
        let o = Options::new(&Json::Null).unwrap();
        let p = problem(url, &o).unwrap();
        let a = r.get("answer");
        let links: Vec<_> = a.get("links").array().unwrap().iter().map(|v| v.number(-1.0) as u8).collect();
        assert_eq!(a.get("width").number(0.0) as usize, p.width());
        assert_eq!(a.get("height").number(0.0) as usize, p.height());
        assert_eq!(links.len(), p.width()*p.height());
        assert_eq!(a.get("has_empty").boolean(false), links.contains(&0));
        let mut seen = vec![false; links.len()];
        for c in 0..links.len() {
            let (x,y) = (c%p.width(),c/p.width());
            assert!(links[c] < 16);
            assert_eq!(links[c].count_ones(), if p[(y,x)].is_some() { 1 } else if links[c] != 0 { 2 } else { 0 });
            if links[c] == 0 || seen[c] { continue; }
            let mut stack = vec![c]; let mut ends = vec![];
            while let Some(c) = stack.pop() {
                if seen[c] { continue; }
                seen[c] = true;
                let (x,y) = (c%p.width(),c/p.width());
                if let Some(n) = p[(y,x)] { ends.push(n); }
                for (bit,back,dx,dy) in [(1,4,0,-1),(2,8,1,0),(4,1,0,1),(8,2,-1,0)] {
                    if links[c] & bit == 0 { continue; }
                    let (nx,ny) = (x as isize+dx,y as isize+dy);
                    assert!(nx>=0 && ny>=0 && nx<p.width() as isize && ny<p.height() as isize);
                    let n = ny as usize*p.width()+nx as usize;
                    assert_ne!(links[n]&back,0); stack.push(n);
                }
            }
            assert_eq!(ends.len(),2); assert_eq!(ends[0],ends[1]);
        }
    }
    #[test]
    fn first_answer_geometry_all_transforms() {
        // Rectangles, sparse/extended labels, unused cells, single-row boards,
        // and ambiguous boards catch both coordinate and direction inversions.
        for url in ["p?numlin/4/3/1h1g33g7h7", "p?numlin/3/2/-10g-10i", "p?numlin/2/1/11", "p?numlin/3/3/1m1"] {
            for k in 0..8 {
                let input = json::parse(&format!(r#"{{"edges":[],"next":0,"options":{{"rules":"off","transform":{k}}}}}"#)).unwrap();
                let r = json::parse(&solve(url,&input,2).unwrap()).unwrap();
                assert!(r.get("answers").number(0.0) > 0.0, "{url}, transform {k}");
                validate_answer(url,&r);
            }
        }
        let input = json::parse(r#"{"edges":[],"next":0}"#).unwrap();
        let r = json::parse(&solve("p?numlin/2/2/1221",&input,2).unwrap()).unwrap();
        assert_eq!(r.get("answers").number(-1.0),0.0);
        assert!(matches!(r.get("answer"), Json::Null));
    }

}
