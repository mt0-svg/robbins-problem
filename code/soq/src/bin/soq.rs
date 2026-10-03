// Fixed-point evaluator of the second-order certificate (Section 4 and Appendix B of the paper; the
// parts 1 to 6 of its specification, Robbins/Cert/SO/Spec.lean). Every quantity is an integer (i128,
// overflow checked); every rounding is in the direction stated in the specification. The tables it writes
// (option emitall) are checked by the Lean kernel (Section 6 of the paper); the program is not trusted.
// Usage: soq N M RHO Q WMIN WMAX [kwin=K] [mc=COUNT] [nsub=S] [edge] [perstep] [emit=T:FILE] [emitall=DIR]
//        [checklists]
#[path = "../common.rs"]
mod common;
use common::Ms;
use rayon::prelude::*;
use std::time::Instant;

const SH: u32 = 36;
const D: i128 = 1 << SH;
const D2: i128 = D * D;

// Section 1: grid data. gpt[0..J-1] strictly increasing in (0, D), gpt[J] = D; start[1..n].
struct GridQ {
    n: usize,
    kwin: usize,
    gpt: Vec<i128>,
    start: Vec<usize>,
}

impl GridQ {
    fn from_f64(n: usize, rho: f64, q: usize, wmin: f64, wmax: f64, kwin: Option<usize>) -> GridQ {
        let g = common::Grid::new(n, rho, q, wmin, wmax, kwin);
        let mut gpt: Vec<i128> = g.gam.iter().map(|&v| (v * D as f64).floor() as i128).collect();
        for j in 0..gpt.len() {
            assert!(gpt[j] > 0 && gpt[j] < D && (j == 0 || gpt[j - 1] < gpt[j]));
        }
        gpt.push(D);
        let start = g.start.clone();
        for t in 1..n {
            assert!(start[t] <= start[t + 1]);
        }
        GridQ { n, kwin: g.kwin, gpt, start }
    }
    fn jtop(&self) -> usize {
        self.gpt.len() - 1
    }
    fn window(&self, t: usize) -> (usize, usize) {
        let s = self.start[t].min(self.jtop());
        let e = (self.start[t] + self.kwin).min(self.jtop());
        (s, e - s)
    }
    fn nt(&self, t: usize) -> usize {
        self.window(t).1 + 1
    }
    fn global(&self, t: usize, k: usize) -> usize {
        let (s, c) = self.window(t);
        if k < c { s + k } else { self.jtop() }
    }
    fn ceil_local(&self, t: usize, j: usize) -> usize {
        let (s, c) = self.window(t);
        if j >= self.jtop() || c == 0 {
            c
        } else if j < s {
            0
        } else if j < s + c {
            j - s
        } else {
            c
        }
    }
}

// Section 3: penalty tables E_t[j], t = 0..n, j = 0..J.
fn penalty_tables(g: &GridQ) -> Vec<Vec<i128>> {
    let jt = g.jtop();
    let mut e = vec![vec![0i128; jt + 1]; g.n + 1];
    e[g.n] = vec![D; jt + 1];
    for t in (0..g.n).rev() {
        for j in 0..=jt {
            e[t][j] = (e[t + 1][j] * (D - g.gpt[j])) >> SH;
        }
    }
    e
}

// Section 5.1: 2 * int_{pa}^{pb} min(a0 + a1 X, b0 - b1 X) dX, rounded down; a1 > 0, b1 >= 0.
#[inline]
fn cell2(pa: i128, pb: i128, a0: i128, a1: i128, b0: i128, b1: i128) -> i128 {
    let k = a1 + b1;
    let da = a0 - b0 + k * pa;
    let db = da + k * (pb - pa);
    let int_a = |x0: i128, x1: i128| 2 * a0 * (x1 - x0) + a1 * (x1 * x1 - x0 * x0);
    let int_b = |x0: i128, x1: i128| 2 * b0 * (x1 - x0) - b1 * (x1 * x1 - x0 * x0);
    if db <= 0 {
        int_a(pa, pb)
    } else if da >= 0 {
        int_b(pa, pb)
    } else {
        let z = pa + (-da) / k; // floor of the crossing point
        int_a(pa, z) + int_b(z, pb) - 2 * k
    }
}

// Section 5.2: bounds of 2 * int_{pa}^{pb} (Delta(X) - c)^+ dX, Delta(X) = da + k (X - pa), k > 0.
// Returns (lower, upper).
#[inline]
fn pos2(pa: i128, pb: i128, da: i128, k: i128, c: i128) -> (i128, i128) {
    let h = pb - pa;
    let ac = da - c;
    let bc = ac + k * h;
    if bc <= 0 {
        (0, 0)
    } else if ac >= 0 {
        ((ac + bc) * h, (ac + bc) * h)
    } else {
        let z = pa + (-ac) / k;
        let dz = ac + k * (z - pa);
        let lo = (dz + k + bc) * (pb - z - 1);
        let up = (dz + bc) * (pb - z) + 2 * k;
        (lo, up)
    }
}

// Section 5.2: lower bound (point units) of int_{pa}^{pb} min(1, Delta(X)^+ / s) dX, s > 0.
#[inline]
fn chord(pa: i128, pb: i128, a0: i128, a1: i128, b0: i128, b1: i128, s: i128) -> i128 {
    let k = a1 + b1;
    let da = a0 - b0 + k * pa;
    let h = pb - pa;
    if da + k * h <= 0 {
        return 0;
    }
    if da >= s {
        return h;
    }
    let (lo0, _) = pos2(pa, pb, da, k, 0);
    let (_, up1) = pos2(pa, pb, da, k, s);
    let num = lo0 - up1;
    if num <= 0 { 0 } else { num / (2 * s) }
}


// Case of cell2 (0: stop cost below the continuation on the whole cell, 1: continuation below, 2:
// crossing inside) and of chord (3: zero, 4: one on the whole cell, 5: ramp), for the cost count.
#[inline]
fn cell_cases(pa: i128, pb: i128, a0: i128, a1: i128, b0: i128, b1: i128, s: i128) -> (usize, usize) {
    let k = a1 + b1;
    let da = a0 - b0 + k * pa;
    let db = da + k * (pb - pa);
    let c = if db <= 0 { 0 } else if da >= 0 { 1 } else { 2 };
    let q = if s <= 0 { 6 } else if db <= 0 { 3 } else if da >= s { 4 } else { 5 };
    (c, q)
}
struct Ctx {
    m: usize,
    r: i128,
    l: usize,
    pts: Vec<usize>,  // global index of p_i, i = 1..L (pts[0] unused)
    pv: Vec<i128>,    // p_0 = 0, ..., p_L = D
    nxt: Vec<usize>,  // local index in G_{t+1} of ceil_{t+1}(p_i)
    pos: Vec<usize>,  // cell of local point k of G_t
    cmap: Vec<usize>, // local index in G_{t+1} of ceil_{t+1}(local point k)
    vals0: Vec<i128>, // value of local point k of G_t
    gidx0: Vec<usize>,
    dbox: Vec<i128>,  // box width of local point k (0 for the point 1)
    vals1: Vec<i128>, // value of local point of G_{t+1}
    et: Vec<i128>,    // E_t on global points
    et1: Vec<i128>,   // E_{t+1}
    etm1: Vec<i128>,  // E_{t-1}
    nt0: usize,
}

fn ctx_new(g: &GridQ, e: &[Vec<i128>], m: usize, t: usize) -> Ctx {
    let (s0, c0) = g.window(t);
    let (s1, c1) = g.window(t + 1);
    let jt = g.jtop();
    let mut p: Vec<usize> = (s0..s0 + c0).chain(s1..s1 + c1).collect();
    p.sort();
    p.dedup();
    p.push(jt);
    let l = p.len();
    let mut pts = vec![0usize; l + 1];
    let mut pv = vec![0i128; l + 1];
    let mut nxt = vec![0usize; l + 1];
    for i in 1..=l {
        pts[i] = p[i - 1];
        pv[i] = g.gpt[p[i - 1]];
        nxt[i] = g.ceil_local(t + 1, p[i - 1]);
    }
    let nt0 = c0 + 1;
    let mut pos = vec![0; nt0];
    let mut cmap = vec![0; nt0];
    let mut vals0 = vec![0i128; nt0];
    let mut gidx0 = vec![0usize; nt0];
    let mut dbox = vec![0i128; nt0];
    for k in 0..nt0 {
        let gj = g.global(t, k);
        pos[k] = 1 + p.binary_search(&gj).unwrap();
        cmap[k] = g.ceil_local(t + 1, gj);
        vals0[k] = g.gpt[gj];
        gidx0[k] = gj;
    }
    for k in 0..nt0 - 1 {
        dbox[k] = vals0[k] - if k == 0 { 0 } else { vals0[k - 1] };
    }
    let vals1 = (0..c1 + 1).map(|k| g.gpt[g.global(t + 1, k)]).collect();
    Ctx { m, r: (g.n - t) as i128, l, pts, pv, nxt, pos, cmap, vals0, gidx0, dbox, vals1, et: e[t].clone(), et1: e[t + 1].clone(), etm1: e[t - 1].clone(), nt0 }
}

#[derive(Clone, Copy, Default)]
struct Co {
    pos: usize,
    val: i128,
    dl: i128,
    cm: usize,
    gi: usize,
    forg: bool,
}

fn co_local(c: &Ctx, kj: usize) -> Co {
    let forg = kj == c.nt0 - 1;
    Co { pos: c.pos[kj], val: c.vals0[kj], dl: c.dbox[kj], cm: c.cmap[kj], gi: c.gidx0[kj], forg }
}

#[derive(Default, Clone, Copy)]
struct Cnt {
    inner: u64,
    tailc: u64,
    chords: u64,
    lookups: u64,
    exact_tail: u64,
    cases: [u64; 7],
    nonmono: u64,
}

// Section 5.3 to 5.5: corner value T0 (units 1/D) and slope bounds mu (units 1/D) of one memory.
fn state(c: &Ctx, ms1: &Ms, uh1: &[i128], sg1: &[i128], co: &[Co], cnt: &mut Cnt) -> (i128, [i128; 8]) {
    let m = c.m;
    let r = c.r;
    let rd = r * D;
    let tf = co[m - 1].forg;
    let im = co[m - 1].pos;
    let mut ev = [0i128; 8];
    for j in 0..m {
        if !co[j].forg {
            ev[j] = c.vals1[co[j].cm] - co[j].val;
            assert!(ev[j] >= 0);
        }
    }
    let em = c.et[co[m - 1].gi];
    let pm = r * c.et1[co[m - 1].gi];
    let mut big_r: i128 = 0; // units 1/(2 D^3)
    let mut acc = [0i128; 8]; // units 1/D^2
    let mut lam = [0i128; 8]; // units 1/D
    let mut tup = [0usize; 8];
    let mut coef = [0i128; 8];
    let mut seen = false;
    let mut nonmono = false;
    for i in 1..=im {
        let (pa, pb) = (c.pv[i - 1], c.pv[i]);
        let mut below = 0;
        for j in 0..m - 1 {
            if co[j].pos <= i - 1 {
                below += 1;
            }
        }
        let alpha = 1 + below as i128;
        let x1 = c.nxt[i];
        let mut p = 0;
        for j in 0..m - 1 {
            if j == below {
                tup[p] = x1;
                p += 1;
            }
            tup[p] = co[j].cm;
            p += 1;
        }
        if below == m - 1 {
            tup[p] = x1;
        }
        let r1 = ms1.rank(&tup[..m]);
        cnt.lookups += 1;
        let v = uh1[r1];
        let sl = &sg1[r1 * m..r1 * m + m];
        let sins = sl[below];
        let mut beta = D * (em + v) + sins * c.vals1[x1];
        for j in 0..m - 1 {
            beta += ev[j] * if co[j].pos >= i { sl[j + 1] } else { sl[j] };
        }
        let a0 = alpha * D2;
        big_r += cell2(pa, pb, a0, rd, beta, sins);
        cnt.inner += 1;
        {
            let (cc, qq) = cell_cases(pa, pb, a0, rd, beta, sins, { let mut s0 = 0i128; for j in 0..m { s0 += (if j == m - 1 { if tf || i == im { 0 } else { pm } } else if co[j].forg || co[j].pos == i { 0 } else if co[j].pos > i { sl[j + 1] } else { sl[j] }) * co[j].dl; } s0 });
            cnt.cases[cc] += 1;
            if cc == 0 && seen {
                nonmono = true;
            }
            if cc > 0 {
                seen = true;
            }
            cnt.cases[qq] += 1;
        }
        coef[m - 1] = if tf || i == im { 0 } else { pm };
        for j in 0..m - 1 {
            coef[j] = if co[j].forg {
                0
            } else if co[j].pos > i {
                sl[j + 1]
            } else if co[j].pos == i {
                0
            } else {
                sl[j]
            };
        }
        let mut sm = 0i128;
        for j in 0..m {
            sm += coef[j] * co[j].dl;
        }
        if sm > 0 {
            let q = chord(pa, pb, a0, rd, beta, sins, sm);
            cnt.chords += 1;
            for j in 0..m {
                acc[j] += coef[j] * q;
            }
        }
        // stop count of the coordinates in their own cell (section 5.4)
        let gap = beta - sins * pb - (a0 + rd * pb);
        let mg = if gap > 0 { gap / D } else { 0 };
        let mut lc = 0i128;
        for j in 0..m {
            if !co[j].forg && co[j].pos == i {
                lam[j] += ((lc + 1) * D).min(mg) - (lc * D).min(mg);
                lc += 1;
            }
        }
    }
    if !tf {
        // section 5.5: the tail (g_m, 1]
        let mut cmt = [0usize; 8];
        for j in 0..m {
            cmt[j] = co[j].cm;
        }
        let cr = ms1.rank(&cmt[..m]);
        cnt.lookups += 1;
        let slc = &sg1[cr * m..cr * m + m];
        let mut uu = D * uh1[cr];
        for j in 0..m {
            uu += ev[j] * slc[j];
        }
        let mut sm = 0i128;
        for j in 0..m {
            coef[j] = slc[j];
            sm += coef[j] * co[j].dl;
        }
        let a0 = (1 + m as i128) * D2;
        let mut jt = im;
        while jt < c.l {
            let x = c.pv[jt];
            if a0 + rd * x >= D * (c.et[c.pts[jt]] + r) + uu + sm {
                break;
            }
            jt += 1;
        }
        for i in im + 1..=jt {
            let (pa, pb) = (c.pv[i - 1], c.pv[i]);
            let s = r * c.et1[c.pts[i]];
            let beta = D * c.et[c.pts[i]] + uu + s * pb;
            big_r += cell2(pa, pb, a0, rd, beta, s);
            cnt.tailc += 1;
            {
                let (cc, qq) = cell_cases(pa, pb, a0, rd, beta, s, sm);
                cnt.cases[cc] += 1;
                if cc == 0 && seen {
                    nonmono = true;
                }
                if cc > 0 {
                    seen = true;
                }
                cnt.cases[qq] += 1;
            }
            if sm > 0 {
                let q = chord(pa, pb, a0, rd, beta, s, sm);
                cnt.chords += 1;
                for j in 0..m {
                    acc[j] += coef[j] * q;
                }
            }
        }
        let xt = c.pv[jt];
        if xt < D {
            big_r += 2 * D2 * c.etm1[c.pts[jt]] / (r + 1) + 2 * (D - xt) * uu;
            cnt.exact_tail += 1;
            for j in 0..m {
                acc[j] += coef[j] * (D - xt);
            }
        }
    }
    if nonmono {
        cnt.nonmono += 1;
    }
    let uh = big_r.div_euclid(2 * D2);
    let mut mu = [0i128; 8];
    for j in 0..m {
        mu[j] = if co[j].forg { 0 } else { lam[j] + acc[j] / D };
        assert!(mu[j] >= 0);
    }
    (uh, mu)
}

// Section 6: forgotten coordinates; min over the boxes of G_{t+1} above the top of G_t.
fn eval_state(c: &Ctx, ms1: &Ms, uh1: &[i128], sg1: &[i128], k: &[usize], newp: &[Co], cnt: &mut Cnt) -> (i128, [i128; 8], usize) {
    let m = c.m;
    let mut co = [Co::default(); 8];
    for j in 0..m {
        co[j] = co_local(c, k[j]);
    }
    let base = state(c, ms1, uh1, sg1, &co[..m], cnt);
    let f = (0..m).filter(|&j| co[j].forg).count();
    if f == 0 || newp.is_empty() {
        return (base.0, base.1, 0);
    }
    let nc = newp.len() + 1;
    let mut ch = vec![0usize; f];
    let (mut t0, mut mu) = base;
    let mut evals = 0;
    let mut first = true;
    loop {
        let mut p = f;
        while !first {
            if p == 0 {
                return (t0, mu, evals);
            }
            p -= 1;
            if ch[p] + 1 < nc {
                ch[p] += 1;
                for q in p + 1..f {
                    ch[q] = ch[p];
                }
                break;
            }
        }
        first = false;
        if ch.iter().all(|&x| x == nc - 1) {
            continue;
        }
        let mut co2 = co;
        for (q, &x) in ch.iter().enumerate() {
            if x < nc - 1 {
                co2[m - f + q] = newp[x];
            }
        }
        let (a, b) = state(c, ms1, uh1, sg1, &co2[..m], cnt);
        evals += 1;
        t0 = t0.min(a);
        for j in 0..m {
            mu[j] = mu[j].min(b[j]);
        }
    }
}

// Regression check of section 6, independent of eval_state: for every state of Y_t and every record
// list of section 6 (all nondecreasing f-tuples over the new points and J, enumerated here directly),
// uh_t(k) <= T0 and sg_t(k)_l <= mu_l (sg_t(k)_l = 0 for the forgotten l). Returns (lists, failures).
fn check_lists(g: &GridQ, e: &[Vec<i128>], m: usize, t: usize, uh1: &[i128], sg1: &[i128], uh: &[i128], sg: &[i128]) -> (u64, u64) {
    let c = ctx_new(g, e, m, t);
    let ms = Ms::new(m, c.nt0 + 2);
    let ms1 = Ms::new(m, g.nt(t + 1) + 2);
    let (s0, c0) = g.window(t);
    let (s1, c1) = g.window(t + 1);
    let mut newp = Vec::new();
    for gj in s1..s1 + c1 {
        if gj >= s0 + c0 {
            let pos = (1..=c.l).find(|&i| c.pts[i] == gj).unwrap();
            newp.push(Co { pos, val: g.gpt[gj], dl: 0, cm: gj - s1, gi: gj, forg: false });
        }
    }
    let nc = newp.len() + 1;
    let res: Vec<(u64, u64)> = (0..uh.len())
        .into_par_iter()
        .map(|idx| {
            let mut k = [0usize; 8];
            ms.unrank(idx, &mut k[..m]);
            let mut co = [Co::default(); 8];
            for j in 0..m {
                co[j] = co_local(&c, k[j]);
            }
            let f = (0..m).filter(|&j| co[j].forg).count();
            let mut tuples: Vec<Vec<usize>> = vec![vec![]];
            for _ in 0..f {
                let mut next = Vec::new();
                for tu in &tuples {
                    let lo = *tu.last().unwrap_or(&0);
                    for x in lo..nc {
                        let mut v = tu.clone();
                        v.push(x);
                        next.push(v);
                    }
                }
                tuples = next;
            }
            let (mut lists, mut bad) = (0u64, 0u64);
            for tu in &tuples {
                let mut co2 = co;
                for (q, &x) in tu.iter().enumerate() {
                    if x < nc - 1 {
                        co2[m - f + q] = newp[x];
                    }
                }
                let mut cnt = Cnt::default();
                let (a, b) = state(&c, &ms1, uh1, sg1, &co2[..m], &mut cnt);
                lists += 1;
                let mut ok = uh[idx] <= a;
                for j in 0..m {
                    let s = sg[idx * m + j];
                    ok &= if co[j].forg { s == 0 } else { s <= b[j] };
                }
                if !ok {
                    bad += 1;
                    if bad == 1 {
                        println!("check_lists failure t={} k={:?} tuple={:?} uh={} T0={} sg={:?} mu={:?}", t, &k[..m], tu, uh[idx], a, &sg[idx * m..idx * m + m], &b[..m]);
                    }
                }
            }
            (lists, bad)
        })
        .collect();
    res.iter().fold((0, 0), |acc, r| (acc.0 + r.0, acc.1 + r.1))
}

fn step(g: &GridQ, e: &[Vec<i128>], m: usize, t: usize, uh1: &[i128], sg1: &[i128]) -> (Vec<i128>, Vec<i128>, Cnt, usize) {
    let c = ctx_new(g, e, m, t);
    let ms = Ms::new(m, c.nt0 + 2);
    let ms1 = Ms::new(m, g.nt(t + 1) + 2);
    let ns = ms.count(c.nt0);
    let (s0, c0) = g.window(t);
    let (s1, c1) = g.window(t + 1);
    let mut newp = Vec::new();
    for loc in 0..c1 {
        let gj = s1 + loc;
        if gj >= s0 + c0 {
            let pos = (1..=c.l).find(|&i| c.pts[i] == gj).unwrap();
            newp.push(Co { pos, val: g.gpt[gj], dl: 0, cm: loc, gi: gj, forg: false });
        }
    }
    let res: Vec<(i128, [i128; 8], usize, Cnt)> = (0..ns)
        .into_par_iter()
        .map(|idx| {
            let mut k = [0usize; 8];
            ms.unrank(idx, &mut k[..m]);
            let mut cnt = Cnt::default();
            let (a, b, ev) = eval_state(&c, &ms1, uh1, sg1, &k[..m], &newp, &mut cnt);
            (a, b, ev, cnt)
        })
        .collect();
    let mut tot = Cnt::default();
    let mut evals = 0;
    let mut uh = vec![0i128; ns];
    let mut sl = vec![0i128; ns * m];
    for idx in 0..ns {
        let (a, b, ev, cn) = res[idx];
        uh[idx] = a;
        for j in 0..m {
            sl[idx * m + j] = b[j];
        }
        evals += ev;
        tot.inner += cn.inner;
        tot.tailc += cn.tailc;
        tot.chords += cn.chords;
        tot.lookups += cn.lookups;
        tot.exact_tail += cn.exact_tail;
        tot.nonmono += cn.nonmono;
        for z in 0..7 {
            tot.cases[z] += cn.cases[z];
        }
    }
    (uh, sl, tot, evals)
}

// u_t at a memory y (values in [0, 1], sorted), from the integer tables, in f64 (for the check only)
fn u_at(vals: &[f64], m: usize, ms: &Ms, uh: &[i128], sl: &[i128], y: &[f64]) -> f64 {
    let nt = vals.len();
    let mut kk = [0usize; 8];
    for j in 0..m {
        kk[j] = vals.partition_point(|&v| v < y[j]).min(nt - 1);
    }
    let r0 = ms.rank(&kk[..m]);
    let df = D as f64;
    let mut u = uh[r0] as f64 / df;
    for j in 0..m {
        if kk[j] < nt - 1 {
            u += sl[r0 * m + j] as f64 / df * (vals[kk[j]] - y[j]);
        }
    }
    u
}

fn gl16() -> ([f64; 16], [f64; 16]) {
    let p = [0.0950125098376374, 0.2816035507792589, 0.4580167776572274, 0.6178762444026438, 0.7554044083550030, 0.8656312023878318, 0.9445750230732326, 0.9894009349916499];
    let w = [0.1894506104550685, 0.1826034150449236, 0.1691565193950025, 0.1495959888165767, 0.1246289712555339, 0.0951585116824928, 0.0622535239386479, 0.0271524594117541];
    let mut xs = [0.0; 16];
    let mut ws = [0.0; 16];
    for i in 0..8 {
        xs[2 * i] = -p[i];
        xs[2 * i + 1] = p[i];
        ws[2 * i] = w[i];
        ws[2 * i + 1] = w[i];
    }
    (xs, ws)
}

// T_t[u_{t+1}](y) by Gauss-Legendre quadrature on the pieces between grid points and memory values
fn t_at(g: &GridQ, m: usize, t: usize, ms1: &Ms, uh1: &[i128], sl1: &[i128], y: &[f64], nsub: usize) -> f64 {
    let df = D as f64;
    let ri = (g.n - t) as i32;
    let r = ri as f64;
    let vals1: Vec<f64> = (0..g.nt(t + 1)).map(|k| g.gpt[g.global(t + 1, k)] as f64 / df).collect();
    let mut br: Vec<f64> = vec![0.0, 1.0];
    for tt in [t, t + 1] {
        for k in 0..g.nt(tt) {
            br.push(g.gpt[g.global(tt, k)] as f64 / df);
        }
    }
    br.extend_from_slice(y);
    br.sort_by(|a, b| a.partial_cmp(b).unwrap());
    br.dedup();
    let (xg, wg) = gl16();
    let f = |x: f64| -> f64 {
        let cnt = y.iter().filter(|&&v| v < x).count() as f64;
        let s = 1.0 + cnt + r * x;
        let mut ins = [0.0f64; 8];
        for kq in 0..m {
            let lo = if kq == 0 { 0.0 } else { y[kq - 1] };
            ins[kq] = lo.max(y[kq].min(x));
        }
        let drop = y[m - 1].max(x);
        s.min((1.0 - drop).powi(ri) + u_at(&vals1, m, ms1, uh1, sl1, &ins[..m]))
    };
    let mut tot = 0.0;
    for w in br.windows(2) {
        let (a, b) = (w[0], w[1]);
        if b <= a {
            continue;
        }
        for q in 0..nsub {
            let aa = a + (b - a) * q as f64 / nsub as f64;
            let bb = a + (b - a) * (q + 1) as f64 / nsub as f64;
            let (cc, h) = (0.5 * (aa + bb), 0.5 * (bb - aa));
            for i in 0..16 {
                tot += h * wg[i] * f(cc + h * xg[i]);
            }
        }
    }
    tot
}

// One table of option emitall: the number of states, then uh sg_0 .. sg_{m-1} per state in rank order.
fn write_table(path: &str, uh: &[i128], sg: &[i128], m: usize) {
    use std::io::Write;
    let mut w = std::io::BufWriter::new(std::fs::File::create(path).unwrap());
    writeln!(w, "{}", uh.len()).unwrap();
    for idx in 0..uh.len() {
        let mut line = uh[idx].to_string();
        for j in 0..m {
            line.push(' ');
            line.push_str(&sg[idx * m + j].to_string());
        }
        writeln!(w, "{}", line).unwrap();
    }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let n: usize = a[1].parse().unwrap();
    let m: usize = a[2].parse().unwrap();
    let rho: f64 = a[3].parse().unwrap();
    let q: usize = a[4].parse().unwrap();
    let wmin: f64 = a[5].parse().unwrap();
    let wmax: f64 = a[6].parse().unwrap();
    let opt = |key: &str| -> Option<String> { a.iter().find_map(|x| x.strip_prefix(&format!("{}=", key)).map(|s| s.to_string())) };
    let kwin: Option<usize> = opt("kwin").map(|s| s.parse().unwrap());
    let mc: usize = opt("mc").map_or(0, |s| s.parse().unwrap());
    let edge = a.iter().any(|x| x == "edge");
    let nsub: usize = opt("nsub").map_or(32, |s| s.parse().unwrap());
    // emit=T:FILE writes the grid and the tables of times T + 1 and T (text, one state per line in rank
    // order: uh sg_0 .. sg_{m-1}); perstep prints, per step, t, start[t], states and shift corner evaluations.
    let emit: Option<(usize, String)> = opt("emit").map(|s| {
        let (a, b) = s.split_once(':').unwrap();
        (a.parse().unwrap(), b.to_string())
    });
    // emitall=DIR writes DIR/grid.txt (n m SH K J, then gpt[0..J-1], then start[1..n]) and, for every time
    // T = n, n - 1, ..., 1, DIR/table-T.txt (the number of states, then uh sg_0 .. sg_{m-1} per state in rank
    // order, as in emit).
    let emitall: Option<String> = opt("emitall");
    let perstep = a.iter().any(|x| x == "perstep");
    let checklists = a.iter().any(|x| x == "checklists");
    let (mut chk_lists, mut chk_bad) = (0u64, 0u64);
    let t_start = Instant::now();
    let g = GridQ::from_f64(n, rho, q, wmin, wmax, kwin);
    let e = penalty_tables(&g);
    println!("soq n={} m={} rho={} q={} wmin={} wmax={} K={} J={} SH={}", n, m, rho, q, wmin, wmax, g.kwin, g.jtop(), SH);
    // section 4: time n
    let ms = Ms::new(m, g.nt(n) + 2);
    let ns = ms.count(g.nt(n));
    let ntn = g.nt(n);
    let mut uh = vec![0i128; ns];
    let mut sg = vec![0i128; ns * m];
    let mut k = [0usize; 8];
    for idx in 0..ns {
        ms.unrank(idx, &mut k[..m]);
        let mut v = (1 + m as i128) * D;
        for j in 0..m {
            v -= g.gpt[g.global(n, k[j])];
            if k[j] < ntn - 1 {
                sg[idx * m + j] = D;
            }
        }
        uh[idx] = v;
    }
    if let Some(dir) = &emitall {
        use std::io::Write;
        std::fs::create_dir_all(dir).unwrap();
        let mut w = std::io::BufWriter::new(std::fs::File::create(format!("{}/grid.txt", dir)).unwrap());
        writeln!(w, "{} {} {} {} {}", n, m, SH, g.kwin, g.jtop()).unwrap();
        writeln!(w, "{}", g.gpt[..g.jtop()].iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ")).unwrap();
        writeln!(w, "{}", (1..=n).map(|tt| g.start[tt].to_string()).collect::<Vec<_>>().join(" ")).unwrap();
        write_table(&format!("{}/table-{}.txt", dir, n), &uh, &sg, m);
    }
    let mut state_steps: u64 = 0;
    let mut maxstates = 0usize;
    let mut tot = Cnt::default();
    let mut evals = 0usize;
    let mut maxsl: i128 = 0;
    let mut maxuh: i128 = 0;
    let (mut mc_n, mut mc_bad, mut worst) = (0usize, 0usize, f64::INFINITY);
    let mut worst_at = String::new();
    let mut seed: u64 = 0x9e3779b97f4a7c15;
    let mut rnd = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        (seed >> 11) as f64 / (1u64 << 53) as f64
    };
    for t in (1..n).rev() {
        let (u2, s2, cn, ev) = step(&g, &e, m, t, &uh, &sg);
        if checklists {
            let (l, b) = check_lists(&g, &e, m, t, &uh, &sg, &u2, &s2);
            chk_lists += l;
            chk_bad += b;
        }
        if perstep {
            println!("step t={} start={} states={} shift_evals={} min_uh={}", t, g.start[t], u2.len(), ev, u2.iter().min().unwrap());
        }
        if let Some((te, path)) = &emit {
            if *te == t {
                use std::io::Write;
                let mut w = std::io::BufWriter::new(std::fs::File::create(path).unwrap());
                writeln!(w, "# soq emit: n m SH K J T, then gpt[0..J-1], start[1..n], the table of time T+1 (count, then uh sg_0 .. sg_{{m-1}} per state in rank order), the table of time T").unwrap();
                writeln!(w, "{} {} {} {} {} {}", n, m, SH, g.kwin, g.jtop(), t).unwrap();
                writeln!(w, "{}", g.gpt[..g.jtop()].iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ")).unwrap();
                writeln!(w, "{}", (1..=n).map(|tt| g.start[tt].to_string()).collect::<Vec<_>>().join(" ")).unwrap();
                for (uu, ss) in [(&uh, &sg), (&u2, &s2)] {
                    writeln!(w, "{}", uu.len()).unwrap();
                    for idx in 0..uu.len() {
                        let mut line = uu[idx].to_string();
                        for j in 0..m {
                            line.push(' ');
                            line.push_str(&ss[idx * m + j].to_string());
                        }
                        writeln!(w, "{}", line).unwrap();
                    }
                }
                println!("emitted the tables of times {} and {} to {}", t + 1, t, path);
            }
        }
        if let Some(dir) = &emitall {
            write_table(&format!("{}/table-{}.txt", dir, t), &u2, &s2, m);
        }
        state_steps += u2.len() as u64;
        maxstates = maxstates.max(u2.len());
        tot.inner += cn.inner;
        tot.tailc += cn.tailc;
        tot.chords += cn.chords;
        tot.lookups += cn.lookups;
        tot.exact_tail += cn.exact_tail;
        tot.nonmono += cn.nonmono;
        for z in 0..7 {
            tot.cases[z] += cn.cases[z];
        }
        evals += ev;
        maxsl = maxsl.max(*s2.iter().max().unwrap());
        maxuh = maxuh.max(*u2.iter().max().unwrap());
        if mc > 0 && (t % (n / 7).max(1) == 0 || t == 1 || t == n - 1 || (g.start[t + 1] != g.start[t] && rnd() < 0.2)) {
            let ms0 = Ms::new(m, g.nt(t) + 2);
            let ms1 = Ms::new(m, g.nt(t + 1) + 2);
            let df = D as f64;
            let vals0: Vec<f64> = (0..g.nt(t)).map(|kk| g.gpt[g.global(t, kk)] as f64 / df).collect();
            let (s0, c0) = g.window(t);
            let lo = (g.gpt[s0] as f64 / df).ln() - 1.0;
            let hi = (g.gpt[s0 + c0.max(1) - 1] as f64 / df).ln() + 0.7;
            for _ in 0..mc {
                let mut y: Vec<f64> = (0..m).map(|_| (lo + (hi - lo) * rnd()).exp().min(1.0)).collect();
                if rnd() < 0.2 {
                    y[m - 1] = 1.0;
                }
                if edge && rnd() < 0.7 {
                    // coordinates at box corners, just inside, mid-box, at the box bottom, and 0
                    let fr = [0.0, 1e-12, 0.5, 1.0 - 1e-12, 1.0];
                    for j in 0..m {
                        let kq = ((rnd() * vals0.len() as f64) as usize).min(vals0.len() - 1);
                        let lower = if kq == 0 { 0.0 } else { vals0[kq - 1] };
                        let f = fr[((rnd() * 5.0) as usize).min(4)];
                        y[j] = vals0[kq] - f * (vals0[kq] - lower);
                    }
                    if rnd() < 0.3 {
                        let j = ((rnd() * m as f64) as usize).min(m - 1);
                        y[(j + 1) % m] = y[j];
                    }
                }
                y.sort_by(|a, b| a.partial_cmp(b).unwrap());
                let ut = u_at(&vals0, m, &ms0, &u2, &s2, &y);
                let tt = t_at(&g, m, t, &ms1, &uh, &sg, &y, nsub);
                let slack = tt - ut;
                mc_n += 1;
                if slack < worst {
                    worst = slack;
                    worst_at = format!("t={} y={:?} u={:.12} T={:.12}", t, y, ut, tt);
                }
                if slack < -1e-9 * tt.abs().max(1.0) {
                    mc_bad += 1;
                    if mc_bad <= 5 {
                        println!("MC violation t={} y={:?} u={} T={}", t, y, ut, tt);
                    }
                }
            }
        }
        if t % 100 == 0 || t <= 2 {
            eprintln!("t={} states={} top={:.9} [{:.1}s]", t, u2.len(), u2[u2.len() - 1] as f64 / D as f64, t_start.elapsed().as_secs_f64());
        }
        uh = u2;
        sg = s2;
    }
    let top = uh[uh.len() - 1];
    println!("state_steps={} max_states_per_step={}", state_steps, maxstates);
    println!("per state step: inner cells {:.3}, tail tangent cells {:.3}, chords {:.3}, table lookups {:.3}, exact tails {:.3}; shift corner evaluations {}", tot.inner as f64 / state_steps as f64, tot.tailc as f64 / state_steps as f64, tot.chords as f64 / state_steps as f64, tot.lookups as f64 / state_steps as f64, tot.exact_tail as f64 / state_steps as f64, evals);
    {
        let ss = state_steps as f64;
        let c = &tot.cases;
        println!("cell cases per state step: stop-only {:.3}, continuation-only {:.3}, crossing {:.3}; chord cases: zero {:.3}, full {:.3}, ramp {:.3}, no credited slope {:.3}; corner evaluations with a stop-only cell above a continuation cell: {}", c[0] as f64 / ss, c[1] as f64 / ss, c[2] as f64 / ss, c[3] as f64 / ss, c[4] as f64 / ss, c[5] as f64 / ss, c[6] as f64 / ss, tot.nonmono);
    }
    println!("max slope numerator {} (2^{:.2}), max value numerator {} (2^{:.2})", maxsl, (maxsl as f64).log2(), maxuh, (maxuh as f64).log2());
    if mc > 0 {
        println!("MC sub-solution check: {} samples, worst slack {:.3e}, violations {}", mc_n, worst, mc_bad);
        println!("MC worst sample: {}", worst_at);
    }
    if checklists {
        println!("record list check (section 6): {} lists, {} failures", chk_lists, chk_bad);
    }
    println!("uhat_1(1..1) = {} / 2^{}", top, SH);
    println!("value={:.9}", top as f64 / D as f64);
    println!("certified_gt_2={}", top > 2 * D);
    println!("time {:.2}s", t_start.elapsed().as_secs_f64());
}
