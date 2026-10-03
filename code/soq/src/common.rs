// The rank order of sorted tuples and the geometric grid with sliding windows (Section 5.1 of the
// paper, in f64; the grid integers are data of the certificate).

pub struct Ms {
    pub m: usize,
    binom: Vec<Vec<usize>>,
}

impl Ms {
    // ranks of sorted m-tuples over an alphabet of at most amax letters
    pub fn new(m: usize, amax: usize) -> Ms {
        let nmax = amax + m + 2;
        let mut b = vec![vec![0usize; m + 2]; nmax + 1];
        for n in 0..=nmax {
            b[n][0] = 1;
            for k in 1..=(m + 1).min(n) {
                b[n][k] = b[n - 1][k - 1] + if k <= n - 1 { b[n - 1][k] } else { 0 };
            }
        }
        Ms { m, binom: b }
    }
    pub fn count(&self, a: usize) -> usize {
        if self.m == 0 {
            return 1;
        }
        self.binom[a + self.m - 1][self.m]
    }
    #[inline]
    pub fn rank(&self, t: &[usize]) -> usize {
        let mut r = 0usize;
        for j in 0..self.m {
            r += self.binom[t[j] + j][j + 1];
        }
        r
    }
    pub fn unrank(&self, mut r: usize, t: &mut [usize]) {
        for j in (0..self.m).rev() {
            let mut c = j;
            while self.binom[c + 1][j + 1] <= r {
                c += 1;
            }
            r -= self.binom[c][j + 1];
            t[j] = c - j;
        }
    }
}

// Global grid gam[j] = wmin rho^j / n (< 1), the point 1 at index J = gam.len().
// Window at time t: global indices start[t] .. start[t] + kwin (capped at J), plus J.
pub struct Grid {
    pub n: usize,
    pub kwin: usize,
    pub gam: Vec<f64>,
    pub start: Vec<usize>,
}

impl Grid {
    pub fn new(n: usize, rho: f64, q: usize, wmin: f64, wmax: f64, kwin: Option<usize>) -> Grid {
        let kwin = kwin.unwrap_or(((wmax / wmin).ln() / rho.ln()).floor() as usize + 1);
        let mut gam = Vec::new();
        let mut j = 0i32;
        loop {
            let v = wmin * (j as f64 * rho.ln()).exp() / n as f64;
            if v >= 1.0 {
                break;
            }
            gam.push(v);
            j += 1;
        }
        let mut start = vec![0usize; n + 2];
        for t in 1..=n {
            let s = n - t + 1;
            let b = ((n as f64 / s as f64).ln() / (q as f64 * rho.ln()) + 1e-12).floor() as usize;
            start[t] = q * b;
        }
        Grid { n, kwin, gam, start }
    }
    pub fn jtop(&self) -> usize {
        self.gam.len()
    }
    pub fn val(&self, j: usize) -> f64 {
        if j >= self.gam.len() { 1.0 } else { self.gam[j] }
    }
    // (s, cnt): finite points of G_t are global s..s+cnt
    pub fn window(&self, t: usize) -> (usize, usize) {
        let s = self.start[t].min(self.jtop());
        let e = (self.start[t] + self.kwin).min(self.jtop());
        (s, e - s)
    }
    pub fn nt(&self, t: usize) -> usize {
        self.window(t).1 + 1
    }
    pub fn global(&self, t: usize, k: usize) -> usize {
        let (s, c) = self.window(t);
        if k < c { s + k } else { self.jtop() }
    }
    // local index in G_t of ceil_t(global point j)
    pub fn ceil_local(&self, t: usize, j: usize) -> usize {
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
