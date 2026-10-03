import Robbins.Cert.Grid

/-!
# The fixed-point evaluator of the certificate

The first-order certificate (values only, no slopes), sections 1 to 4 of its format (the data, the
states, the penalty tables, the tables), in natural numbers: from the grid data it computes the
tables `uhat_t` for `t = n, n - 1, ..., 1` and returns `uhat_1 (1, ..., 1)`, in units of
`1 / D`, `D = 2 ^ 40`.

Tables. A table of sorted `d`-tuples over the local indices `0, ..., a - 1` is a `Tab Nat d`:
`Tab α 0 = α`, `Tab α (d + 1) = List (Tab α d)`, the entry `b` of the outer list being the table
of the tuples whose top coordinate is `b` (a table over `0, ..., b`). Flattened, this is the rank
order of section 2 of the format.

One step (`step`, section 4 of the format) goes in five forward passes:

* `lines`: for every head `h` (a sorted `(m - 1)`-tuple of `G_{t+1}`) the list of
  `N (sort (h, x))` over the local points `x` of `G_{t+1}`;
* `selectTab`: the lines of the heads `map (k_1, ..., k_{m-1})` of `G_t`;
* `headRow`: per head of `G_t`, the values `Btilde (k_1, ..., k_m)` for every top coordinate
  `k_m`, with a cursor on the cells for `k_m` and a zipper for the crossing index;
* `headToTop`: the same values in rank order;
* `closeTab`: the min-closure of section 4.4.

The evaluator checks the data conditions of section 1 (and `start` nondecreasing, which makes the
local index `k < cnt_t` of `G_t` the cell `k + 1`); on data that fail them it returns `0`.
-/

namespace Robbins.Cert

/-- Tables of sorted `d`-tuples (see the module docstring). -/
def Tab (α : Type) : Nat → Type
  | 0 => α
  | d + 1 => List (Tab α d)

/-! ## List helpers -/

/-- `f` on the common prefix of `xs` and `ys`, then the rest of `xs`. -/
def zipLong {α β : Type} (f : α → β → α) : List α → List β → List α
  | x :: xs, y :: ys => f x y :: zipLong f xs ys
  | xs, [] => xs
  | [], _ :: _ => []

/-- Prepend the entries of `row` to the first lists of `acc`, starting new lists when `acc` runs
out. -/
def zipPrepend {α : Type} : List α → List (List α) → List (List α)
  | x :: xs, c :: cs => (x :: c) :: zipPrepend xs cs
  | x :: xs, [] => [x] :: zipPrepend xs []
  | [], cs => cs

/-- The columns of a triangle `[T_0, ..., T_{a-1}]`, `T_x` of length `x + 1`: column `j` is
`[T_j[j], T_{j+1}[j], ..., T_{a-1}[j]]`. -/
def triCols {α : Type} (l : List (List α)) : List (List α) :=
  l.foldr zipPrepend []

/-- `selWalk pos idx l`: the entries of `l` at the indices `idx` (nondecreasing, all at least
`pos`), where `l` is the original list with its first `pos` entries dropped. -/
def selWalk {α : Type} (dflt : α) : Nat → List Nat → List α → List α
  | _, [], _ => []
  | pos, i :: is, l =>
    let l' := l.drop (i - pos)
    l'.headD dflt :: selWalk dflt i is l'

/-- The entries of `l` at the nondecreasing indices `idx`. -/
def select {α : Type} (dflt : α) (idx : List Nat) (l : List α) : List α :=
  selWalk dflt 0 idx l

/-! ## Tables -/

/-- Entrywise map. -/
def Tab.map {α β : Type} (f : α → β) : (d : Nat) → Tab α d → Tab β d
  | 0, x => f x
  | d + 1, l => List.map (Tab.map f d) (l : List (Tab α d))

/-- Entrywise zip of two tables of the same shape. -/
def Tab.zipWith {α β γ : Type} (f : α → β → γ) : (d : Nat) → Tab α d → Tab β d → Tab γ d
  | 0, x, y => f x y
  | d + 1, xs, ys => List.zipWith (Tab.zipWith f d) (xs : List (Tab α d)) (ys : List (Tab β d))

/-- Flatten in rank order. -/
def Tab.flat : (d : Nat) → Tab Nat d → List Nat
  | 0, x => [x]
  | d + 1, l => (List.map (Tab.flat d) (l : List (Tab Nat d))).flatten

/-- `mapIdxFrom k f [x_0, x_1, ...] = [f k x_0, f (k + 1) x_1, ...]`. -/
def mapIdxFrom {α β : Type} (f : Nat → α → β) : Nat → List α → List β
  | _, [] => []
  | k, x :: xs => f k x :: mapIdxFrom f (k + 1) xs

/-- Entrywise map with the tuple of the entry (ascending coordinates appended to `pre`). -/
def Tab.mapTup {α β : Type} : (d : Nat) → (List Nat → α → β) → Tab α d → Tab β d
  | 0, f, x => f [] x
  | d + 1, f, l =>
    mapIdxFrom (fun j (tj : Tab α d) => Tab.mapTup d (fun κ x => f (κ ++ [j]) x) tj) 0
      (l : List (Tab α d))

/-- The table of the tuples over `0, ..., a - 1` with entry `base - sum_l v[k_l]`
(the values `v` as a list, at least `a` long). -/
def Tab.tabulate : (d : Nat) → Nat → List Nat → Nat → Tab Nat d
  | 0, base, _, _ => base
  | d + 1, base, v, a =>
    mapIdxFrom (fun j vj => Tab.tabulate d (base - vj) (v.take (j + 1)) (j + 1)) 0 (v.take a)

/-- Read the slices `j, j + 1, ..., j + k - 1` of a table from a flat rank-order list, with `f`
reading one slice over `0, ..., a - 1`; returns the slices and the rest. -/
def unflatLoop {β : Type} (f : Nat → List Nat → β × List Nat) : Nat → Nat → List Nat →
    List β × List Nat
  | 0, _, l => ([], l)
  | k + 1, j, l =>
    let p := f (j + 1) l
    let q := unflatLoop f k (j + 1) p.2
    (p.1 :: q.1, q.2)

/-- Read a table over `0, ..., a - 1` from a flat rank-order list; returns the table and the
rest of the list. -/
def Tab.unflat : (d : Nat) → Nat → List Nat → Tab Nat d × List Nat
  | 0, _, l => (l.headD 0, l.tail)
  | d + 1, a, l => unflatLoop (Tab.unflat d) a 0 l

/-- The min-closure combination of the slice `T_j` with the closed slice `C_{j-1}`: entries of
`T_j` that have a neighbour in `C_{j-1}` take the min. -/
def Tab.combine : (d : Nat) → Tab Nat d → Tab Nat d → Tab Nat d
  | 0, x, y => (min (x : Nat) (y : Nat) : Nat)
  | d + 1, xs, ys => zipLong (Tab.zipWith min d) (xs : List (Tab Nat d)) (ys : List (Tab Nat d))

/-- The closure of the slices `T_j, T_{j+1}, ...` given the closed slice before them. -/
def closeAux (d : Nat) (close : Tab Nat d → Tab Nat d) : Option (Tab Nat d) → List (Tab Nat d) →
    List (Tab Nat d)
  | _, [] => []
  | none, t :: ts =>
    let c := close t
    c :: closeAux d close (some c) ts
  | some p, t :: ts =>
    let c := close (Tab.combine d t p)
    c :: closeAux d close (some c) ts

/-- The min-closure of section 4.4: the entry at `k` is the min of `Btilde` over the sorted
tuples below `k`. -/
def closeTab : (d : Nat) → Tab Nat d → Tab Nat d
  | 0, x => x
  | d + 1, l => closeAux d (closeTab d) none (l : List (Tab Nat d))

/-- Collect a list of tables of the same shape into one table of lists; `tmpl` gives the shape. -/
def collect {α : Type} (d : Nat) (tmpl : Tab α d) (ts : List (Tab α d)) : Tab (List α) d :=
  ts.foldr (fun x acc => Tab.zipWith List.cons d x acc) (Tab.map (fun _ => []) d tmpl)

/-- Lines of a table `T` of `(d + 1)`-tuples over `0, ..., a - 1`: for every `d`-tuple `h`, the
list of `T (sort (h, x))` for `x = 0, ..., a - 1`. -/
def lines : (d : Nat) → Tab Nat (d + 1) → Tab (List Nat) d
  | 0, t => (t : List Nat)
  | d + 1, t =>
    let ts : List (Tab Nat (d + 1)) := t
    let cols : List (List (Tab Nat d)) := triCols (ts : List (List (Tab Nat d)))
    List.zipWith
      (fun (tj : Tab Nat (d + 1)) (col : List (Tab Nat d)) =>
        match col with
        | [] => Tab.map (fun _ => []) d (Tab.map (fun _ => 0) d (lines d tj))
        | diag :: above => Tab.zipWith (· ++ ·) d (lines d tj) (collect d diag above))
      ts cols

/-- The table of the tuples `T (f k_1, ..., f k_d)` over `0, ..., |f| - 1`, for a nondecreasing
`f` given as the list of its values. -/
def selectTab {α : Type} (dflt : α) : (d : Nat) → List Nat → Tab α d → Tab α d
  | 0, _, x => x
  | d + 1, f, l =>
    let rows := select (Tab.map (fun _ => dflt) d (Tab.tabulate d 0 [] 0)) f (l : List (Tab α d))
    mapIdxFrom (fun j (r : Tab α d) => selectTab dflt d (f.take (j + 1)) r) 0 rows

/-- From head-major lists (the list of the head `κ` over the top coordinates `b ≥ κ_top`) to rank
order: `act` holds the slices `H_j` (`j < b`) advanced to `b`. -/
def headToTopAux (d : Nat) : List (Tab (List Nat) d) → List (Tab (List Nat) d) →
    List (List (Tab Nat d))
  | _, [] => []
  | act, h :: hs =>
    let act' := act ++ [h]
    (act'.map (Tab.map (fun l => l.headD 0) d)) :: headToTopAux d (act'.map (Tab.map List.tail d)) hs

/-- From head-major lists to rank order: `H : Tab (List Nat) d` over `0, ..., a - 1` to the table
of `(d + 1)`-tuples. -/
def headToTop : (d : Nat) → Tab (List Nat) d → Tab Nat (d + 1)
  | 0, h => (h : List Nat)
  | d + 1, h => headToTopAux d [] (h : List (Tab (List Nat) d))

/-! ## One step -/

/-- A cell `(p_{i-1}, p_i]` of `P_t` with its data. -/
structure Cell where
  /-- The index `i`. -/
  i : Nat
  /-- `p_{i-1}`. -/
  pa : Nat
  /-- `p_i`. -/
  pb : Nat
  /-- `E_t (p_i)`. -/
  ep : Nat
  /-- `E_{t-1} (p_i)`. -/
  e1p : Nat
  /-- `(1 + m) D + r p_i`. -/
  mDrp : Nat
  /-- `2 (p_i - p_{i-1})`. -/
  h2 : Nat
  /-- `2 D (p_i - p_{i-1})`. -/
  hD2 : Nat
  /-- `r (p_i ^ 2 - p_{i-1} ^ 2)`. -/
  sq : Nat

/-- A cell with the data of one head. -/
structure HCell where
  /-- The cell. -/
  c : Cell
  /-- `alpha_i`. -/
  alpha : Nat
  /-- `alpha_i D + r p_i`. -/
  aDrp : Nat
  /-- `row (h, i)`. -/
  row : Nat
  /-- `Q (h, i)`. -/
  qb : Nat
  /-- `Sint_head (p_{i-1})`: `Sint` without the top coordinate. -/
  spa : Nat

/-- The cell integral (section 4.3 of the format), units `2 ^ -81`. -/
def jcellK (r a b alpha C : Nat) : Nat :=
  let S := 2 * D * alpha * (b - a) + r * (b * b - a * a)
  if alpha * D + r * b ≤ C then S
  else if C ≤ alpha * D + r * a then 2 * (b - a) * C
  else
    let F := alpha * D + r * b - C
    S - (F * F + r - 1) / r

/-- Condition (T) at `X`: `U + EX + r ≤ (1 + m) D + r X`. -/
def condTK (r m U EX X : Nat) : Bool :=
  U + EX + r ≤ (1 + m) * D + r * X

/-- The tail term: `floor (2 D E1X / (r + 1)) + 2 (D - X) U` if `X < D` and (T) holds, else `0`. -/
def tailTK (r m U X EX E1X : Nat) : Nat :=
  if X < D && condTK r m U EX X then 2 * D * E1X / (r + 1) + 2 * (D - X) * U else 0

/-- The test `Pos_i` of 4.3 at a head cell, for the top cell index `im`, `Em` and `U`. -/
def posAt (im Em U : Nat) (hc : HCell) : Bool :=
  if hc.c.i ≤ im then Em + hc.row ≤ hc.aDrp else hc.c.ep + U ≤ hc.c.mDrp

/-- Move the zipper left while the cell before it passes the test. -/
def goLeft (im Em U : Nat) : List HCell → List HCell → List HCell × List HCell
  | [], suf => ([], suf)
  | q :: qs, suf => if posAt im Em U q then goLeft im Em U qs (q :: suf) else (q :: qs, suf)

/-- Move the zipper right while the cell under it fails the test. -/
def goRight (im Em U : Nat) : List HCell → List HCell → List HCell × List HCell
  | pre, [] => (pre, [])
  | pre, r :: rs => if posAt im Em U r then (pre, r :: rs) else goRight im Em U (r :: pre) rs

/-- The crossing search: the zipper `(pre, suf)` (cells before the cursor reversed, cells from the
cursor on) moved to the least `c` with `Pos_c` (`suf = []` for `c = L + 1`). -/
def search (im Em U : Nat) (pre suf : List HCell) : List HCell × List HCell :=
  match suf with
  | r :: _ => if posAt im Em U r then goLeft im Em U pre suf else goRight im Em U pre suf
  | [] => goLeft im Em U pre suf

/-- `R (k)` of 4.3 for the state with top cell `top` (`im`, `g_m`, `E_m`, `U`, `Q (h, im)`,
`E_{t-1} (g_m)`), the zipper suffix `suf` at the crossing, and `spL = Sint_head (D)`. -/
def stateR (r m : Nat) (top : HCell) (spL : Nat) (suf : List HCell) : Nat :=
  let im := top.c.i
  let gm := top.c.pb
  let Em := top.c.ep
  let U := top.row
  match suf with
  | [] => spL + 2 * D * (D - gm)
  | hc :: rest =>
    if hc.c.i ≤ im then
      hc.spa + jcellK r hc.c.pa hc.c.pb hc.alpha (Em + hc.row) + 2 * Em * (gm - hc.c.pb) +
        (top.qb - hc.qb) + tailTK r m U gm Em top.c.e1p
    else
      let base := hc.spa + 2 * D * (hc.c.pa - gm) + jcellK r hc.c.pa hc.c.pb (1 + m) (hc.c.ep + U)
      if hc.c.pb == D || condTK r m U hc.c.ep hc.c.pb then
        base + tailTK r m U hc.c.pb hc.c.ep hc.c.e1p
      else
        match rest with
        | [] => base
        | nx :: _ => base + nx.c.h2 * (nx.c.ep + U) + tailTK r m U nx.c.pb nx.c.ep nx.c.e1p

/-- The head cells of one head: `alpha_i = 1 + #{l : pos κ_l ≤ i - 1}` with `pos k = k + 1`
(`κ` the head's points below the point `1`), `row`, the prefix sums `Q` and `Sint_head`.
Returns the cells and `Sint_head (D)`. -/
def headCells (r : Nat) (κ : List Nat) : List Cell → List Nat → Nat → Nat → List HCell × Nat
  | [], _, _, sp => ([], sp)
  | c :: cs, rows, q, sp =>
    let al := 1 + (κ.filter (fun k => k + 2 ≤ c.i)).length
    let rw := rows.headD 0
    let q' := q + c.h2 * rw
    let hc : HCell := ⟨c, al, al * D + r * c.pb, rw, q', sp⟩
    let p := headCells r κ cs rows.tail q' (sp + al * c.hD2 + c.sq)
    (hc :: p.1, p.2)

/-- The values `Btilde (κ, b)` for the top cells `tops` (in increasing order), the zipper moving
from state to state. -/
def headStates (r m spL : Nat) : List HCell → List HCell → List HCell → List Nat
  | [], _, _ => []
  | top :: tops, pre, suf =>
    let z := search top.c.i top.c.ep top.row pre suf
    (stateR r m top spL z.2 / 2199023255552) :: headStates r m spL tops z.1 z.2

/-- The per-step data computed once. -/
structure StepData where
  /-- `r = n - t`. -/
  r : Nat
  /-- The cells of `P_t`. -/
  cells : List Cell
  /-- `nxt_i = ceil_{t+1} (pts[i])`. -/
  nxt : List Nat
  /-- `map k = ceil_{t+1} (global_t k)` for the local points `k` of `G_t`. -/
  mp : List Nat
  /-- `cnt_t`. -/
  cnt : Nat

/-- A placeholder head cell. -/
def HCell.dflt : HCell := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩, 0, 0, 0, 0, 0⟩

/-- One head: its cells, then its states `b = κ_top, ..., cnt_t`. -/
def headRow (m : Nat) (sd : StepData) (κ : List Nat) (line : List Nat) : List Nat :=
  let rows := select 0 sd.nxt line
  let hp := headCells sd.r (κ.filter (· < sd.cnt)) sd.cells rows 0 0
  let hcs := hp.1
  let top := κ.getLastD 0
  -- top cells: cells top + 1, ..., cnt (local points top, ..., cnt - 1), then cell L (the point 1)
  let last := hcs.getLastD HCell.dflt
  let tops := if top < sd.cnt then (hcs.drop top).take (sd.cnt - top) ++ [last] else [last]
  headStates sd.r m hp.2 tops (hcs.take top).reverse (hcs.drop top)

/-- The sorted union of `[s, s + c)` and `[s1, s1 + c1)` (for `s ≤ s1`, `s + c ≤ s1 + c1`). -/
def unionWin (w w1 : Win) : List Nat :=
  let e := w.s + w.cnt
  let lo := max w1.s e
  List.range' w.s w.cnt ++ List.range' lo (w1.s + w1.cnt - lo)

/-- The step data at time `t` (`r = n - t`), windows `w` (time `t`) and `w1` (time `t + 1`). -/
def stepData (m J r : Nat) (w w1 : Win) (gptD Et Etm1 : List Nat) : StepData :=
  let pts := unionWin w w1 ++ [J]
  let pv := select 0 pts gptD
  let ep := select 0 pts Et
  let e1p := select 0 pts Etm1
  let mk := fun (i : Nat) (x : (Nat × Nat) × (Nat × Nat)) =>
    let pa := x.1.1
    let pb := x.1.2
    (⟨i, pa, pb, x.2.1, x.2.2, (1 + m) * D + r * pb, 2 * (pb - pa), 2 * D * (pb - pa),
      r * (pb * pb - pa * pa)⟩ : Cell)
  let cells := mapIdxFrom mk 1 (List.zip (List.zip (0 :: pv) pv) (List.zip ep e1p))
  let nxt := pts.map (ceilLocal J w1)
  let mp := (List.range' w.s w.cnt).map (ceilLocal J w1) ++ [ceilLocal J w1 J]
  ⟨r, cells, nxt, mp, w.cnt⟩

/-- One step `t < n` for memory size `m = d + 1`: the table `uhat_t` from `N = uhat_{t+1}`. -/
def step (d J r : Nat) (w w1 : Win) (gptD Et Etm1 : List Nat) (N : Tab Nat (d + 1)) :
    Tab Nat (d + 1) :=
  let sd := stepData (d + 1) J r w w1 gptD Et Etm1
  let sel := selectTab [] d sd.mp (lines d N)
  closeTab (d + 1) (headToTop d (Tab.mapTup d (fun κ line => headRow (d + 1) sd κ line) sel))

/-- `E_{t-1}` from `E_t`: `floor (E_t[j] (D - gpt[j]) / D)`. -/
def nextE (gptD Et : List Nat) : List Nat :=
  List.zipWith (fun e p => e * (D - p) / D) Et gptD

/-- Run the steps `t = t0 - 1, ..., t1`, given the windows `[w_{t0}, w_{t0 - 1}, ..., w_{t1}]`,
from `N = uhat_{t0}`, `E = E_{t0}` and `E1 = E_{t0 - 1}`. Returns `uhat_{t1}` and `E_{t1}`. -/
def runSteps (d n J : Nat) (gptD : List Nat) : Nat → List Win → Tab Nat (d + 1) → List Nat →
    List Nat → Tab Nat (d + 1) × List Nat
  | _, [], N, E, _ => (N, E)
  | _, [_], N, E, _ => (N, E)
  | t0, w1 :: w :: ws, N, _, E1 =>
    let E2 := nextE gptD E1
    let N' := step d J (n - (t0 - 1)) w w1 gptD E1 E2 N
    runSteps d n J gptD (t0 - 1) (w :: ws) N' E1 E2

/-- The table at time `n`: `uhat_n (k) = (1 + m) D - sum_l gpt[global k_l]`. -/
def lastTab (m : Nat) (gptD : List Nat) (w : Win) : Tab Nat m :=
  Tab.tabulate m ((1 + m) * D) ((gptD.drop w.s).take w.cnt ++ [D]) (w.cnt + 1)

/-- The windows of the times `t0, t0 - 1, ..., t1` (`1 ≤ t1 ≤ t0 ≤ n`). -/
def Grid.winsDown (g : Grid) (t0 t1 : Nat) : List Win :=
  ((g.start.map g.win |>.drop (t1 - 1)).take (t0 - t1 + 1)).reverse

/-- The evaluator for `m = d + 1`: `uhat_1 (cnt_1, ..., cnt_1)`. -/
def evalD (g : Grid) (d : Nat) : Nat :=
  let gptD := g.gpt ++ [D]
  let ws := g.winsDown g.n 1
  let E := List.replicate (g.gpt.length + 1) D
  let res := runSteps d g.n g.gpt.length gptD g.n ws (lastTab (d + 1) gptD (ws.headD ⟨0, 0⟩)) E
    (nextE gptD E)
  (Tab.flat (d + 1) res.1).getLastD 0

/-- The evaluator: `uhat_1 (cnt_1, ..., cnt_1)` in units of `1 / D`, or `0` on data that fail
`Grid.ok`. -/
def eval (g : Grid) : Nat :=
  if g.ok then
    match g.m with
    | 0 => 0
    | d + 1 => evalD g d
  else 0

/-- From time `n` down to `t1`, `m = d + 1`: `uhat_{t1}` (flat, rank order) and `E_{t1}`. -/
def fromTop (g : Grid) (d t1 : Nat) : List Nat × List Nat :=
  let gptD := g.gpt ++ [D]
  let ws := g.winsDown g.n t1
  let E := List.replicate (g.gpt.length + 1) D
  let res := runSteps d g.n g.gpt.length gptD g.n ws (lastTab (d + 1) gptD (ws.headD ⟨0, 0⟩)) E
    (nextE gptD E)
  (Tab.flat (d + 1) res.1, res.2)

/-- A block between checkpoints, `m = d + 1`: from `uhat_{t0}` (flat, rank order) and `E_{t0}` to
`uhat_{t1}` (flat) and `E_{t1}`. -/
def block (g : Grid) (d t0 t1 : Nat) (U0 E0 : List Nat) : List Nat × List Nat :=
  let gptD := g.gpt ++ [D]
  let ws := g.winsDown t0 t1
  let N0 := (Tab.unflat (d + 1) ((ws.headD ⟨0, 0⟩).cnt + 1) U0).1
  let res := runSteps d g.n g.gpt.length gptD t0 ws N0 E0 (nextE gptD E0)
  (Tab.flat (d + 1) res.1, res.2)

end Robbins.Cert
