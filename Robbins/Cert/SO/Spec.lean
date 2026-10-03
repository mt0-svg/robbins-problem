import Robbins.Cert.Spec

/-!
# The specification of the second-order evaluator

The second-order certificate of Section 4 and Appendix B of the paper, as functions of the abstract tables of time `t + 1`
(`N` the values, `Sg` the slopes, read at sorted tuples of local indices of `G_{t+1}`) and of a
list of records, with no data structure. The denominator `D` is a parameter (`2 ^ 36` in the
run of the paper); the windows, the cells of `P_t`, `pos`, `map` and `nxt` are those
of Robbins/Cert/Spec.lean (they do not depend on `D`).

* `pt D g j`, `cp D g t i`: the points over `D` (`D` for the point `1`);
* `Epen D z r`: the penalty `E_{n-r}` at the point `z` (section 3);
* `cell2`, `pos2`, `chord`: section 5.1 and 5.2;
* `Rec`, `locRec`, `newPts`, `newRec`, `recList`: the records of section 5.0 and the record lists of
  section 6 (`ValidChoice`: a nondecreasing choice of new points or `J`);
* `bound`: `(T0, mu)` of one record list, sections 5.3 to 5.5.

All arithmetic of section 5 is over `ℤ`; `/` on `ℤ` is the floor for a positive divisor.
Robbins/Cert/SO/Sound.lean states the soundness of tables bounded by `bound`.

The comments of Robbins/Cert/SO number the parts of this specification and of its soundness:
1 the data, 2 the states and tables, 3 the penalty tables, 4 time `n`, 5 the bound of one list of
records (5.0 the records, 5.1 and 5.2 the cells and chords, 5.3 to 5.5 the bound), 6 the tables of
time `t < n`; 8.1 the grid facts (Lemma 4.1 of the paper), 8.2 and 8.3 the pointwise bounds in a cell
and in the tail (Lemmas 4.5 and 4.6), 8.4 the scalar lemma (Lemma 4.4), 8.5 the integral lemmas
(Lemma B.2), 8.6 the bound of one list (Proposition 4.7), 8.7 (R_t) and (R_n) (Theorem 4.3). The
first-order certificate, with values only, has the same parts 1 to 4 (its format).
-/

namespace Robbins.Cert.SO

open Robbins.Cert

section Grid

variable (D : ℕ) (g : Grid)

/-- The value (over `D`) of the global index `j`: `gpt[j]` for `j < J`, `D` (the point `1`) for
`j ≥ J`. -/
def pt (j : ℕ) : ℕ := if j < g.J then g.gpt.getD j 0 else D

/-- The endpoint `p_i` of the cells of `P_t` (over `D`), `p_0 = 0`. -/
def cp (t i : ℕ) : ℕ := if i = 0 then 0 else pt D g ((g.cellPts t).getD (i - 1) 0)

/-- The data conditions of section 1: `1 ≤ m`, `2 ≤ n`, `gpt` strictly increasing in `(0, D)`,
`n` start values, nondecreasing, and `cnt_t ≥ 1` for `t = 1, ..., n`. -/
def ok : Bool :=
  1 ≤ g.m && 2 ≤ g.n && strictInc 0 g.gpt && g.gpt.all (· < D) && g.start.length == g.n &&
    nondec 0 g.start && (List.range g.n).all fun t => 1 ≤ g.cnt (t + 1)

/-- `ceil_t` on values: the least local index `k ≤ cnt_t` of `G_t` with `y D ≤ pt (glob t k)`, or
`cnt_t` if there is none. -/
noncomputable def ceilR (t : ℕ) (y : ℝ) : ℕ := by
  classical
  exact if h : ∃ k, k ≤ g.cnt t ∧ y * D ≤ pt D g (g.glob t k) then Nat.find h else g.cnt t

end Grid

/-- The penalty of section 3: `Epen D z 0 = D`, `Epen D z (r + 1) = floor (Epen D z r (D - z) / D)`,
so `E_t[j] = Epen D (pt j) (n - t)`. -/
def Epen (D z : ℕ) : ℕ → ℕ
  | 0 => D
  | r + 1 => Epen D z r * (D - z) / D

/-! ## Cell integral and chord (section 5.1, 5.2) -/

/-- `2 int over [Pa, Pb] of min (a0 + a1 X, b0 - b1 X) dX`, rounded down (section 5.1). -/
def cell2 (Pa Pb a0 a1 b0 b1 : ℤ) : ℤ :=
  let k := a1 + b1
  let da := a0 - b0 + k * Pa
  let db := da + k * (Pb - Pa)
  let IA := fun x0 x1 : ℤ => 2 * a0 * (x1 - x0) + a1 * (x1 * x1 - x0 * x0)
  let IB := fun x0 x1 : ℤ => 2 * b0 * (x1 - x0) - b1 * (x1 * x1 - x0 * x0)
  if db ≤ 0 then IA Pa Pb
  else if 0 ≤ da then IB Pa Pb
  else
    let Z := Pa + (-da) / k
    IA Pa Z + IB Z Pb - 2 * k

/-- The lower and upper bounds of `2 int over [Pa, Pb] of max (0, da + k (X - Pa) - c) dX`
(section 5.2). -/
def pos2 (Pa Pb da k c : ℤ) : ℤ × ℤ :=
  let h := Pb - Pa
  let ac := da - c
  let bc := ac + k * h
  if bc ≤ 0 then (0, 0)
  else if 0 ≤ ac then ((ac + bc) * h, (ac + bc) * h)
  else
    let Zc := Pa + (-ac) / k
    let dz := ac + k * (Zc - Pa)
    ((dz + k + bc) * (Pb - Zc - 1), (dz + bc) * (Pb - Zc) + 2 * k)

/-- A lower bound of `int over [Pa, Pb] of min (1, max (0, Delta X) / S) dX`,
`Delta X = a0 - b0 + (a1 + b1) X` (section 5.2), for `S > 0`. -/
def chord (Pa Pb a0 a1 b0 b1 S : ℤ) : ℤ :=
  let k := a1 + b1
  let da := a0 - b0 + k * Pa
  let db := da + k * (Pb - Pa)
  if db ≤ 0 then 0
  else if S ≤ da then Pb - Pa
  else
    let num := (pos2 Pa Pb da k 0).1 - (pos2 Pa Pb da k S).2
    if 0 < num then num / (2 * S) else 0

/-! ## Records (section 5.0, 6) -/

/-- A record: the cell `pos`, the value `val` (over `D`), the global index `gi`, `map`
(`ceil_{t+1}` of the value, a local index of `G_{t+1}`), the width `w`, `forg` (the point `1` of
`G_t`, a forgotten coordinate). -/
structure Rec where
  /-- The cell index. -/
  pos : ℕ
  /-- The value, over `D`. -/
  val : ℕ
  /-- The global index. -/
  gi : ℕ
  /-- `ceil_{t+1}` of the value, a local index of `G_{t+1}`. -/
  map : ℕ
  /-- The width of the box (credited when `0 < w`). -/
  w : ℕ
  /-- The point `1` of `G_t`. -/
  forg : Bool

section Records

variable (D : ℕ) (g : Grid)

/-- The width `w (k)` of the local point `k` of `G_t`: `gpt[s_t]` for `k = 0`,
`gpt[s_t + k] - gpt[s_t + k - 1]` for `1 ≤ k < cnt_t`, `0` for `k = cnt_t`. -/
def width (t k : ℕ) : ℕ :=
  if k < g.cnt t then pt D g (g.glob t k) - (if k = 0 then 0 else pt D g (g.glob t (k - 1))) else 0

/-- The record of the local point `k` of `G_t`. -/
def locRec (t k : ℕ) : Rec :=
  ⟨g.pos t k, pt D g (g.glob t k), g.glob t k, g.mapL t k, width D g t k, decide (k = g.cnt t)⟩

/-- The new points: the finite points `j` of `G_{t+1}` above `top_t` (`j ≥ e_t = s_t + cnt_t`),
increasing. -/
def newPts (t : ℕ) : List ℕ :=
  (List.range g.J).filter fun j =>
    g.inWin (t + 1) j && decide ((g.wt t).s + (g.wt t).cnt ≤ j)

/-- The record of the new point `j`. -/
def newRec (t j : ℕ) : Rec :=
  ⟨(g.cellPts t).idxOf j + 1, pt D g j, j, j - (g.wt (t + 1)).s, 0, false⟩

/-- A choice for section 6: a nondecreasing tuple of new points or `J` (the point `1`). Only its
values at the forgotten coordinates matter. -/
def ValidChoice (t : ℕ) {m : ℕ} (x : Fin m → ℕ) : Prop :=
  Monotone x ∧ ∀ l, x l ∈ newPts g t ∨ x l = g.J

/-- The record list of the state `k` of `G_t` and the choice `x`: the record of the new point
`x l` at a forgotten coordinate `l` with `x l` a new point, the record of `k l` otherwise. -/
def recList (t : ℕ) {m : ℕ} (k x : Fin m → ℕ) : Fin m → Rec := fun l =>
  if k l = g.cnt t ∧ x l ∈ newPts g t then newRec D g t (x l) else locRec D g t (k l)

end Records

/-! ## The bound of one record list (section 5.3 to 5.5) -/

section Bound

variable (D : ℕ) (g : Grid) (d : ℕ) (N : (Fin (d + 1) → ℕ) → ℕ) (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ)
  (t : ℕ) (c : Fin (d + 1) → Rec)

/-- `ev_l = gpt[global_{t+1} (map_l)] - val_l` (`0` for a forgotten record). -/
def ev (l : Fin (d + 1)) : ℤ :=
  if (c l).forg then 0 else (pt D g (g.glob (t + 1) (c l).map) : ℤ) - (c l).val

/-- `im = pos_{m-1}`. -/
def im : ℕ := (c (Fin.last d)).pos

/-- `below_i = #{l ≤ m - 2 : pos_l ≤ i - 1}`. -/
def below (i : ℕ) : ℕ := (Finset.univ.filter fun l : Fin d => (c l.castSucc).pos + 1 ≤ i).card

/-- `below_i ≤ m - 1`. -/
theorem below_le (i : ℕ) : below d c i ≤ d := by
  unfold below
  exact (Finset.card_le_univ _).trans (by simp)

/-- `below_i` as a slot. -/
def belowF (i : ℕ) : Fin (d + 1) := ⟨below d c i, Nat.lt_succ_of_le (below_le d c i)⟩

/-- `H_i = (map_0, ..., map_{below - 1}, nxt_i, map_below, ..., map_{m-2})`. -/
def Hc (i : ℕ) : Fin (d + 1) → ℕ := fun l =>
  if (l : ℕ) < below d c i then (c l).map
  else if (l : ℕ) = below d c i then g.nxt t i
  else (c ⟨l - 1, by omega⟩).map

/-- `slot (l) = l + 1` if `pos_l ≥ i`, `l` if `pos_l < i` (`l ≤ m - 2`). -/
def slot (i : ℕ) (l : Fin d) : Fin (d + 1) :=
  if i ≤ (c l.castSucc).pos then l.succ else l.castSucc

/-- `beta` of the cell `i ≤ im`. -/
def betaC (i : ℕ) : ℤ :=
  let H := Hc g d t c i
  let sl := Sg H
  let Em := Epen D (pt D g (c (Fin.last d)).gi) (g.n - t)
  (D : ℤ) * (Em + N H) + (sl (belowF d c i) : ℤ) * pt D g (g.glob (t + 1) (g.nxt t i)) +
    ∑ l : Fin d, (sl (slot d c i l) : ℤ) * ev D g d t c l.castSucc

/-- `sigma` of the cell `i ≤ im`: the slope of `H_i` at the slot `below_i`. -/
def sigmaC (i : ℕ) : ℤ :=
  Sg (Hc g d t c i) (belowF d c i)

/-- The coefficients of the cell `i ≤ im`. -/
def coefC (i : ℕ) (l : Fin (d + 1)) : ℤ :=
  let sl := Sg (Hc g d t c i)
  if h : (l : ℕ) = d then
    if (c (Fin.last d)).forg ∨ i = im d c then 0
    else ((g.n - t) * Epen D (pt D g (c (Fin.last d)).gi) (g.n - t - 1) : ℕ)
  else
    let l' : Fin d := ⟨l, by omega⟩
    if (c l).forg then 0
    else if i < (c l).pos then sl l'.succ
    else if (c l).pos = i then 0
    else sl l'.castSucc

/-- `S = sum over l of coef_l w_l` of the cell `i ≤ im`. -/
def SC (i : ℕ) : ℤ := ∑ l, coefC D g d Sg t c i l * (c l).w

/-- `a0 = alpha_i D ^ 2` of the cell `i ≤ im`. -/
def a0C (i : ℕ) : ℤ := ((1 + below d c i) * D * D : ℕ)

/-- The cell integral of the cell `i ≤ im` (units `1 / (2 D ^ 3)`). -/
def RC (i : ℕ) : ℤ :=
  cell2 (cp D g t (i - 1)) (cp D g t i) (a0C D d c i) ((g.n - t) * D : ℕ) (betaC D g d N Sg t c i)
    (sigmaC g d Sg t c i)

/-- The chord of the cell `i ≤ im` (`0` if `S ≤ 0`). -/
def QC (i : ℕ) : ℤ :=
  if 0 < SC D g d Sg t c i then
    chord (cp D g t (i - 1)) (cp D g t i) (a0C D d c i) ((g.n - t) * D : ℕ) (betaC D g d N Sg t c i)
      (sigmaC g d Sg t c i) (SC D g d Sg t c i)
  else 0

/-- `M` of the own cell `i ≤ im`: `floor (gap / D)` if `gap > 0`, else `0`. -/
def MC (i : ℕ) : ℤ :=
  let gap := betaC D g d N Sg t c i - sigmaC g d Sg t c i * cp D g t i - a0C D d c i -
    ((g.n - t) * D : ℕ) * cp D g t i
  if 0 < gap then gap / D else 0

/-- The own-cell credit of the record `l` in the cell `i`: with `q` the number of records `l' < l`
with `pos_l' = i`, not forgotten, `min ((q + 1) D, M) - min (q D, M)` if `pos_l = i` and `l` is
not forgotten, else `0`. -/
def lamC (i : ℕ) (l : Fin (d + 1)) : ℤ :=
  if (c l).pos = i ∧ (c l).forg = false then
    let q := (Finset.univ.filter fun l' : Fin (d + 1) => l' < l ∧ (c l').pos = i ∧ (c l').forg = false).card
    min (((q + 1) * D : ℕ) : ℤ) (MC D g d N Sg t c i) - min ((q * D : ℕ) : ℤ) (MC D g d N Sg t c i)
  else 0

/-- The tail continuation `U = D Vc + sum over l of slc_l ev_l`, `Hc = map`. -/
def UT : ℤ :=
  (D : ℤ) * N (fun l => (c l).map) + ∑ l, (Sg (fun l => (c l).map) l : ℤ) * ev D g d t c l

/-- `S` of the tail: `sum over l of slc_l w_l`. -/
def ST : ℤ := ∑ l, (Sg (fun l => (c l).map) l : ℤ) * (c l).w

/-- `jT`: the least `j` with `im ≤ j ≤ L - 1` and `a0 + a1 p_j ≥ D (E_t (p_j) + r) + U + S`, `L` if
there is none (section 5.4). -/
def jT : ℕ :=
  (((List.range' (im d c) (g.L t - im d c)).find? fun j =>
    decide ((((d + 2) * D * D + (g.n - t) * D * cp D g t j : ℕ) : ℤ) ≥
      (D : ℤ) * (Epen D (cp D g t j) (g.n - t) + (g.n - t) : ℕ) + UT D g d N Sg t c + ST d Sg c)).getD
    (g.L t))

/-- The cell integral of the tail cell `i` (`im < i ≤ jT`). -/
def RT (i : ℕ) : ℤ :=
  let sig : ℤ := ((g.n - t) * Epen D (cp D g t i) (g.n - t - 1) : ℕ)
  cell2 (cp D g t (i - 1)) (cp D g t i) (((d + 2) * D * D : ℕ) : ℤ) ((g.n - t) * D : ℕ)
    ((D : ℤ) * Epen D (cp D g t i) (g.n - t) + UT D g d N Sg t c + sig * cp D g t i) sig

/-- The chord of the tail cell `i` (`0` if `S ≤ 0`). -/
def QT (i : ℕ) : ℤ :=
  let sig : ℤ := ((g.n - t) * Epen D (cp D g t i) (g.n - t - 1) : ℕ)
  if 0 < ST d Sg c then
    chord (cp D g t (i - 1)) (cp D g t i) (((d + 2) * D * D : ℕ) : ℤ) ((g.n - t) * D : ℕ)
      ((D : ℤ) * Epen D (cp D g t i) (g.n - t) + UT D g d N Sg t c + sig * cp D g t i) sig
      (ST d Sg c)
  else 0

/-- The exact tail `[p_jT, 1]`: `floor (2 D ^ 2 E_{t-1} (p_jT) / (r + 1)) + 2 (D - p_jT) U` if
`p_jT < D`, else `0`. -/
def RE : ℤ :=
  let j := jT D g d N Sg t c
  if cp D g t j < D then
    ((2 * D * D * Epen D (cp D g t j) (g.n - t + 1) / (g.n - t + 1) : ℕ) : ℤ) +
      2 * ((D - cp D g t j : ℕ) : ℤ) * UT D g d N Sg t c
  else 0

/-- `R` of the record list (units `1 / (2 D ^ 3)`): the cells `1, ..., im`, and when the last
record is not forgotten the tail cells `im + 1, ..., jT` and the exact tail. -/
def Rtot : ℤ :=
  ∑ i ∈ Finset.Icc 1 (im d c), RC D g d N Sg t c i +
    if (c (Fin.last d)).forg then 0
    else ∑ i ∈ Finset.Ioc (im d c) (jT D g d N Sg t c), RT D g d N Sg t c i + RE D g d N Sg t c

/-- `acc_l` (units `1 / D ^ 2`). -/
def acc (l : Fin (d + 1)) : ℤ :=
  ∑ i ∈ Finset.Icc 1 (im d c), coefC D g d Sg t c i l * QC D g d N Sg t c i +
    if (c (Fin.last d)).forg then 0
    else (Sg (fun l => (c l).map) l : ℤ) *
      (∑ i ∈ Finset.Ioc (im d c) (jT D g d N Sg t c), QT D g d N Sg t c i +
        if cp D g t (jT D g d N Sg t c) < D then ((D - cp D g t (jT D g d N Sg t c) : ℕ) : ℤ)
        else 0)

/-- `lam_l` (units `1 / D`). -/
def lam (l : Fin (d + 1)) : ℤ := ∑ i ∈ Finset.Icc 1 (im d c), lamC D g d N Sg t c i l

/-- The output of section 5.5: `T0 = floor (R / (2 D ^ 2))` and
`mu_l = lam_l + floor (acc_l / D)` (`0` for a forgotten record). -/
def bound : ℤ × (Fin (d + 1) → ℤ) :=
  (Rtot D g d N Sg t c / (2 * D * D : ℕ), fun l =>
    if (c l).forg then 0 else lam D g d N Sg t c l + acc D g d N Sg t c l / D)

end Bound

end Robbins.Cert.SO
