import Robbins.Cert.Grid
import Robbins.Cert.SpecArith

/-!
# The specification of the evaluator

The first-order certificate, sections 1 to 4 of its format, written as functions of an abstract table
`N : (Fin (d + 1) → ℕ) → ℕ` (the table `uhat_{t+1}` of memory size `m = d + 1`, read at sorted
tuples of local indices of `G_{t+1}`), with no data structure: the grid quantities of time `t`, the
cells of `P_t`, and for a state `k` of `G_t` the integral bound `specR g d N t k c` (units `2 ^ -81`)
for a crossing index `c`. The penalty recurrence `Epen`, the cell integral `jcell`, the condition
`condT` and the tail `tailT` are those of Robbins/Cert/SpecArith.lean.

The crossing index is a parameter: `crossOK` asks only that `c` be a local crossing (`Pos` fails
at `c - 1` and holds at `c`). Since `Pos` is monotone in the cell index when `N` is nonincreasing
(`pos_of_crossOK` of Robbins/Cert/SoundState.lean), a local crossing is the least index of section 4.3.

Robbins/Cert/Eval.lean computes these values; Robbins/Cert/Sound.lean states the soundness of tables
bounded by them.
-/

namespace Robbins.Cert

namespace Grid

variable (g : Grid)

/-- `J`, the number of global points below `1`. -/
def J : ℕ := g.gpt.length

/-- The value (over `D`) of the global index `j`: `gpt[j]` for `j < J`, and `D` (the point `1`)
for `j ≥ J`. -/
def pt (j : ℕ) : ℕ := if j < g.J then g.gpt.getD j 0 else D

/-- The window of time `t ≥ 1`, from `start[t]`. -/
def wt (t : ℕ) : Win := g.win (g.start.getD (t - 1) 0)

/-- `cnt_t`: `G_t` has the local points `0, ..., cnt_t`. -/
def cnt (t : ℕ) : ℕ := (g.wt t).cnt

/-- The global index of the local point `k` of `G_t` (`J` for `k = cnt_t`). -/
def glob (t k : ℕ) : ℕ := if k < g.cnt t then (g.wt t).s + k else g.J

/-- `ceil_t` of the global index `j`, as a local index of `G_t`. -/
def ceilG (t j : ℕ) : ℕ := ceilLocal g.J (g.wt t) j

/-- A state of `G_t`: a sorted tuple of local indices of `G_t`. -/
def IsState (t : ℕ) {m : ℕ} (k : Fin m → ℕ) : Prop :=
  Monotone k ∧ ∀ l, k l ≤ g.cnt t

/-- The global index `j` is a point of the window of time `t`. -/
def inWin (t j : ℕ) : Bool :=
  (g.wt t).s ≤ j && j < (g.wt t).s + (g.wt t).cnt

/-- The endpoints of the cells of `P_t` as global indices, increasing: the points of `G_t` and of
`G_{t+1}` (the point `1` is `J`). -/
def cellPts (t : ℕ) : List ℕ :=
  (List.range (g.J + 1)).filter fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j

/-- `L`, the number of cells of `P_t`. -/
def L (t : ℕ) : ℕ := (g.cellPts t).length

/-- The endpoint `p_i` of the cells of `P_t` (over `D`), `p_0 = 0`. -/
def cp (t i : ℕ) : ℕ := if i = 0 then 0 else g.pt ((g.cellPts t).getD (i - 1) 0)

/-- `pos k`: the cell index `i` with `p_i` the local point `k` of `G_t`. -/
def pos (t k : ℕ) : ℕ := (g.cellPts t).idxOf (g.glob t k) + 1

/-- `map k = ceil_{t+1} (global_t k)`. -/
def mapL (t k : ℕ) : ℕ := g.ceilG (t + 1) (g.glob t k)

/-- `nxt_i = ceil_{t+1} (pts[i])`. -/
def nxt (t i : ℕ) : ℕ := g.ceilG (t + 1) ((g.cellPts t).getD (i - 1) 0)

/-- `Ep_i = E_t (p_i)`. -/
def cE (t i : ℕ) : ℕ := Epen (g.cp t i) (g.n - t)

/-- `E1p_i = E_{t-1} (p_i)`. -/
def cE1 (t i : ℕ) : ℕ := Epen (g.cp t i) (g.n - t + 1)

end Grid

/-- The sorted tuple of the head `h_0, ..., h_{d-1}` (the first `d` coordinates of `h`, sorted)
with `x` inserted; the top coordinate of `h` is ignored. -/
def insIdx {d : ℕ} (h : Fin (d + 1) → ℕ) (x : ℕ) : Fin (d + 1) → ℕ :=
  fun l => max (if hl : (l : ℕ) = 0 then 0 else h ⟨l - 1, by omega⟩)
    (if (l : ℕ) = d then x else min (h l) x)

namespace Grid

variable (g : Grid) (d : ℕ) (N : (Fin (d + 1) → ℕ) → ℕ) (t : ℕ) (k : Fin (d + 1) → ℕ)

/-- `map (k)`, coordinatewise. -/
def kmap : Fin (d + 1) → ℕ := fun l => g.mapL t (k l)

/-- `row (h, i) = N (sort (h, nxt_i))`, `h` the head of `map (k)`. -/
def row (i : ℕ) : ℕ := N (insIdx (g.kmap d t k) (g.nxt t i))

/-- `U = N (map (k))`. -/
def uN : ℕ := N (g.kmap d t k)

/-- `im = pos (k_m)`. -/
def im : ℕ := g.pos t (k (Fin.last d))

/-- `alpha_i`: `1 + #{l ≤ m - 1 : pos k_l ≤ i - 1}` for `i ≤ im`, `1 + m` above. -/
def alpha (i : ℕ) : ℕ :=
  if i ≤ g.im d t k then
    1 + (Finset.univ.filter fun l : Fin d => g.pos t (k l.castSucc) + 1 ≤ i).card
  else d + 2

/-- `C_i`: `Em + row (h, i)` for `i ≤ im`, `Ep_i + U` above. -/
def cC (i : ℕ) : ℕ :=
  if i ≤ g.im d t k then g.cE t (g.im d t k) + g.row d N t k i else g.cE t i + g.uN d N t k

/-- The test `Pos_i`: `alpha_i D + r p_i ≥ C_i`. -/
def Pos (i : ℕ) : Bool :=
  decide (g.cC d N t k i ≤ g.alpha d t k i * D + (g.n - t) * g.cp t i)

/-- `c` is a local crossing: `1 ≤ c ≤ L + 1`, `Pos` fails at `c - 1` (or `c = 1`) and holds at
`c` (or `c = L + 1`). -/
def crossOK (c : ℕ) : Prop :=
  1 ≤ c ∧ c ≤ g.L t + 1 ∧ (c = 1 ∨ g.Pos d N t k (c - 1) = false) ∧
    (c = g.L t + 1 ∨ g.Pos d N t k c = true)

/-- The prefix sums `Q (h, i) = sum over i' ≤ i of 2 h_{i'} row (h, i')`. -/
def Q (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 i, 2 * (g.cp t j - g.cp t (j - 1)) * g.row d N t k j

/-- The stop part `Sint (X) = 2 D X + r X ^ 2 + 2 D sum_l max (0, X - g_l)`. -/
def Sint (X : ℕ) : ℕ :=
  2 * D * X + (g.n - t) * X * X + 2 * D * ∑ l, (X - g.pt (g.glob t (k l)))

/-- `R (k)` of section 4.3 of the format for the crossing index `c` (units `2 ^ -81`). -/
def specR (c : ℕ) : ℕ :=
  let r := g.n - t
  let p := g.cp t
  let im := g.im d t k
  let gm := p im
  let Em := g.cE t im
  let U := g.uN d N t k
  if c = g.L t + 1 then g.Sint d t k D
  else if c ≤ im then
    g.Sint d t k (p (c - 1)) + jcell r (p (c - 1)) (p c) (g.alpha d t k c) (Em + g.row d N t k c) +
      2 * Em * (gm - p c) + (g.Q d N t k im - g.Q d N t k c) +
      tailT r (d + 1) U gm Em (g.cE1 t im)
  else
    let base := g.Sint d t k (p (c - 1)) + jcell r (p (c - 1)) (p c) (d + 2) (g.cE t c + U)
    if p c = D ∨ condT r (d + 1) U (g.cE t c) (p c) = true then
      base + tailT r (d + 1) U (p c) (g.cE t c) (g.cE1 t c)
    else
      base + 2 * (p (c + 1) - p c) * (g.cE t (c + 1) + U) +
        tailT r (d + 1) U (p (c + 1)) (g.cE t (c + 1)) (g.cE1 t (c + 1))

/-- `ceil_t` on values: the least local index `k ≤ cnt_t` of `G_t` with `y D ≤ pt (glob t k)`, or
`cnt_t` if there is none. -/
noncomputable def ceilR (t : ℕ) (y : ℝ) : ℕ := by
  classical
  exact if h : ∃ k, k ≤ g.cnt t ∧ y * D ≤ g.pt (g.glob t k) then Nat.find h else g.cnt t

end Grid

end Robbins.Cert
