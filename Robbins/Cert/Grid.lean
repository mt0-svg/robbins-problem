/-!
# The grid data of the certificate

Section 1 of the certificate format: the denominator `D = 2 ^ 40`, the grid data (`n`, `m`, the window
length `K`, the global points `gpt`, the start values), the data conditions `Grid.ok`, the windows
and `ceil_t` on global indices. Shared by the evaluator (Robbins/Cert/Eval.lean) and its
specification (Robbins/Cert/Spec.lean).
-/

namespace Robbins.Cert

/-- The denominator `D = 2 ^ 40`. -/
def D : Nat := 1099511627776


/-- The grid data of section 1 of the certificate format. -/
structure Grid where
  /-- The number of values. -/
  n : Nat
  /-- The memory size. -/
  m : Nat
  /-- The window length. -/
  K : Nat
  /-- The global points `gpt[0], ..., gpt[J-1]` (numerators over `D`). -/
  gpt : List Nat
  /-- `start[1], ..., start[n]`. -/
  start : List Nat

/-- `gpt` strictly increasing in `(0, D)`. -/
def strictInc : Nat → List Nat → Bool
  | _, [] => true
  | p, x :: xs => p < x && strictInc x xs

/-- `start` nondecreasing. -/
def nondec : Nat → List Nat → Bool
  | _, [] => true
  | p, x :: xs => p ≤ x && nondec x xs

/-- The data conditions: `1 ≤ m`, `2 ≤ n`, `gpt` strictly increasing in `(0, D)`, `n` start
values, nondecreasing. -/
def Grid.ok (g : Grid) : Bool :=
  1 ≤ g.m && 2 ≤ g.n && strictInc 0 g.gpt && g.gpt.all (· < D) && g.start.length == g.n &&
    nondec 0 g.start

/-- The window of time `t`: `s_t = min (start t) J`, `cnt_t = min (start t + K) J - s_t`. -/
structure Win where
  /-- `s_t`. -/
  s : Nat
  /-- `cnt_t`. -/
  cnt : Nat

/-- The window of a start value. -/
def Grid.win (g : Grid) (st : Nat) : Win :=
  let J := g.gpt.length
  ⟨min st J, min (st + g.K) J - min st J⟩

/-- `ceil_t` of the global index `j`, as a local index of `G_t` (section 1). -/
def ceilLocal (J : Nat) (w : Win) (j : Nat) : Nat :=
  if j == J || w.cnt == 0 then w.cnt
  else if j < w.s then 0
  else if j < w.s + w.cnt then j - w.s
  else w.cnt

end Robbins.Cert
