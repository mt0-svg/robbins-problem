import Robbins.Statement

/-!
# The drop penalty relaxation: the interface of the certificate

Section 2.1 of the paper (Definition 2.1), with its indexing: `n` values, times `t = 1, ..., n`. A
memory is a sorted `m`-tuple `y 0 ≤ ... ≤ y (m - 1)` of values in `[0, 1]` (`IsMemory`); the
coordinate `y k` here is `y_{k+1}` of the paper.

* `ins y x`: the `m` smallest of `y 0, ..., y (m - 1), x`, sorted: coordinate `k` is
  `max (y (k - 1)) (min (y k) x)`, with `y (-1) = 0`;
* `drop y x`: the largest of them, `max (y (m - 1)) x`, and `x` when `m = 0`;
* `relaxStop n t y x = 1 + #{k | y k < x} + (n - t) x`: the relaxed stop cost `S_t(y, x)`;
* `dropPenalty n t y x = (1 - drop y x) ^ (n - t)`: the drop penalty `pi_t(y, x)`.

A `RelaxedSubSolution n m` is a family `u t` of functions on memories, measurable and bounded on
memories for `1 ≤ t ≤ n`, with (R_n) and (R_t) at every memory. Theorem B
(`RelaxedSubSolution.val_one_le_v`, Robbins/Relax/TheoremB.lean): `u 1` at the memory
`(1, ..., 1)` is a lower bound of `v n`.
-/

namespace Robbins

open MeasureTheory

/-- A memory: a sorted tuple of values in `[0, 1]`. -/
def IsMemory {m : ℕ} (y : Fin m → ℝ) : Prop :=
  Monotone y ∧ ∀ k, y k ∈ Set.Icc (0 : ℝ) 1

/-- The `m` smallest of `y 0, ..., y (m - 1), x`, sorted (for a sorted `y`): coordinate `k` is
`max (y (k - 1)) (min (y k) x)`, with `y (-1) = 0`. -/
noncomputable def ins {m : ℕ} (y : Fin m → ℝ) (x : ℝ) : Fin m → ℝ :=
  fun k => max (if h : (k : ℕ) = 0 then 0 else y ⟨k - 1, by omega⟩) (min (y k) x)

/-- The largest of `y 0, ..., y (m - 1), x` (for a sorted `y`): `max (y (m - 1)) x`, and `x` when
`m = 0`. -/
noncomputable def drop {m : ℕ} (y : Fin m → ℝ) (x : ℝ) : ℝ :=
  if h : m = 0 then x else max (y ⟨m - 1, by omega⟩) x

/-- The relaxed stop cost at time `t` of `n`, memory `y`, current value `x`:
`1 + #{k | y k < x} + (n - t) x`. -/
noncomputable def relaxStop (n t : ℕ) {m : ℕ} (y : Fin m → ℝ) (x : ℝ) : ℝ :=
  1 + ((Finset.univ.filter fun k => y k < x).card : ℝ) + ((n : ℝ) - t) * x

/-- The drop penalty at time `t` of `n`, memory `y`, current value `x`: `(1 - drop y x) ^ (n - t)`. -/
noncomputable def dropPenalty (n t : ℕ) {m : ℕ} (y : Fin m → ℝ) (x : ℝ) : ℝ :=
  (1 - drop y x) ^ (n - t)

/-- A relaxed sub-solution for `n` values and memory size `m` (Definition 2.1 of the paper). -/
structure RelaxedSubSolution (n m : ℕ) where
  /-- The value `u t y` at time `t` and memory `y`. -/
  u : ℕ → (Fin m → ℝ) → ℝ
  /-- Each `u t` is measurable, `1 ≤ t ≤ n`. -/
  measurable : ∀ t, 1 ≤ t → t ≤ n → Measurable (u t)
  /-- Each `u t` is bounded on memories, `1 ≤ t ≤ n`. -/
  bounded : ∀ t, 1 ≤ t → t ≤ n → ∃ C, ∀ y, IsMemory y → |u t y| ≤ C
  /-- (R_n). -/
  last : ∀ y, IsMemory y → u n y ≤ ∫ x in Set.Icc (0 : ℝ) 1, relaxStop n n y x
  /-- (R_t), `1 ≤ t < n`. -/
  step : ∀ t, 1 ≤ t → t < n → ∀ y, IsMemory y →
    u t y ≤ ∫ x in Set.Icc (0 : ℝ) 1,
      min (relaxStop n t y x) (dropPenalty n t y x + u (t + 1) (ins y x))

end Robbins
