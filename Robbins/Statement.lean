import Mathlib

/-!
# Robbins' problem: the frozen definitions

Values `x 0, x 1, ..., x n` (that is `n + 1` values, `x t` being the value `X_{t+1}` of the
textbook) are drawn independently and uniformly on `[0, 1]` and shown one at a time. After seeing
`x t` the decision maker either stops and selects `x t`, or rejects it for good and goes on; at the
last time `n` it must select `x n`. The rule may use every value seen so far (full information).
The loss is the rank of the selected value among all `n + 1` values: one plus the number of values
strictly below it. `v (n + 1)` is the least expected rank over all stopping rules; `v 0 = 0` is a
convention (there is no value to select).

Model.
* The law of the values (`law`) is the product of `n` copies of Lebesgue measure restricted to
  `[0, 1]`: the uniform distribution on the unit cube. It is a probability measure
  (`isProbabilityMeasure_law`).
* A stopping rule (`Rule`) gives, for each time `t`, a measurable set `stopSet t` of histories
  `x 0, ..., x t` (`history x t : Fin (t + 1) → ℝ`) on which it stops. The selected time
  (`Rule.time`) is the first time `t` whose history lies in `stopSet t`, and the last time if there
  is none; so the set given for the last time plays no role. Every stopping time adapted to the
  values has this form (take for `stopSet t` a Borel set whose preimage is the event of stopping at
  `t`), so the rules here are exactly the deterministic stopping rules. Randomized rules do not
  lower the infimum and are not part of this statement.
* Ties have probability `0`; the rank counts the values strictly below the selected one.
* `v (n + 1) = ⨅ r, r.expectedRank` is an infimum in `ℝ`. The set of rules is nonempty (the
  instance below) and the expected ranks are at least `1`, so this is the true infimum and not a
  junk value; `Robbins/Basic` proves the bounds.

The targets are stated in `Robbins/Target.lean`.
-/

namespace Robbins

open MeasureTheory

/-- The uniform distribution on `[0, 1]`, Lebesgue measure restricted to `[0, 1]`, is a probability
measure. -/
instance isProbabilityMeasure_unitInterval :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

/-- The law of `n` values: independent, each uniform on `[0, 1]`. -/
noncomputable def law (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)

instance isProbabilityMeasure_law (n : ℕ) : IsProbabilityMeasure (law n) := by
  unfold law
  infer_instance

/-- The values seen up to time `t` included: `x 0, ..., x t`. -/
def history {n : ℕ} (x : Fin n → ℝ) (t : Fin n) : Fin (t + 1) → ℝ :=
  fun s => x (Fin.castLE t.isLt s)

/-- A stopping rule for `n` values: for each time `t`, a measurable set of histories
`x 0, ..., x t` on which the rule stops at `t`. -/
structure Rule (n : ℕ) where
  /-- The histories up to time `t` on which the rule stops at time `t`. -/
  stopSet : (t : Fin n) → Set (Fin (t + 1) → ℝ)
  /-- Each stop set is measurable. -/
  measurableSet_stopSet : ∀ t, MeasurableSet (stopSet t)

/-- There are rules (for instance the rule that never stops before the last time). -/
instance (n : ℕ) : Nonempty (Rule n) :=
  ⟨⟨fun _ => ∅, fun _ => MeasurableSet.empty⟩⟩

open Classical in
/-- The time selected by the rule `r` on the values `x`: the first time `t` whose history is in the
stop set of `t`, and the last time `n` if there is none. -/
noncomputable def Rule.time {n : ℕ} (r : Rule (n + 1)) (x : Fin (n + 1) → ℝ) : Fin (n + 1) :=
  (Finset.univ.filter fun t => history x t ∈ r.stopSet t ∨ t = Fin.last n).min'
    ⟨Fin.last n, by simp⟩

/-- The rank of the value selected by `r` among the `n + 1` values `x`: one plus the number of
values strictly below it. -/
noncomputable def Rule.rank {n : ℕ} (r : Rule (n + 1)) (x : Fin (n + 1) → ℝ) : ℕ :=
  1 + (Finset.univ.filter fun j => x j < x (r.time x)).card

/-- The expected rank of the value selected by `r`, the `n + 1` values being independent and
uniform on `[0, 1]`. -/
noncomputable def Rule.expectedRank {n : ℕ} (r : Rule (n + 1)) : ℝ :=
  ∫ x, (r.rank x : ℝ) ∂law (n + 1)

/-- `v n`: the least expected rank of the selected value over all stopping rules for `n` values
(Robbins' problem with full information). `v 0 = 0` by convention. -/
noncomputable def v : ℕ → ℝ
  | 0 => 0
  | n + 1 => ⨅ r : Rule (n + 1), r.expectedRank

end Robbins
