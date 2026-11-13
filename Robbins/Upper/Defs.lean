import Robbins.Statement

/-!
# The threshold rule

For `N` values the rule of Bruss and Ferguson (1993, (1.10)) stops at time `t` (from `0` to `N - 1`)
when `x t ≤ thr N t = 2 / (N - t + 1)`; the threshold of the last time is `1`. Each earlier time is
passed with probability `1 - thr N s`; `survive N t` is the product of these factors over `s < t`.
On the event that the rule stops at `t`, every value `x j < x t` puts the values in the box
`box N t j` (coordinates `s < t` above their thresholds, `x t ≤ thr N t`, `x j < thr N t`).
-/

namespace Robbins.Threshold

open MeasureTheory

/-- The threshold at time `t` for `N` values. -/
noncomputable def thr (N t : ℕ) : ℝ := 2 / ((N : ℝ) - t + 1)

/-- The probability that the rule passes the times `0, ..., t - 1`. -/
noncomputable def survive (N t : ℕ) : ℝ := ∏ s ∈ Finset.range t, (1 - thr N s)

/-- The threshold rule for `n + 1` values. -/
noncomputable def rule (n : ℕ) : Rule (n + 1) where
  stopSet t := {y | y (Fin.last t) ≤ thr (n + 1) t}
  measurableSet_stopSet _ := measurableSet_le (measurable_pi_apply _) measurable_const

/-- The coordinates of the box of `(t, j)`: the values `x s` (`s < t`, `s ≠ j`) above their
thresholds, `x t ≤ thr N t`, `x j` between its threshold and `thr N t` if `j < t`, below
`thr N t` if `j > t`. -/
noncomputable def box (N : ℕ) (t j : Fin N) (s : Fin N) : Set ℝ :=
  if s = t then Set.Iic (thr N t)
  else if s = j then (if j < t then Set.Ioo (thr N j) (thr N t) else Set.Iio (thr N t))
  else if s < t then Set.Ioi (thr N s) else Set.univ

end Robbins.Threshold
