import Robbins.Statement
import Robbins.Target
import Robbins.Upper.Expect

/-!
# A uniform upper bound on `v`, hence the limit

`v n ≤ 5` for every `n`: the threshold rule that stops at time `t` when `x t ≤ 2 / (N - t + 1)`
(`N = n + 1` values; Bruss and Ferguson 1993, (1.10)) has expected rank at most `5`
(Robbins/Upper/Expect.lean). With `v_mono` (Theorem C), `v` is nondecreasing and bounded above, so
it converges.
-/

namespace Robbins

open Filter Topology

/-- The least expected rank is at most `5` for every number of values. -/
theorem v_le_five : ∀ n, v n ≤ 5 := by
  intro n
  cases n with
  | zero => simp [v]
  | succ n => exact (v_succ_le (Threshold.rule n)).trans (Threshold.expectedRank_le_five n)

/-- The least expected rank `v n` converges. -/
theorem exists_tendsto_v : ∃ V : ℝ, Tendsto v atTop (𝓝 V) :=
  ⟨⨆ n, v n, tendsto_atTop_ciSup v_mono ⟨5, by rintro _ ⟨n, rfl⟩; exact v_le_five n⟩⟩

end Robbins
