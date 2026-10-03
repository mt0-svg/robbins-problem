import Robbins.Target
import RobbinsSO.N300.Final

/-!
# The lower bound `v n > 2`

The second-order certificate of Section 5 of the paper (`m = 5`, `n = 300`, `rho = 1.3`, window `[0.35, 14]`,
tables written by the program soq of code/soq), checked in the kernel step by step: the steps whose window changes and the time `300` by `checkRange` and
`checkLast` (Robbins/Cert/SO/EvalK.lean), the fixed-window steps in packed lanes by `lanesRange`
(Robbins/Cert/SO/Lanes.lean, with `checkStep_of_lanesRanges` of Robbins/Cert/SO/LanesSound.lean), chained by
`ChainSO` (Robbins/Cert/SO/EvalKChain.lean): `uh_1 (cnt_1, ..., cnt_1) = 137704521264`, so
`v 300 ≥ 137704521264 / 2 ^ 36 > 2.0038`.

The generated modules (`RobbinsSO.N300`) are not in the repository: code/formal-proof/gen.sh writes them from
the tables of soq (code/soq/run.sh), as the job data of .github/workflows/ci.yml does.
-/

namespace Robbins

open Filter Topology

/-- `v 300 ≥ 137704521264 / 2 ^ 36`. -/
theorem v300 : ((137704521264 : ℝ) / 2 ^ 36) ≤ v 300 := by
  have h := RobbinsSO.N300.le_v
  norm_num [Cert.SO.K.DS] at h ⊢
  exact h

/-- `v n ≥ 137704521264 / 2 ^ 36` for every `n ≥ 300`. -/
theorem main_so : ∀ n ≥ 300, ((137704521264 : ℝ) / 2 ^ 36) ≤ v n :=
  lower_bound_of_base v300

/-- The limit of `v n`, if it exists, is at least `137704521264 / 2 ^ 36`. -/
theorem main_so_limit : ∀ V : ℝ, Tendsto v atTop (𝓝 V) → (137704521264 : ℝ) / 2 ^ 36 ≤ V :=
  limit_lower_bound_of_base v300

/-- `v n > 2` for every `n ≥ 300`. -/
theorem two_lt_v : ∀ n ≥ 300, (2 : ℝ) < v n :=
  fun n hn => lt_of_lt_of_le (by norm_num) (main_so n hn)

/-- A relaxed sub-solution of horizon `300` and memory `5` of value `137704521264 / 2 ^ 36` at time `1` and the
memory `(1, ..., 1)`. -/
theorem relaxed300 :
    ∃ u : RelaxedSubSolution 300 5, u.u 1 (fun _ => 1) = (137704521264 : ℝ) / 2 ^ 36 := by
  obtain ⟨u, hu⟩ := RobbinsSO.N300.relaxed
  refine ⟨u, ?_⟩
  rw [hu]
  norm_num [Cert.SO.K.DS]

end Robbins
