import Robbins.Statement
import Robbins.Mono.TheoremC

/-!
# Robbins' problem: the targets

Stated on the frozen definitions of `Robbins/Statement.lean`.

* `v_mono`: `v` is nondecreasing (Theorem C, Robbins/Mono/TheoremC.lean);
* `lower_bound_of_base`: a bound `c ≤ v N` holds at every `n ≥ N`;
* `limit_lower_bound_of_base`: a bound `c ≤ v N` bounds the limit of `v n`, if it exists.

The bound `c ≤ v 300` comes from the certificate of Section 5 of the paper (the generated modules of
code/formal-proof/gen.sh) and is stated in Robbins/Main.lean.
-/

namespace Robbins

open Filter Topology

/-- The least expected rank is nondecreasing in the number of values. -/
theorem v_mono : Monotone v := v_monotone

/-- A bound at one number of values holds at every larger number. -/
theorem lower_bound_of_base {c : ℝ} {N : ℕ} (h : c ≤ v N) : ∀ n ≥ N, c ≤ v n :=
  fun _ hn => h.trans (v_mono hn)

/-- A bound at one number of values bounds the limit. -/
theorem limit_lower_bound_of_base {c : ℝ} {N : ℕ} (h : c ≤ v N) (V : ℝ) (hV : Tendsto v atTop (𝓝 V)) :
    c ≤ V :=
  ge_of_tendsto hV (eventually_atTop.mpr ⟨N, lower_bound_of_base h⟩)

end Robbins
