import Robbins.Basic.Fubini
import Robbins.Basic.Time

/-!
# Monotonicity of `v`: definitions

Appendix A of the paper, 0-indexed. A rule `σ` for `N + 1` values is compared with rules for `N`
values: cut `[0, 1]^{N+1}` by the position `J` of the first maximal coordinate (`firstMax J`), write
a point of `firstMax J` as `Fin.insertNth J w z` with maximum `w` and other coordinates
`z ∈ belowMax J w`, scale `z = scale w y`, and simulate `σ` on `virt J w y = Fin.insertNth J w
(scale w y)` by the rule `simRule σ J w` for `N` values, which skips the inserted maximum.
-/

namespace Robbins

open MeasureTheory

/-- `scale w y = w • y`, coordinatewise. -/
def scale {N : ℕ} (w : ℝ) (y : Fin N → ℝ) : Fin N → ℝ := fun i => w * y i

/-- The points whose first maximal coordinate is `J`. -/
def firstMax {N : ℕ} (J : Fin (N + 1)) : Set (Fin (N + 1) → ℝ) :=
  {x | ∀ i, (i < J → x i < x J) ∧ (J < i → x i ≤ x J)}

/-- The other coordinates of a point of `firstMax J` with maximum `w`: below `w` before position
`J`, at most `w` from position `J` on. -/
def belowMax {N : ℕ} (J : Fin (N + 1)) (w : ℝ) : Set (Fin N → ℝ) :=
  {z | ∀ j : Fin N, ((j : ℕ) < J → z j < w) ∧ ((J : ℕ) ≤ j → z j ≤ w)}

/-- The sequence of `N + 1` values with the maximum `w` inserted at position `J` and the values
`w * y j` elsewhere. -/
noncomputable def virt {N : ℕ} (J : Fin (N + 1)) (w : ℝ) (y : Fin N → ℝ) : Fin (N + 1) → ℝ :=
  Fin.insertNth (α := fun _ => ℝ) J w (scale w y)

/-- A history of length `i + 1`, extended by zeros to a sequence of `N` values. -/
noncomputable def pad {N : ℕ} (i : Fin N) (h : Fin (i + 1) → ℝ) : Fin N → ℝ :=
  fun j => if hj : (j : ℕ) ≤ i then h ⟨j, by omega⟩ else 0

/-- The stop condition of the simulating rule at time `i`, on the sequence `y`: before `J`, `σ`
stops at time `i` on `virt J w y`; from `J` on, `σ` stops at `J` (on the inserted maximum, which the
simulation replaces by the next value) or at time `i + 1`. -/
def simCond {n : ℕ} (σ : Rule (n + 2)) (J : Fin (n + 2)) (w : ℝ) (i : Fin (n + 1))
    (y : Fin (n + 1) → ℝ) : Prop :=
  if (i : ℕ) < J then history (virt J w y) i.castSucc ∈ σ.stopSet i.castSucc
  else history (virt J w y) J ∈ σ.stopSet J ∨ history (virt J w y) i.succ ∈ σ.stopSet i.succ

theorem measurable_pad {N : ℕ} (i : Fin N) : Measurable (pad i) := by
  refine measurable_pi_iff.mpr fun j => ?_
  unfold pad
  by_cases hle : (j : ℕ) ≤ i
  · simp [hle, measurable_pi_apply (⟨j, by omega⟩ : Fin (i + 1))]
  · simp [hle]

theorem measurable_virt {N : ℕ} (J : Fin (N + 1)) (w : ℝ) :
    Measurable (virt J w : (Fin N → ℝ) → Fin (N + 1) → ℝ) := by
  unfold virt
  have h_scale : Measurable (scale w : (Fin N → ℝ) → Fin N → ℝ) := by
    unfold scale
    refine Measurable.of_eval fun i => ?_
    exact (measurable_const.mul (measurable_pi_apply i))
  have h_insertNth : Measurable (fun (y : Fin N → ℝ) => (Fin.insertNth J w y : Fin (N + 1) → ℝ)) := by
    rw [measurable_pi_iff]
    intro i
    by_cases h : i = J
    · subst h
      simp only [Fin.insertNth_apply_same]
      exact measurable_const
    · have h_exists : ∃ j, i = J.succAbove j := by
        have := Fin.exists_succAbove_eq h
        rcases this with ⟨j, hj⟩
        exact ⟨j, hj.symm⟩
      rcases h_exists with ⟨j, rfl⟩
      simp only [Fin.insertNth_apply_succAbove]
      -- Now we need: Measurable (fun y : Fin N → ℝ => y j)
      -- which is measurable_pi_apply
      exact measurable_pi_apply j
  exact h_insertNth.comp h_scale

theorem measurableSet_simCond {n : ℕ} (σ : Rule (n + 2)) (J : Fin (n + 2)) (w : ℝ)
    (i : Fin (n + 1)) : MeasurableSet {y | simCond σ J w i y} := by
  unfold simCond
  split_ifs with h
  · have hmeas : Measurable fun y : Fin (n + 1) → ℝ => history (virt J w y) i.castSucc :=
      (measurable_history i.castSucc).comp (measurable_virt J w)
    exact (σ.measurableSet_stopSet i.castSucc).preimage hmeas
  · have hmeasJ : Measurable fun y : Fin (n + 1) → ℝ => history (virt J w y) J :=
      (measurable_history J).comp (measurable_virt J w)
    have hmeasi : Measurable fun y : Fin (n + 1) → ℝ => history (virt J w y) i.succ :=
      (measurable_history i.succ).comp (measurable_virt J w)
    have hsetJ : MeasurableSet {y | history (virt J w y) J ∈ σ.stopSet J} :=
      (σ.measurableSet_stopSet J).preimage hmeasJ
    have hseti : MeasurableSet {y | history (virt J w y) i.succ ∈ σ.stopSet i.succ} :=
      (σ.measurableSet_stopSet i.succ).preimage hmeasi
    rw [Set.ofPred_or]
    exact MeasurableSet.union hsetJ hseti

/-- The rule for `n + 1` values that simulates `σ` (for `n + 2` values) with a maximum `w` inserted
at position `J`. -/
noncomputable def simRule {n : ℕ} (σ : Rule (n + 2)) (J : Fin (n + 2)) (w : ℝ) : Rule (n + 1) where
  stopSet i := {h | simCond σ J w i (pad i h)}
  measurableSet_stopSet i := measurable_pad i (measurableSet_simCond σ J w i)

end Robbins
