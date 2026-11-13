import Robbins.Basic.Time
import Robbins.Upper.Defs

/-!
# The rank of the threshold rule, pointwise

On `[0, 1]^(n + 1)`, if the rule stops at `t`, every value `x j < x t` puts `x` in the box of `(t, j)`:
the rank is at most one plus the number of boxes that contain `x` (`rank_le_sum`).
-/

namespace Robbins.Threshold

open MeasureTheory

theorem history_last {n : ℕ} (x : Fin n → ℝ) (t : Fin n) : history x t (Fin.last t) = x t := by
  simp only [history]
  congr 1

theorem thr_last (n : ℕ) : thr (n + 1) n = 1 := by
  unfold thr
  push_cast
  norm_num

/-- The selected value is at most its threshold. -/
theorem le_thr_time (n : ℕ) (x : Fin (n + 1) → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    x ((rule n).time x) ≤ thr (n + 1) ((rule n).time x) := by
  rcases (rule n).mem_or_last_time x with h | h
  · have h' : history x ((rule n).time x) (Fin.last _) ≤ thr (n + 1) ((rule n).time x) := h
    rwa [history_last] at h'
  · rw [h, Fin.val_last, thr_last]
    exact (hx _).2

/-- The values before the selected time are above their thresholds. -/
theorem thr_lt_of_lt_time (n : ℕ) (x : Fin (n + 1) → ℝ) (s : Fin (n + 1)) (hs : s < (rule n).time x) :
    thr (n + 1) s < x s := by
  have h := (rule n).not_mem_of_lt_time x s hs
  have h' : ¬ history x s (Fin.last s) ≤ thr (n + 1) s := h
  rw [history_last] at h'
  exact lt_of_not_ge h'

theorem mem_box (n : ℕ) (x : Fin (n + 1) → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) (j : Fin (n + 1))
    (hj : x j < x ((rule n).time x)) : x ∈ Set.univ.pi (box (n + 1) ((rule n).time x) j) := by
  set τ := (rule n).time x with hτ
  have hτle : x τ ≤ thr (n + 1) τ := le_thr_time n x hx
  intro s _
  unfold box
  split_ifs with h1 h2 h3 h4
  · rw [h1]; exact hτle
  · subst h2
    exact ⟨thr_lt_of_lt_time n x s h3, hj.trans_le hτle⟩
  · subst h2
    exact hj.trans_le hτle
  · exact thr_lt_of_lt_time n x s h4
  · exact Set.mem_univ _

/-- The rank of the threshold rule is at most one plus the number of boxes containing `x`. -/
theorem rank_le_sum (n : ℕ) (x : Fin (n + 1) → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    ((rule n).rank x : ℝ) ≤ 1 + ∑ t : Fin (n + 1), ∑ j ∈ Finset.univ.erase t,
      (Set.univ.pi (box (n + 1) t j)).indicator 1 x := by
  classical
  set τ := (rule n).time x with hτ
  have hcard : ((Finset.univ.filter fun j => x j < x τ).card : ℝ) ≤
      ∑ j ∈ Finset.univ.erase τ, (Set.univ.pi (box (n + 1) τ j)).indicator 1 x := by
    have hsub : (Finset.univ.filter fun j => x j < x τ) ⊆ Finset.univ.erase τ := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact Finset.mem_erase.mpr ⟨fun h => lt_irrefl (x τ) (by rw [h] at hj; exact hj), Finset.mem_univ _⟩
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    calc ∑ j ∈ Finset.univ.filter (fun j => x j < x τ), (1 : ℝ)
        = ∑ j ∈ Finset.univ.filter (fun j => x j < x τ),
            (Set.univ.pi (box (n + 1) τ j)).indicator 1 x := by
          refine Finset.sum_congr rfl fun j hj => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rw [Set.indicator_of_mem (mem_box n x hx j hj)]
          rfl
      _ ≤ ∑ j ∈ Finset.univ.erase τ, (Set.univ.pi (box (n + 1) τ j)).indicator 1 x :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ =>
            Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hsingle : ∑ j ∈ Finset.univ.erase τ, (Set.univ.pi (box (n + 1) τ j)).indicator 1 x ≤
      ∑ t : Fin (n + 1), ∑ j ∈ Finset.univ.erase t, (Set.univ.pi (box (n + 1) t j)).indicator 1 x :=
    Finset.single_le_sum (f := fun t => ∑ j ∈ Finset.univ.erase t,
        (Set.univ.pi (box (n + 1) t j)).indicator (1 : (Fin (n + 1) → ℝ) → ℝ) x)
      (fun t _ => Finset.sum_nonneg fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
      (Finset.mem_univ τ)
  unfold Rule.rank
  push_cast
  linarith

end Robbins.Threshold
