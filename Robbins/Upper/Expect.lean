import Robbins.Basic.Rank
import Robbins.Basic.Fubini
import Robbins.Upper.Measure
import Robbins.Upper.Rank

/-!
# The expected rank of the threshold rule is at most `5`

Integrating `rank_le_sum` bounds the expected rank by one plus the laws of the boxes
(`expectedRank_le_sum`); each is at most `survive N t * thr N t ^ 2`, and there are `N - 1` of them
per time, so `sum_le_four` concludes (`expectedRank_le_five`).
-/

namespace Robbins.Threshold

open MeasureTheory

theorem expectedRank_le_sum (n : ℕ) :
    (rule n).expectedRank ≤
      1 + ∑ t : Fin (n + 1), ∑ j ∈ Finset.univ.erase t, (law (n + 1)).real (Set.univ.pi (box (n + 1) t j)) := by
  set g := fun x : Fin (n + 1) → ℝ =>
    (1 : ℝ) + ∑ t : Fin (n + 1), ∑ j ∈ Finset.univ.erase t,
      (Set.univ.pi (box (n + 1) t j)).indicator (fun (_ : Fin (n + 1) → ℝ) => (1 : ℝ)) x
    with hg_def
  have h_meas_box (t j : Fin (n + 1)) : MeasurableSet (Set.univ.pi (box (n + 1) t j)) :=
    measurableSet_box (n + 1) t j
  have h_int_one : Integrable (fun _ : Fin (n + 1) → ℝ => (1 : ℝ)) (law (n + 1)) :=
    integrable_const _
  have h_int_indicator (t j : Fin (n + 1)) :
      Integrable ((Set.univ.pi (box (n + 1) t j)).indicator (fun (_ : Fin (n + 1) → ℝ) => (1 : ℝ)))
        (law (n + 1)) := by
    have h_meas : MeasurableSet (Set.univ.pi (box (n + 1) t j)) := h_meas_box t j
    refine ((integrableOn_const (μ := law (n + 1)) (s := Set.univ.pi (box (n + 1) t j))).integrable_indicator
      h_meas)
  have h_int_sum : Integrable (fun x : Fin (n + 1) → ℝ =>
      ∑ t : Fin (n + 1), ∑ j ∈ Finset.univ.erase t,
        (Set.univ.pi (box (n + 1) t j)).indicator (fun (_ : Fin (n + 1) → ℝ) => (1 : ℝ)) x) (law (n + 1)) := by
    refine integrable_finsetSum Finset.univ fun t ht => ?_
    refine integrable_finsetSum (Finset.univ.erase t) fun j hj => h_int_indicator t j
  have h_int_g : Integrable g (law (n + 1)) := by
    rw [hg_def]
    exact h_int_one.add h_int_sum
  have h_bound : (fun x => ((rule n).rank x : ℝ)) ≤ᵐ[law (n + 1)] g := by
    filter_upwards [ae_mem_Icc (n + 1)] with x hx
    rw [hg_def]
    exact rank_le_sum n x hx
  have h_int_sum_t (t : Fin (n + 1)) : Integrable (fun x : Fin (n + 1) → ℝ =>
      ∑ j ∈ Finset.univ.erase t, (Set.univ.pi (box (n + 1) t j)).indicator (fun (_ : Fin (n + 1) → ℝ) => (1 : ℝ)) x)
      (law (n + 1)) := by
    refine integrable_finsetSum (Finset.univ.erase t) fun j hj => h_int_indicator t j
  calc
    (rule n).expectedRank = ∫ x, ((rule n).rank x : ℝ) ∂law (n + 1) := rfl
    _ ≤ ∫ x, g x ∂law (n + 1) := integral_mono_ae (Rule.integrable_rank _) h_int_g h_bound
    _ = ∫ x, ((1 : ℝ) + ∑ t : Fin (n + 1), ∑ j ∈ Finset.univ.erase t,
          (Set.univ.pi (box (n + 1) t j)).indicator (fun (_ : Fin (n + 1) → ℝ) => (1 : ℝ)) x) ∂law (n + 1) := by
      rw [hg_def]
    _ = (∫ x, (1 : ℝ) ∂law (n + 1)) +
        (∫ x, (∑ t : Fin (n + 1), ∑ j ∈ Finset.univ.erase t,
          (Set.univ.pi (box (n + 1) t j)).indicator (fun (_ : Fin (n + 1) → ℝ) => (1 : ℝ)) x) ∂law (n + 1)) := by
      rw [integral_add h_int_one h_int_sum]
    _ = ((law (n + 1)).real Set.univ • (1 : ℝ)) +
        (∫ x, (∑ t : Fin (n + 1), ∑ j ∈ Finset.univ.erase t,
          (Set.univ.pi (box (n + 1) t j)).indicator (fun (_ : Fin (n + 1) → ℝ) => (1 : ℝ)) x) ∂law (n + 1)) := by
      rw [integral_const]
    _ = (1 : ℝ) + (∫ x, (∑ t : Fin (n + 1), ∑ j ∈ Finset.univ.erase t,
          (Set.univ.pi (box (n + 1) t j)).indicator (fun (_ : Fin (n + 1) → ℝ) => (1 : ℝ)) x) ∂law (n + 1)) := by
      have h_prob : (law (n + 1)).real Set.univ = (1 : ℝ) := by
        simp [measureReal_def, measure_univ]
      rw [h_prob, one_smul]
    _ = (1 : ℝ) + ∑ t : Fin (n + 1), (∫ x, (∑ j ∈ Finset.univ.erase t,
          (Set.univ.pi (box (n + 1) t j)).indicator (fun (_ : Fin (n + 1) → ℝ) => (1 : ℝ)) x) ∂law (n + 1)) := by
      rw [integral_finsetSum Finset.univ fun t ht => h_int_sum_t t]
    _ = (1 : ℝ) + ∑ t : Fin (n + 1), ∑ j ∈ Finset.univ.erase t,
          (∫ x, (Set.univ.pi (box (n + 1) t j)).indicator (fun (_ : Fin (n + 1) → ℝ) => (1 : ℝ)) x ∂law (n + 1)) := by
      refine congrArg (fun s => (1 : ℝ) + s) (Finset.sum_congr rfl fun t ht => ?_)
      rw [integral_finsetSum (Finset.univ.erase t) fun j hj => h_int_indicator t j]
    _ = (1 : ℝ) + ∑ t : Fin (n + 1), ∑ j ∈ Finset.univ.erase t,
          ((law (n + 1)).real (Set.univ.pi (box (n + 1) t j))) := by
      refine congrArg (fun s => (1 : ℝ) + s) (Finset.sum_congr rfl fun t ht => ?_)
      refine Finset.sum_congr rfl fun j hj => ?_
      apply integral_indicator_one
      exact h_meas_box t j
    _ = 1 + ∑ t : Fin (n + 1), ∑ j ∈ Finset.univ.erase t,
          (law (n + 1)).real (Set.univ.pi (box (n + 1) t j)) := rfl

/-- The threshold rule has expected rank at most `5`. -/
theorem expectedRank_le_five (n : ℕ) : (rule n).expectedRank ≤ 5 := by
  calc (rule n).expectedRank
      ≤ 1 + ∑ t : Fin (n + 1), ∑ j ∈ Finset.univ.erase t,
          (law (n + 1)).real (Set.univ.pi (box (n + 1) t j)) := expectedRank_le_sum n
    _ ≤ 1 + ∑ t : Fin (n + 1), ∑ _j ∈ Finset.univ.erase t,
          survive (n + 1) t * thr (n + 1) t ^ 2 := by
        gcongr with t _ j hj
        exact law_real_box_le (n + 1) t j (Finset.ne_of_mem_erase hj)
    _ = 1 + ∑ t : Fin (n + 1), (((n + 1 : ℕ) : ℝ) - 1) * survive (n + 1) t * thr (n + 1) t ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ = 1 + ∑ t ∈ Finset.range (n + 1), (((n + 1 : ℕ) : ℝ) - 1) * survive (n + 1) t * thr (n + 1) t ^ 2 := by
        rw [Fin.sum_univ_eq_sum_range
          (fun t => (((n + 1 : ℕ) : ℝ) - 1) * survive (n + 1) t * thr (n + 1) t ^ 2)]
    _ ≤ 1 + 4 := by gcongr; exact sum_le_four (n + 1)
    _ = 5 := by norm_num

end Robbins.Threshold
