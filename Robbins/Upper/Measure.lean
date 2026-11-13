import Robbins.Upper.Arith

/-!
# The law of a box

The law of the values is a product measure, so the law of a box is the product of the lengths of
its sides in `[0, 1]` (`law_real_pi`); for the box of `(t, j)` this is at most
`survive N t * thr N t ^ 2` (`law_real_box_le`).
-/

namespace Robbins.Threshold

open MeasureTheory

theorem measureReal_Ioi {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Ioi a) = 1 - a := by
  rw [measureReal_def, Measure.restrict_apply measurableSet_Ioi]
  have h_eq : Set.Ioi a ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc a 1 := by
    ext x; constructor
    · rintro ⟨hx_gt, ⟨hx_ge0, hx_le1⟩⟩; exact ⟨hx_gt, hx_le1⟩
    · rintro ⟨hx_gt, hx_le1⟩; exact ⟨hx_gt, ⟨by linarith, hx_le1⟩⟩
  rw [h_eq, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - a)]

theorem measureReal_Iic {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Iic a) = a := by
  have h_eq : Set.Iic a ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) a := by
    ext x
    constructor
    · intro ⟨hx_le_a, ⟨hx_ge_0, hx_le_1⟩⟩
      exact ⟨hx_ge_0, hx_le_a⟩
    · intro ⟨hx_ge_0, hx_le_a⟩
      exact ⟨hx_le_a, ⟨hx_ge_0, le_trans hx_le_a ha1⟩⟩
  calc
    (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Iic a)
        = volume.real (Set.Iic a ∩ Set.Icc (0 : ℝ) 1) := by
      rw [MeasureTheory.measureReal_restrict_apply measurableSet_Iic]
    _ = volume.real (Set.Icc (0 : ℝ) a) := by rw [h_eq]
    _ = (volume (Set.Icc (0 : ℝ) a)).toReal := rfl
    _ = (ENNReal.ofReal (a - (0 : ℝ))).toReal := by rw [Real.volume_Icc]
    _ = (ENNReal.ofReal a).toReal := by rw [sub_zero]
    _ = a := by rw [ENNReal.toReal_ofReal ha0]

theorem measureReal_Iio {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Iio a) = a := by
  have h_eq : Set.Iio a ∩ Set.Icc (0 : ℝ) 1 = Set.Ico (0 : ℝ) a := by
    ext x
    constructor
    · intro h
      rcases h with ⟨hx_lt_a, hx_ge_0, hx_le_1⟩
      exact ⟨hx_ge_0, hx_lt_a⟩
    · intro h
      rcases h with ⟨hx_ge_0, hx_lt_a⟩
      have hx_le_1 : x ≤ 1 := le_trans (le_of_lt hx_lt_a) ha1
      exact ⟨hx_lt_a, hx_ge_0, hx_le_1⟩
  calc
    (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Iio a) =
      ((volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iio a)).toReal := by
      rw [Measure.real_def]
    _ = (volume (Set.Iio a ∩ Set.Icc (0 : ℝ) 1)).toReal := by
      rw [Measure.restrict_apply measurableSet_Iio]
    _ = (volume (Set.Ico (0 : ℝ) a)).toReal := by rw [h_eq]
    _ = (ENNReal.ofReal (a - (0 : ℝ))).toReal := by rw [Real.volume_Ico]
    _ = (ENNReal.ofReal a).toReal := by rw [sub_zero]
    _ = a := by rw [ENNReal.toReal_ofReal ha0]

theorem measureReal_Ioo_le {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) : (volume.restrict (Set.Icc (0 : ℝ) 1)).real (Set.Ioo a b) ≤ b * (1 - a) := by
  rw [measureReal_restrict_apply measurableSet_Ioo]
  calc volume.real (Set.Ioo a b ∩ Set.Icc 0 1) ≤ volume.real (Set.Ioo a b) :=
        measureReal_mono Set.inter_subset_left measure_Ioo_lt_top.ne
    _ = max (b - a) 0 := by rw [Real.volume_real_Ioo]
    _ ≤ b * (1 - a) := max_le (by nlinarith) (by nlinarith)

theorem law_real_pi (N : ℕ) (I : Fin N → Set ℝ) :
    (law N).real (Set.univ.pi I) = ∏ s, (volume.restrict (Set.Icc (0 : ℝ) 1)).real (I s) := by
  unfold law
  rw [measureReal_def, MeasureTheory.Measure.pi_pi]
  simp_rw [measureReal_def]
  rw [ENNReal.toReal_prod]

theorem prod_ite_box (N : ℕ) (t j : Fin N) (hjt : j ≠ t) (a : ℝ) (f : ℕ → ℝ) :
    ∏ s : Fin N, (if s = t then a else if s = j then (if j < t then a * f (j : ℕ) else a)
      else if s < t then f (s : ℕ) else 1) = (∏ s ∈ Finset.range (t : ℕ), f s) * a ^ 2 := by
  have h_factor (s : Fin N) : (if s = t then a else if s = j then (if j < t then a * f (j : ℕ) else a)
      else if s < t then f (s : ℕ) else 1) =
      ((if s < t then f (s : ℕ) else 1) * (if s = t then a else 1) * (if s = j then a else 1)) := by
    by_cases hst : s = t
    · subst hst
      simp [hjt.symm]
    · by_cases hsj : s = j
      · subst hsj
        by_cases hlt : s < t
        · simp [hst, hlt, mul_comm]
        · simp [hst, hlt]
      · by_cases hlt : s < t
        · simp [hst, hsj, hlt]
        · simp [hst, hsj, hlt]
  rw [Finset.prod_congr rfl (fun s _ => h_factor s)]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have h_prod_t : ∏ s : Fin N, (if s = t then a else (1 : ℝ)) = a := by
    simp
  have h_prod_j : ∏ s : Fin N, (if s = j then a else (1 : ℝ)) = a := by
    simp
  have h_prod_range : ∏ s : Fin N, (if s < t then f (s : ℕ) else (1 : ℝ)) =
      ∏ s ∈ Finset.range (t : ℕ), f s := by
    have h_eq : (fun (s : Fin N) => if s < t then f (s : ℕ) else (1 : ℝ)) =
        (fun (s : Fin N) => if (s : ℕ) < (t : ℕ) then f (s : ℕ) else (1 : ℝ)) := by
      ext s
      by_cases h : s < t
      · simp [h]
      · simp [h]
    rw [h_eq]
    rw [Fin.prod_univ_eq_prod_range (fun i => if i < (t : ℕ) then f i else (1 : ℝ)) N]
    rw [Finset.prod_ite (p := fun i => i < (t : ℕ)) (f := fun i => f i) (g := fun _ => (1 : ℝ))]
    have h_filter_eq : (Finset.range N).filter (· < (t : ℕ)) = Finset.range (t : ℕ) := by
      apply Finset.Subset.antisymm
      · intro i hi
        rw [Finset.mem_filter] at hi
        rcases hi with ⟨_, hi_lt⟩
        rw [Finset.mem_range]
        exact hi_lt
      · intro i hi
        rw [Finset.mem_range] at hi
        have hiN : i < N := lt_trans hi t.2
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨hiN, hi⟩
    rw [h_filter_eq]
    simp
  rw [h_prod_range, h_prod_t, h_prod_j]
  ring

theorem measurableSet_box (N : ℕ) (t j : Fin N) :
    MeasurableSet (Set.univ.pi (box N t j)) := by
  apply MeasurableSet.univ_pi
  intro s
  unfold box
  split_ifs with hst hst_eq_j hj_lt
  · exact measurableSet_Iic
  · exact measurableSet_Ioo
  · exact measurableSet_Iio
  · exact measurableSet_Ioi
  · exact MeasurableSet.univ

theorem law_real_box_le (N : ℕ) (t j : Fin N) (hjt : j ≠ t) :
    (law N).real (Set.univ.pi (box N t j)) ≤ survive N t * thr N t ^ 2 := by
  have hthr : ∀ s : Fin N, 0 ≤ thr N s ∧ thr N s ≤ 1 := fun s => thr_mem N s s.isLt
  rw [law_real_pi]
  calc ∏ s, (volume.restrict (Set.Icc (0 : ℝ) 1)).real (box N t j s)
      ≤ ∏ s : Fin N, (if s = t then thr N t else if s = j then
          (if j < t then thr N t * (1 - thr N j) else thr N t)
          else if s < t then 1 - thr N s else 1) := by
        refine Finset.prod_le_prod₀ (fun s _ => measureReal_nonneg) (fun s _ => ?_)
        unfold box
        split_ifs with h1 h2 h3 h4
        · exact (measureReal_Iic (hthr t).1 (hthr t).2).le
        · exact measureReal_Ioo_le (hthr j).1 (hthr j).2 (hthr t).1 (hthr t).2
        · exact (measureReal_Iio (hthr t).1 (hthr t).2).le
        · exact (measureReal_Ioi (hthr s).1 (hthr s).2).le
        · exact probReal_univ.le
    _ = survive N t * thr N t ^ 2 := prod_ite_box N t j hjt (thr N t) (fun s => 1 - thr N s)

end Robbins.Threshold
