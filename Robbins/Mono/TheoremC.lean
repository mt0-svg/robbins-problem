import Robbins.Mono.Compare

/-!
# Theorem C: `v` is nondecreasing

Theorem 2.3 of the paper (Appendix A). For a rule `σ` for `n + 2` values, the integral of its rank over the
points whose first maximum `w` is at `J` is `∫_0^1 F_J(w) dw` with
`F_J(w) = ∫ 1{z ∈ belowMax J w} rank(insertNth J w z) dz = w ^ (n + 1) ∫_{belowMax J 1} rank(virt J w y) dy`
(`sliceIntegral_eq`), and `rank(virt J w y) ≥ rank of simRule σ J w at y` almost everywhere, so
`F_J(w) ≥ w ^ (n + 1) v (n + 1)`; summing over `J` and integrating `(n + 2) w ^ (n + 1)` gives
`σ.expectedRank ≥ v (n + 1)`.
-/

namespace Robbins

open MeasureTheory

/-- The integral `F_J(w)` of the rank of `σ` over the slice of `firstMax J` with maximum `w`. -/
noncomputable def sliceIntegral {n : ℕ} (σ : Rule (n + 2)) (J : Fin (n + 2)) (w : ℝ) : ℝ :=
  ∫ z, (belowMax J w).indicator
    (fun z => (σ.rank (Fin.insertNth (α := fun _ => ℝ) J w z) : ℝ)) z ∂law (n + 1)

theorem measurable_insertNth {N : ℕ} (J : Fin (N + 1)) (w : ℝ) :
    Measurable fun z : Fin N → ℝ => Fin.insertNth (α := fun _ => ℝ) J w z := by
  have h := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) J).symm.measurable.comp
    (measurable_const.prodMk measurable_id : Measurable fun z : Fin N → ℝ => (w, z))
  convert h using 1
  funext z
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

theorem Rule.integrable_rank_comp {n N : ℕ} (σ : Rule (n + 1)) {φ : (Fin N → ℝ) → Fin (n + 1) → ℝ}
    (hφ : Measurable φ) : Integrable (fun y => (σ.rank (φ y) : ℝ)) (law N) := by
  refine Integrable.of_bound ((σ.measurable_rank).comp hφ).aestronglyMeasurable (n + 1 : ℝ)
    (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast σ.rank_le (φ y)

theorem indicator_firstMax_insertNth {N : ℕ} (J : Fin (N + 1)) (w : ℝ)
    (f : (Fin (N + 1) → ℝ) → ℝ) (z : Fin N → ℝ) :
    (firstMax J).indicator f (Fin.insertNth (α := fun _ => ℝ) J w z) =
      (belowMax J w).indicator (fun z => f (Fin.insertNth (α := fun _ => ℝ) J w z)) z := by
  by_cases hz : z ∈ belowMax J w
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((insertNth_mem_firstMax J w z).mpr hz)]
  · rw [Set.indicator_of_notMem hz,
      Set.indicator_of_notMem (fun h => hz ((insertNth_mem_firstMax J w z).mp h))]

theorem le_integral_virt {n : ℕ} (σ : Rule (n + 2)) (J : Fin (n + 2)) {w : ℝ} (hw0 : 0 < w) :
    v (n + 1) ≤
      ∫ y, (belowMax J 1).indicator (fun y => (σ.rank (virt J w y) : ℝ)) y ∂law (n + 1) := by
  refine (v_succ_le (simRule σ J w)).trans ?_
  unfold Rule.expectedRank
  refine integral_mono_ae (simRule σ J w).integrable_rank
    ((σ.integrable_rank_comp (measurable_virt J w)).indicator (measurableSet_belowMax J 1)) ?_
  filter_upwards [ae_ne_one (n + 1), ae_mem_Icc (n + 1)] with y h1 h2
  have hy : ∀ j, y j < 1 := fun j => lt_of_le_of_ne (h2 j).2 (h1 j)
  rw [Set.indicator_of_mem (mem_belowMax_one J hy)]
  exact_mod_cast rank_simRule_le σ J hw0 y hy

theorem sliceIntegral_eq {n : ℕ} (σ : Rule (n + 2)) (J : Fin (n + 2)) {w : ℝ} (hw0 : 0 < w)
    (hw1 : w ≤ 1) :
    sliceIntegral σ J w = w ^ (n + 1) *
      ∫ y, (belowMax J 1).indicator (fun y => (σ.rank (virt J w y) : ℝ)) y ∂law (n + 1) := by
  have hg : Measurable ((belowMax J w).indicator
      (fun z => (σ.rank (Fin.insertNth (α := fun _ => ℝ) J w z) : ℝ))) :=
    ((σ.measurable_rank).comp (measurable_insertNth J w)).indicator (measurableSet_belowMax J w)
  unfold sliceIntegral
  rw [integral_scale hw0 hw1 _ hg fun z hz => le_of_mem_belowMax (Set.mem_of_indicator_ne_zero hz)]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only
  by_cases hy : y ∈ belowMax J 1
  · rw [Set.indicator_of_mem ((scale_mem_belowMax J hw0 y).mpr hy), Set.indicator_of_mem hy]
    rfl
  · rw [Set.indicator_of_notMem (fun h => hy ((scale_mem_belowMax J hw0 y).mp h)),
      Set.indicator_of_notMem hy]

theorem le_sliceIntegral {n : ℕ} (σ : Rule (n + 2)) (J : Fin (n + 2)) {w : ℝ}
    (hw : w ∈ Set.Icc (0 : ℝ) 1) : w ^ (n + 1) * v (n + 1) ≤ sliceIntegral σ J w := by
  rcases eq_or_lt_of_le hw.1 with h0 | h0
  · subst h0
    rw [zero_pow (Nat.succ_ne_zero n), zero_mul]
    exact integral_nonneg fun z => Set.indicator_nonneg (fun _ _ => Nat.cast_nonneg _) z
  · rw [sliceIntegral_eq σ J h0 hw.2]
    exact mul_le_mul_of_nonneg_left (le_integral_virt σ J h0) (pow_nonneg hw.1 _)

theorem integral_firstMax_eq {n : ℕ} (σ : Rule (n + 2)) (J : Fin (n + 2)) :
    ∫ x, (firstMax J).indicator (fun x => (σ.rank x : ℝ)) x ∂law (n + 2) =
      ∫ w in Set.Icc (0 : ℝ) 1, sliceIntegral σ J w := by
  rw [integral_law_succ_insertNth J _ (σ.integrable_rank.indicator (measurableSet_firstMax J))]
  unfold sliceIntegral
  simp_rw [indicator_firstMax_insertNth]

theorem integrableOn_sliceIntegral {n : ℕ} (σ : Rule (n + 2)) (J : Fin (n + 2)) :
    Integrable (fun w => sliceIntegral σ J w) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have h := integrable_integral_insertNth J _
    (σ.integrable_rank.indicator (measurableSet_firstMax J))
  unfold sliceIntegral
  simp_rw [indicator_firstMax_insertNth] at h
  exact h

theorem Rule.expectedRank_eq_sum_firstMax {n : ℕ} (σ : Rule (n + 2)) :
    σ.expectedRank = ∑ J, ∫ x, (firstMax J).indicator (fun x => (σ.rank x : ℝ)) x ∂law (n + 2) := by
  unfold Rule.expectedRank
  rw [← integral_finset_sum _ fun J _ => σ.integrable_rank.indicator (measurableSet_firstMax J)]
  exact integral_congr_ae (ae_of_all _ fun x =>
    (sum_indicator_firstMax (fun x => (σ.rank x : ℝ)) x).symm)

/-- Theorem C for one rule: a rule for `n + 2` values has expected rank at least `v (n + 1)`. -/
theorem Rule.v_le_expectedRank {n : ℕ} (σ : Rule (n + 2)) : v (n + 1) ≤ σ.expectedRank := by
  rw [Robbins.Rule.expectedRank_eq_sum_firstMax]
  simp_rw [Robbins.integral_firstMax_eq]
  have hc : Integrable (fun w : ℝ => w ^ (n + 1) * v (n + 1)) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ((continuous_pow (n + 1)).mul continuous_const).integrableOn_Icc
  have hJ : ∀ J : Fin (n + 2), (∫ w in Set.Icc (0 : ℝ) 1, w ^ (n + 1) * v (n + 1)) ≤
      ∫ w in Set.Icc (0 : ℝ) 1, sliceIntegral σ J w := fun J =>
    setIntegral_mono_on hc (Robbins.integrableOn_sliceIntegral σ J) measurableSet_Icc
      fun w hw => Robbins.le_sliceIntegral σ J hw
  have hI : (∫ w in Set.Icc (0 : ℝ) 1, w ^ (n + 1) * v (n + 1)) = v (n + 1) / ((n : ℝ) + 2) := by
    rw [integral_mul_const, integral_Icc_pow]
    push_cast
    ring
  calc v (n + 1) = ∑ _J : Fin (n + 2), v (n + 1) / ((n : ℝ) + 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp
    _ ≤ _ := Finset.sum_le_sum fun J _ => hI ▸ hJ J

/-- Theorem C. -/
theorem v_succ_le_v_succ_succ (n : ℕ) : v (n + 1) ≤ v (n + 2) :=
  le_v_succ fun σ => σ.v_le_expectedRank

/-- `v` is nondecreasing. -/
theorem v_monotone : Monotone v := by
  refine monotone_nat_of_le_succ fun n => ?_
  cases n with
  | zero => exact (one_le_v_succ 0).trans' (by simp [v])
  | succ n => exact v_succ_le_v_succ_succ n

end Robbins
