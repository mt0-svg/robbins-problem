import Robbins.Basic.Coord

/-!
# The stop payoff

Stopping at time `t` with history `h` (values `h 0, ..., h t`, the current one `h t`) when `n - t`
values are still to come costs on average `stopPayoff n h = 1 + #{i | h i < h t} + (n - t) h t`:
each later value falls below `h t` with probability `h t`. `Rule.integral_ite_time_eq_rank` is this
fact integrated over the event that the rule stops at `t`.
-/

namespace Robbins

open MeasureTheory

/-- The expected rank of the current value `h t` when stopping at time `t` with history `h`, the
values after `t` (there are `n - t` of them, the last time being `n`) still to come. -/
noncomputable def stopPayoff (n : ℕ) {t : ℕ} (h : Fin (t + 1) → ℝ) : ℝ :=
  1 + ((Finset.univ.filter fun i => h i < h (Fin.last t)).card : ℝ) +
    ((n : ℝ) - t) * h (Fin.last t)

theorem measurable_stopPayoff (n t : ℕ) :
    Measurable fun h : Fin (t + 1) → ℝ => stopPayoff n h := by
  unfold stopPayoff
  have h_card_measurable : Measurable fun (x : Fin (t + 1) → ℝ) =>
      ((Finset.univ.filter fun i => x i < x (Fin.last t)).card : ℝ) := by
    have : (fun (x : Fin (t + 1) → ℝ) => ((Finset.univ.filter fun i => x i < x (Fin.last t)).card : ℝ)) =
        (fun (x : Fin (t + 1) → ℝ) => ∑ i : Fin (t + 1), (if x i < x (Fin.last t) then (1 : ℝ) else 0)) := by
      ext x; rw [Finset.card_filter]; simp
    rw [this]
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine Measurable.ite (measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply (Fin.last t)))
      measurable_const measurable_const
  refine Measurable.add (Measurable.add measurable_const h_card_measurable) ?_
  refine Measurable.mul measurable_const (measurable_pi_apply (Fin.last t))

theorem stopPayoff_bound (n t : ℕ) (h : Fin (t + 1) → ℝ) (hh : ∀ i, h i ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ≤ n) : |stopPayoff n h| ≤ n + 2 := by
  have hh_low : ∀ i, 0 ≤ h i := fun i => (hh i).1
  have hh_high : ∀ i, h i ≤ 1 := fun i => (hh i).2
  have hlast_low : 0 ≤ h (Fin.last t) := hh_low _
  have hlast_high : h (Fin.last t) ≤ 1 := hh_high _
  have hcard_nonneg : 0 ≤ ((Finset.univ.filter fun i => h i < h (Fin.last t)).card : ℝ) :=
    Nat.cast_nonneg _
  have hcard_le : ((Finset.univ.filter fun i => h i < h (Fin.last t)).card : ℝ) ≤ (t : ℝ) + 1 := by
    have hcard_univ : (Finset.univ : Finset (Fin (t + 1))).card = t + 1 := by simp
    have hle : (Finset.univ.filter fun i => h i < h (Fin.last t)).card ≤ (Finset.univ : Finset (Fin (t + 1))).card :=
      Finset.card_le_univ _
    have h' : (Finset.univ.filter fun i => h i < h (Fin.last t)).card ≤ t + 1 := by
      linarith
    exact mod_cast h'
  have hprod_nonneg : 0 ≤ ((n : ℝ) - (t : ℝ)) * h (Fin.last t) := by
    have hnonneg : 0 ≤ (n : ℝ) - (t : ℝ) := by
      have : (t : ℝ) ≤ (n : ℝ) := by exact mod_cast ht
      linarith
    nlinarith
  have hprod_le : ((n : ℝ) - (t : ℝ)) * h (Fin.last t) ≤ (n : ℝ) - (t : ℝ) := by
    have hnonneg : 0 ≤ (n : ℝ) - (t : ℝ) := by
      have : (t : ℝ) ≤ (n : ℝ) := by exact mod_cast ht
      linarith
    nlinarith
  rw [stopPayoff]
  have hpos : 0 ≤ 1 + ((Finset.univ.filter fun i => h i < h (Fin.last t)).card : ℝ) + ((n : ℝ) - (t : ℝ)) * h (Fin.last t) := by
    nlinarith
  rw [abs_of_nonneg hpos]
  nlinarith

theorem card_Ioi_fin (n : ℕ) (t : Fin (n + 1)) : ((Finset.Ioi t).card : ℝ) = n - t := by
  have h := Fin.card_Ioi t
  have hle : (t : ℕ) ≤ n := by omega
  calc
    ((Finset.Ioi t).card : ℝ) = (((n + 1) - 1 - (t : ℕ) : ℕ) : ℝ) := by simp [h]
    _ = (n : ℝ) - ((t : ℕ) : ℝ) := by
      simp [show ((n + 1 : ℕ) - 1) = n by omega, Nat.cast_sub hle]
    _ = n - t := by simp

theorem Rule.rank_eq_of_time_eq {n : ℕ} (r : Rule (n + 1)) (x : Fin (n + 1) → ℝ)
    (t : Fin (n + 1)) (h : r.time x = t) :
    (r.rank x : ℝ) = 1 + ((Finset.univ.filter fun i => history x t i < history x t (Fin.last t)).card : ℝ)
      + ∑ j ∈ Finset.Ioi t, (if x j < x t then (1 : ℝ) else 0) := by
  classical
  have hlast : history x t (Fin.last t) = x t := by
    simp only [history]
    congr 1
  have hcard : (Finset.univ.filter fun i : Fin (t + 1) =>
      history x t i < history x t (Fin.last t)).card =
      ((Finset.Iic t).filter fun j => x j < x t).card := by
    rw [hlast]
    apply Finset.card_bij (fun i _ => Fin.castLE t.isLt i)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic] at hi ⊢
      refine ⟨?_, hi⟩
      rw [Fin.le_def, Fin.val_castLE]
      omega
    · intro i _ j _ hij
      exact Fin.castLE_injective _ hij
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_Iic] at hj
      have hjt : (j : ℕ) < t + 1 := by rw [Fin.le_def] at hj; omega
      refine ⟨⟨j, hjt⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hc : Fin.castLE t.isLt ⟨j, hjt⟩ = j := Fin.ext rfl
        show x (Fin.castLE t.isLt ⟨j, hjt⟩) < x t
        rw [hc]
        exact hj.2
      · ext
        simp
  have hsplit : (Finset.univ.filter fun j => x j < x t) =
      ((Finset.Iic t).filter fun j => x j < x t) ∪ ((Finset.Ioi t).filter fun j => x j < x t) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_Iic,
      Finset.mem_Ioi]
    constructor
    · intro hj
      rcases le_or_gt j t with h1 | h1
      · exact Or.inl ⟨h1, hj⟩
      · exact Or.inr ⟨h1, hj⟩
    · rintro (⟨_, hj⟩ | ⟨_, hj⟩) <;> exact hj
  have hdisj : Disjoint ((Finset.Iic t).filter fun j => x j < x t)
      ((Finset.Ioi t).filter fun j => x j < x t) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioi] at h1 h2
    exact absurd h1.1 (not_le.mpr h2.1)
  unfold Rule.rank
  rw [h, hsplit, Finset.card_union_of_disjoint hdisj, hcard, Finset.sum_boole]
  push_cast
  ring

theorem Rule.integral_ite_time_eq_rank {n : ℕ} (r : Rule (n + 1)) (t : Fin (n + 1)) :
    ∫ x, (if r.time x = t then (r.rank x : ℝ) else 0) ∂law (n + 1) =
      ∫ x, (if r.time x = t then stopPayoff n (history x t) else 0) ∂law (n + 1) := by
  set F := fun x : Fin (n + 1) → ℝ => if r.time x = t then (1 : ℝ) else 0 with hF_def
  have hF_measSet : MeasurableSet {x | r.time x = t} := Rule.measurableSet_time_eq r t
  have hF_meas : Measurable F := by
    -- F is the indicator of the measurable set {x | r.time x = t}
    have : F = ({x | r.time x = t} : Set (Fin (n + 1) → ℝ)).indicator (fun _ => (1 : ℝ)) := by
      ext x
      dsimp [F, Set.indicator]
      by_cases h : r.time x = t
      · simp [h]
      · simp [h]
    rw [this]
    exact Measurable.indicator measurable_const hF_measSet
  have hF_bound : ∀ x, |F x| ≤ 1 := by
    intro x
    dsimp [F]
    split
    · simp
    · simp
  have hF_int : Integrable F (law (n + 1)) := by
    refine MeasureTheory.Integrable.of_bound hF_meas.aestronglyMeasurable 1 ?_
    filter_upwards with x
    simpa using hF_bound x
  have hF_update (j : Fin (n + 1)) (hjt : t < j) (a : ℝ) (x : Fin (n + 1) → ℝ) : F (Function.update x j a) = F x := by
    dsimp [F]
    by_cases h : r.time x = t
    · have h_eq : r.time (Function.update x j a) = t := by
        rw [Rule.time_update_eq_iff r x t j a hjt, h]
      simp [h, h_eq]
    · have h_ne : r.time (Function.update x j a) ≠ t :=
        mt ((Rule.time_update_eq_iff r x t j a hjt).mp) h
      simp [h, h_ne]
  have h_last (x : Fin (n + 1) → ℝ) : history x t (Fin.last t) = x t := by
    dsimp [history]
    have : Fin.castLE t.isLt (Fin.last t) = t := by
      ext
      simp
    simp [this]
  have h_stop_decomp (x : Fin (n + 1) → ℝ) : stopPayoff n (history x t) =
      1 + ((Finset.univ.filter fun i => history x t i < history x t (Fin.last t)).card : ℝ) +
        ∑ j ∈ Finset.Ioi t, x t := by
    dsimp [stopPayoff]
    rw [h_last x]
    have hcard : ((Finset.Ioi t).card : ℝ) = (n : ℝ) - (t : ℝ) := by
      simpa using card_Ioi_fin n t
    rw [← hcard]
    simp [Finset.sum_const]
  have hL_decomp (x : Fin (n + 1) → ℝ) : (if r.time x = t then (r.rank x : ℝ) else 0) =
      F x * (1 + ((Finset.univ.filter fun i => history x t i < history x t (Fin.last t)).card : ℝ)) +
        ∑ j ∈ Finset.Ioi t, F x * (if x j < x t then (1 : ℝ) else 0) := by
    dsimp [F]
    by_cases h : r.time x = t
    · simp [h, Rule.rank_eq_of_time_eq r x t h]
    · simp [h]
  have hR_decomp (x : Fin (n + 1) → ℝ) : (if r.time x = t then stopPayoff n (history x t) else 0) =
      F x * (1 + ((Finset.univ.filter fun i => history x t i < history x t (Fin.last t)).card : ℝ)) +
        ∑ j ∈ Finset.Ioi t, F x * x t := by
    dsimp [F]
    by_cases h : r.time x = t
    · simp [h, h_stop_decomp x]
    · simp [h]
  have h_meas_ite (j : Fin (n + 1)) : Measurable (fun x : Fin (n + 1) → ℝ => if x j < x t then (1 : ℝ) else 0) := by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply t)
  have h_bound_ite (j : Fin (n + 1)) : ∀ᵐ x ∂law (n + 1), |(if x j < x t then (1 : ℝ) else 0)| ≤ 1 := by
    filter_upwards with x
    split <;> simp
  have h_bound_xt : ∀ᵐ x ∂law (n + 1), |x t| ≤ 1 := by
    have h := ae_mem_Icc (n + 1)
    filter_upwards [h] with x hx
    have hx_t := hx t
    rcases hx_t with ⟨hlo, hhi⟩
    have h_right : x t ≤ 1 := hhi
    have h_left : -1 ≤ x t := by linarith
    simpa [abs_le] using ⟨h_left, h_right⟩
  have h_int_ite (j : Fin (n + 1)) : Integrable (fun x => F x * (if x j < x t then (1 : ℝ) else 0)) (law (n + 1)) := by
    have := hF_int.bdd_mul (h_meas_ite j).aestronglyMeasurable (h_bound_ite j)
    simpa [mul_comm] using this
  have h_int_xt : Integrable (fun x => F x * x t) (law (n + 1)) := by
    have := hF_int.bdd_mul (measurable_pi_apply t).aestronglyMeasurable h_bound_xt
    simpa [mul_comm] using this
  have h_int_sum_L : Integrable (fun x => ∑ j ∈ Finset.Ioi t, F x * (if x j < x t then (1 : ℝ) else 0)) (law (n + 1)) :=
    integrable_finset_sum _ fun j hj => h_int_ite j
  have h_int_sum_R : Integrable (fun x => ∑ j ∈ Finset.Ioi t, F x * x t) (law (n + 1)) :=
    integrable_finset_sum _ fun j hj => h_int_xt
  have h_int_sum : ∫ x, (∑ j ∈ Finset.Ioi t, F x * (if x j < x t then (1 : ℝ) else 0)) ∂law (n + 1) =
      ∫ x, (∑ j ∈ Finset.Ioi t, F x * x t) ∂law (n + 1) := by
    calc
      ∫ x, (∑ j ∈ Finset.Ioi t, F x * (if x j < x t then (1 : ℝ) else 0)) ∂law (n + 1)
          = ∑ j ∈ Finset.Ioi t, ∫ x, F x * (if x j < x t then (1 : ℝ) else 0) ∂law (n + 1) := by
        rw [integral_finset_sum]
        intro j hj
        exact h_int_ite j
      _ = ∑ j ∈ Finset.Ioi t, ∫ x, F x * x t ∂law (n + 1) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjt : t < j := Finset.mem_Ioi.mp hj
        have h_ne : j ≠ t := hjt.ne.symm
        rw [integral_mul_ite_lt F hF_int j t h_ne (fun x a => hF_update j hjt a x)]
      _ = ∫ x, (∑ j ∈ Finset.Ioi t, F x * x t) ∂law (n + 1) := by
        rw [integral_finset_sum]
        intro j hj
        exact h_int_xt
  -- Now relate the original integrals to the decomposed ones
  have h_int_L : ∫ x, (if r.time x = t then (r.rank x : ℝ) else 0) ∂law (n + 1) =
      ∫ x, (F x * (1 + ((Finset.univ.filter fun i => history x t i < history x t (Fin.last t)).card : ℝ)) +
        ∑ j ∈ Finset.Ioi t, F x * (if x j < x t then (1 : ℝ) else 0)) ∂law (n + 1) := by
    refine integral_congr_ae (ae_of_all _ hL_decomp)
  have h_int_R : ∫ x, (if r.time x = t then stopPayoff n (history x t) else 0) ∂law (n + 1) =
      ∫ x, (F x * (1 + ((Finset.univ.filter fun i => history x t i < history x t (Fin.last t)).card : ℝ)) +
        ∑ j ∈ Finset.Ioi t, F x * x t) ∂law (n + 1) := by
    refine integral_congr_ae (ae_of_all _ hR_decomp)
  rw [h_int_L, h_int_R]
  -- Now we need to show the two decomposed integrals are equal
  -- Both are of the form ∫ (F x * (1+card) + sum)
  -- The first terms are identical, the sums differ but have equal integrals by h_int_sum
  -- We use the fact that F * (1+card) is integrable (F is integrable, 1+card is bounded and measurable)
  set B := fun x : Fin (n + 1) → ℝ => 1 + ((Finset.univ.filter fun i => history x t i < history x t (Fin.last t)).card : ℝ) with hB_def
  have hB_meas : AEStronglyMeasurable B (law (n + 1)) := by
    have h_meas_hist : Measurable fun x : Fin (n + 1) → ℝ => history x t :=
      measurable_history t
    have h_meas_card : Measurable (fun x : Fin (n + 1) → ℝ => ((Finset.univ.filter fun i => history x t i < history x t (Fin.last t)).card : ℝ)) := by
      -- The card is ∑ i, (if history x t i < history x t (Fin.last t) then 1 else 0)
      have h_eq : (fun x : Fin (n + 1) → ℝ => ((Finset.univ.filter fun i => history x t i < history x t (Fin.last t)).card : ℝ)) =
          (fun x => ∑ i : Fin (t + 1), (if history x t i < history x t (Fin.last t) then (1 : ℝ) else 0)) := by
        ext x
        simp
      rw [h_eq]
      refine Finset.measurable_sum _ fun i hi => ?_
      have h_meas_i : Measurable (fun x : Fin (n + 1) → ℝ => history x t i) :=
        (measurable_pi_apply i).comp h_meas_hist
      have h_meas_last : Measurable (fun x : Fin (n + 1) → ℝ => history x t (Fin.last t)) :=
        (measurable_pi_apply (Fin.last t)).comp h_meas_hist
      have h_meas_lt : MeasurableSet {x : Fin (n + 1) → ℝ | history x t i < history x t (Fin.last t)} :=
        measurableSet_lt h_meas_i h_meas_last
      exact Measurable.ite h_meas_lt measurable_const measurable_const
    have h_meas_B : Measurable B := by
      dsimp [B]
      refine Measurable.add measurable_const h_meas_card
    exact h_meas_B.aestronglyMeasurable
  have hB_bound : ∀ᵐ x ∂law (n + 1), ‖B x‖ ≤ (n + 2 : ℝ) := by
    filter_upwards with x
    dsimp [B]
    have h_card : ((Finset.univ.filter fun i => history x t i < history x t (Fin.last t)).card : ℝ) ≤ (t : ℝ) + 1 := by
      -- The filter is a subset of Finset.univ, so its card ≤ card(univ) = t.val + 1
      have : ((Finset.univ.filter fun i => history x t i < history x t (Fin.last t)).card : ℝ) ≤
          (Finset.univ : Finset (Fin (t + 1))).card := by
        exact mod_cast Finset.card_filter_le _ _
      simpa [Finset.card_fin (t + 1)] using this
    have h_card_nonneg : 0 ≤ ((Finset.univ.filter fun i => history x t i < history x t (Fin.last t)).card : ℝ) := by
      exact mod_cast Nat.zero_le _
    have : |1 + ((Finset.univ.filter fun i => history x t i < history x t (Fin.last t)).card : ℝ)| ≤ (n + 2 : ℝ) := by
      have hle : ((Finset.univ.filter fun i => history x t i < history x t (Fin.last t)).card : ℝ) ≤ (n : ℝ) + 1 := by
        -- t.val + 1 ≤ n + 1
        have h_t_le_n : (t : ℝ) + 1 ≤ (n : ℝ) + 1 := by
          have : (t : ℕ) < n + 1 := t.is_lt
          exact mod_cast (by omega)
        linarith
      have h_nonneg : 0 ≤ 1 + ((Finset.univ.filter fun i => history x t i < history x t (Fin.last t)).card : ℝ) := by linarith
      rw [abs_of_nonneg h_nonneg]
      linarith
    simpa using this
  have hB_int : Integrable (fun x => F x * B x) (law (n + 1)) := by
    have := hF_int.bdd_mul hB_meas hB_bound
    simpa [mul_comm] using this
  calc
    ∫ x, (F x * B x + ∑ j ∈ Finset.Ioi t, F x * (if x j < x t then (1 : ℝ) else 0)) ∂law (n + 1)
        = (∫ x, F x * B x ∂law (n + 1)) + (∫ x, (∑ j ∈ Finset.Ioi t, F x * (if x j < x t then (1 : ℝ) else 0)) ∂law (n + 1)) := by
      rw [integral_add hB_int h_int_sum_L]
    _ = (∫ x, F x * B x ∂law (n + 1)) + (∫ x, (∑ j ∈ Finset.Ioi t, F x * x t) ∂law (n + 1)) := by rw [h_int_sum]
    _ = ∫ x, (F x * B x + ∑ j ∈ Finset.Ioi t, F x * x t) ∂law (n + 1) := by
      rw [integral_add hB_int h_int_sum_R]

end Robbins
