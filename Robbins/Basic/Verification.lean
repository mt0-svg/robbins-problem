import Robbins.Basic.Payoff

/-!
# The verification lemma

Functions `L k` of the first `k` values (`k = 0, ..., n + 1`) with
* (V1) `L (t + 1) h ≤ stopPayoff n h` for every history `h` of `t + 1 ≤ n + 1` values in `[0, 1]`,
* (V2) `L k h ≤ ∫ a in [0, 1], L (k + 1) (h, a)` for every `h` of `k ≤ n` values in `[0, 1]`,
give `L 0 ≤ r.expectedRank` for every rule `r` for `n + 1` values, hence `L 0 ≤ v (n + 1)`
(Lemma 3.1 of the paper). Proof: the quantities
`E k = ∫ (if time < k then rank else L k (first k values))` increase with `k`, from `E 0 = L 0` to
`E (n + 1) = expectedRank`.
-/

namespace Robbins

open MeasureTheory

/-- One step of the verification lemma: the quantity `∫ (if time < k then rank else L k (first k
values))` does not decrease from `k` to `k + 1`. -/
theorem Rule.verification_step {n : ℕ} (r : Rule (n + 1)) (L : (k : ℕ) → (Fin k → ℝ) → ℝ)
    (hL : ∀ k ≤ n + 1, Measurable (L k))
    (hLb : ∀ k ≤ n + 1, ∃ C, ∀ h : Fin k → ℝ, (∀ i, h i ∈ Set.Icc (0 : ℝ) 1) → |L k h| ≤ C)
    (hV1 : ∀ (t : ℕ) (h : Fin (t + 1) → ℝ), t ≤ n → (∀ i, h i ∈ Set.Icc (0 : ℝ) 1) →
      L (t + 1) h ≤ stopPayoff n h)
    (hV2 : ∀ (k : ℕ) (h : Fin k → ℝ), k ≤ n → (∀ i, h i ∈ Set.Icc (0 : ℝ) 1) →
      L k h ≤ ∫ a in Set.Icc (0 : ℝ) 1, L (k + 1) (Fin.snoc (α := fun _ => ℝ) h a))
    (k : ℕ) (hkn : k ≤ n) :
    ∫ x, (if (r.time x : ℕ) < k then (r.rank x : ℝ)
      else if hk : k ≤ n + 1 then L k (Fin.take k hk x) else 0) ∂law (n + 1) ≤
    ∫ x, (if (r.time x : ℕ) < k + 1 then (r.rank x : ℝ)
      else if hk : k + 1 ≤ n + 1 then L (k + 1) (Fin.take (k + 1) hk x) else 0) ∂law (n + 1) := by
  classical
  have hkN : k < n + 1 := by omega
  have hk0 : k ≤ n + 1 := hkN.le
  have hk1 : k + 1 ≤ n + 1 := hkN
  have hA : MeasurableSet {x : Fin (n + 1) → ℝ | (r.time x : ℕ) < k} := r.measurableSet_time_lt k
  have hB : MeasurableSet {x : Fin (n + 1) → ℝ | r.time x = ⟨k, hkN⟩} :=
    r.measurableSet_time_eq ⟨k, hkN⟩
  have hC : MeasurableSet {x : Fin (n + 1) → ℝ | k + 1 ≤ (r.time x : ℕ)} :=
    r.measurableSet_le_time (k + 1)
  have hD : MeasurableSet {x : Fin (n + 1) → ℝ | k ≤ (r.time x : ℕ)} := r.measurableSet_le_time k
  have hR : Integrable (fun x => (r.rank x : ℝ)) (law (n + 1)) := r.integrable_rank
  have hLk : Integrable (fun x : Fin (n + 1) → ℝ => L k (Fin.take k hk0 x)) (law (n + 1)) :=
    integrable_comp_take k hk0 (L k) (hL k hk0) (hLb k hk0)
  have hLk1 : Integrable (fun x : Fin (n + 1) → ℝ => L (k + 1) (Fin.take (k + 1) hkN x))
      (law (n + 1)) :=
    integrable_comp_take (k + 1) hkN (L (k + 1)) (hL (k + 1) hk1) (hLb (k + 1) hk1)
  have hP : Integrable (fun x : Fin (n + 1) → ℝ => stopPayoff n (history x ⟨k, hkN⟩))
      (law (n + 1)) :=
    integrable_comp_take (k + 1) hkN (fun h => stopPayoff n h) (measurable_stopPayoff n k)
      ⟨n + 2, fun h hh => stopPayoff_bound n k h hh hkn⟩
  have hM : Integrable (fun x : Fin (n + 1) → ℝ => ∫ a in Set.Icc (0 : ℝ) 1,
      L (k + 1) (Fin.snoc (α := fun _ => ℝ) (Fin.take k hkN.le x) a)) (law (n + 1)) :=
    integrable_integral_snoc_take k hkN (L (k + 1)) (hL (k + 1) hk1) (hLb (k + 1) hk1)
  have hteq : ∀ x : Fin (n + 1) → ℝ, r.time x = ⟨k, hkN⟩ ↔ (r.time x : ℕ) = k := fun x =>
    ⟨fun h => by rw [h], fun h => Fin.ext h⟩
  -- the two integrands as sums of indicators
  have e1 : ∀ x : Fin (n + 1) → ℝ, (if (r.time x : ℕ) < k then (r.rank x : ℝ)
      else if hk : k ≤ n + 1 then L k (Fin.take k hk x) else 0) =
      {x : Fin (n + 1) → ℝ | (r.time x : ℕ) < k}.indicator (fun x => (r.rank x : ℝ)) x +
      {x : Fin (n + 1) → ℝ | k ≤ (r.time x : ℕ)}.indicator
        (fun x => L k (Fin.take k hk0 x)) x := by
    intro x
    by_cases h : (r.time x : ℕ) < k
    · have h' : ¬ k ≤ (r.time x : ℕ) := by omega
      rw [if_pos h, Set.indicator_of_mem (show x ∈ {x | (r.time x : ℕ) < k} from h),
        Set.indicator_of_notMem (show x ∉ {x | k ≤ (r.time x : ℕ)} from h'), add_zero]
    · have h' : k ≤ (r.time x : ℕ) := by omega
      rw [if_neg h, dif_pos hk0, Set.indicator_of_notMem (show x ∉ {x | (r.time x : ℕ) < k} from h),
        Set.indicator_of_mem (show x ∈ {x | k ≤ (r.time x : ℕ)} from h'), zero_add]
  have e2 : ∀ x : Fin (n + 1) → ℝ, (if (r.time x : ℕ) < k + 1 then (r.rank x : ℝ)
      else if hk : k + 1 ≤ n + 1 then L (k + 1) (Fin.take (k + 1) hk x) else 0) =
      {x : Fin (n + 1) → ℝ | (r.time x : ℕ) < k}.indicator (fun x => (r.rank x : ℝ)) x +
      ({x : Fin (n + 1) → ℝ | r.time x = ⟨k, hkN⟩}.indicator (fun x => (r.rank x : ℝ)) x +
      {x : Fin (n + 1) → ℝ | k + 1 ≤ (r.time x : ℕ)}.indicator
        (fun x => L (k + 1) (Fin.take (k + 1) hkN x)) x) := by
    intro x
    by_cases h1 : (r.time x : ℕ) < k
    · have h2 : ¬ r.time x = ⟨k, hkN⟩ := by rw [hteq]; omega
      have h3 : ¬ k + 1 ≤ (r.time x : ℕ) := by omega
      rw [if_pos (by omega), Set.indicator_of_mem (show x ∈ {x | (r.time x : ℕ) < k} from h1),
        Set.indicator_of_notMem (show x ∉ {x | r.time x = ⟨k, hkN⟩} from h2),
        Set.indicator_of_notMem (show x ∉ {x | k + 1 ≤ (r.time x : ℕ)} from h3), add_zero,
        add_zero]
    · by_cases h2 : (r.time x : ℕ) = k
      · have h3 : ¬ k + 1 ≤ (r.time x : ℕ) := by omega
        rw [if_pos (by omega), Set.indicator_of_notMem (show x ∉ {x | (r.time x : ℕ) < k} from h1),
          Set.indicator_of_mem (show x ∈ {x | r.time x = ⟨k, hkN⟩} from (hteq x).mpr h2),
          Set.indicator_of_notMem (show x ∉ {x | k + 1 ≤ (r.time x : ℕ)} from h3), add_zero,
          zero_add]
      · have h3 : k + 1 ≤ (r.time x : ℕ) := by omega
        have h4 : ¬ r.time x = ⟨k, hkN⟩ := by rw [hteq]; exact h2
        rw [if_neg (by omega), dif_pos hk1,
          Set.indicator_of_notMem (show x ∉ {x | (r.time x : ℕ) < k} from h1),
          Set.indicator_of_notMem (show x ∉ {x | r.time x = ⟨k, hkN⟩} from h4),
          Set.indicator_of_mem (show x ∈ {x | k + 1 ≤ (r.time x : ℕ)} from h3), zero_add,
          zero_add]
  have e3 : ∀ x : Fin (n + 1) → ℝ,
      {x : Fin (n + 1) → ℝ | r.time x = ⟨k, hkN⟩}.indicator
        (fun x => L (k + 1) (Fin.take (k + 1) hkN x)) x +
      {x : Fin (n + 1) → ℝ | k + 1 ≤ (r.time x : ℕ)}.indicator
        (fun x => L (k + 1) (Fin.take (k + 1) hkN x)) x =
      {x : Fin (n + 1) → ℝ | k ≤ (r.time x : ℕ)}.indicator
        (fun x => L (k + 1) (Fin.take (k + 1) hkN x)) x := by
    intro x
    by_cases h2 : (r.time x : ℕ) = k
    · have h3 : ¬ k + 1 ≤ (r.time x : ℕ) := by omega
      rw [Set.indicator_of_mem (show x ∈ {x | r.time x = ⟨k, hkN⟩} from (hteq x).mpr h2),
        Set.indicator_of_notMem (show x ∉ {x | k + 1 ≤ (r.time x : ℕ)} from h3),
        Set.indicator_of_mem (show x ∈ {x | k ≤ (r.time x : ℕ)} from h2.ge), add_zero]
    · have h4 : ¬ r.time x = ⟨k, hkN⟩ := by rw [hteq]; exact h2
      rw [Set.indicator_of_notMem (show x ∉ {x | r.time x = ⟨k, hkN⟩} from h4), zero_add]
      by_cases h3 : k + 1 ≤ (r.time x : ℕ)
      · rw [Set.indicator_of_mem (show x ∈ {x | k + 1 ≤ (r.time x : ℕ)} from h3),
          Set.indicator_of_mem (show x ∈ {x | k ≤ (r.time x : ℕ)} from (by omega : k ≤ _))]
      · rw [Set.indicator_of_notMem (show x ∉ {x | k + 1 ≤ (r.time x : ℕ)} from h3),
          Set.indicator_of_notMem (show x ∉ {x | k ≤ (r.time x : ℕ)} from (by omega : ¬ k ≤ _))]
  have I1 : ∫ x, (if (r.time x : ℕ) < k then (r.rank x : ℝ)
      else if hk : k ≤ n + 1 then L k (Fin.take k hk x) else 0) ∂law (n + 1) =
      ∫ x, {x : Fin (n + 1) → ℝ | (r.time x : ℕ) < k}.indicator (fun x => (r.rank x : ℝ)) x
        ∂law (n + 1) +
      ∫ x, {x : Fin (n + 1) → ℝ | k ≤ (r.time x : ℕ)}.indicator
        (fun x => L k (Fin.take k hk0 x)) x ∂law (n + 1) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall e1)]
    exact integral_add (hR.indicator hA) (hLk.indicator hD)
  have I2 : ∫ x, (if (r.time x : ℕ) < k + 1 then (r.rank x : ℝ)
      else if hk : k + 1 ≤ n + 1 then L (k + 1) (Fin.take (k + 1) hk x) else 0) ∂law (n + 1) =
      ∫ x, {x : Fin (n + 1) → ℝ | (r.time x : ℕ) < k}.indicator (fun x => (r.rank x : ℝ)) x
        ∂law (n + 1) +
      (∫ x, {x : Fin (n + 1) → ℝ | r.time x = ⟨k, hkN⟩}.indicator (fun x => (r.rank x : ℝ)) x
        ∂law (n + 1) +
      ∫ x, {x : Fin (n + 1) → ℝ | k + 1 ≤ (r.time x : ℕ)}.indicator
        (fun x => L (k + 1) (Fin.take (k + 1) hkN x)) x ∂law (n + 1)) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall e2)]
    rw [integral_add (hR.indicator hA)
      (show Integrable (fun x =>
        {x : Fin (n + 1) → ℝ | r.time x = ⟨k, hkN⟩}.indicator (fun x => (r.rank x : ℝ)) x +
        {x : Fin (n + 1) → ℝ | k + 1 ≤ (r.time x : ℕ)}.indicator
          (fun x => L (k + 1) (Fin.take (k + 1) hkN x)) x) (law (n + 1)) from
        (hR.indicator hB).add (hLk1.indicator hC))]
    rw [integral_add (hR.indicator hB) (hLk1.indicator hC)]
  -- the stop part: rank = stop payoff on {time = k}, and (V1)
  have s1 : ∫ x, {x : Fin (n + 1) → ℝ | r.time x = ⟨k, hkN⟩}.indicator
        (fun x => (r.rank x : ℝ)) x ∂law (n + 1) =
      ∫ x, {x : Fin (n + 1) → ℝ | r.time x = ⟨k, hkN⟩}.indicator
        (fun x => stopPayoff n (history x ⟨k, hkN⟩)) x ∂law (n + 1) := by
    simp only [Set.indicator, Set.mem_setOf_eq]
    exact r.integral_ite_time_eq_rank ⟨k, hkN⟩
  have s2 : ∫ x, {x : Fin (n + 1) → ℝ | r.time x = ⟨k, hkN⟩}.indicator
        (fun x => L (k + 1) (Fin.take (k + 1) hkN x)) x ∂law (n + 1) ≤
      ∫ x, {x : Fin (n + 1) → ℝ | r.time x = ⟨k, hkN⟩}.indicator
        (fun x => stopPayoff n (history x ⟨k, hkN⟩)) x ∂law (n + 1) := by
    refine integral_mono_ae (hLk1.indicator hB) (hP.indicator hB) ?_
    filter_upwards [ae_mem_Icc (n + 1)] with x hx
    by_cases hxB : r.time x = ⟨k, hkN⟩
    · rw [Set.indicator_of_mem (show x ∈ {x | r.time x = ⟨k, hkN⟩} from hxB),
        Set.indicator_of_mem (show x ∈ {x | r.time x = ⟨k, hkN⟩} from hxB)]
      exact hV1 k (Fin.take (k + 1) hkN x) hkn (take_mem_Icc (k + 1) hkN x hx)
    · rw [Set.indicator_of_notMem (show x ∉ {x | r.time x = ⟨k, hkN⟩} from hxB),
        Set.indicator_of_notMem (show x ∉ {x | r.time x = ⟨k, hkN⟩} from hxB)]
  -- the continuation part: integrate out the value at `k`, then (V2)
  have s3 : ∫ x, {x : Fin (n + 1) → ℝ | k ≤ (r.time x : ℕ)}.indicator
        (fun x => L (k + 1) (Fin.take (k + 1) hkN x)) x ∂law (n + 1) =
      ∫ x, {x : Fin (n + 1) → ℝ | k ≤ (r.time x : ℕ)}.indicator
        (fun x => ∫ a in Set.Icc (0 : ℝ) 1,
          L (k + 1) (Fin.snoc (α := fun _ => ℝ) (Fin.take k hkN.le x) a)) x ∂law (n + 1) :=
    integral_indicator_take_succ k hkN _ hD
      (fun x a => r.le_time_update_iff x k ⟨k, hkN⟩ a le_rfl) (L (k + 1)) (hL (k + 1) hk1)
      (hLb (k + 1) hk1)
  have s4 : ∫ x, {x : Fin (n + 1) → ℝ | k ≤ (r.time x : ℕ)}.indicator
        (fun x => L k (Fin.take k hk0 x)) x ∂law (n + 1) ≤
      ∫ x, {x : Fin (n + 1) → ℝ | k ≤ (r.time x : ℕ)}.indicator
        (fun x => ∫ a in Set.Icc (0 : ℝ) 1,
          L (k + 1) (Fin.snoc (α := fun _ => ℝ) (Fin.take k hkN.le x) a)) x ∂law (n + 1) := by
    refine integral_mono_ae (hLk.indicator hD) (hM.indicator hD) ?_
    filter_upwards [ae_mem_Icc (n + 1)] with x hx
    by_cases hxD : k ≤ (r.time x : ℕ)
    · rw [Set.indicator_of_mem (show x ∈ {x | k ≤ (r.time x : ℕ)} from hxD),
        Set.indicator_of_mem (show x ∈ {x | k ≤ (r.time x : ℕ)} from hxD)]
      exact hV2 k (Fin.take k hk0 x) hkn (take_mem_Icc k hk0 x hx)
    · rw [Set.indicator_of_notMem (show x ∉ {x | k ≤ (r.time x : ℕ)} from hxD),
        Set.indicator_of_notMem (show x ∉ {x | k ≤ (r.time x : ℕ)} from hxD)]
  have s5 := integral_add (hLk1.indicator hB) (hLk1.indicator hC)
  rw [integral_congr_ae (Filter.Eventually.of_forall e3)] at s5
  rw [I1, I2]
  linarith

theorem Rule.expectedRank_ge_of_verification {n : ℕ} (L : (k : ℕ) → (Fin k → ℝ) → ℝ)
    (hL : ∀ k ≤ n + 1, Measurable (L k))
    (hLb : ∀ k ≤ n + 1, ∃ C, ∀ h : Fin k → ℝ, (∀ i, h i ∈ Set.Icc (0 : ℝ) 1) → |L k h| ≤ C)
    (hV1 : ∀ (t : ℕ) (h : Fin (t + 1) → ℝ), t ≤ n → (∀ i, h i ∈ Set.Icc (0 : ℝ) 1) →
      L (t + 1) h ≤ stopPayoff n h)
    (hV2 : ∀ (k : ℕ) (h : Fin k → ℝ), k ≤ n → (∀ i, h i ∈ Set.Icc (0 : ℝ) 1) →
      L k h ≤ ∫ a in Set.Icc (0 : ℝ) 1, L (k + 1) (Fin.snoc (α := fun _ => ℝ) h a))
    (r : Rule (n + 1)) : L 0 ![] ≤ r.expectedRank := by
  classical
  -- `E k`: the rule's rank if it has stopped before `k`, else `L k` of the first `k` values.
  let E : ℕ → ℝ := fun k => ∫ x, (if (r.time x : ℕ) < k then (r.rank x : ℝ)
      else if hk : k ≤ n + 1 then L k (Fin.take k hk x) else 0) ∂law (n + 1)
  have hE0 : E 0 = L 0 ![] := by
    have h : ∀ x : Fin (n + 1) → ℝ, (if (r.time x : ℕ) < 0 then (r.rank x : ℝ)
        else if hk : 0 ≤ n + 1 then L 0 (Fin.take 0 hk x) else 0) = L 0 ![] := by
      intro x
      rw [if_neg (Nat.not_lt_zero _), dif_pos (Nat.zero_le _)]
      congr 1
      exact Subsingleton.elim _ _
    simp only [E, h, integral_const, probReal_univ, one_smul]
  have hEn : E (n + 1) = r.expectedRank := by
    simp only [E]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [if_pos (r.time x).isLt]
  have hstep : ∀ k, k ≤ n → E k ≤ E (k + 1) := by
    intro k hkn
    exact r.verification_step L hL hLb hV1 hV2 k hkn
  have hchain : ∀ k, k ≤ n + 1 → E 0 ≤ E k := by
    intro k hk
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (ih (by omega)).trans (hstep k (by omega))
  rw [← hE0]
  exact (hchain (n + 1) le_rfl).trans hEn.le

theorem le_v_of_verification {n : ℕ} (L : (k : ℕ) → (Fin k → ℝ) → ℝ)
    (hL : ∀ k ≤ n + 1, Measurable (L k))
    (hLb : ∀ k ≤ n + 1, ∃ C, ∀ h : Fin k → ℝ, (∀ i, h i ∈ Set.Icc (0 : ℝ) 1) → |L k h| ≤ C)
    (hV1 : ∀ (t : ℕ) (h : Fin (t + 1) → ℝ), t ≤ n → (∀ i, h i ∈ Set.Icc (0 : ℝ) 1) →
      L (t + 1) h ≤ stopPayoff n h)
    (hV2 : ∀ (k : ℕ) (h : Fin k → ℝ), k ≤ n → (∀ i, h i ∈ Set.Icc (0 : ℝ) 1) →
      L k h ≤ ∫ a in Set.Icc (0 : ℝ) 1, L (k + 1) (Fin.snoc (α := fun _ => ℝ) h a)) :
    L 0 ![] ≤ v (n + 1) := by
  exact le_v_succ fun r => r.expectedRank_ge_of_verification L hL hLb hV1 hV2

end Robbins
