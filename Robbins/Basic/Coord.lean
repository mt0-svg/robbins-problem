import Robbins.Basic.Rank
import Robbins.Basic.Fubini
import Robbins.Basic.Integrals

/-!
# One coordinate at a time

Integrating out one value inside the full space (`integral_update`), the first `k` values
(`Fin.take`), and how the selected time sees a change of a later value.
-/

namespace Robbins

open MeasureTheory

theorem history_eq_take {n : ℕ} (x : Fin n → ℝ) (t : Fin n) :
    history x t = Fin.take (t + 1) t.isLt x := rfl

theorem measurable_take {N : ℕ} (k : ℕ) (hk : k ≤ N) :
    Measurable fun x : Fin N → ℝ => (Fin.take k hk x : Fin k → ℝ) := by
  apply Measurable.of_eval; intro i; exact measurable_pi_apply (Fin.castLE hk i)

theorem take_mem_Icc {N : ℕ} (k : ℕ) (hk : k ≤ N) (x : Fin N → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) : ∀ i, (Fin.take k hk x : Fin k → ℝ) i ∈ Set.Icc (0 : ℝ) 1 := by
  intro i
  rw [Fin.take_apply]
  exact hx (Fin.castLE hk i)

theorem integrable_comp_take {N : ℕ} (k : ℕ) (hk : k ≤ N) (G : (Fin k → ℝ) → ℝ)
    (hG : Measurable G) (hGb : ∃ C, ∀ h : Fin k → ℝ, (∀ i, h i ∈ Set.Icc (0 : ℝ) 1) → |G h| ≤ C) :
    Integrable (fun x : Fin N → ℝ => G (Fin.take k hk x)) (law N) := by
  rcases hGb with ⟨C, hC⟩
  refine MeasureTheory.Integrable.of_bound ?_ C ?_
  · exact (hG.comp (measurable_take k hk)).aestronglyMeasurable
  · filter_upwards [ae_mem_Icc N] with x hx
    have hx' : ∀ i, (Fin.take k hk x : Fin k → ℝ) i ∈ Set.Icc (0 : ℝ) 1 :=
      take_mem_Icc k hk x hx
    have hbound : |G (Fin.take k hk x)| ≤ C := hC (Fin.take k hk x) hx'
    calc
      ‖G (Fin.take k hk x)‖ = |G (Fin.take k hk x)| := by rw [Real.norm_eq_abs]
      _ ≤ C := hbound

theorem integral_update {N : ℕ} (j : Fin N) (f : (Fin N → ℝ) → ℝ) (hf : Integrable f (law N)) :
    ∫ x, f x ∂law N = ∫ x, (∫ a in Set.Icc (0 : ℝ) 1, f (Function.update x j a)) ∂law N := by
  cases N with
  | zero => exact j.elim0
  | succ m =>
    have hmp := measurePreserving_piFinSuccAbove
      (fun _ : Fin (m + 1) => volume.restrict (Set.Icc (0 : ℝ) 1)) j
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j
    have hlaw : law (m + 1) = Measure.pi fun _ => volume.restrict (Set.Icc (0 : ℝ) 1) := rfl
    have hlawm : (Measure.pi fun _ : Fin m => volume.restrict (Set.Icc (0 : ℝ) 1)) = law m := rfl
    have hsymm : ∀ p : ℝ × (Fin m → ℝ), e.symm p = j.insertNth p.1 p.2 := fun p => rfl
    have happ : ∀ x : Fin (m + 1) → ℝ, (e x).2 = j.removeNth x := fun x => rfl
    have hf' : Integrable (fun p => f (e.symm p))
        ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (law m)) := by
      have := (hmp.symm e).integrable_comp_emb e.symm.measurableEmbedding (g := f)
      rw [hlawm] at this
      exact this.mpr (hlaw ▸ hf)
    have L : ∫ x, f x ∂law (m + 1) =
        ∫ y, (∫ a in Set.Icc (0 : ℝ) 1, f (j.insertNth a y)) ∂law m := by
      have h1 := hmp.integral_comp' (fun p => f (e.symm p))
      simp only [MeasurableEquiv.symm_apply_apply] at h1
      rw [hlaw, h1, hlawm, integral_prod_symm _ hf']
      rfl
    have R : ∫ x, (∫ a in Set.Icc (0 : ℝ) 1, f (Function.update x j a)) ∂law (m + 1) =
        ∫ y, (∫ a in Set.Icc (0 : ℝ) 1, f (j.insertNth a y)) ∂law m := by
      have h2 := hmp.integral_comp'
        (fun p => ∫ a in Set.Icc (0 : ℝ) 1, f (j.insertNth a p.2))
      simp only [happ, Fin.insertNth_removeNth] at h2
      rw [hlaw, h2, integral_fun_snd (fun y : Fin m → ℝ => ∫ a in Set.Icc (0 : ℝ) 1, f (j.insertNth a y)), hlawm]
      simp
    rw [L, R]

theorem integral_mul_ite_lt {N : ℕ} (F : (Fin N → ℝ) → ℝ) (hF : Integrable F (law N))
    (j k : Fin N) (hjk : j ≠ k) (hFj : ∀ x a, F (Function.update x j a) = F x) :
    ∫ x, F x * (if x j < x k then 1 else 0) ∂law N = ∫ x, F x * x k ∂law N := by
  set f := fun (x : Fin N → ℝ) => F x * (if x j < x k then (1 : ℝ) else 0) with hf_def
  have h_indicator_meas : Measurable (fun (x : Fin N → ℝ) => (if x j < x k then (1 : ℝ) else 0)) := by
    have h_set : MeasurableSet {x : Fin N → ℝ | x j < x k} :=
      measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply k)
    exact Measurable.ite h_set measurable_const measurable_const
  have h_indicator_bound : ∀ᵐ x ∂(law N), ‖(if x j < x k then (1 : ℝ) else 0)‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    by_cases h : x j < x k
    · simp [h]
    · simp [h]
  have hf_int : Integrable f (law N) := by
    rw [hf_def]
    exact hF.mul_bdd h_indicator_meas.aestronglyMeasurable h_indicator_bound
  calc
    ∫ x, F x * (if x j < x k then 1 else 0) ∂law N = ∫ x, f x ∂law N := rfl
    _ = ∫ x, (∫ a in Set.Icc (0 : ℝ) 1, f (Function.update x j a)) ∂law N := by
      rw [integral_update j f hf_int]
    _ = ∫ x, (∫ a in Set.Icc (0 : ℝ) 1, (F x * (if a < x k then (1 : ℝ) else 0))) ∂law N := by
      refine integral_congr_ae ?_
      filter_upwards [] with x
      congr with a
      simp [f, hFj x a, Function.update_self, Function.update_of_ne hjk.symm]
    _ = ∫ x, F x * (∫ a in Set.Icc (0 : ℝ) 1, (if a < x k then (1 : ℝ) else 0)) ∂law N := by
      refine integral_congr_ae ?_
      filter_upwards [] with x
      rw [integral_const_mul (F x) (fun a => (if a < x k then (1 : ℝ) else 0))]
    _ = ∫ x, F x * x k ∂law N := by
      refine integral_congr_ae ?_
      filter_upwards [ae_mem_Icc N] with x hx
      have hxk : x k ∈ Set.Icc (0 : ℝ) 1 := hx k
      rw [integral_Icc_ite_lt hxk]

theorem integral_indicator_take_succ {N : ℕ} (k : ℕ) (hk : k < N) (S : Set (Fin N → ℝ))
    (hS : MeasurableSet S) (hSk : ∀ x a, Function.update x ⟨k, hk⟩ a ∈ S ↔ x ∈ S)
    (G : (Fin (k + 1) → ℝ) → ℝ) (hG : Measurable G)
    (hGb : ∃ C, ∀ h : Fin (k + 1) → ℝ, (∀ i, h i ∈ Set.Icc (0 : ℝ) 1) → |G h| ≤ C) :
    ∫ x, S.indicator (fun x => G (Fin.take (k + 1) hk x)) x ∂law N =
      ∫ x, S.indicator (fun x => ∫ a in Set.Icc (0 : ℝ) 1,
        G (Fin.snoc (α := fun _ => ℝ) (Fin.take k hk.le x) a)) x ∂law N := by
  have hk' : k + 1 ≤ N := Nat.succ_le_of_lt hk
  have h_int_comp : Integrable (fun x : Fin N → ℝ => G (Fin.take (k + 1) hk x)) (law N) := by
    have h := integrable_comp_take (k + 1) hk' G hG hGb
    simpa using h
  have h_int : Integrable (fun x : Fin N → ℝ => S.indicator (fun x => G (Fin.take (k + 1) hk x)) x) (law N) :=
    h_int_comp.indicator hS
  rw [Robbins.integral_update ⟨k, hk⟩ (fun x => S.indicator (fun x => G (Fin.take (k + 1) hk x)) x) h_int]
  refine integral_congr_ae ?_
  filter_upwards with x
  by_cases hxS : x ∈ S
  · have hUS : ∀ a, Function.update x ⟨k, hk⟩ a ∈ S := by
      intro a; rw [hSk x a]; exact hxS
    have h_eq : ∀ a, Fin.take (k + 1) hk (Function.update x ⟨k, hk⟩ a) = Fin.snoc (Fin.take k hk.le x) a := by
      intro a
      rw [Fin.take_succ_eq_snoc k hk (Function.update x ⟨k, hk⟩ a)]
      rw [Function.update_self]
      rw [Fin.take_update_of_ge k hk.le x ⟨k, hk⟩ (by simp) a]
    simp [hxS, hUS, Set.indicator_of_mem, h_eq]
  · have hUNS : ∀ a, Function.update x ⟨k, hk⟩ a ∉ S := by
      intro a; rw [hSk x a]; exact hxS
    simp [hxS, hUNS]

theorem integrable_integral_snoc_take {N : ℕ} (k : ℕ) (hk : k < N) (G : (Fin (k + 1) → ℝ) → ℝ)
    (hG : Measurable G)
    (hGb : ∃ C, ∀ h : Fin (k + 1) → ℝ, (∀ i, h i ∈ Set.Icc (0 : ℝ) 1) → |G h| ≤ C) :
    Integrable (fun x : Fin N → ℝ => ∫ a in Set.Icc (0 : ℝ) 1,
      G (Fin.snoc (α := fun _ => ℝ) (Fin.take k hk.le x) a)) (law N) := by
  obtain ⟨C, hC⟩ := hGb
  have hsnoc : Measurable fun p : (Fin N → ℝ) × ℝ =>
      (Fin.snoc (α := fun _ => ℝ) (Fin.take k hk.le p.1) p.2 : Fin (k + 1) → ℝ) := by
    refine Measurable.of_eval fun i => ?_
    cases i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using measurable_snd
    | cast j =>
      simp only [Fin.snoc_castSucc, Fin.take_apply]
      exact (measurable_pi_apply _).comp measurable_fst
  have hmeas : StronglyMeasurable fun x : Fin N → ℝ => ∫ a in Set.Icc (0 : ℝ) 1,
      G (Fin.snoc (α := fun _ => ℝ) (Fin.take k hk.le x) a) :=
    (hG.comp hsnoc).stronglyMeasurable.integral_prod_right'
  refine Integrable.of_bound hmeas.aestronglyMeasurable C ?_
  filter_upwards [ae_mem_Icc N] with x hx
  have h1 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (0 : ℝ) 1) (C := C)
    (f := fun a => G (Fin.snoc (α := fun _ => ℝ) (Fin.take k hk.le x) a)) (by simp) (fun a ha => by
      rw [Real.norm_eq_abs]
      apply hC
      intro i
      cases i using Fin.lastCases with
      | last => simpa only [Fin.snoc_last] using ha
      | cast j => simpa only [Fin.snoc_castSucc, Fin.take_apply] using hx _)
  simpa using h1

theorem history_update_of_lt {n : ℕ} (x : Fin n → ℝ) (j s : Fin n) (a : ℝ) (h : s < j) :
    history (Function.update x j a) s = history x s := by
  unfold history; ext i; simp [Function.update]; intro h_eq
  have hval := congrArg Fin.val h_eq
  rw [Fin.val_castLE s.isLt i] at hval
  have hi : (i : ℕ) < (s : ℕ) + 1 := i.isLt
  have hs : (s : ℕ) < (j : ℕ) := h
  omega

theorem Rule.time_update_eq_iff {n : ℕ} (r : Rule (n + 1)) (x : Fin (n + 1) → ℝ)
    (t j : Fin (n + 1)) (a : ℝ) (h : t < j) :
    r.time (Function.update x j a) = t ↔ r.time x = t := by
  rw [Rule.time_eq_iff, Rule.time_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [history_update_of_lt x j t a h] at h1
      exact h1
    · intro s hs
      have hsj : s < j := lt_trans hs h
      have h2s := h2 s hs
      rw [history_update_of_lt x j s a hsj] at h2s
      exact h2s
  · rintro ⟨h1, h2⟩
    constructor
    · rw [history_update_of_lt x j t a h]
      exact h1
    · intro s hs
      have hsj : s < j := lt_trans hs h
      have h2s := h2 s hs
      rw [history_update_of_lt x j s a hsj]
      exact h2s

theorem Rule.le_time_iff {n : ℕ} (r : Rule (n + 1)) (x : Fin (n + 1) → ℝ) (k : ℕ) (hk : k ≤ n) :
    k ≤ (r.time x : ℕ) ↔ ∀ s : Fin (n + 1), (s : ℕ) < k → history x s ∉ r.stopSet s := by
  constructor
  · intro h s hs
    have hst : (s : ℕ) < (r.time x : ℕ) := by
      omega
    exact Rule.not_mem_of_lt_time r x s hst
  · intro h
    by_contra! h_lt
    have h_cases := Rule.mem_or_last_time r x
    rcases h_cases with (h_mem | h_last)
    · have h_contra := h (r.time x) h_lt
      exact h_contra h_mem
    · have h_val : (r.time x : ℕ) = n := by
        simpa [h_last] using Fin.val_last n
      have : n < k := by
        calc
          n = (r.time x : ℕ) := by symm; exact h_val
          _ < k := h_lt
      omega

theorem Rule.le_time_update_iff {n : ℕ} (r : Rule (n + 1)) (x : Fin (n + 1) → ℝ) (k : ℕ)
    (j : Fin (n + 1)) (a : ℝ) (h : k ≤ (j : ℕ)) :
    k ≤ (r.time (Function.update x j a) : ℕ) ↔ k ≤ (r.time x : ℕ) := by
  have hk : k ≤ n := by
    have hj : (j : ℕ) < n + 1 := j.isLt
    omega
  rw [Rule.le_time_iff r (Function.update x j a) k hk, Rule.le_time_iff r x k hk]
  constructor
  · intro H s hs
    have h_s_lt_j : s < j := by
      rw [Fin.lt_def]
      exact lt_of_lt_of_le hs h
    rw [← history_update_of_lt x j s a h_s_lt_j]
    exact H s hs
  · intro H s hs
    have h_s_lt_j : s < j := by
      rw [Fin.lt_def]
      exact lt_of_lt_of_le hs h
    rw [history_update_of_lt x j s a h_s_lt_j]
    exact H s hs

theorem Rule.measurableSet_le_time {n : ℕ} (r : Rule (n + 1)) (k : ℕ) :
    MeasurableSet {x : Fin (n + 1) → ℝ | k ≤ (r.time x : ℕ)} := by
  have h_meas_time : Measurable r.time := Rule.measurable_time r
  have h_meas_set : MeasurableSet {t : Fin (n + 1) | k ≤ (t : ℕ)} :=
    MeasurableSet.of_discrete (s := {t : Fin (n + 1) | k ≤ (t : ℕ)})
  exact h_meas_time h_meas_set

theorem Rule.measurableSet_time_lt {n : ℕ} (r : Rule (n + 1)) (k : ℕ) :
    MeasurableSet {x : Fin (n + 1) → ℝ | (r.time x : ℕ) < k} := by
  have hmeas : Measurable r.time := Rule.measurable_time r
  have hset : MeasurableSet {t : Fin (n + 1) | (t : ℕ) < k} := MeasurableSet.of_discrete
  exact hmeas hset

end Robbins
