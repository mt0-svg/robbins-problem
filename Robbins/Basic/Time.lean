import Robbins.Statement

/-!
# The selected time of a rule

The selected time is characterized by `Rule.time_eq_iff`: the rule stops at `t` and at no earlier
time. Its events are measurable (`Rule.measurableSet_time_eq`, `Rule.measurable_time`).
-/

namespace Robbins

open MeasureTheory

theorem measurable_history {n : ℕ} (t : Fin n) :
    Measurable fun x : Fin n → ℝ => history x t := by
  unfold history
  refine Measurable.of_eval ?_
  intro s
  exact measurable_pi_apply _

theorem Rule.time_eq_iff {n : ℕ} (r : Rule (n + 1)) (x : Fin (n + 1) → ℝ) (t : Fin (n + 1)) :
    r.time x = t ↔
      (history x t ∈ r.stopSet t ∨ t = Fin.last n) ∧ ∀ s < t, history x s ∉ r.stopSet s := by
  classical
    let S := Finset.univ.filter fun t => history x t ∈ r.stopSet t ∨ t = Fin.last n
    have hS : S.Nonempty := ⟨Fin.last n, by
      dsimp [S]
      simp⟩
    have htime_def : r.time x = S.min' hS := by
      unfold Rule.time
      rfl
    constructor
    · intro h
      rw [htime_def] at h
      -- h: S.min' hS = t
      have hmem : S.min' hS ∈ S := Finset.min'_mem _ hS
      have hmem_filter : history x t ∈ r.stopSet t ∨ t = Fin.last n := by
        rw [h] at hmem
        simpa [S] using hmem
      have h_forall : ∀ s < t, history x s ∉ r.stopSet s := by
        intro s hs_lt hs_stop
        have hs_mem : s ∈ S := by
          dsimp [S]
          simp [hs_stop]
        have hle : S.min' hS ≤ s := Finset.min'_le _ _ hs_mem
        rw [h] at hle
        exact not_lt.mpr hle hs_lt
      exact And.intro hmem_filter h_forall
    · intro ⟨ht_mem, h_forall⟩
      have hmem : t ∈ S := by
        dsimp [S]
        simp [ht_mem]
      apply le_antisymm
      · -- S.min' hS ≤ t
        exact Finset.min'_le _ _ hmem
      · -- t ≤ S.min' hS
        apply Finset.le_min' _ hS
        intro s hs_mem
        have hs_filter : history x s ∈ r.stopSet s ∨ s = Fin.last n := by
          simpa [S] using hs_mem
        rcases hs_filter with (hs_stop | hs_last)
        · -- history x s ∈ r.stopSet s
          by_cases hle : t ≤ s
          · exact hle
          · have h_lt : s < t := lt_of_not_ge hle
            exfalso
            exact h_forall s h_lt hs_stop
        · -- s = Fin.last n
          rw [hs_last]
          exact Fin.le_last t

theorem Rule.time_le_of_mem {n : ℕ} (r : Rule (n + 1)) (x : Fin (n + 1) → ℝ) (t : Fin (n + 1))
    (h : history x t ∈ r.stopSet t) : r.time x ≤ t := by
  classical
  unfold Rule.time
  apply Finset.min'_le
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ t, Or.inl h⟩

theorem Rule.not_mem_of_lt_time {n : ℕ} (r : Rule (n + 1)) (x : Fin (n + 1) → ℝ) (s : Fin (n + 1))
    (h : s < r.time x) : history x s ∉ r.stopSet s := by
  classical
    intro hmem
    have hmem_filter : s ∈ Finset.univ.filter fun t => history x t ∈ r.stopSet t ∨ t = Fin.last n :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hmem⟩
    have hle : r.time x ≤ s := by
      simpa [Rule.time] using Finset.min'_le _ _ hmem_filter
    exact not_lt.mpr hle h

theorem Rule.mem_or_last_time {n : ℕ} (r : Rule (n + 1)) (x : Fin (n + 1) → ℝ) :
    history x (r.time x) ∈ r.stopSet (r.time x) ∨ r.time x = Fin.last n := by
  classical
    unfold Rule.time
    have hmem : (Fin.last n : Fin (n + 1)) ∈ (Finset.univ : Finset (Fin (n + 1))).filter (fun t => history x t ∈ r.stopSet t ∨ t = Fin.last n) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      right; rfl
    have hm := Finset.min'_mem _ ⟨Fin.last n, hmem⟩
    exact (Finset.mem_filter.1 hm).2

theorem Rule.time_eq_last_of_empty {n : ℕ} (r : Rule (n + 1)) (h : ∀ t, r.stopSet t = ∅)
    (x : Fin (n + 1) → ℝ) : r.time x = Fin.last n := by
  classical
    unfold Rule.time
    have hfilter : (Finset.univ.filter fun t => history x t ∈ r.stopSet t ∨ t = Fin.last n) = {Fin.last n} := by
      ext t
      simp [h t]
    simp [hfilter, Finset.min'_singleton]

theorem Rule.measurableSet_time_eq {n : ℕ} (r : Rule (n + 1)) (t : Fin (n + 1)) :
    MeasurableSet {x : Fin (n + 1) → ℝ | r.time x = t} := by
  have h_eq : {x : Fin (n + 1) → ℝ | r.time x = t} =
      ({x | history x t ∈ r.stopSet t} ∪ {x | t = Fin.last n}) ∩
      {x | ∀ s < t, history x s ∉ r.stopSet s} := by
    ext x; simp [Rule.time_eq_iff]
  rw [h_eq]
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.union ?_ ?_
    · exact (r.measurableSet_stopSet t).preimage (measurable_history t)
    · by_cases h : t = Fin.last n
      · subst h; simp
      · simp [h]
  · have h_meas : Measurable (fun x : Fin (n + 1) → ℝ => ∀ s < t, history x s ∉ r.stopSet s) := by
      refine Measurable.forall ?_
      intro s
      have h_set : MeasurableSet {x : Fin (n + 1) → ℝ | (s < t → history x s ∉ r.stopSet s)} := by
        have h_eq' : {x : Fin (n + 1) → ℝ | (s < t → history x s ∉ r.stopSet s)} =
            {x | ¬ (s < t)} ∪ {x | history x s ∉ r.stopSet s} := by
          ext x; simp [imp_iff_not_or]
        rw [h_eq']
        refine MeasurableSet.union ?_ ?_
        · by_cases h : s < t
          · simp [h]
          · simp [h]
        · have h_preimage : MeasurableSet {x | history x s ∈ r.stopSet s} :=
            (r.measurableSet_stopSet s).preimage (measurable_history s)
          exact h_preimage.compl
      exact measurableSet_setOfPred.mp h_set
    exact measurableSet_setOfPred.mpr h_meas

theorem Rule.measurable_time {n : ℕ} (r : Rule (n + 1)) : Measurable r.time := by
  apply measurable_to_countable'
  intro t
  exact Rule.measurableSet_time_eq r t

theorem history_snoc_castSucc {n : ℕ} (y : Fin n → ℝ) (a : ℝ) (t : Fin n) :
    history (Fin.snoc (α := fun _ => ℝ) y a) t.castSucc = history y t := by
  funext s; simp only [history]; have h : Fin.castLE (t.castSucc).isLt s = (Fin.castLE t.isLt s).castSucc := Fin.ext rfl; rw [h, Fin.snoc_castSucc]

end Robbins
