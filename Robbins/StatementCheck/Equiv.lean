import Robbins.Basic.Rank
import Robbins.Basic.Fubini
import Robbins.Basic.Coord
import Robbins.StatementCheck.Indep

/-!
# The frozen statement against the second formalization

`robbinsValue_eq_v`: the optimal value of `Robbins/StatementCheck/Indep.lean` (stopping times for the
filtration of the first values, rank among the distinct values) equals `v` for every positive
number of values. A rule of `Robbins/Statement.lean` is such a stopping time (`Rule.toIndep`), and
such a stopping time is the selected time of a rule (`ofIndep`, by the Doob-Dynkin form of
measurability for the filtration); the ranks agree whenever the values are pairwise distinct, which
holds almost surely (`ae_injective`).
-/

namespace Robbins

open MeasureTheory

theorem law_coord_eq_null {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    law N {x | x i = x j} = 0 := by
  have hS : MeasurableSet {x : Fin N → ℝ | x i = x j} :=
    measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
  have hint : Integrable ({x : Fin N → ℝ | x i = x j}.indicator (1 : (Fin N → ℝ) → ℝ)) (law N) :=
    (integrable_const (1 : ℝ)).indicator hS
  have h := integral_update j _ hint
  rw [integral_indicator_one hS] at h
  have hin : ∀ x : Fin N → ℝ, (∫ a in Set.Icc (0 : ℝ) 1,
      {x : Fin N → ℝ | x i = x j}.indicator (1 : (Fin N → ℝ) → ℝ) (Function.update x j a)) = 0 := by
    intro x
    have he : (fun a => {x : Fin N → ℝ | x i = x j}.indicator (1 : (Fin N → ℝ) → ℝ)
        (Function.update x j a)) = ({x i} : Set ℝ).indicator (1 : ℝ → ℝ) := by
      funext a
      by_cases ha : a = x i
      · rw [Set.indicator_of_mem (by simp [ha, Function.update_of_ne hij]),
          Set.indicator_of_mem (by simp [ha])]
        rfl
      · rw [Set.indicator_of_notMem, Set.indicator_of_notMem (by simpa using ha)]
        simp only [Set.mem_ofPred_eq, Function.update_self, Function.update_of_ne hij]
        exact fun e => ha e.symm
    rw [he, integral_indicator_one (measurableSet_singleton _)]
    simp only [Measure.real, Measure.restrict_apply (measurableSet_singleton _)]
    rw [measure_mono_null Set.inter_subset_left (Real.volume_singleton), ENNReal.toReal_zero]
  simp only [hin, integral_zero] at h
  exact (measureReal_eq_zero_iff).mp h

/-- The values are pairwise distinct almost surely. -/
theorem ae_injective (N : ℕ) : ∀ᵐ x ∂law N, Function.Injective x := by
  rw [MeasureTheory.ae_iff]
  have h_eq : {x : Fin N → ℝ | ¬ Function.Injective x} = {x : Fin N → ℝ | ∃ (a b : Fin N), x a = x b ∧ a ≠ b} := by
    ext x; simp [Function.not_injective_iff]
  rw [h_eq]
  let I : Set (Fin N × Fin N) := {p | p.1 ≠ p.2}
  have hI_countable : I.Countable := by
    have : Countable (Fin N × Fin N) := inferInstance
    exact Set.Countable.mono (by intro p hp; exact Set.mem_univ p) (Set.countable_univ (α := Fin N × Fin N))
  have h_eq' : {x : Fin N → ℝ | ∃ (a b : Fin N), x a = x b ∧ a ≠ b} = ⋃ p ∈ I, {x : Fin N → ℝ | x p.1 = x p.2} := by
    ext x; simp [I, and_comm]
  rw [h_eq']
  rw [MeasureTheory.measure_biUnion_null_iff hI_countable]
  intro p hp
  rw [Set.mem_ofPred_eq] at hp
  exact law_coord_eq_null p.1 p.2 hp

theorem P_eq_law (N : ℕ) : Indep.P N = law N := rfl

theorem Rule.time_le_iff {n : ℕ} (r : Rule (n + 1)) (x : Fin (n + 1) → ℝ) (t : Fin (n + 1)) :
    r.time x ≤ t ↔ ∃ s ≤ t, history x s ∈ r.stopSet s ∨ s = Fin.last n := by
  refine ⟨?_, ?_⟩
  · intro hle
    refine ⟨r.time x, hle, ?_⟩
    exact Rule.mem_or_last_time r x
  · intro h
    rcases h with ⟨s, hs_le, hs⟩
    rcases hs with (hs_mem | hs_last)
    · have htime_le_s : r.time x ≤ s := Rule.time_le_of_mem r x s hs_mem
      exact le_trans htime_le_s hs_le
    · have h_last_eq_t : t = Fin.last n := by
        apply Fin.ext
        have h_last_le_t : (Fin.last n : Fin (n + 1)) ≤ t := hs_last ▸ hs_le
        exact le_antisymm (Fin.le_last t) h_last_le_t
      have htime_le_last : r.time x ≤ Fin.last n := Fin.le_last _
      rw [h_last_eq_t]
      exact htime_le_last

theorem Rule.measurableSet_time_le_filtration {n : ℕ} (r : Rule (n + 1)) (t : Fin (n + 1)) :
    MeasurableSet[Indep.filtration (n + 1) (t.val + 1) t.isLt]
      {ω : Indep.Ω (n + 1) | (r.time ω).val ≤ t.val} := by
  -- The filtration is definitionally a comap: MeasurableSpace.comap f inferInstance
  -- where f ω i = ω (Fin.castLE t.isLt i)
  let f : Indep.Ω (n + 1) → Fin (t.val + 1) → ℝ := fun ω i => ω (Fin.castLE t.isLt i)
  -- Use MeasurableSpace.measurableSet_comap to convert to an existential
  refine ((MeasurableSpace.measurableSet_comap (f := f) (m := inferInstance) (s := {ω : Indep.Ω (n + 1) | (r.time ω).val ≤ t.val})).mpr ?_)
  -- Goal: ∃ (B : Set (Fin (t.val + 1) → ℝ)), MeasurableSet B ∧ f ⁻¹' B = {ω | (r.time ω).val ≤ t.val}
  -- Define the embedding of Fin (s.val + 1) into Fin (t.val + 1) for s ≤ t
  let emb (s : Fin (n + 1)) (hs : s ≤ t) : Fin (s.val + 1) → Fin (t.val + 1) :=
    Fin.castLE (Nat.add_le_add_right (Fin.le_iff_val_le_val.mp hs) 1)
  -- B = {h | ∃ s ≤ t, (h ∘ emb s hs) ∈ r.stopSet s ∨ s = Fin.last n}
  set B := {h : Fin (t.val + 1) → ℝ | ∃ (s : Fin (n + 1)) (hs : s ≤ t),
    (h ∘ emb s hs) ∈ r.stopSet s ∨ s = Fin.last n} with hB
  refine ⟨B, ?_, ?_⟩
  · -- MeasurableSet B
    rw [hB]
    -- The map Φ_s : h ↦ h ∘ emb s hs is measurable
    have h_meas (s : Fin (n + 1)) (hs : s ≤ t) : Measurable (fun (h : Fin (t.val + 1) → ℝ) => h ∘ emb s hs) := by
      refine Measurable.of_eval (fun i => ?_)
      simpa [emb] using measurable_pi_apply (emb s hs i)
    -- The preimage of a measurable set under a measurable map is measurable
    have h_preimage (s : Fin (n + 1)) (hs : s ≤ t) : MeasurableSet {h : Fin (t.val + 1) → ℝ | (h ∘ emb s hs) ∈ r.stopSet s} := by
      have : {h | (h ∘ emb s hs) ∈ r.stopSet s} = (fun (h : Fin (t.val + 1) → ℝ) => h ∘ emb s hs) ⁻¹' (r.stopSet s) := rfl
      rw [this]
      exact (h_meas s hs) (r.measurableSet_stopSet s)
    -- Define S as the finite set of s ≤ t
    let S : Set (Fin (n + 1)) := {s | s ≤ t}
    have hS_fin : S.Finite := by
      -- Fin (n+1) is finite, so any subset is finite
      exact Set.toFinite _
    -- Define the family f : Fin (n+1) → Set (Fin (t.val + 1) → ℝ)
    -- For s ≤ t, f s = {h | (h ∘ emb s hs) ∈ r.stopSet s ∨ s = Fin.last n}
    -- For s not ≤ t, f s = ∅
    -- But we can't refer to hs in f s. Instead, we define f s conditionally.
    -- Actually, we can define f s using a match on whether s ≤ t
    -- But the simplest is to use dite
    let f (s : Fin (n + 1)) : Set (Fin (t.val + 1) → ℝ) :=
      if hs : s ≤ t then {h | (h ∘ emb s hs) ∈ r.stopSet s ∨ s = Fin.last n} else ∅
    have hf_meas (s : Fin (n + 1)) : MeasurableSet (f s) := by
      dsimp [f]
      by_cases hs : s ≤ t
      · rw [dif_pos hs]
        by_cases hs_last : s = Fin.last n
        · subst hs_last
          have : {h : Fin (t.val + 1) → ℝ | (h ∘ emb (Fin.last n) hs) ∈ r.stopSet (Fin.last n) ∨ Fin.last n = Fin.last n} = Set.univ := by
            ext h; simp
          rw [this]
          exact MeasurableSet.univ
        · have : {h : Fin (t.val + 1) → ℝ | (h ∘ emb s hs) ∈ r.stopSet s ∨ s = Fin.last n} =
              {h | (h ∘ emb s hs) ∈ r.stopSet s} := by
            ext h; simp [hs_last]
          rw [this]
          exact h_preimage s hs
      · rw [dif_neg hs]
        exact MeasurableSet.empty
    have hB_eq : {h : Fin (t.val + 1) → ℝ | ∃ (s : Fin (n + 1)) (hs : s ≤ t), (h ∘ emb s hs) ∈ r.stopSet s ∨ s = Fin.last n} =
        (⋃ s ∈ S, f s) := by
      ext h
      constructor
      · rintro ⟨s, hs, hmem | hlast⟩
        · -- case hmem : (h ∘ emb s hs) ∈ r.stopSet s
          have hsS : s ∈ S := hs
          refine Set.mem_biUnion hsS ?_
          dsimp [f]
          rw [dif_pos hs]
          simp [hmem]
        · -- case hlast : s = Fin.last n
          -- We have hs : s ≤ t and hlast : s = Fin.last n, so Fin.last n ≤ t
          -- Thus Fin.last n ∈ S
          have hlastS : Fin.last n ∈ S := by
            rw [← hlast]
            exact hs
          refine Set.mem_biUnion hlastS ?_
          dsimp [f]
          rw [dif_pos (by rwa [← hlast])]
          simp
      · intro hmem_iUnion
        rcases Set.mem_iUnion₂.mp hmem_iUnion with ⟨s, hsS, hmem⟩
        -- hsS : s ∈ S, and S = {s | s ≤ t}, so hsS is definitionally s ≤ t
        -- hmem : h ∈ f s
        have hs_le : s ≤ t := hsS
        unfold f at hmem
        rw [dif_pos hs_le] at hmem
        simp at hmem
        rcases hmem with (hmem | hlast)
        · exact ⟨s, hs_le, Or.inl hmem⟩
        · exact ⟨s, hs_le, Or.inr hlast⟩
    rw [hB_eq]
    -- Now use Set.Finite.measurableSet_biUnion
    refine hS_fin.measurableSet_biUnion (fun s hs => ?_)
    -- hs : s ∈ S, and S = {s | s ≤ t}, so hs is definitionally s ≤ t
    have hs_le : s ≤ t := hs
    unfold f
    rw [dif_pos hs_le]
    -- Need to show MeasurableSet {h | (h ∘ emb s hs) ∈ r.stopSet s ∨ s = Fin.last n}
    by_cases hs_last : s = Fin.last n
    · subst hs_last
      have : {h : Fin (t.val + 1) → ℝ | (h ∘ emb (Fin.last n) hs) ∈ r.stopSet (Fin.last n) ∨ Fin.last n = Fin.last n} = Set.univ := by
        ext h; simp
      rw [this]
      exact MeasurableSet.univ
    · have : {h : Fin (t.val + 1) → ℝ | (h ∘ emb s hs) ∈ r.stopSet s ∨ s = Fin.last n} =
          {h | (h ∘ emb s hs) ∈ r.stopSet s} := by
        ext h; simp [hs_last]
      rw [this]
      exact h_preimage s hs
  · -- f ⁻¹' B = {ω | ↑(r.time ω) ≤ ↑t}
    ext ω
    simp [Set.mem_preimage, Set.mem_setOf_eq]
    -- Goal: f ω ∈ B ↔ ↑(r.time ω) ≤ ↑t
    have h_mem_B : f ω ∈ B ↔ ∃ (s : Fin (n + 1)) (hs : s ≤ t), (f ω ∘ emb s hs) ∈ r.stopSet s ∨ s = Fin.last n := by
      simp [B]
    rw [h_mem_B]
    -- Goal: (∃ s, ∃ (hs : s ≤ t), (f ω ∘ emb s hs) ∈ r.stopSet s ∨ s = Fin.last n) ↔ ↑(r.time ω) ≤ ↑t
    have h_comp (s : Fin (n + 1)) (hs : s ≤ t) : f ω ∘ emb s hs = Robbins.history ω s := by
      ext i
      simp [f, emb, Robbins.history, Fin.castLE_comp_castLE (Nat.add_le_add_right (Fin.le_iff_val_le_val.mp hs) 1) t.isLt]
    simp_rw [h_comp]
    -- Goal: (∃ s, ∃ (_ : s ≤ t), Robbins.history ω s ∈ r.stopSet s ∨ s = Fin.last n) ↔ r.time ω ≤ t
    -- Rule.time_le_iff r ω t : r.time ω ≤ t ↔ ∃ s ≤ t, Robbins.history ω s ∈ r.stopSet s ∨ s = Fin.last n
    simpa using (Rule.time_le_iff r ω t).symm

/-- A rule, as a stopping rule of the separate formalization. -/
noncomputable def Rule.toIndep {n : ℕ} (r : Rule (n + 1)) : Indep.StoppingRule (n + 1) where
  τ := r.time
  measurable_τ := r.measurable_time
  stopping_time t := r.measurableSet_time_le_filtration t

theorem selectedRank_eq_of_injective {n : ℕ} (τ : Indep.StoppingRule n) (x : Fin n → ℝ)
    (hx : Function.Injective x) :
    Indep.selectedRank n τ x = 1 + (Finset.univ.filter fun j => x j < x (τ.τ x)).card := by
  unfold Indep.selectedRank Indep.rankValue Indep.X
  dsimp
  congr 1
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injective _ hx]

theorem Rule.expectedRank_toIndep {n : ℕ} (r : Rule (n + 1)) :
    Indep.expectedRank (n + 1) r.toIndep = r.expectedRank := by
  unfold Indep.expectedRank Rule.expectedRank
  rw [P_eq_law]
  refine integral_congr_ae ?_
  filter_upwards [ae_injective (n + 1)] with x hx
  rw [selectedRank_eq_of_injective r.toIndep x hx]
  rfl

theorem exists_stopSet {n : ℕ} (τ : Indep.StoppingRule (n + 1)) (t : Fin (n + 1)) :
    ∃ B : Set (Fin (t + 1) → ℝ), MeasurableSet B ∧
      ∀ x : Fin (n + 1) → ℝ, (history x t ∈ B ↔ (τ.τ x).val ≤ t.val) := by
  have h_stop := τ.stopping_time t
  let hk : t.val + 1 ≤ n + 1 := by
    have := t.is_lt
    omega
  let f : Indep.Ω (n + 1) → (Fin (t + 1) → ℝ) := fun ω i => ω (Fin.castLE hk i)
  have h_meas : @MeasurableSet (Indep.Ω (n + 1)) (MeasurableSpace.comap f inferInstance) {ω | (τ.τ ω).val ≤ t.val} := by
    simpa [Indep.filtration, f] using h_stop
  rcases ((MeasurableSpace.measurableSet_comap (f := f)).mp h_meas) with ⟨B, hB_meas, hB_eq⟩
  refine ⟨B, hB_meas, ?_⟩
  intro x
  have h_history_eq_fx : history x t = f x := by
    ext s
    simp [Robbins.history, f]
  rw [h_history_eq_fx]
  rw [← Set.mem_preimage]
  rw [hB_eq]
  simp

/-- A stopping rule of the separate formalization, as a rule: at time `t`, the histories on which it
has stopped by `t`. -/
noncomputable def ofIndep {n : ℕ} (τ : Indep.StoppingRule (n + 1)) : Rule (n + 1) where
  stopSet t := (exists_stopSet τ t).choose
  measurableSet_stopSet t := (exists_stopSet τ t).choose_spec.1

theorem time_ofIndep {n : ℕ} (τ : Indep.StoppingRule (n + 1)) (x : Fin (n + 1) → ℝ) :
    (ofIndep τ).time x = τ.τ x := by
  apply (Rule.time_eq_iff (ofIndep τ) x (τ.τ x)).mpr
  constructor
  · left
    have h := (exists_stopSet τ (τ.τ x)).choose_spec.2 x
    simpa [ofIndep] using (h.2 le_rfl)
  · intro s hs
    have h := (exists_stopSet τ s).choose_spec.2 x
    have hlt : (s : ℕ) < (τ.τ x : ℕ) := Fin.lt_def.mp hs
    simpa [ofIndep] using fun hmem => by
      have hle := h.1 hmem
      omega

theorem expectedRank_ofIndep {n : ℕ} (τ : Indep.StoppingRule (n + 1)) :
    (ofIndep τ).expectedRank = Indep.expectedRank (n + 1) τ := by
  unfold Indep.expectedRank Rule.expectedRank
  rw [P_eq_law]
  refine integral_congr_ae ?_
  filter_upwards [ae_injective (n + 1)] with x hx
  have hrank : (ofIndep τ).rank x = Indep.selectedRank (n + 1) τ x := by
    dsimp [Rule.rank]
    rw [time_ofIndep τ x, selectedRank_eq_of_injective τ x hx]
  simp [hrank]

/-- The two formalizations give the same optimal value for every positive number of values. -/
theorem robbinsValue_eq_v (n : ℕ) : Indep.robbinsValue (n + 1) = v (n + 1) := by
  have h : {c : ℝ | ∃ τ : Indep.StoppingRule (n + 1), Indep.expectedRank (n + 1) τ = c} =
      Set.range fun r : Rule (n + 1) => r.expectedRank := by
    ext c
    constructor
    · rintro ⟨τ, rfl⟩
      exact ⟨ofIndep τ, expectedRank_ofIndep τ⟩
    · rintro ⟨r, rfl⟩
      exact ⟨r.toIndep, r.expectedRank_toIndep⟩
  rw [Indep.robbinsValue, h]
  rfl

end Robbins
