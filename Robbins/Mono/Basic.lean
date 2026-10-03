import Robbins.Mono.Defs
import Robbins.Basic.Rank

/-!
# Monotonicity of `v`: integration, scaling, the first-argmax partition

* `integral_law_succ_insertNth`: integrate the coordinate `J` out (`MeasurableEquiv.piFinSuccAbove`);
* `integral_scale`: the substitution `z = w y` on `[0, w]^N`, Jacobian `w ^ N`;
* `sum_indicator_firstMax`: the sets `firstMax J` partition the space;
* the values of `virt` and the count `card_virt_lt`.
-/

namespace Robbins

open MeasureTheory

theorem integral_law_succ_insertNth {N : ℕ} (J : Fin (N + 1)) (f : (Fin (N + 1) → ℝ) → ℝ)
    (hf : Integrable f (law (N + 1))) :
    ∫ x, f x ∂law (N + 1) =
      ∫ w in Set.Icc (0 : ℝ) 1, (∫ z, f (Fin.insertNth (α := fun _ => ℝ) J w z) ∂law N) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) J with he
  have hmp : MeasurePreserving e (law (N + 1)) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (law N)) := by
    rw [he]
    exact measurePreserving_piFinSuccAbove (fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)) J
  have h_symm_apply : ∀ (w : ℝ) (z : Fin N → ℝ) (j : Fin (N + 1)),
      e.symm (w, z) j = Fin.insertNth (α := fun _ : Fin (N + 1) => ℝ) J w z j := by
    intro w z j
    rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv_apply (α := fun _ : Fin (N + 1) => ℝ) (p := J)]
  have h_int : Integrable (fun (p : ℝ × (Fin N → ℝ)) => f (e.symm p))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (law N)) :=
    hmp.symm.integrable_comp_of_integrable hf
  calc
    ∫ x, f x ∂law (N + 1) = ∫ p, f (e.symm p) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (law N)) := by
      rw [hmp.symm.integral_comp' f]
    _ = ∫ w, ∫ z, f (e.symm (w, z)) ∂law N ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      rw [integral_prod _ h_int]
    _ = ∫ w in Set.Icc (0 : ℝ) 1, (∫ z, f (e.symm (w, z)) ∂law N) := rfl
    _ = ∫ w in Set.Icc (0 : ℝ) 1, (∫ z, f (Fin.insertNth (α := fun _ => ℝ) J w z) ∂law N) := by
      refine setIntegral_congr_fun measurableSet_Icc ?_
      intro w hw
      refine integral_congr_ae ?_
      filter_upwards with z
      have h_eq : e.symm (w, z) = Fin.insertNth (α := fun _ => ℝ) J w z := by
        ext j
        exact h_symm_apply w z j
      simp [h_eq]

theorem integrable_integral_insertNth {N : ℕ} (J : Fin (N + 1)) (f : (Fin (N + 1) → ℝ) → ℝ)
    (hf : Integrable f (law (N + 1))) :
    Integrable (fun w => ∫ z, f (Fin.insertNth (α := fun _ => ℝ) J w z) ∂law N)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) J
  have hmp : MeasurePreserving e (law (N + 1)) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (law N)) :=
    MeasureTheory.measurePreserving_piFinSuccAbove (fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)) J
  have hg : Integrable (f ∘ e.symm) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (law N)) :=
    hmp.symm.integrable_comp_of_integrable hf
  have h_int := hg.integral_prod_left
  have h_eq : (fun (x : ℝ) => ∫ (y : Fin N → ℝ), (f ∘ e.symm) (x, y) ∂law N) =
      (fun (w : ℝ) => ∫ (z : Fin N → ℝ), f (J.insertNth w z) ∂law N) := by
    ext w
    refine integral_congr_ae ?_
    filter_upwards with y
    have : (Fin.insertNthEquiv (fun _ : Fin (N + 1) => ℝ) J) (w, y) = J.insertNth w y := by
      ext j
      simp [Fin.insertNthEquiv]
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, this]
  convert h_int using 1
  exact h_eq.symm

theorem ae_ne_one (N : ℕ) : ∀ᵐ y ∂law N, ∀ j, y j ≠ 1 := by
  rw [MeasureTheory.ae_all_iff]
  intro j
  exact MeasureTheory.Measure.ae_eval_ne (μ := fun _ : Fin N => volume.restrict (Set.Icc (0 : ℝ) 1)) (i := j) (x := 1)

theorem integral_Icc_pow (N : ℕ) : ∫ w in Set.Icc (0 : ℝ) 1, w ^ N = 1 / ((N : ℝ) + 1) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le zero_le_one]
  rw [integral_pow]
  simp

theorem measurable_scale {N : ℕ} (w : ℝ) : Measurable (scale w : (Fin N → ℝ) → Fin N → ℝ) := by
  refine measurable_pi_iff.mpr fun i => ?_
  apply measurable_const.mul
  exact measurable_pi_apply i

theorem law_restrict_box {N : ℕ} {w : ℝ} (hw0 : 0 < w) (hw1 : w ≤ 1) :
    (law N).restrict {z | ∀ i, z i ≤ w} = ENNReal.ofReal (w ^ N) • (law N).map (scale w) := by
  have hB : {z : Fin N → ℝ | ∀ i, z i ≤ w} = Set.pi Set.univ (fun _ => Set.Iic w) := by
    ext z
    exact ⟨fun h i _ => h i, fun h i => h i trivial⟩
  rw [hB]
  unfold law
  rw [Measure.restrict_pi_pi]
  refine Measure.pi_eq fun s hs => ?_
  have hpre : scale w ⁻¹' Set.pi Set.univ s = Set.pi Set.univ (fun i => (fun a => w * a) ⁻¹' s i) := by
    ext z; simp [scale, Set.mem_pi]
  have hA : ∀ i, (fun a : ℝ => w * a) ⁻¹' s i ∩ Set.Icc 0 1 =
      (fun a : ℝ => w * a) ⁻¹' (s i ∩ Set.Icc 0 w) := by
    intro i
    ext a
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by positivity, by nlinarith⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, ?_⟩
      · by_contra h; rw [not_le] at h; nlinarith
      · by_contra h; rw [not_le] at h; nlinarith
  have hC : ∀ i, s i ∩ Set.Iic w ∩ Set.Icc 0 1 = s i ∩ Set.Icc 0 w := by
    intro i
    ext a
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, _⟩; exact ⟨h1, h3, h2⟩
    · rintro ⟨h1, h3, h2⟩; exact ⟨⟨h1, h2⟩, h3, h2.trans hw1⟩
  rw [Measure.smul_apply, Measure.map_apply (measurable_scale w) (MeasurableSet.univ_pi hs), hpre,
    Measure.pi_pi, smul_eq_mul]
  simp_rw [Measure.restrict_apply' measurableSet_Iic, Measure.restrict_apply' measurableSet_Icc, hA, hC, Real.volume_preimage_mul_left hw0.ne',
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_assoc]
  rw [abs_of_pos (inv_pos.mpr hw0), ← ENNReal.ofReal_pow (inv_pos.mpr hw0).le,
    ← ENNReal.ofReal_mul (pow_nonneg hw0.le N), ← mul_pow, mul_inv_cancel₀ hw0.ne', one_pow,
    ENNReal.ofReal_one, one_mul]

theorem integral_scale {N : ℕ} {w : ℝ} (hw0 : 0 < w) (hw1 : w ≤ 1) (g : (Fin N → ℝ) → ℝ)
    (hg : Measurable g) (hsupp : ∀ z, g z ≠ 0 → ∀ i, z i ≤ w) :
    ∫ z, g z ∂law N = w ^ N * ∫ y, g (scale w y) ∂law N := by
  have hwN_nonneg : 0 ≤ w ^ N := pow_nonneg (by linarith) N
  set s := {z : Fin N → ℝ | ∀ i, z i ≤ w} with hs
  have hmeas : MeasurableSet s := by
    dsimp [s]
    refine MeasurableSet.univ_pi' (t := fun _ : Fin N => Set.Iic w) (fun i => ?_)
    exact measurableSet_Iic
  have h_vanishes : ∀ z, z ∉ s → g z = 0 := by
    intro z hz
    by_contra! hgz
    have hz' := hsupp z hgz
    exact hz hz'
  calc
    ∫ z, g z ∂law N = ∫ z in s, g z ∂law N :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero h_vanishes).symm
    _ = ∫ z, g z ∂(ENNReal.ofReal (w ^ N) • (law N).map (scale w)) := by
      rw [law_restrict_box hw0 hw1]
    _ = (ENNReal.ofReal (w ^ N)).toReal • ∫ z, g z ∂((law N).map (scale w)) := by
      rw [integral_smul_measure]
    _ = (ENNReal.ofReal (w ^ N)).toReal * ∫ z, g z ∂((law N).map (scale w)) := by simp
    _ = w ^ N * ∫ z, g z ∂((law N).map (scale w)) := by
      rw [ENNReal.toReal_ofReal hwN_nonneg]
    _ = w ^ N * ∫ y, g (scale w y) ∂law N := by
      rw [integral_map (measurable_scale w).aemeasurable hg.aestronglyMeasurable]

theorem measurableSet_firstMax {N : ℕ} (J : Fin (N + 1)) : MeasurableSet (firstMax J) := by
  unfold firstMax
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => ?_
  by_cases h : (i : Fin (N + 1)) < J
  · have h' : ¬ (J < (i : Fin (N + 1))) := by
      intro hji
      exact Fin.lt_asymm h hji
    have hset : {x : Fin (N + 1) → ℝ | ((i : Fin (N + 1)) < J → x i < x J) ∧ (J < (i : Fin (N + 1)) → x i ≤ x J)} = {x : Fin (N + 1) → ℝ | x i < x J} := by
      ext x; simp [h, h']
    rw [hset]
    exact measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply J)
  · by_cases h' : J < (i : Fin (N + 1))
    · have hset : {x : Fin (N + 1) → ℝ | ((i : Fin (N + 1)) < J → x i < x J) ∧ (J < (i : Fin (N + 1)) → x i ≤ x J)} = {x : Fin (N + 1) → ℝ | x i ≤ x J} := by
        ext x; simp [h, h']
      rw [hset]
      exact measurableSet_le (measurable_pi_apply i) (measurable_pi_apply J)
    · have hset : {x : Fin (N + 1) → ℝ | ((i : Fin (N + 1)) < J → x i < x J) ∧ (J < (i : Fin (N + 1)) → x i ≤ x J)} = Set.univ := by
        ext x; simp [h, h']
      rw [hset]
      exact MeasurableSet.univ

theorem measurableSet_belowMax {N : ℕ} (J : Fin (N + 1)) (w : ℝ) :
    MeasurableSet (belowMax J w) := by
  unfold belowMax
  have h_eq : {z : Fin N → ℝ | ∀ j : Fin N, ((j : ℕ) < J → z j < w) ∧ ((J : ℕ) ≤ j → z j ≤ w)} =
      ⋂ j : Fin N, {z : Fin N → ℝ | ((j : ℕ) < J → z j < w) ∧ ((J : ℕ) ≤ j → z j ≤ w)} := by
    ext z; simp
  rw [h_eq]
  refine MeasurableSet.iInter fun j => ?_
  by_cases hlt : (j : ℕ) < J
  · have h_eq2 : {z : Fin N → ℝ | ((j : ℕ) < J → z j < w) ∧ ((J : ℕ) ≤ j → z j ≤ w)} =
        {z : Fin N → ℝ | z j < w} := by
      ext z; simp [hlt, not_le.mpr hlt]
    rw [h_eq2]
    exact measurableSet_lt (measurable_pi_apply j) measurable_const
  · have hle : (J : ℕ) ≤ j := by omega
    have h_eq2 : {z : Fin N → ℝ | ((j : ℕ) < J → z j < w) ∧ ((J : ℕ) ≤ j → z j ≤ w)} =
        {z : Fin N → ℝ | z j ≤ w} := by
      ext z; simp [hlt, hle]
    rw [h_eq2]
    exact measurableSet_le (measurable_pi_apply j) measurable_const

theorem existsUnique_firstMax {N : ℕ} (x : Fin (N + 1) → ℝ) : ∃! J, x ∈ firstMax J := by
  have h_nonempty : (Finset.univ : Finset (Fin (N + 1))).Nonempty := Finset.univ_nonempty
  -- Obtain an index M where x attains its maximum
  obtain ⟨M, hM_mem, hM_max⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (N + 1))) x h_nonempty
  have hM_max' : ∀ i, x i ≤ x M := by
    intro i
    exact hM_max i (Finset.mem_univ i)
  -- The set of indices where x equals the maximum value x M
  let S : Finset (Fin (N + 1)) := Finset.univ.filter fun i => x i = x M
  have hS_nonempty : S.Nonempty := by
    refine ⟨M, ?_⟩
    simp [S, hM_mem]
  -- J is the smallest index where the maximum is attained
  let J := S.min' hS_nonempty
  have hJ_mem_S : J ∈ S := Finset.min'_mem _ hS_nonempty
  have hJ_max : x J = x M := by
    simpa [S] using hJ_mem_S
  have hJ_min : ∀ i, i ∈ S → J ≤ i := fun i hi => Finset.min'_le S i hi
  -- Show x ∈ firstMax J
  have h_firstMax : x ∈ firstMax J := by
    dsimp [firstMax]
    intro i
    constructor
    · intro hi
      have h_le : x i ≤ x J := by
        rw [hJ_max]
        exact hM_max' i
      have h_ne : x i ≠ x J := by
        intro h_eq
        have hi_mem_S : i ∈ S := by
          simp [S, h_eq, hJ_max]
        have h_le' : J ≤ i := hJ_min i hi_mem_S
        exact Fin.not_lt.mpr h_le' hi
      exact lt_of_le_of_ne h_le h_ne
    · intro hi
      rw [hJ_max]
      exact hM_max' i
  -- Uniqueness
  refine ⟨J, h_firstMax, ?_⟩
  intro K hK
  by_contra! h_ne
  have h_lt_or : J < K ∨ K < J := Fin.lt_or_lt_of_ne h_ne.symm
  rcases h_lt_or with (h_lt | h_lt)
  · -- J < K
    have hJK : x J < x K := ((hK J).1 h_lt)
    have hKJ : x K ≤ x J := ((h_firstMax K).2 h_lt)
    exact not_lt.mpr hKJ hJK
  · -- K < J
    have hKJ : x K < x J := ((h_firstMax K).1 h_lt)
    have hJK : x J ≤ x K := ((hK J).2 h_lt)
    exact not_lt.mpr hJK hKJ

theorem sum_indicator_firstMax {N : ℕ} (f : (Fin (N + 1) → ℝ) → ℝ) (x : Fin (N + 1) → ℝ) :
    ∑ J, (firstMax J).indicator f x = f x := by
  rcases existsUnique_firstMax x with ⟨J, hJ, huniq⟩
  have hsum := Finset.sum_eq_single J
    (by
      intro K _ hK_ne_J
      have hnot : x ∉ firstMax K := mt (huniq K) hK_ne_J
      exact Set.indicator_of_notMem hnot f)
    (by
      intro hJ_not_mem
      exact absurd (Finset.mem_univ J) hJ_not_mem)
  simpa [Set.indicator_of_mem hJ f] using hsum

theorem insertNth_mem_firstMax {N : ℕ} (J : Fin (N + 1)) (w : ℝ) (z : Fin N → ℝ) :
    Fin.insertNth (α := fun _ => ℝ) J w z ∈ firstMax J ↔ z ∈ belowMax J w := by
  constructor
  · intro h j
    have hmem := h (J.succAbove j)
    rcases hmem with ⟨hlt, hle⟩
    have h_same := Fin.insertNth_apply_same (α := fun _ => ℝ) J w z
    have h_insert := Fin.insertNth_apply_succAbove (α := fun _ => ℝ) J w z j
    constructor
    · intro hj
      have h_cast_lt : j.castSucc < J := by
        change (j.castSucc).val < J.val
        rw [Fin.val_castSucc j]
        exact hj
      have h_eq : J.succAbove j = j.castSucc := Fin.succAbove_of_castSucc_lt J j h_cast_lt
      have h_lt' : J.succAbove j < J := by
        rw [h_eq]
        exact h_cast_lt
      have h_lt_w : (Fin.insertNth (α := fun _ => ℝ) J w z) (J.succAbove j) < w := by
        simpa [h_same] using hlt h_lt'
      simpa [h_insert] using h_lt_w
    · intro hJ
      have h_le : J ≤ j.castSucc := by
        change J.val ≤ (j.castSucc).val
        rw [Fin.val_castSucc j]
        exact hJ
      have h_eq : J.succAbove j = j.succ := Fin.succAbove_of_le_castSucc J j h_le
      have h_lt' : J < J.succAbove j := by
        rw [Fin.lt_succAbove_iff_le_castSucc]
        exact h_le
      have h_le_w : (Fin.insertNth (α := fun _ => ℝ) J w z) (J.succAbove j) ≤ w := by
        simpa [h_same] using hle h_lt'
      simpa [h_insert] using h_le_w
  · intro hz i
    by_cases h_eq : i = J
    · rw [h_eq]
      constructor
      · intro h; exact absurd h (lt_irrefl J)
      · intro h; exact absurd h (lt_irrefl J)
    · rcases Fin.exists_succAbove_eq h_eq with ⟨j, hj_eq⟩
      -- hj_eq : J.succAbove j = i
      have hz_j := hz j
      rcases hz_j with ⟨hz_lt, hz_le⟩
      have h_insert := Fin.insertNth_apply_succAbove (α := fun _ => ℝ) J w z j
      have h_same := Fin.insertNth_apply_same (α := fun _ => ℝ) J w z
      constructor
      · intro h_lt
        -- h_lt : i < J, and hj_eq: J.succAbove j = i
        -- So J.succAbove j < J
        have h_lt_sa : J.succAbove j < J := by
          rwa [← hj_eq] at h_lt
        by_cases hj : (j : ℕ) < J
        · have h_cast_lt : j.castSucc < J := by
            change (j.castSucc).val < J.val
            rw [Fin.val_castSucc j]
            exact hj
          have h_eq_sa : J.succAbove j = j.castSucc := Fin.succAbove_of_castSucc_lt J j h_cast_lt
          have h_lt_w : z j < w := hz_lt hj
          rw [h_eq_sa] at h_lt_sa
          -- Now h_lt_sa: j.castSucc < J, which is consistent
          simpa [← hj_eq, h_insert] using h_lt_w
        · have hJ_le : (J : ℕ) ≤ j := Nat.ge_of_not_lt hj
          have h_le : J ≤ j.castSucc := by
            change J.val ≤ (j.castSucc).val
            rw [Fin.val_castSucc j]
            exact hJ_le
          have h_eq_sa : J.succAbove j = j.succ := Fin.succAbove_of_le_castSucc J j h_le
          rw [h_eq_sa] at h_lt_sa
          -- Now h_lt_sa: j.succ < J, but this contradicts hJ_le
          have : ¬ (j.succ < J) := by
            intro h_contra
            have h_contra' : (j.succ : ℕ) < J := h_contra
            have h_val_succ : (j.succ : ℕ) = (j : ℕ) + 1 := Fin.val_succ j
            have : (j : ℕ) < J := by omega
            exact hj this
          exact absurd h_lt_sa this
      · intro h_lt
        -- h_lt : J < i, and hj_eq: J.succAbove j = i
        -- So J < J.succAbove j
        have h_lt_sa : J < J.succAbove j := by
          rwa [← hj_eq] at h_lt
        by_cases hj : (j : ℕ) < J
        · have h_cast_lt : j.castSucc < J := by
            change (j.castSucc).val < J.val
            rw [Fin.val_castSucc j]
            exact hj
          have h_eq_sa : J.succAbove j = j.castSucc := Fin.succAbove_of_castSucc_lt J j h_cast_lt
          rw [h_eq_sa] at h_lt_sa
          -- Now h_lt_sa: J < j.castSucc, but this contradicts hj
          have : ¬ (J < j.castSucc) := by
            intro h_contra
            have : (J : ℕ) < (j : ℕ) := by
              -- from J < j.castSucc we get J.val < (j.castSucc).val = j.val
              change J.val < (j.castSucc).val at h_contra
              rw [Fin.val_castSucc j] at h_contra
              exact h_contra
            omega
          exact absurd h_lt_sa this
        · have hJ_le : (J : ℕ) ≤ j := Nat.ge_of_not_lt hj
          have h_le : J ≤ j.castSucc := by
            change J.val ≤ (j.castSucc).val
            rw [Fin.val_castSucc j]
            exact hJ_le
          have h_eq_sa : J.succAbove j = j.succ := Fin.succAbove_of_le_castSucc J j h_le
          have h_le_w : z j ≤ w := hz_le hJ_le
          rw [h_eq_sa] at h_lt_sa
          -- Now h_lt_sa: J < j.succ, which is consistent
          simpa [← hj_eq, h_insert] using h_le_w

theorem scale_mem_belowMax {N : ℕ} (J : Fin (N + 1)) {w : ℝ} (hw : 0 < w) (y : Fin N → ℝ) :
    scale w y ∈ belowMax J w ↔ y ∈ belowMax J 1 := by
  unfold belowMax scale
  constructor
  · intro h j
    have hj := h j
    constructor
    · intro hlt
      exact (mul_lt_iff_lt_one_right hw).mp (hj.1 hlt)
    · intro hle
      exact (mul_le_iff_le_one_right hw).mp (hj.2 hle)
  · intro h j
    have hj := h j
    constructor
    · intro hlt
      exact (mul_lt_iff_lt_one_right hw).mpr (hj.1 hlt)
    · intro hle
      exact (mul_le_iff_le_one_right hw).mpr (hj.2 hle)

theorem le_of_mem_belowMax {N : ℕ} {J : Fin (N + 1)} {w : ℝ} {z : Fin N → ℝ}
    (hz : z ∈ belowMax J w) (i : Fin N) : z i ≤ w := by
  have hi := hz i
  rcases hi with ⟨hlt, hle⟩
  by_cases h : (i : ℕ) < (J : ℕ)
  · exact (hlt h).le
  · have hge : (J : ℕ) ≤ (i : ℕ) := Nat.le_of_not_lt h
    exact hle hge

theorem mem_belowMax_one {N : ℕ} (J : Fin (N + 1)) {y : Fin N → ℝ} (hy : ∀ j, y j < 1) :
    y ∈ belowMax J 1 := by
  exact fun j => ⟨fun _ => hy j, fun _ => (hy j).le⟩

theorem virt_apply_same {N : ℕ} (J : Fin (N + 1)) (w : ℝ) (y : Fin N → ℝ) : virt J w y J = w := by
  simpa [virt] using Fin.insertNth_apply_same J w (scale w y)

theorem virt_apply_lt {N : ℕ} (J : Fin (N + 1)) (w : ℝ) (y : Fin N → ℝ) (t : Fin (N + 1))
    (ht : (t : ℕ) < J) : virt J w y t = w * y ⟨t, by omega⟩ := by
  set j : Fin N := ⟨t, by
    have : (t : ℕ) < N := by
      have hJ : (J : ℕ) ≤ N := by omega
      omega
    exact this
    ⟩ with hj
  have h_lt : j.castSucc < J := by
    simpa [hj] using ht
  have h_eq : J.succAbove j = j.castSucc :=
    Fin.succAbove_of_castSucc_lt J j h_lt
  have h_cast_eq : j.castSucc = t := by
    ext; simp [hj]
  dsimp [virt, scale]
  have h_t_eq : t = J.succAbove j := by
    rw [h_eq, h_cast_eq]
  rw [h_t_eq]
  rw [Fin.insertNth_apply_succAbove]
  rfl

theorem virt_apply_gt {N : ℕ} (J : Fin (N + 1)) (w : ℝ) (y : Fin N → ℝ) (t : Fin (N + 1))
    (ht : (J : ℕ) < t) : virt J w y t = w * y ⟨t - 1, by omega⟩ := by
  have ht0 : t ≠ 0 := by
    intro hzero
    have hzero' : (t : ℕ) = 0 := by simpa [hzero] using rfl
    have : (J : ℕ) < 0 := by simpa [hzero'] using ht
    exact Nat.not_lt_zero _ this
  set j := t.pred ht0 with hj_def
  have hj_succ : j.succ = t := Fin.succ_pred t ht0
  have hJ_lt : (J : Fin (N + 1)) < j.succ := by
    simpa [hj_succ] using ht
  have h_succAbove : J.succAbove j = t := by
    calc
      J.succAbove j = j.succ := Fin.succAbove_of_lt_succ J j hJ_lt
      _ = t := hj_succ
  have hj_eq : j = ⟨(t : ℕ) - 1, by
    have : (t : ℕ) < N + 1 := t.isLt
    omega
  ⟩ := by
    ext
    simpa [hj_def] using Fin.val_pred t ht0
  calc
    virt J w y t = virt J w y (J.succAbove j) := by rw [h_succAbove]
    _ = (Fin.insertNth (α := fun _ => ℝ) J w (scale w y)) (J.succAbove j) := rfl
    _ = scale w y j := by
      rw [Fin.insertNth_apply_succAbove (α := fun _ => ℝ) J w (scale w y) j]
    _ = w * y j := rfl
    _ = w * y ⟨(t : ℕ) - 1, by
      have : (t : ℕ) < N + 1 := t.isLt
      omega
    ⟩ := by rw [hj_eq]

theorem card_virt_lt {N : ℕ} (J : Fin (N + 1)) (w : ℝ) (y : Fin N → ℝ) (c : ℝ) :
    (Finset.univ.filter fun k => virt J w y k < c).card =
      (Finset.univ.filter fun j => w * y j < c).card + (if w < c then 1 else 0) := by
  calc
    (Finset.univ.filter fun k => virt J w y k < c).card
        = ∑ k : Fin (N + 1), if virt J w y k < c then 1 else 0 := by
      rw [Finset.card_filter]
    _ = (if virt J w y J < c then 1 else 0) + ∑ j : Fin N, if virt J w y (J.succAbove j) < c then 1 else 0 := by
      rw [Fin.sum_univ_succAbove]
    _ = (if w < c then 1 else 0) + ∑ j : Fin N, if w * y j < c then 1 else 0 := by
      simp [virt, scale, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    _ = (∑ j : Fin N, if w * y j < c then 1 else 0) + (if w < c then 1 else 0) := by
      rw [add_comm]
    _ = (Finset.univ.filter fun j => w * y j < c).card + (if w < c then 1 else 0) := by
      rw [Finset.card_filter]

theorem history_virt_congr {N : ℕ} (J : Fin (N + 1)) (w : ℝ) {y y' : Fin N → ℝ} (k : Fin (N + 1))
    (hyy : ∀ j : Fin N, (J.succAbove j : ℕ) ≤ k → y j = y' j) :
    history (virt J w y) k = history (virt J w y') k := by
  ext s
  unfold history
  by_cases hJ : Fin.castLE k.isLt s = J
  · subst hJ
    simp [virt]
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hJ
    have h_val_le : (Fin.castLE k.isLt s : ℕ) ≤ (k : ℕ) := by
      have h_s_le_k : (s : ℕ) ≤ (k : ℕ) := by
        have := s.2
        omega
      simpa [Fin.val_castLE] using h_s_le_k
    have h_succAbove_le_k : (J.succAbove j : ℕ) ≤ (k : ℕ) := by
      rw [hj]
      exact h_val_le
    have hy_eq : y j = y' j := hyy j h_succAbove_le_k
    have hleft : virt J w y (Fin.castLE k.isLt s) = w * y j := by
      dsimp [virt]
      rw [← hj, Fin.insertNth_apply_succAbove]
      rfl
    have hright : virt J w y' (Fin.castLE k.isLt s) = w * y' j := by
      dsimp [virt]
      rw [← hj, Fin.insertNth_apply_succAbove]
      rfl
    rw [hleft, hright, hy_eq]

theorem pad_history {N : ℕ} (y : Fin N → ℝ) (i j : Fin N) (hj : (j : ℕ) ≤ i) :
    pad i (history y i) j = y j := by
  unfold pad history
  simp [hj]

end Robbins
