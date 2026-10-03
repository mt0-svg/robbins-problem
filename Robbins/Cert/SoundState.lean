import Robbins.Cert.SoundGrid
import Robbins.Relax.TheoremB

/-!
# The bound at one state of the certificate

The first-order certificate. Fix a time `t < n`, a state `k`
of `G_t` (a sorted tuple of local indices), its memory `val t k` (the point values over `D`), and a
table `N` of time `t + 1`, nonincreasing on states. The integrand of (R_t) at `val t k` is
`min (relaxStop n t (val t k) x) (dropPenalty n t (val t k) x + N (ceil_{t+1} (ins (val t k) x)) / D)`.

On the cell `i` of `P_t` (`cp t (i - 1) < x D ≤ cp t i`): the stop cost is `alpha i + r x`
(`relaxStop_of_cell`), the continuation is at least `C_i / D` (`cont_ge_of_cell`); above the top
`g_m` of the memory the continuation is `(1 - x) ^ r + U / D` exactly (`cont_of_ge`). The sequence
`C_i` is nonincreasing and `alpha_i` nondecreasing (`cC_anti`, `alpha_mono`), so a local crossing
`c` separates the stop cells from the continuation cells (`pos_of_crossOK`, `not_pos_of_crossOK`).
`specR_le_integral` is the bound `R ≤ 2 D ^ 2 ∫`.
-/

namespace Robbins.Cert

open MeasureTheory intervalIntegral

/-! ## Memories and integrals -/

theorem drop_of_le {d : ℕ} (y : Fin (d + 1) → ℝ) {x : ℝ} (hx : x ≤ y (Fin.last d)) :
    drop y x = y (Fin.last d) := by
  unfold drop
  simp [Fin.last] at hx
  simp [Fin.last]
  exact hx

theorem drop_of_ge {d : ℕ} (y : Fin (d + 1) → ℝ) {x : ℝ} (hx : y (Fin.last d) ≤ x) :
    drop y x = x := by
  unfold drop
  split
  · omega
  · rename_i h
    have hlast : (⟨d + 1 - 1, by omega⟩ : Fin (d + 1)) = Fin.last d := by
      ext; simp
    rw [hlast]
    exact max_eq_right hx

theorem ins_of_ge {d : ℕ} {y : Fin (d + 1) → ℝ} (hy : IsMemory y) {x : ℝ}
    (hx : y (Fin.last d) ≤ x) : ins y x = y := by
  ext l
  unfold ins
  have hmem := hy.2 l
  have h0 : (0 : ℝ) ≤ y l := hmem.1
  have hle_last : y l ≤ y (Fin.last d) := hy.1 (Fin.le_last l)
  have hmin : min (y l) x = y l := min_eq_left (hle_last.trans hx)
  split_ifs with hzero
  · rw [hmin]
    exact max_eq_right h0
  · have hval : (l : ℕ) - 1 < d + 1 := by
      have hl' : (l : ℕ) < d + 1 := l.2
      omega
    have hfinle : (⟨(l : ℕ) - 1, hval⟩ : Fin (d + 1)) ≤ l :=
      (Fin.mk_le_mk.mpr (by omega))
    have hyle : y ⟨(l : ℕ) - 1, hval⟩ ≤ y l := hy.1 hfinle
    rw [hmin]
    exact max_eq_right hyle

theorem integral_ite_lt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫ x in (0 : ℝ)..b, (if a < x then (1 : ℝ) else 0) = max 0 (b - a) := by
  set f : ℝ → ℝ := fun x => if a < x then (1 : ℝ) else 0
  by_cases h : b ≤ a
  · -- case b ≤ a: max 0 (b - a) = 0, integrand is 0 on [0, b]
    have hmax : max 0 (b - a) = 0 := by
      rw [max_eq_left (sub_nonpos.mpr h)]
    rw [hmax]
    -- on [0, b], f x = 0 because x ≤ b ≤ a
    have h_eq_on : ∀ x, x ∈ Set.uIcc (0 : ℝ) b → f x = (0 : ℝ) := by
      intro x hx
      rcases Set.mem_uIcc.1 hx with (⟨hx0, hxb⟩ | ⟨hbx, hx0⟩)
      · -- 0 ≤ x ∧ x ≤ b
        have hxa : x ≤ a := le_trans hxb h
        dsimp [f]
        simp [not_lt.mpr hxa]
      · -- b ≤ x ∧ x ≤ 0, which with hb: 0 ≤ b gives b = 0, x = 0
        have hb0 : b = 0 := le_antisymm (le_trans hbx hx0) hb
        have h0x : (0 : ℝ) ≤ x := by
          rw [hb0] at hbx
          exact hbx
        have hx0' : x = 0 := le_antisymm hx0 h0x
        subst hx0' hb0
        dsimp [f]
        simp [not_lt.mpr ha]
    rw [intervalIntegral.integral_congr h_eq_on, intervalIntegral.integral_const]
    simp
  · -- case a < b: max 0 (b - a) = b - a, split integral at a
    have hlt : a < b := by linarith
    have hmax : max 0 (b - a) = b - a := by
      rw [max_eq_right (sub_nonneg.mpr (by linarith))]
    rw [hmax]
    have h0a : (0 : ℝ) ≤ a := ha
    have hab : a ≤ b := by linarith
    -- f is measurable (it's an indicator of Ioi a)
    have hf_meas : Measurable f := by
      dsimp [f]
      refine Measurable.ite ?_ measurable_const measurable_const
      exact measurableSet_Ioi
    -- f is bounded by 1
    have hf_bound : ∀ x, ‖f x‖ ≤ (1 : ℝ) := by
      intro x
      dsimp [f]
      split <;> norm_num
    -- prove f is interval integrable on relevant intervals
    have hf_int_0a : IntervalIntegrable f volume (0 : ℝ) a := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h0a]
      refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) ?_ ?_ ?_
      · -- volume (Ioc 0 a) ≠ ⊤
        simp
      · -- AEStronglyMeasurable f volume
        exact hf_meas.aestronglyMeasurable
      · -- ∀ᵐ x ∂ volume.restrict (Ioc 0 a), ‖f x‖ ≤ 1
        filter_upwards with x
        exact hf_bound x
    have hf_int_ab : IntervalIntegrable f volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      refine MeasureTheory.Measure.integrableOn_of_bounded (M := 1) ?_ ?_ ?_
      · simp
      · exact hf_meas.aestronglyMeasurable
      · filter_upwards with x
        exact hf_bound x
    -- split integral at a: ∫_0^b = ∫_0^a + ∫_a^b
    have h_split := intervalIntegral.integral_add_adjacent_intervals hf_int_0a hf_int_ab
    -- h_split : ∫_0^a f + ∫_a^b f = ∫_0^b f
    -- we want ∫_0^b f = b - a
    rw [← h_split]
    have h_int_0a : ∫ x in (0 : ℝ)..a, f x = 0 := by
      have h_eq_on : ∀ x, x ∈ Set.uIcc (0 : ℝ) a → f x = (0 : ℝ) := by
        intro x hx
        rcases Set.mem_uIcc.1 hx with (⟨hx0, hxa⟩ | ⟨hax, hx0⟩)
        · dsimp [f]
          simp [not_lt.mpr hxa]
        · -- a ≤ x ∧ x ≤ 0, which with ha: 0 ≤ a gives a = 0, x = 0
          have ha0 : a = 0 := le_antisymm (le_trans hax hx0) ha
          have h0x : (0 : ℝ) ≤ x := by
            rw [ha0] at hax
            exact hax
          have hx0' : x = 0 := le_antisymm hx0 h0x
          subst hx0' ha0
          dsimp [f]
          simp
      rw [intervalIntegral.integral_congr h_eq_on, intervalIntegral.integral_const]
      simp
    have h_int_ab : ∫ x in a..b, f x = b - a := by
      -- on (a, b], f x = 1 except at x = a which has measure zero
      have hae : ∀ᵐ x ∂ (volume : MeasureTheory.Measure ℝ), x ∈ Set.uIoc a b → f x = (1 : ℝ) := by
        have h_singleton : ∀ᵐ x ∂ (volume : MeasureTheory.Measure ℝ), x ≠ a := by
          have hvol : volume ({a} : Set ℝ) = 0 := Real.volume_singleton (a := a)
          rwa [MeasureTheory.measure_eq_zero_iff_ae_notMem] at hvol
        filter_upwards [h_singleton] with x hx_ne
        intro hx_uIoc
        rcases Set.mem_uIoc.1 hx_uIoc with (⟨hax, hxb⟩ | ⟨hbx, hxa⟩)
        · -- a < x ∧ x ≤ b
          dsimp [f]
          simp [hax]
        · -- b < x ∧ x ≤ a: impossible since a < b
          exfalso
          linarith
      rw [intervalIntegral.integral_congr_ae hae]
      exact integral_one
    rw [h_int_0a, h_int_ab]
    ring

theorem relaxStop_mono (n t : ℕ) {m : ℕ} (y : Fin m → ℝ) (htn : t ≤ n) :
    Monotone fun x => relaxStop n t y x := by
  exact fun x x' h => by
    dsimp
    have hcard : (Finset.univ.filter fun k => y k < x) ⊆ Finset.univ.filter fun k => y k < x' := by
      apply Finset.monotone_filter_right
      intro k hk hlt
      exact lt_of_lt_of_le hlt h
    have hcard' : ((Finset.univ.filter fun k => y k < x).card : ℝ) ≤ ((Finset.univ.filter fun k => y k < x').card : ℝ) := by
      exact mod_cast Finset.card_le_card hcard
    have hcoeff : (0 : ℝ) ≤ (n : ℝ) - t := by
      have htn' : (t : ℝ) ≤ (n : ℝ) := by exact mod_cast htn
      linarith
    unfold relaxStop
    gcongr

theorem integral_relaxStop (n t : ℕ) {m : ℕ} (y : Fin m → ℝ) (hy : ∀ l, 0 ≤ y l) {b : ℝ}
    (hb : 0 ≤ b) :
    ∫ x in (0 : ℝ)..b, relaxStop n t y x =
      b + ∑ l, max 0 (b - y l) + ((n : ℝ) - t) * b ^ 2 / 2 := by
  dsimp [relaxStop]
  have hcard : ∀ x, ((Finset.univ.filter fun k => y k < x).card : ℝ) = ∑ l : Fin m, (if y l < x then (1 : ℝ) else 0) := by
    intro x; simpa using Finset.natCast_card_filter (fun k => y k < x) Finset.univ
  have h_eq_on : (fun x : ℝ => 1 + ((Finset.univ.filter fun k => y k < x).card : ℝ) + ((n : ℝ) - t) * x) = (fun x : ℝ => 1 + (∑ l : Fin m, (if y l < x then (1 : ℝ) else 0)) + ((n : ℝ) - t) * x) := by
    ext x; rw [hcard x]
  rw [h_eq_on]
  have hint_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 b :=
    intervalIntegrable_const
  have hint_term : ∀ l, IntervalIntegrable (fun x : ℝ => if y l < x then (1 : ℝ) else 0) volume 0 b := by
    intro l
    have hmono : Monotone fun x : ℝ => if y l < x then (1 : ℝ) else 0 := by
      intro a b' h
      by_cases ha : y l < a
      · have hb' : y l < b' := lt_of_lt_of_le ha h
        simp [ha, hb']
      · by_cases hb' : y l < b'
        · simp [ha, hb']
        · simp [ha, hb']
    exact hmono.intervalIntegrable
  have hint_sum : IntervalIntegrable (fun x : ℝ => ∑ l : Fin m, (if y l < x then (1 : ℝ) else 0)) volume 0 b := by
    have h := IntervalIntegrable.sum (s := Finset.univ) (fun l hl => hint_term l)
    -- h: IntervalIntegrable (∑ i, fun x => ...) volume 0 b
    -- goal: IntervalIntegrable (fun x => ∑ l, ...) volume 0 b
    convert h using 1
    ext x; simp
  have hint_mul : IntervalIntegrable (fun x : ℝ => ((n : ℝ) - t) * x) volume 0 b :=
    (intervalIntegral.intervalIntegrable_id).const_mul ((n : ℝ) - t)
  rw [intervalIntegral.integral_add (hint_const.add hint_sum) hint_mul]
  rw [intervalIntegral.integral_add hint_const hint_sum]
  rw [intervalIntegral.integral_const]
  rw [show (∫ x in (0 : ℝ)..b, ((n : ℝ) - t) * x) = ((n : ℝ) - t) * (b ^ 2 / 2) by
    rw [intervalIntegral.integral_const_mul]
    rw [integral_id]
    ring]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [integral_ite_lt (hy _) hb]
    ring
  · intro l hl
    exact hint_term l

theorem sum_le_integral_cells (P : ℕ → ℝ) (f : ℝ → ℝ) (v : ℕ → ℝ) {i0 i1 : ℕ} (h01 : i0 ≤ i1)
    (hP : ∀ i, i0 < i → i ≤ i1 → P (i - 1) ≤ P i)
    (hf : ∀ i, i0 < i → i ≤ i1 → IntervalIntegrable f volume (P (i - 1)) (P i))
    (h : ∀ i, i0 < i → i ≤ i1 → ∀ x ∈ Set.Ioo (P (i - 1)) (P i), v i ≤ f x) :
    ∑ i ∈ Finset.Ioc i0 i1, (P i - P (i - 1)) * v i ≤ ∫ x in P i0..P i1, f x := by
  induction i1, h01 using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top hn]
    have hInt : IntervalIntegrable f volume (P i0) (P n) := by
      have := IntervalIntegrable.trans_iterate (a := fun k => P (i0 + k)) (n := n - i0)
        (μ := volume) (f := f) (fun k hk => by
          have := hf (i0 + k + 1) (by omega) (by omega)
          simpa [add_assoc] using this)
      simpa [Nat.add_sub_cancel' hn] using this
    have hlast := hf (n + 1) (by omega) le_rfl
    simp only [add_tsub_cancel_right] at hlast
    rw [← intervalIntegral.integral_add_adjacent_intervals hInt hlast]
    have hle : P n ≤ P (n + 1) := by simpa using hP (n + 1) (by omega) le_rfl
    have hcell : (P (n + 1) - P n) * v (n + 1) ≤ ∫ x in P n..P (n + 1), f x := by
      have := intervalIntegral.integral_mono_on_of_le_Ioo hle intervalIntegrable_const hlast
        (fun x hx => by simpa using h (n + 1) (by omega) le_rfl x (by simpa using hx))
      simpa [intervalIntegral.integral_const, smul_eq_mul] using this
    have := ih (fun i hi hi' => hP i hi (by omega)) (fun i hi hi' => hf i hi (by omega))
      (fun i hi hi' => h i hi (by omega))
    simp only [add_tsub_cancel_right]
    linarith

theorem exists_bound_of_le {m : ℕ} (N : (Fin m → ℕ) → ℕ) (c : ℕ) :
    ∃ B : ℕ, ∀ k : Fin m → ℕ, (∀ l, k l ≤ c) → N k ≤ B := by
  refine ⟨(Fintype.piFinset fun _ : Fin m => Finset.range (c + 1)).sup N, ?_⟩
  intro k hk
  apply Finset.le_sup
  rw [Fintype.mem_piFinset]
  intro i
  apply Finset.mem_range.mpr
  exact Nat.lt_succ_of_le (hk i)

theorem natCast_sub_eq_max (a b : ℕ) : ((a - b : ℕ) : ℝ) = max 0 ((a : ℝ) - b) := by
  by_cases h : b ≤ a
  · rw [Nat.cast_sub h, max_eq_right (sub_nonneg.mpr (Nat.cast_le.mpr h))]
  · have h' : a ≤ b := Nat.le_of_not_le h
    rw [Nat.sub_eq_zero_of_le h', Nat.cast_zero, max_eq_left (sub_nonpos.mpr (Nat.cast_le.mpr h'))]

namespace Grid

variable (g : Grid)

/-- The memory of a state `k` of time `t`: the point values `pt (glob t (k l)) / D`. -/
noncomputable def val (t : ℕ) {m : ℕ} (k : Fin m → ℕ) : Fin m → ℝ :=
  fun l => (g.pt (g.glob t (k l)) : ℝ) / D

/-! ## Memories and states -/

theorem isMemory_val (hg : g.ok = true) {t m : ℕ} {k : Fin m → ℕ} (hk : Monotone k) :
    IsMemory (g.val t k) := by
  have hpt_mono : Monotone fun (l : Fin m) => g.pt (g.glob t (k l)) := by
    intro a b h
    exact pt_glob_mono g hg t (hk h)
  have h_mono : Monotone (g.val t k) := by
    intro a b h
    have h_nat : g.pt (g.glob t (k a)) ≤ g.pt (g.glob t (k b)) := hpt_mono h
    have h_real : (g.pt (g.glob t (k a)) : ℝ) ≤ (g.pt (g.glob t (k b)) : ℝ) := Nat.cast_le.mpr h_nat
    exact div_le_div_of_nonneg_right h_real (by exact mod_cast D_pos.le)
  have h_bound : ∀ l, g.val t k l ∈ Set.Icc (0 : ℝ) 1 := by
    intro l
    have hpt_nonneg : 0 ≤ (g.pt (g.glob t (k l)) : ℝ) := Nat.cast_nonneg _
    have hpt_le_D : (g.pt (g.glob t (k l)) : ℝ) ≤ (D : ℝ) := by
      have h := pt_le_D g hg (g.glob t (k l))
      exact mod_cast h
    have h_div_nonneg : 0 ≤ (g.pt (g.glob t (k l)) : ℝ) / (D : ℝ) :=
      div_nonneg hpt_nonneg (by positivity)
    have h_div_le_one : (g.pt (g.glob t (k l)) : ℝ) / (D : ℝ) ≤ 1 :=
      (div_le_one (by exact mod_cast D_pos)).mpr hpt_le_D
    exact ⟨h_div_nonneg, h_div_le_one⟩
  exact And.intro h_mono h_bound

theorem le_val_ceilR {t m : ℕ} {y : Fin m → ℝ} (hy : IsMemory y) :
    y ≤ g.val t (fun l => g.ceilR t (y l)) := by
  intro l
  have h := le_pt_ceilR g t (hy.2 l).2
  simp only [Grid.val]
  have hDpos : 0 < (D : ℝ) := Nat.cast_pos.mpr D_pos
  exact (le_div_iff₀ hDpos).2 h

theorem isState_ceilR {t m : ℕ} {y : Fin m → ℝ} (hy : IsMemory y) :
    g.IsState t (fun l => g.ceilR t (y l)) := by
  exact ⟨fun a b h => g.ceilR_mono t (hy.1 h), fun l => g.ceilR_le_cnt t (y l)⟩

theorem ceilR_val (hg : g.ok = true) {t d : ℕ} (k : Fin (d + 1) → ℕ) :
    (fun l => g.ceilR (t + 1) (g.val t k l)) = g.kmap d t k := by
  funext l
  simp only [Grid.val, Grid.kmap, Grid.mapL]
  exact g.ceilR_pt hg (t + 1) (g.glob_le_J t (k l))

theorem im_spec {t d : ℕ} {k : Fin (d + 1) → ℕ} (hk : g.IsState t k) :
    1 ≤ g.im d t k ∧ g.im d t k ≤ g.L t ∧
      g.val t k (Fin.last d) = (g.cp t (g.im d t k) : ℝ) / D := by
  have hk_last : k (Fin.last d) ≤ g.cnt t := hk.2 (Fin.last d)
  have hpos := g.pos_spec hk_last
  have hcp := g.cp_pos hk_last
  have h_im : g.im d t k = g.pos t (k (Fin.last d)) := rfl
  have h_val : g.val t k (Fin.last d) = (g.pt (g.glob t (k (Fin.last d))) : ℝ) / D := rfl
  have h_cp_im : g.cp t (g.im d t k) = g.pt (g.glob t (k (Fin.last d))) := by
    simpa [h_im] using hcp
  have hthird : g.val t k (Fin.last d) = (g.cp t (g.im d t k) : ℝ) / D := by
    rw [h_val, h_im, hcp]
  exact ⟨hpos.1, hpos.2.1, hthird⟩

/-! ## The integrand on a cell -/

theorem relaxStop_of_cell (hg : g.ok = true) {t d : ℕ} {k : Fin (d + 1) → ℕ} (htn : t ≤ g.n)
    (hk : g.IsState t k) {i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ g.L t) {x : ℝ}
    (hxa : (g.cp t (i - 1) : ℝ) < x * D) (hxb : x * D ≤ g.cp t i) :
    relaxStop g.n t (g.val t k) x = g.alpha d t k i + ((g.n - t : ℕ) : ℝ) * x := by
  have hD : (0 : ℝ) < D := by exact_mod_cast D_pos
  unfold relaxStop
  rw [← Nat.cast_sub htn]
  have hiff : ∀ l, g.val t k l < x ↔ g.pos t (k l) < i := fun l => by
    rw [← g.lt_iff_pos_lt hg hi1 hiL (hk.2 l) hxa hxb]
    simp only [Grid.val]
    rw [div_lt_iff₀ hD]
  have hcard : (Finset.univ.filter fun l => g.val t k l < x) =
      Finset.univ.filter fun l => g.pos t (k l) < i := by
    ext l
    simp [hiff l]
  rw [hcard]
  have hkey : 1 + (Finset.univ.filter fun l : Fin (d + 1) => g.pos t (k l) < i).card =
      g.alpha d t k i := by
    unfold Grid.alpha
    split_ifs with h
    · rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
      have hlast : ¬ g.pos t (k (Fin.last d)) < i := by unfold Grid.im at h; omega
      simp only [hlast, ↓reduceIte, add_zero, Nat.lt_iff_add_one_le]
    · have hall : ∀ l : Fin (d + 1), g.pos t (k l) < i := fun l => by
        have := g.pos_mono hg (hk.1 (Fin.le_last l)) (hk.2 _)
        unfold Grid.im at h
        omega
      rw [Finset.filter_true_of_mem fun l _ => hall l, Finset.card_univ, Fintype.card_fin]
      omega
  rw [← hkey]
  push_cast
  ring

theorem relaxStop_of_gt {t d : ℕ} {k : Fin (d + 1) → ℕ} (htn : t ≤ g.n) (hg : g.ok = true)
    (hk : g.IsState t k) {x : ℝ} (hx : g.val t k (Fin.last d) < x) :
    relaxStop g.n t (g.val t k) x = ((d + 2 : ℕ) : ℝ) + ((g.n - t : ℕ) : ℝ) * x := by
  have hmem : IsMemory (g.val t k) := isMemory_val g hg hk.1
  have h_all_lt : ∀ l, g.val t k l < x := by
    intro l
    have hle : g.val t k l ≤ g.val t k (Fin.last d) := hmem.1 (Fin.le_last l)
    linarith
  unfold relaxStop
  have hfilter : Finset.filter (fun k' => g.val t k k' < x) Finset.univ = Finset.univ :=
    Finset.filter_true_of_mem (by
      intro l hl
      simp [h_all_lt l])
  have hcard : (Finset.univ : Finset (Fin (d + 1))).card = d + 1 :=
    Finset.card_fin (d + 1)
  rw [hfilter, hcard]
  push_cast
  rw [Nat.cast_sub htn]
  ring

theorem ceilR_ins_of_cell (hg : g.ok = true) {t d : ℕ} {k : Fin (d + 1) → ℕ}
    (hk : g.IsState t k) {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ g.im d t k) {x : ℝ}
    (hxa : (g.cp t (i - 1) : ℝ) < x * D) (hxb : x * D ≤ g.cp t i) :
    (fun l => g.ceilR (t + 1) (ins (g.val t k) x l)) = insIdx (g.kmap d t k) (g.nxt t i) := by
  have hD : (0 : ℝ) < D := by exact_mod_cast D_pos
  obtain ⟨_, hmL, htop⟩ := g.im_spec hk
  have hiL : i ≤ g.L t := him.trans hmL
  have hx_le : x ≤ g.val t k (Fin.last d) := by
    rw [htop, le_div_iff₀ hD]
    exact hxb.trans (by exact_mod_cast g.cp_mono hg him hmL)
  have hmono := g.ceilR_mono (t + 1)
  have hcx : g.ceilR (t + 1) x = g.nxt t i := g.ceilR_of_cell hg hi1 hiL hxa hxb
  have hcv : ∀ l, g.ceilR (t + 1) (g.val t k l) = g.kmap d t k l :=
    fun l => congrFun (g.ceilR_val hg k) l
  funext l
  unfold ins insIdx
  rw [hmono.map_max]
  congr 1
  · split_ifs with h0
    · exact g.ceilR_of_nonpos (t + 1) le_rfl
    · exact hcv _
  · split_ifs with hd
    · have hl : l = Fin.last d := Fin.ext hd
      subst hl
      rw [min_eq_right hx_le, hcx]
    · rw [hmono.map_min, hcv, hcx]

theorem cont_ge_of_cell (hg : g.ok = true) {t d : ℕ} {k : Fin (d + 1) → ℕ} (hk : g.IsState t k)
    (N : (Fin (d + 1) → ℕ) → ℕ) {i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ g.L t) {x : ℝ}
    (hxa : (g.cp t (i - 1) : ℝ) < x * D) (hxb : x * D ≤ g.cp t i) :
    (g.cC d N t k i : ℝ) / D ≤
      dropPenalty g.n t (g.val t k) x +
        (N (fun l => g.ceilR (t + 1) (ins (g.val t k) x l)) : ℝ) / D := by
  have hD : (0 : ℝ) < D := by exact_mod_cast D_pos
  obtain ⟨hm1, hmL, htop⟩ := g.im_spec hk
  have hmem := g.isMemory_val hg (t := t) hk.1
  unfold Grid.cC Grid.cE dropPenalty
  by_cases him : i ≤ g.im d t k
  · simp only [him, ↓reduceIte]
    have hx_le : x ≤ g.val t k (Fin.last d) := by
      rw [htop, le_div_iff₀ hD]
      exact hxb.trans (by exact_mod_cast g.cp_mono hg him hmL)
    rw [drop_of_le _ hx_le, g.ceilR_ins_of_cell hg hk hi1 him hxa hxb, htop]
    have hE := Epen_le (g.cp t (g.im d t k)) (g.n - t) (g.cp_le_D hg t _)
    have hE' : (Epen (g.cp t (g.im d t k)) (g.n - t) : ℝ) / D ≤
        (1 - (g.cp t (g.im d t k) : ℝ) / D) ^ (g.n - t) := by
      rw [div_le_iff₀ hD]
      linarith
    simp only [Grid.row]
    push_cast
    rw [add_div]
    linarith
  · simp only [him, ↓reduceIte]
    have hgt : g.val t k (Fin.last d) ≤ x := by
      rw [htop, div_le_iff₀ hD]
      have h1 : g.cp t (g.im d t k) ≤ g.cp t (i - 1) := g.cp_mono hg (by omega) (by omega)
      have h2 : (g.cp t (g.im d t k) : ℝ) ≤ g.cp t (i - 1) := by exact_mod_cast h1
      linarith
    rw [drop_of_ge _ hgt, ins_of_ge hmem hgt, g.ceilR_val hg k]
    have hx1 : x ≤ (g.cp t i : ℝ) / D := by rw [le_div_iff₀ hD]; exact hxb
    have hc1 : (g.cp t i : ℝ) / D ≤ 1 := by
      rw [div_le_one hD]; exact_mod_cast g.cp_le_D hg t i
    have hpow : (1 - (g.cp t i : ℝ) / D) ^ (g.n - t) ≤ (1 - x) ^ (g.n - t) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have hE := Epen_le (g.cp t i) (g.n - t) (g.cp_le_D hg t _)
    have hE' : (Epen (g.cp t i) (g.n - t) : ℝ) / D ≤ (1 - (g.cp t i : ℝ) / D) ^ (g.n - t) := by
      rw [div_le_iff₀ hD]
      linarith
    simp only [Grid.uN]
    push_cast
    rw [add_div]
    linarith

theorem cont_of_ge (hg : g.ok = true) {t d : ℕ} {k : Fin (d + 1) → ℕ} (hk : g.IsState t k)
    (N : (Fin (d + 1) → ℕ) → ℕ) {x : ℝ} (hx : g.val t k (Fin.last d) ≤ x) :
    dropPenalty g.n t (g.val t k) x +
        (N (fun l => g.ceilR (t + 1) (ins (g.val t k) x l)) : ℝ) / D =
      (1 - x) ^ (g.n - t) + (g.uN d N t k : ℝ) / D := by
  unfold dropPenalty
  rw [drop_of_ge (g.val t k) hx]
  rw [ins_of_ge (isMemory_val g hg hk.1) hx]
  rw [ceilR_val g hg k]
  rw [Grid.uN]

/-! ## Monotonicity in the cell index (6.2) -/

theorem row_im (hg : g.ok = true) {t d : ℕ} {k : Fin (d + 1) → ℕ} (hk : g.IsState t k)
    (N : (Fin (d + 1) → ℕ) → ℕ) : g.row d N t k (g.im d t k) = g.uN d N t k := by
  have hD : (0 : ℝ) < D := by exact_mod_cast D_pos
  obtain ⟨hm1, hmL, htop⟩ := g.im_spec hk
  have hmem := g.isMemory_val hg (t := t) hk.1
  have hxD : g.val t k (Fin.last d) * D = g.cp t (g.im d t k) := by rw [htop]; field_simp
  have hxa : (g.cp t (g.im d t k - 1) : ℝ) < g.val t k (Fin.last d) * D := by
    rw [hxD]; exact_mod_cast g.cp_lt_cp hg (by omega) hmL
  have h1 := g.ceilR_ins_of_cell hg hk hm1 le_rfl hxa hxD.le
  rw [ins_of_ge hmem le_rfl, g.ceilR_val hg k] at h1
  unfold Grid.row Grid.uN
  rw [← h1]

theorem row_anti (hg : g.ok = true) {t d : ℕ} {k : Fin (d + 1) → ℕ} (hk : g.IsState t k)
    {N : (Fin (d + 1) → ℕ) → ℕ}
    (hN : ∀ k k', g.IsState (t + 1) k → g.IsState (t + 1) k' → k ≤ k' → N k' ≤ N k)
    {i i' : ℕ} (hi1 : 1 ≤ i) (h : i ≤ i') (hi' : i' ≤ g.im d t k) :
    g.row d N t k i' ≤ g.row d N t k i := by
  have hD : (0 : ℝ) < D := by exact_mod_cast D_pos
  obtain ⟨hm1, hmL, htop⟩ := g.im_spec hk
  have hmem := g.isMemory_val hg (t := t) hk.1
  have hrow : ∀ j, 1 ≤ j → j ≤ g.im d t k → g.row d N t k j =
      N (fun l => g.ceilR (t + 1) (ins (g.val t k) ((g.cp t j : ℝ) / D) l)) := by
    intro j hj1 hjm
    have hxD : (g.cp t j : ℝ) / D * D = g.cp t j := by field_simp
    have hxa : (g.cp t (j - 1) : ℝ) < (g.cp t j : ℝ) / D * D := by
      rw [hxD]; exact_mod_cast g.cp_lt_cp hg (by omega) (hjm.trans hmL)
    rw [g.ceilR_ins_of_cell hg hk hj1 hjm hxa hxD.le]
    rfl
  rw [hrow i hi1 (h.trans hi'), hrow i' (hi1.trans h) hi']
  have hx : ∀ j, (g.cp t j : ℝ) / D ∈ Set.Icc (0 : ℝ) 1 := fun j =>
    ⟨by positivity, by rw [div_le_one hD]; exact_mod_cast g.cp_le_D hg t j⟩
  have hle : (g.cp t i : ℝ) / D ≤ (g.cp t i' : ℝ) / D := by
    gcongr; exact_mod_cast g.cp_mono hg h (hi'.trans hmL)
  have hins : ins (g.val t k) ((g.cp t i : ℝ) / D) ≤ ins (g.val t k) ((g.cp t i' : ℝ) / D) :=
    ins_mono le_rfl hle
  apply hN
  · exact g.isState_ceilR (ins_mem hmem (hx i))
  · exact g.isState_ceilR (ins_mem hmem (hx i'))
  · exact fun l => g.ceilR_mono (t + 1) (hins l)

theorem cC_anti (hg : g.ok = true) {t d : ℕ} {k : Fin (d + 1) → ℕ} (hk : g.IsState t k)
    {N : (Fin (d + 1) → ℕ) → ℕ}
    (hN : ∀ k k', g.IsState (t + 1) k → g.IsState (t + 1) k' → k ≤ k' → N k' ≤ N k)
    {i i' : ℕ} (hi1 : 1 ≤ i) (h : i ≤ i') (hi' : i' ≤ g.L t) :
    g.cC d N t k i' ≤ g.cC d N t k i := by
  unfold Grid.cC Grid.cE
  by_cases h1 : i' ≤ g.im d t k
  · have h2 : i ≤ g.im d t k := h.trans h1
    simp only [h1, h2, ↓reduceIte]
    exact Nat.add_le_add_left (g.row_anti hg hk hN hi1 h h1) _
  · simp only [h1, ↓reduceIte]
    by_cases h2 : i ≤ g.im d t k
    · simp only [h2, ↓reduceIte]
      have hrow : g.uN d N t k ≤ g.row d N t k i := by
        rw [← g.row_im hg hk N]
        exact g.row_anti hg hk hN hi1 h2 le_rfl
      have hE : Epen (g.cp t i') (g.n - t) ≤ Epen (g.cp t (g.im d t k)) (g.n - t) :=
        Epen_anti (g.cp_mono hg (by omega) hi') _
      omega
    · simp only [h2, ↓reduceIte]
      exact Nat.add_le_add_right (Epen_anti (g.cp_mono hg h hi') _) _

theorem alpha_mono {t d : ℕ} {k : Fin (d + 1) → ℕ} {i i' : ℕ} (h : i ≤ i') :
    g.alpha d t k i ≤ g.alpha d t k i' := by
  unfold alpha
  split_ifs with hle hle'
  · -- both i ≤ im
    apply Nat.add_le_add_left
    apply Finset.card_le_card
    apply Finset.monotone_filter_right
    intro l hl
    omega
  · -- i ≤ im, i' > im
    have hcard : (Finset.univ.filter fun l : Fin d => g.pos t (k l.castSucc) + 1 ≤ i).card ≤ d := by
      calc
        _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_filter_le _ _
        _ = d := by simp
    omega
  · -- i > im, i' ≤ im: impossible since i ≤ i'
    omega
  · -- both > im: equal
    rfl

theorem Pos_mono (hg : g.ok = true) {t d : ℕ} {k : Fin (d + 1) → ℕ} (hk : g.IsState t k)
    {N : (Fin (d + 1) → ℕ) → ℕ}
    (hN : ∀ k k', g.IsState (t + 1) k → g.IsState (t + 1) k' → k ≤ k' → N k' ≤ N k)
    {i i' : ℕ} (hi1 : 1 ≤ i) (h : i ≤ i') (hi' : i' ≤ g.L t) (hp : g.Pos d N t k i = true) :
    g.Pos d N t k i' = true := by
  unfold Grid.Pos at hp ⊢
  rw [decide_eq_true_eq] at hp ⊢
  have hcC := cC_anti g hg hk hN hi1 h hi'
  have halpha := alpha_mono (g := g) (t := t) (d := d) (k := k) h
  have hcp := cp_mono (g := g) (t := t) hg h hi'
  have hsum : g.alpha d t k i * D + (g.n - t) * g.cp t i ≤ g.alpha d t k i' * D + (g.n - t) * g.cp t i' := by
    have h1 : g.alpha d t k i * D ≤ g.alpha d t k i' * D := Nat.mul_le_mul_right D halpha
    have h2 : (g.n - t) * g.cp t i ≤ (g.n - t) * g.cp t i' := Nat.mul_le_mul_left (g.n - t) hcp
    exact Nat.add_le_add h1 h2
  calc
    g.cC d N t k i' ≤ g.cC d N t k i := hcC
    _ ≤ g.alpha d t k i * D + (g.n - t) * g.cp t i := hp
    _ ≤ g.alpha d t k i' * D + (g.n - t) * g.cp t i' := hsum

theorem pos_of_crossOK (hg : g.ok = true) {t d : ℕ} {k : Fin (d + 1) → ℕ} (hk : g.IsState t k)
    {N : (Fin (d + 1) → ℕ) → ℕ}
    (hN : ∀ k k', g.IsState (t + 1) k → g.IsState (t + 1) k' → k ≤ k' → N k' ≤ N k)
    {c : ℕ} (hc : g.crossOK d N t k c) {i : ℕ} (hci : c ≤ i) (hiL : i ≤ g.L t) :
    g.Pos d N t k i = true := by
  obtain ⟨h1, hL, hcross, hc2⟩ := hc
  have hc_ne : c ≠ g.L t + 1 := by
    intro h_eq
    have hc_le_L : c ≤ g.L t := le_trans hci hiL
    have h_lt : c < g.L t + 1 := by omega
    exact h_lt.ne h_eq
  have hPos_c : g.Pos d N t k c = true := hc2.resolve_left hc_ne
  exact Pos_mono g hg hk hN h1 hci hiL hPos_c

theorem not_pos_of_crossOK (hg : g.ok = true) {t d : ℕ} {k : Fin (d + 1) → ℕ}
    (hk : g.IsState t k) {N : (Fin (d + 1) → ℕ) → ℕ}
    (hN : ∀ k k', g.IsState (t + 1) k → g.IsState (t + 1) k' → k ≤ k' → N k' ≤ N k)
    {c : ℕ} (hc : g.crossOK d N t k c) {i : ℕ} (hi1 : 1 ≤ i) (hic : i < c) :
    g.Pos d N t k i = false := by
  obtain ⟨h1, hL, hc1, -⟩ := hc
  have hc_ne_one : c ≠ 1 := by omega
  have hc1' : g.Pos d N t k (c - 1) = false := by
    rcases hc1 with (hc1 | hc1)
    · exfalso; exact hc_ne_one hc1
    · exact hc1
  by_cases hpos : g.Pos d N t k i = true
  · have hi_le_c1 : i ≤ c - 1 := by omega
    have hc1_le_L : c - 1 ≤ g.L t := by omega
    have hpos_mono := Pos_mono g hg hk hN hi1 hi_le_c1 hc1_le_L hpos
    rw [hc1'] at hpos_mono
    exfalso; exact Bool.false_ne_true hpos_mono
  · simpa using hpos

/-! ## Arithmetic of `R` -/

theorem Sint_eq {t d : ℕ} (k : Fin (d + 1) → ℕ) (X : ℕ) :
    (g.Sint d t k X : ℝ) =
      2 * (D : ℝ) ^ 2 * (((X : ℝ) / D) + ∑ l, max 0 ((X : ℝ) / D - g.val t k l) +
        ((g.n - t : ℕ) : ℝ) * ((X : ℝ) / D) ^ 2 / 2) := by
  have hD : (0 : ℝ) < D := by exact_mod_cast D_pos
  have hmax : ∀ a : ℝ, max 0 (a / D) = max 0 a / D := fun a => by
    rcases le_total a 0 with h | h
    · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg h hD.le), max_eq_left h, zero_div]
    · rw [max_eq_right (div_nonneg h hD.le), max_eq_right h]
  unfold Grid.Sint
  simp only [Grid.val, div_sub_div_same, hmax, ← Finset.sum_div]
  push_cast
  simp only [natCast_sub_eq_max]
  field_simp
  ring

theorem Q_add {t d : ℕ} {k : Fin (d + 1) → ℕ} (N : (Fin (d + 1) → ℕ) → ℕ) {i i' : ℕ}
    (h : i ≤ i') :
    g.Q d N t k i' =
      g.Q d N t k i + ∑ j ∈ Finset.Ioc i i', 2 * (g.cp t j - g.cp t (j - 1)) * g.row d N t k j := by
  unfold Grid.Q
  have h_disjoint : Disjoint (Finset.Icc 1 i) (Finset.Ioc i i') :=
    Finset.disjoint_left.mpr fun x hx1 hx2 => by
      rcases Finset.mem_Icc.mp hx1 with ⟨hx1l, hx1r⟩
      rcases Finset.mem_Ioc.mp hx2 with ⟨hx2l, hx2r⟩
      omega
  have h_union : Finset.Icc 1 i' = Finset.Icc 1 i ∪ Finset.Ioc i i' := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
    constructor
    · rintro ⟨hx1, hx2⟩
      by_cases hxi : x ≤ i
      · left; exact ⟨hx1, hxi⟩
      · right; exact ⟨Nat.lt_of_not_ge hxi, hx2⟩
    · rintro (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩)
      · exact ⟨hx1, Nat.le_trans hx2 h⟩
      · have hx1' : 1 ≤ x := by omega
        exact ⟨hx1', hx2⟩
  rw [h_union]
  rw [Finset.sum_union h_disjoint]

end Grid

end Robbins.Cert
