import Robbins.Cert.SO.SoundCell

/-!
# The bound of one record list (sections 8.5 and 8.6 of Robbins/Cert/SO/Spec.lean)

`bound_le_integral`: for a record list `c` that the memory `y` fits (the list of section 6 at any
choice), `T0 / D + sum over the credited l of (mu_l / D) delta_l`, `delta_l = val_l / D - y_l`, is at
most the integral over `[0, 1]` of the integrand of (R_t). The integral is cut at the cell
endpoints `p_i / D`: the cells `1, ..., im` (`head_cell`: 8.4 with the bounds of 8.2 and 8.5 (a),
(c), (d)), the tail cells `im + 1, ..., jT` (`tail_cell`: 8.3, 8.5 (a), (c)) and `[p_jT / D, 1]`
(`final_seg`: 8.5 (e)). The pointwise bounds are used on the open cells only
(`intervalIntegral.integral_mono_on_of_le_Ioo`), so the endpoints, null sets, need no care; the
integrand is integrable on `[0, 1]` (`integrableOn_integrandSO`), and so are the lower bounds
(continuous, or monotone counts).
-/

namespace Robbins.Cert.SO

open MeasureTheory intervalIntegral Robbins.Cert

/-! ## Integral lemmas over the reals -/

/-- The substitution `X = x D`. -/
theorem integral_comp_mul_div {D : ℝ} (hD : 0 < D) (f : ℝ → ℝ) (a b : ℝ) :
    ∫ x in a / D..b / D, f (x * D) = (∫ X in a..b, f X) / D := by
  rw [intervalIntegral.integral_comp_mul_right f hD.ne', div_mul_cancel₀ _ hD.ne',
    div_mul_cancel₀ _ hD.ne', smul_eq_mul, inv_mul_eq_div]

/-- 8.5 (a) in the variable `x = X / D`. -/
theorem cell2_div_le {D : ℝ} (hD : 0 < D) {Pa Pb a0 a1 b0 b1 : ℤ} (hab : Pa < Pb) (ha1 : 0 < a1)
    (hb1 : 0 ≤ b1) :
    (cell2 Pa Pb a0 a1 b0 b1 : ℝ) / (2 * D ^ 3) ≤
      ∫ x in (Pa : ℝ) / D..(Pb : ℝ) / D,
        min (((a0 : ℝ) + a1 * (x * D)) / D ^ 2) (((b0 : ℝ) - b1 * (x * D)) / D ^ 2) := by
  have h := cell2_le (a0 := a0) (b0 := b0) hab ha1 hb1
  have he : ∫ x in (Pa : ℝ) / D..(Pb : ℝ) / D,
      min (((a0 : ℝ) + a1 * (x * D)) / D ^ 2) (((b0 : ℝ) - b1 * (x * D)) / D ^ 2) =
      (∫ X in (Pa : ℝ)..Pb, min ((a0 : ℝ) + a1 * X) ((b0 : ℝ) - b1 * X) / D ^ 2) / D := by
    have := integral_comp_mul_div hD
      (fun X => min ((a0 : ℝ) + a1 * X) ((b0 : ℝ) - b1 * X) / D ^ 2) Pa Pb
    beta_reduce at this
    rw [← this]
    congr 1
    funext x
    exact min_div_div_right (by positivity : (0 : ℝ) ≤ D ^ 2) _ _
  rw [he, intervalIntegral.integral_div]
  set I := ∫ X in (Pa : ℝ)..Pb, min ((a0 : ℝ) + a1 * X) ((b0 : ℝ) - b1 * X)
  have hD3 : (0 : ℝ) < 2 * D ^ 3 := by positivity
  rw [div_le_iff₀ hD3]
  have : I / D ^ 2 / D * (2 * D ^ 3) = 2 * I := by field_simp
  linarith

/-- 8.5 (c) in the variable `x = X / D`. -/
theorem chord_div_le {D : ℝ} (hD : 0 < D) {Pa Pb a0 a1 b0 b1 S : ℤ} (hab : Pa < Pb) (ha1 : 0 < a1)
    (hb1 : 0 ≤ b1) (hS : 0 < S) :
    (chord Pa Pb a0 a1 b0 b1 S : ℝ) / D ≤
      ∫ x in (Pa : ℝ) / D..(Pb : ℝ) / D,
        min 1 (max 0 (((a0 : ℝ) + a1 * (x * D)) / D ^ 2 - ((b0 : ℝ) - b1 * (x * D)) / D ^ 2) /
          ((S : ℝ) / D ^ 2)) := by
  have h := chord_le (a0 := a0) (b0 := b0) hab ha1 hb1 hS
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  have he : ∀ x : ℝ,
      min 1 (max 0 (((a0 : ℝ) + a1 * (x * D)) / D ^ 2 - ((b0 : ℝ) - b1 * (x * D)) / D ^ 2) /
        ((S : ℝ) / D ^ 2)) =
      (fun X => min 1 (max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X) / S)) (x * D) := by
    intro x
    have hD2 : (0 : ℝ) < D ^ 2 := by positivity
    have e1 : ((a0 : ℝ) + a1 * (x * D)) / D ^ 2 - ((b0 : ℝ) - b1 * (x * D)) / D ^ 2 =
        ((a0 : ℝ) - b0 + (a1 + b1) * (x * D)) / D ^ 2 := by ring
    rw [e1]
    congr 1
    rcases le_total 0 ((a0 : ℝ) - b0 + (a1 + b1) * (x * D)) with hv | hv
    · rw [max_eq_right (div_nonneg hv hD2.le), max_eq_right hv]
      field_simp
    · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg hv hD2.le), max_eq_left hv]
      simp
  simp only [he]
  rw [integral_comp_mul_div hD (fun X => min 1 (max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X) / S))]
  exact div_le_div_of_nonneg_right h hD.le

/-- The integral over a cell of the scalar bound of 8.4. -/
theorem cell_int_le {a b : ℝ} (hab : a ≤ b) {F A B N : ℝ → ℝ} {s S M : ℝ}
    (hF : IntervalIntegrable F volume a b) (hA : Continuous A) (hB : Continuous B)
    (hN : IntervalIntegrable N volume a b) (hN0 : ∀ x ∈ Set.Ioo a b, 0 ≤ N x) (hS : 0 < S)
    (hs0 : 0 ≤ s) (hsS : s ≤ S) (hM : 0 ≤ M) (hMB : ∀ x ∈ Set.Ioo a b, M ≤ max 0 (B x - A x))
    (hFx : ∀ x ∈ Set.Ioo a b, min (A x + N x) (B x + s) ≤ F x) :
    (∫ x in a..b, min (A x) (B x)) + s * (∫ x in a..b, min 1 (max 0 (A x - B x) / S)) +
      (∫ x in a..b, min (N x) M) ≤ ∫ x in a..b, F x := by
  have hNM : IntervalIntegrable (fun x => min (N x) M) volume a b := by
    have he : (fun x => min (N x) M) = fun x => (N x + M - |N x - M|) / 2 := by
      funext x
      rcases le_total (N x) M with h | h
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]
        ring
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]
        ring
    rw [he]
    exact ((hN.add intervalIntegrable_const).sub (hN.sub intervalIntegrable_const).abs).div_const 2
  have hi1 : IntervalIntegrable (fun x => min (A x) (B x)) volume a b :=
    (hA.min hB).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => s * min 1 (max 0 (A x - B x) / S)) volume a b :=
    (continuous_const.mul (continuous_const.min
      ((continuous_const.max (hA.sub hB)).div_const S))).intervalIntegrable _ _
  have hi12 : IntervalIntegrable
      (fun x => min (A x) (B x) + s * min 1 (max 0 (A x - B x) / S)) volume a b := hi1.add hi2
  have hi123 : IntervalIntegrable (fun x => min (A x) (B x) + s * min 1 (max 0 (A x - B x) / S) +
      min (N x) M) volume a b := hi12.add hNM
  have hsum : (∫ x in a..b, min (A x) (B x) + s * min 1 (max 0 (A x - B x) / S) + min (N x) M) =
      (∫ x in a..b, min (A x) (B x)) + s * (∫ x in a..b, min 1 (max 0 (A x - B x) / S)) +
        (∫ x in a..b, min (N x) M) := by
    rw [intervalIntegral.integral_add hi12 hNM, intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul]
  rw [← hsum]
  apply intervalIntegral.integral_mono_on_of_le_Ioo hab hi123 hF
  intro x hx
  have h1 := scalar_min (A := A x) (B := B x) (C := B x + s) (N := N x) (hN0 x hx) hS hs0 hsS
    le_rfl
  have h2 : min (N x) M ≤ min (N x) (max 0 (B x - A x)) := min_le_min_left _ (hMB x hx)
  calc min (A x) (B x) + s * min 1 (max 0 (A x - B x) / S) + min (N x) M
      ≤ min (A x) (B x) + s * min 1 (max 0 (A x - B x) / S) + min (N x) (max 0 (B x - A x)) := by
        linarith
    _ ≤ min (A x + N x) (B x + s) := h1
    _ ≤ F x := hFx x hx

/-- Abel summation over a subfamily (8.5 (d)): for a monotone `y` and the indices `q` with `P q`
in `[a, b]`, numbered by `#{q' < q | P q'}`. -/
theorem integral_min_count_filter {p : ℕ} {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M) {y : Fin p → ℝ}
    (hy : Monotone y) (P : Fin p → Prop) [DecidablePred P] (hya : ∀ q, P q → a ≤ y q)
    (hyb : ∀ q, P q → y q ≤ b) :
    ∫ x in a..b, min ((Finset.univ.filter fun q => P q ∧ y q < x).card : ℝ) M =
      ∑ q, if P q then
        (min (((Finset.univ.filter fun q' => q' < q ∧ P q').card : ℝ) + 1) M -
          min ((Finset.univ.filter fun q' => q' < q ∧ P q').card : ℝ) M) * (b - y q)
      else 0 := by
  classical
  set s : Finset (Fin p) := Finset.univ.filter P with hs
  set e : Fin s.card ↪o Fin p := s.orderEmbOfFin rfl with he
  have hmem : ∀ i, e i ∈ s := fun i => s.orderEmbOfFin_mem rfl i
  have hP : ∀ i, P (e i) := fun i => (Finset.mem_filter.mp (hmem i)).2
  have hrange : ∀ q, P q → ∃ i, e i = q := by
    intro q hq
    have hq' : q ∈ (s : Set (Fin p)) := by simp [hs, hq]
    rw [← Finset.range_orderEmbOfFin s rfl] at hq'
    exact hq'
  have hy' : Monotone fun i => y (e i) := hy.comp e.monotone
  have key := integral_min_count hab hM hy' (fun i => hya _ (hP i)) (fun i => hyb _ (hP i))
  have hcount : ∀ x, (Finset.univ.filter fun i => y (e i) < x).card =
      (Finset.univ.filter fun q => P q ∧ y q < x).card := by
    intro x
    apply Finset.card_bij (fun i _ => e i)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact ⟨hP i, hi⟩
    · intro i _ j _ h
      exact e.injective h
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      obtain ⟨i, hi⟩ := hrange q hq.1
      refine ⟨i, ?_, hi⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hi]
      exact hq.2
  have hrank : ∀ i : Fin s.card,
      (Finset.univ.filter fun q' => q' < e i ∧ P q').card = (i : ℕ) := by
    intro i
    have hset : (Finset.univ.filter fun q' => q' < e i ∧ P q') =
        (Finset.Iio i).map e.toEmbedding := by
      ext q'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_Iio,
        RelEmbedding.coe_toEmbedding]
      constructor
      · rintro ⟨hlt, hPq⟩
        obtain ⟨j, hj⟩ := hrange q' hPq
        refine ⟨j, ?_, hj⟩
        rw [← hj] at hlt
        exact e.lt_iff_lt.mp hlt
      · rintro ⟨j, hj, rfl⟩
        exact ⟨e.lt_iff_lt.mpr hj, hP j⟩
    rw [hset, Finset.card_map, Fin.card_Iio]
  have hL : (∫ x in a..b, min ((Finset.univ.filter fun q => P q ∧ y q < x).card : ℝ) M) =
      ∫ x in a..b, min ((Finset.univ.filter fun i => y (e i) < x).card : ℝ) M := by
    congr 1
    funext x
    rw [hcount x]
  rw [hL, key, ← Finset.sum_filter, ← hs]
  have himg : Finset.univ.image e = s := Finset.image_orderEmbOfFin_univ s rfl
  conv_rhs => rw [← himg]
  rw [Finset.sum_image (fun i _ j _ h => e.injective h)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hrank i]

/-- A count of the coordinates below `x` is monotone in `x`. -/
theorem monotone_count {p : ℕ} (P : Fin p → Prop) [DecidablePred P] (y : Fin p → ℝ) :
    Monotone fun x : ℝ => ((Finset.univ.filter fun q => P q ∧ y q < x).card : ℝ) := by
  intro x x' h
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro q hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
  exact ⟨hq.1, lt_of_lt_of_le hq.2 h⟩

/-- The own-cell gap of 8.5 (d) (`M` of 5.3): `M / D ≤ max 0 (B x - A x)` below the right end. -/
theorem MC_le_aux {D : ℕ} (hD : 0 < D) {beta sigma a0 a1 P : ℤ} (hk : 0 ≤ sigma + a1) {X : ℝ}
    (hX : X ≤ P) :
    ((if 0 < beta - sigma * P - a0 - a1 * P then (beta - sigma * P - a0 - a1 * P) / (D : ℤ)
        else 0 : ℤ) : ℝ) / D ≤
      max 0 (((beta : ℝ) - sigma * X) / (D : ℝ) ^ 2 - ((a0 : ℝ) + a1 * X) / (D : ℝ) ^ 2) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hX' : ((sigma : ℝ) + a1) * X ≤ ((sigma : ℝ) + a1) * P :=
    mul_le_mul_of_nonneg_left hX (by exact_mod_cast hk)
  have hBA : ((beta : ℝ) - sigma * P - a0 - a1 * P) / (D : ℝ) ^ 2 ≤
      ((beta : ℝ) - sigma * X) / (D : ℝ) ^ 2 - ((a0 : ℝ) + a1 * X) / (D : ℝ) ^ 2 := by
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  split_ifs with hgap
  · have h1 := intCast_ediv_le (a := beta - sigma * P - a0 - a1 * P) (b := (D : ℤ))
      (by exact_mod_cast hD)
    apply le_max_of_le_right
    refine le_trans ?_ hBA
    calc (((beta - sigma * P - a0 - a1 * P) / (D : ℤ) : ℤ) : ℝ) / D
        ≤ (((beta - sigma * P - a0 - a1 * P : ℤ) : ℝ) / ((D : ℤ) : ℝ)) / D :=
          div_le_div_of_nonneg_right h1 hDr.le
      _ = _ := by
        push_cast
        field_simp
  · simp

/-- `chord ≥ 0`. -/
theorem chord_nonneg {Pa Pb a0 a1 b0 b1 S : ℤ} (hab : Pa ≤ Pb) (hS : 0 < S) :
    0 ≤ chord Pa Pb a0 a1 b0 b1 S := by
  unfold chord
  dsimp only
  split_ifs with h1 h2 h3
  · exact le_rfl
  · omega
  · exact Int.ediv_nonneg h3.le (by omega)
  · exact le_rfl

/-- The tangent of `(1 - x) ^ r` at `z / D`, with the penalty tables (8.3):
`E_t (z) / D + r E_{t+1} (z) (z / D - x) / D ≤ (1 - x) ^ r` for `x ≤ z / D`. -/
theorem tangent_Epen_le {D z r : ℕ} (hD : 0 < D) (hz : z ≤ D) (hr : 1 ≤ r) {x : ℝ} (hx0 : 0 ≤ x)
    (hxz : x * D ≤ z) :
    ((D : ℝ) * Epen D z r + ((r * Epen D z (r - 1) : ℕ) : ℝ) * z -
        ((r * Epen D z (r - 1) : ℕ) : ℝ) * (x * D)) / (D : ℝ) ^ 2 ≤ (1 - x) ^ r := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  set p : ℝ := (z : ℝ) / D with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one hDr]
    exact_mod_cast hz
  have hxp : x ≤ p := by
    rw [hp, le_div_iff₀ hDr]
    exact hxz
  have hx1 : x ≤ 1 := hxp.trans hp1
  have h1 := Robbins.Cert.SO.Epen_le hD hz r
  have h2 := Robbins.Cert.SO.Epen_le hD hz (r - 1)
  have ht := tangent_le_one_sub_pow hx0 hx1 hp0 hp1 r
  have hE1 : (Epen D z r : ℝ) / D ≤ (1 - p) ^ r := by
    rw [div_le_iff₀ hDr, hp]
    linarith
  have hE2 : (Epen D z (r - 1) : ℝ) / D ≤ (1 - p) ^ (r - 1) := by
    rw [div_le_iff₀ hDr, hp]
    linarith
  have heq : ((D : ℝ) * Epen D z r + ((r * Epen D z (r - 1) : ℕ) : ℝ) * z -
        ((r * Epen D z (r - 1) : ℕ) : ℝ) * (x * D)) / (D : ℝ) ^ 2 =
      (Epen D z r : ℝ) / D + (r : ℝ) * ((Epen D z (r - 1) : ℝ) / D) * (p - x) := by
    rw [hp]
    push_cast
    field_simp
    ring
  rw [heq]
  have h3 : (r : ℝ) * ((Epen D z (r - 1) : ℝ) / D) * (p - x) ≤
      (r : ℝ) * (1 - p) ^ (r - 1) * (p - x) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_left hE2 (Nat.cast_nonneg r)
  linarith

/-! ## The integrand of (R_t) -/

/-- The integrand of (R_t) for the second-order sub-solution `uSO`. -/
noncomputable def integrandSO (D : ℕ) (g : Grid) (d : ℕ) (uh : ℕ → (Fin (d + 1) → ℕ) → ℕ)
    (sg : ℕ → (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) (t : ℕ) (y : Fin (d + 1) → ℝ) (x : ℝ) : ℝ :=
  min (relaxStop g.n t y x) (dropPenalty g.n t y x + uSO D g d uh sg (t + 1) (ins y x))

variable {D : ℕ} {g : Grid}

/-- `u_t` is measurable. -/
theorem measurable_uSO (d : ℕ) (uh : ℕ → (Fin (d + 1) → ℕ) → ℕ)
    (sg : ℕ → (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) (t : ℕ) : Measurable (uSO D g d uh sg t) := by
  have hk : Measurable fun z : Fin (d + 1) → ℝ => fun l => ceilR D g t (z l) :=
    measurable_pi_iff.mpr fun l => (g.so_measurable_ceilR D t).comp (measurable_pi_apply l)
  unfold uSO
  dsimp only
  apply Measurable.add
  · exact ((measurable_of_countable (fun k : Fin (d + 1) → ℕ => (uh t k : ℝ))).comp hk).div_const _
  · apply Finset.measurable_sum
    intro l _
    apply Measurable.mul
    · exact ((measurable_of_countable
        (fun k : Fin (d + 1) → ℕ => (sg t k l : ℝ))).comp hk).div_const _
    · apply Measurable.sub
      · exact ((measurable_of_countable
          (fun k : Fin (d + 1) → ℕ => (pt D g (g.glob t (k l)) : ℝ))).comp hk).div_const _
      · exact measurable_pi_apply l

/-- `u_t` is bounded on memories. -/
theorem abs_uSO_le (hg : ok D g = true) (d : ℕ) (uh : ℕ → (Fin (d + 1) → ℕ) → ℕ)
    (sg : ℕ → (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) (t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin (d + 1) → ℝ, IsMemory z → |uSO D g d uh sg t z| ≤ C := by
  have hD : 0 < D := g.so_D_pos D hg
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  obtain ⟨B1, hB1⟩ := exists_bound_of_le (uh t) (g.cnt t)
  obtain ⟨B2, hB2⟩ := exists_bound_of_le (fun k => ∑ l, sg t k l) (g.cnt t)
  refine ⟨(B1 : ℝ) / D + (B2 : ℝ) / D, by positivity, fun z hz => ?_⟩
  set k : Fin (d + 1) → ℕ := fun l => ceilR D g t (z l) with hkdef
  have hkc : ∀ l, k l ≤ g.cnt t := fun l => g.so_ceilR_le_cnt D t (z l)
  unfold uSO
  dsimp only
  rw [← hkdef]
  have h1 : |(uh t k : ℝ) / D| ≤ (B1 : ℝ) / D := by
    rw [abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hB1 k hkc) hDr.le
  have hterm : ∀ l, |(sg t k l : ℝ) / D * ((pt D g (g.glob t (k l)) : ℝ) / D - z l)| ≤
      (sg t k l : ℝ) / D := by
    intro l
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (sg t k l : ℝ) / D)]
    have hG0 : (0 : ℝ) ≤ (pt D g (g.glob t (k l)) : ℝ) / D := by positivity
    have hG1 : (pt D g (g.glob t (k l)) : ℝ) / D ≤ 1 := by
      rw [div_le_one hDr]
      exact_mod_cast g.so_pt_le_D D hg _
    have hzl := hz.2 l
    have hab : |(pt D g (g.glob t (k l)) : ℝ) / D - z l| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hzl.1, hzl.2]
    calc _ ≤ (sg t k l : ℝ) / D * 1 := mul_le_mul_of_nonneg_left hab (by positivity)
      _ = _ := mul_one _
  have h2 : |∑ l, (sg t k l : ℝ) / D * ((pt D g (g.glob t (k l)) : ℝ) / D - z l)| ≤
      (B2 : ℝ) / D := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ l, (sg t k l : ℝ) / D := Finset.sum_le_sum fun l _ => hterm l
      _ = ((∑ l, sg t k l : ℕ) : ℝ) / D := by
        push_cast
        rw [Finset.sum_div]
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hB2 k hkc) hDr.le
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem integrableOn_integrandSO (hg : ok D g = true) {t d : ℕ} (htn : t < g.n)
    {y : Fin (d + 1) → ℝ} (hy : IsMemory y) (uh : ℕ → (Fin (d + 1) → ℕ) → ℕ)
    (sg : ℕ → (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) :
    IntegrableOn (integrandSO D g d uh sg t y) (Set.Icc (0 : ℝ) 1) := by
  have he : integrandSO D g d uh sg t y = fun x => relaxStep g.n (uSO D g d uh sg) t y x := by
    funext x
    simp only [integrandSO, relaxStep, htn, ↓reduceIte]
  rw [he]
  have h1 := measurable_relaxStep g.n (uSO D g d uh sg) t fun _ => measurable_uSO d uh sg (t + 1)
  have h2 : Measurable fun x : ℝ => ((y, x) : (Fin (d + 1) → ℝ) × ℝ) :=
    measurable_const.prodMk measurable_id
  have hmeas : Measurable fun x : ℝ => relaxStep g.n (uSO D g d uh sg) t y x := by
    have := h1.comp h2
    exact this
  obtain ⟨C, hC0, hC⟩ := abs_uSO_le hg d uh sg (t + 1)
  exact integrable_Icc_of_bound hmeas _ fun x hx =>
    abs_relaxStep_le g.n _ htn.le hC0 (fun _ z hz => hC z hz) hy hx

theorem intervalIntegrable_integrandSO (hg : ok D g = true) {t d : ℕ} (htn : t < g.n)
    {y : Fin (d + 1) → ℝ} (hy : IsMemory y) (uh : ℕ → (Fin (d + 1) → ℕ) → ℕ)
    (sg : ℕ → (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) : IntervalIntegrable (integrandSO D g d uh sg t y) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact (integrableOn_integrandSO hg htn hy uh sg).mono_set (Set.Icc_subset_Icc ha hb)

/-! ## Signs and the index `jT` -/

section Signs

theorem coefC_nonneg {d : ℕ} (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) (t : ℕ)
    (c : Fin (d + 1) → Rec) (i : ℕ) (l : Fin (d + 1)) : 0 ≤ coefC D g d Sg t c i l := by
  unfold coefC
  dsimp only
  split_ifs <;> first | exact le_rfl | exact Int.natCast_nonneg _ | positivity

theorem lamC_nonneg {d : ℕ} (N : (Fin (d + 1) → ℕ) → ℕ)
    (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) (t : ℕ) (c : Fin (d + 1) → Rec) (i : ℕ)
    (l : Fin (d + 1)) : 0 ≤ lamC D g d N Sg t c i l := by
  unfold lamC
  split_ifs with h
  · dsimp only
    apply sub_nonneg.mpr
    apply min_le_min_right
    exact_mod_cast Nat.mul_le_mul_right D (Nat.le_succ _)
  · exact le_rfl

theorem jT_le_L {d : ℕ} (N : (Fin (d + 1) → ℕ) → ℕ) (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ)
    (t : ℕ) (c : Fin (d + 1) → Rec) : jT D g d N Sg t c ≤ g.L t := by
  unfold jT
  cases hf : List.find? _ _ with
  | none => simp
  | some j =>
    simp only [Option.getD_some]
    have hm := List.mem_of_find?_eq_some hf
    rw [List.mem_range'_1] at hm
    omega

theorem im_le_jT {d : ℕ} (N : (Fin (d + 1) → ℕ) → ℕ) (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ)
    (t : ℕ) (c : Fin (d + 1) → Rec) (h : im d c ≤ g.L t) : im d c ≤ jT D g d N Sg t c := by
  unfold jT
  cases hf : List.find? _ _ with
  | none => simpa using h
  | some j =>
    simp only [Option.getD_some]
    have hm := List.mem_of_find?_eq_some hf
    rw [List.mem_range'_1] at hm
    omega

/-- At `jT < L`, the stop cost at `p_jT` is above the continuation (section 5.4). -/
theorem jT_spec {d : ℕ} (N : (Fin (d + 1) → ℕ) → ℕ) (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ)
    (t : ℕ) (c : Fin (d + 1) → Rec) (h : jT D g d N Sg t c < g.L t) :
    (D : ℤ) * (Epen D (cp D g t (jT D g d N Sg t c)) (g.n - t) + (g.n - t) : ℕ) +
        UT D g d N Sg t c + ST d Sg c ≤
      (((d + 2) * D * D + (g.n - t) * D * cp D g t (jT D g d N Sg t c) : ℕ) : ℤ) := by
  unfold jT at h ⊢
  cases hf : List.find? _ _ with
  | none => simp only [hf, Option.getD_none, lt_self_iff_false] at h
  | some j =>
    simp only [hf, Option.getD_some] at h ⊢
    have := List.find?_some hf
    simpa using this

end Signs

/-! ## The cells -/

section Cells

variable {t d : ℕ} {c : Fin (d + 1) → Rec} {y : Fin (d + 1) → ℝ}

/-- The credited part `s` of the slopes: `0 ≤ s ≤ S / D ^ 2`, `S = sum over l of coef_l w_l`. -/
theorem credit_le (hD : 0 < D) (hy : IsMemory y) (hc : RecOK D g t c) (hfit : Fits D g t c y)
    (coef : Fin (d + 1) → ℤ) (hcoef : ∀ l, 0 ≤ coef l) :
    0 ≤ ∑ l, (if 0 < (c l).w then (coef l : ℝ) * (((c l).val : ℝ) / D - y l) / D else 0) ∧
    ∑ l, (if 0 < (c l).w then (coef l : ℝ) * (((c l).val : ℝ) / D - y l) / D else 0) ≤
      ((∑ l, coef l * (c l).w : ℤ) : ℝ) / (D : ℝ) ^ 2 := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  constructor
  · apply Finset.sum_nonneg
    intro l _
    split_ifs
    · have h1 := fit_delta_nonneg hD hc hfit l
      have h0 : (0 : ℝ) ≤ coef l := by exact_mod_cast hcoef l
      exact div_nonneg (mul_nonneg h0 h1) hDr.le
    · exact le_rfl
  · push_cast
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro l _
    split_ifs with hw
    · have h1 := fit_delta_le hD hy hc hfit l hw
      have h0 : (0 : ℝ) ≤ coef l := by exact_mod_cast hcoef l
      calc (coef l : ℝ) * (((c l).val : ℝ) / D - y l) / D
          ≤ (coef l : ℝ) * (((c l).w : ℝ) / D) / D := by gcongr
        _ = _ := by field_simp
    · have hw0 : (c l).w = 0 := by omega
      simp [hw0]

/-- `M ≥ 0`. -/
theorem MC_nonneg (N : (Fin (d + 1) → ℕ) → ℕ) (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ)
    (i : ℕ) : 0 ≤ MC D g d N Sg t c i := by
  unfold MC
  dsimp only
  split_ifs with h
  · exact Int.ediv_nonneg h.le (Int.natCast_nonneg D)
  · exact le_rfl

/-- 8.5 (d) on the cell `i`: the own-cell credits integrate the count of the coordinates of the
cell below `x`, capped at `M / D`. -/
theorem head_lam (hD : 0 < D) (hy : IsMemory y) (hc : RecOK D g t c) (hfit : Fits D g t c y)
    (N : (Fin (d + 1) → ℕ) → ℕ) (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) {i : ℕ}
    (hab : (cp D g t (i - 1) : ℝ) / D ≤ (cp D g t i : ℝ) / D) :
    ∑ l, (if 0 < (c l).w then
        (lamC D g d N Sg t c i l : ℝ) / D * (((c l).val : ℝ) / D - y l) else 0) ≤
      ∫ x in (cp D g t (i - 1) : ℝ) / D..(cp D g t i : ℝ) / D,
        min ((Finset.univ.filter fun l => (c l).pos = i ∧ y l < x).card : ℝ)
          ((MC D g d N Sg t c i : ℝ) / D) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  set M : ℝ := (MC D g d N Sg t c i : ℝ) / D with hMdef
  have hM : 0 ≤ M := div_nonneg (by exact_mod_cast MC_nonneg N Sg i) hDr.le
  set a : ℝ := (cp D g t (i - 1) : ℝ) / D
  set b : ℝ := (cp D g t i : ℝ) / D
  let P : Fin (d + 1) → Prop := fun l => (c l).pos = i ∧ (c l).forg = false
  have hya : ∀ q, P q → a ≤ y q := by
    intro q hq
    have h := fit_cp_pred_le hy hfit q
    rw [hq.1] at h
    exact (div_le_iff₀ hDr).mpr h
  have hyb : ∀ q, P q → y q ≤ b := by
    intro q hq
    have h := (hfit q).2
    rw [hq.1] at h
    exact (le_div_iff₀ hDr).mpr h
  have hint := integral_min_count_filter hab hM hy.1 P hya hyb
  have hmono : ∫ x in a..b, min ((Finset.univ.filter fun q => P q ∧ y q < x).card : ℝ) M ≤
      ∫ x in a..b, min ((Finset.univ.filter fun l => (c l).pos = i ∧ y l < x).card : ℝ) M := by
    apply intervalIntegral.integral_mono_on hab
    · exact Monotone.intervalIntegrable fun x x' h =>
        min_le_min_right M (monotone_count P y h)
    · exact Monotone.intervalIntegrable fun x x' h =>
        min_le_min_right M (monotone_count (fun l => (c l).pos = i) y h)
    · intro x _
      apply min_le_min_right
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, P] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩
  refine le_trans ?_ (hint ▸ hmono)
  apply Finset.sum_le_sum
  intro l _
  by_cases hP : P l
  · have hlam : (lamC D g d N Sg t c i l : ℝ) / D =
        min (((Finset.univ.filter fun q' => q' < l ∧ P q').card : ℝ) + 1) M -
          min ((Finset.univ.filter fun q' => q' < l ∧ P q').card : ℝ) M := by
      unfold lamC
      rw [ite_eq_left hP]
      dsimp only
      push_cast
      rw [sub_div, hMdef, ← min_div_div_right hDr.le, ← min_div_div_right hDr.le,
        mul_div_cancel_right₀ _ hDr.ne', mul_div_cancel_right₀ _ hDr.ne']
    have hval : ((c l).val : ℝ) / D = b := by
      rw [hc.val_eq l, hP.1]
    rw [ite_eq_left hP, ← hlam, ← hval]
    split_ifs
    · exact le_rfl
    · have h1 := fit_delta_nonneg hD hc hfit l
      have h0 : (0 : ℝ) ≤ (lamC D g d N Sg t c i l : ℝ) / D :=
        div_nonneg (by exact_mod_cast lamC_nonneg N Sg t c i l) hDr.le
      exact mul_nonneg h0 h1
  · have hlam : lamC D g d N Sg t c i l = 0 := by
      unfold lamC
      rw [ite_eq_right hP]
    rw [ite_eq_right hP, hlam]
    split_ifs <;> simp

/-- The cell `1 ≤ i ≤ im` (8.6): 8.4 with the bounds of 8.2 (`relaxStop_cell`, `cont_ge_cell`),
integrated with 8.5 (a), (c), (d). -/
theorem head_cell (hg : ok D g = true) (ht1 : 1 ≤ t) (htn : t < g.n) (hy : IsMemory y)
    (hc : RecOK D g t c) (hfit : Fits D g t c y) (uh : ℕ → (Fin (d + 1) → ℕ) → ℕ)
    (sg : ℕ → (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ im d c) :
    (RC D g d (uh (t + 1)) (sg (t + 1)) t c i : ℝ) / (2 * (D : ℝ) ^ 3) +
      ∑ l, (if 0 < (c l).w then
        ((coefC D g d (sg (t + 1)) t c i l : ℝ) * QC D g d (uh (t + 1)) (sg (t + 1)) t c i /
            (D : ℝ) ^ 2 + (lamC D g d (uh (t + 1)) (sg (t + 1)) t c i l : ℝ) / D) *
          (((c l).val : ℝ) / D - y l) else 0) ≤
      ∫ x in (cp D g t (i - 1) : ℝ) / D..(cp D g t i : ℝ) / D, integrandSO D g d uh sg t y x := by
  have hD : 0 < D := g.so_D_pos D hg
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hiL : i ≤ g.L t := him.trans (hc.pos_le (Fin.last d))
  have hcp : cp D g t (i - 1) < cp D g t i := g.so_cp_lt_cp D hg (by omega) hiL
  have hcpD : cp D g t i ≤ D := g.so_cp_le_D D hg t i
  have hab : (cp D g t (i - 1) : ℝ) / D < (cp D g t i : ℝ) / D :=
    div_lt_div_of_pos_right (by exact_mod_cast hcp) hDr
  have ha0 : 0 ≤ (cp D g t (i - 1) : ℝ) / D := by positivity
  have hb1 : (cp D g t i : ℝ) / D ≤ 1 := by
    rw [div_le_one hDr]
    exact_mod_cast hcpD
  have hrn : 0 < g.n - t := by omega
  -- the data of the cell
  set N := uh (t + 1) with hN
  set Sg := sg (t + 1) with hSg
  have ha1 : (0 : ℤ) < (((g.n - t) * D : ℕ) : ℤ) := by exact_mod_cast Nat.mul_pos hrn hD
  have hsig : (0 : ℤ) ≤ sigmaC g d Sg t c i := by unfold sigmaC; positivity
  -- the functions of 8.4
  set A : ℝ → ℝ := fun x => ((a0C D d c i : ℝ) + ((((g.n - t) * D : ℕ) : ℤ) : ℝ) * (x * D)) /
    (D : ℝ) ^ 2 with hA
  set B : ℝ → ℝ := fun x => ((betaC D g d N Sg t c i : ℝ) -
    (sigmaC g d Sg t c i : ℝ) * (x * D)) / (D : ℝ) ^ 2 with hB
  set NN : ℝ → ℝ := fun x => ((Finset.univ.filter fun l => (c l).pos = i ∧ y l < x).card : ℝ)
    with hNN
  set s : ℝ := ∑ l, (if 0 < (c l).w then
    (coefC D g d Sg t c i l : ℝ) * (((c l).val : ℝ) / D - y l) / D else 0) with hs
  obtain ⟨hs0, hsS⟩ := credit_le hD hy hc hfit (coefC D g d Sg t c i) (coefC_nonneg Sg t c i)
  set S' : ℝ := if 0 < SC D g d Sg t c i then (SC D g d Sg t c i : ℝ) / (D : ℝ) ^ 2 else 1
    with hS'
  have hS'0 : 0 < S' := by
    rw [hS']
    split_ifs with h
    · have : (0 : ℝ) < SC D g d Sg t c i := by exact_mod_cast h
      positivity
    · exact one_pos
  have hsS' : s ≤ S' := by
    rw [hS']
    split_ifs with h
    · exact hsS
    · have h' : (SC D g d Sg t c i : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp h
      have : (SC D g d Sg t c i : ℝ) / (D : ℝ) ^ 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg h' (by positivity)
      unfold SC at this
      linarith
  -- pointwise bounds on the open cell
  have hcell : ∀ x ∈ Set.Ioo ((cp D g t (i - 1) : ℝ) / D) ((cp D g t i : ℝ) / D),
      (cp D g t (i - 1) : ℝ) < x * D ∧ x * D ≤ cp D g t i := by
    intro x hx
    exact ⟨(div_lt_iff₀ hDr).mp hx.1, ((lt_div_iff₀ hDr).mp hx.2).le⟩
  have hFx : ∀ x ∈ Set.Ioo ((cp D g t (i - 1) : ℝ) / D) ((cp D g t i : ℝ) / D),
      min (A x + NN x) (B x + s) ≤ integrandSO D g d uh sg t y x := by
    intro x hx
    obtain ⟨hxa, hxb⟩ := hcell x hx
    unfold integrandSO
    apply min_le_min
    · rw [relaxStop_cell hg htn.le hc hfit hi1 him hxa hxb]
      simp only [hA, hNN, a0C]
      push_cast
      field_simp
      ring_nf
      exact le_rfl
    · exact cont_ge_cell hg ht1 htn hy hc hfit hi1 him hxa hxb uh sg
  have hMB : ∀ x ∈ Set.Ioo ((cp D g t (i - 1) : ℝ) / D) ((cp D g t i : ℝ) / D),
      (MC D g d N Sg t c i : ℝ) / D ≤ max 0 (B x - A x) := by
    intro x hx
    obtain ⟨_, hxb⟩ := hcell x hx
    have h := MC_le_aux hD (beta := betaC D g d N Sg t c i) (a0 := a0C D d c i)
      (hk := add_nonneg hsig ha1.le) (P := (cp D g t i : ℤ)) (by exact_mod_cast hxb)
    unfold MC
    simpa only [hA, hB, Int.cast_natCast] using h
  have hAc : Continuous A := by rw [hA]; fun_prop
  have hBc : Continuous B := by rw [hB]; fun_prop
  have hNi : IntervalIntegrable NN volume ((cp D g t (i - 1) : ℝ) / D) ((cp D g t i : ℝ) / D) :=
    Monotone.intervalIntegrable (monotone_count (fun l => (c l).pos = i) y)
  have hFi := intervalIntegrable_integrandSO hg htn hy uh sg ha0 hab.le hb1
  have key := cell_int_le hab.le hFi hAc hBc hNi (fun x _ => Nat.cast_nonneg _) hS'0 hs0 hsS'
    (div_nonneg (by exact_mod_cast MC_nonneg N Sg i) hDr.le) hMB hFx
  -- the three integrals
  have h1 : (RC D g d N Sg t c i : ℝ) / (2 * (D : ℝ) ^ 3) ≤
      ∫ x in (cp D g t (i - 1) : ℝ) / D..(cp D g t i : ℝ) / D, min (A x) (B x) := by
    have := cell2_div_le hDr (Pa := (cp D g t (i - 1) : ℤ)) (Pb := (cp D g t i : ℤ))
      (a0 := a0C D d c i) (b0 := betaC D g d N Sg t c i) (by exact_mod_cast hcp) ha1 hsig
    simpa only [RC, hA, hB, Int.cast_natCast] using this
  have h2 : s * ((QC D g d N Sg t c i : ℝ) / D) ≤
      s * ∫ x in (cp D g t (i - 1) : ℝ) / D..(cp D g t i : ℝ) / D,
        min 1 (max 0 (A x - B x) / S') := by
    by_cases h : 0 < SC D g d Sg t c i
    · apply mul_le_mul_of_nonneg_left _ hs0
      have := chord_div_le hDr (Pa := (cp D g t (i - 1) : ℤ)) (Pb := (cp D g t i : ℤ))
        (a0 := a0C D d c i) (b0 := betaC D g d N Sg t c i) (by exact_mod_cast hcp) ha1 hsig h
      have hQ : QC D g d N Sg t c i = chord (cp D g t (i - 1)) (cp D g t i) (a0C D d c i)
          ((g.n - t) * D : ℕ) (betaC D g d N Sg t c i) (sigmaC g d Sg t c i)
          (SC D g d Sg t c i) := by
        unfold QC
        rw [ite_eq_left h]
      rw [hQ, hS', ite_eq_left h]
      simpa only [hA, hB, Int.cast_natCast] using this
    · have hSn : (SC D g d Sg t c i : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp h
      have : (SC D g d Sg t c i : ℝ) / (D : ℝ) ^ 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hSn (by positivity)
      have hs00 : s = 0 := by
        apply le_antisymm _ hs0
        unfold SC at this
        linarith
      rw [hs00, zero_mul, zero_mul]
  have h3 := head_lam hD hy hc hfit N Sg hab.le
  -- the credited sum splits
  have hsplit : ∑ l, (if 0 < (c l).w then
        ((coefC D g d Sg t c i l : ℝ) * QC D g d N Sg t c i / (D : ℝ) ^ 2 +
          (lamC D g d N Sg t c i l : ℝ) / D) * (((c l).val : ℝ) / D - y l) else 0) =
      s * ((QC D g d N Sg t c i : ℝ) / D) +
        ∑ l, (if 0 < (c l).w then
          (lamC D g d N Sg t c i l : ℝ) / D * (((c l).val : ℝ) / D - y l) else 0) := by
    rw [hs, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs
    · field_simp
    · simp
  rw [hsplit]
  linarith

/-- A tail cell `im < i ≤ L` (8.6), the last record not forgotten: 8.4 with `N = 0` and the
bounds of 8.3 (`relaxStop_tail`, `cont_tail`, the tangent `tangent_Epen_le`), integrated with
8.5 (a), (c). -/
theorem tail_cell (hg : ok D g = true) (ht1 : 1 ≤ t) (htn : t < g.n) (hy : IsMemory y)
    (hc : RecOK D g t c) (hfit : Fits D g t c y) (htf : (c (Fin.last d)).forg = false)
    (uh : ℕ → (Fin (d + 1) → ℕ) → ℕ) (sg : ℕ → (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) {i : ℕ}
    (hi : im d c < i) (hiL : i ≤ g.L t) :
    (RT D g d (uh (t + 1)) (sg (t + 1)) t c i : ℝ) / (2 * (D : ℝ) ^ 3) +
      ∑ l, (if 0 < (c l).w then
        (sg (t + 1) (fun l => (c l).map) l : ℝ) * QT D g d (uh (t + 1)) (sg (t + 1)) t c i /
          (D : ℝ) ^ 2 * (((c l).val : ℝ) / D - y l) else 0) ≤
      ∫ x in (cp D g t (i - 1) : ℝ) / D..(cp D g t i : ℝ) / D, integrandSO D g d uh sg t y x := by
  have hD : 0 < D := g.so_D_pos D hg
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hcp : cp D g t (i - 1) < cp D g t i := g.so_cp_lt_cp D hg (by omega) hiL
  have hcpD : cp D g t i ≤ D := g.so_cp_le_D D hg t i
  have him : cp D g t (im d c) ≤ cp D g t (i - 1) := g.so_cp_mono D hg (by omega) (by omega)
  have hab : (cp D g t (i - 1) : ℝ) / D < (cp D g t i : ℝ) / D :=
    div_lt_div_of_pos_right (by exact_mod_cast hcp) hDr
  have ha0 : 0 ≤ (cp D g t (i - 1) : ℝ) / D := by positivity
  have hb1 : (cp D g t i : ℝ) / D ≤ 1 := by
    rw [div_le_one hDr]
    exact_mod_cast hcpD
  have hrn : 1 ≤ g.n - t := by omega
  set N := uh (t + 1) with hN
  set Sg := sg (t + 1) with hSg
  set slc : Fin (d + 1) → ℕ := Sg (fun l => (c l).map) with hslc
  set sig : ℤ := (((g.n - t) * Epen D (cp D g t i) (g.n - t - 1) : ℕ) : ℤ) with hsig
  set beta : ℤ := (D : ℤ) * Epen D (cp D g t i) (g.n - t) + UT D g d N Sg t c + sig * cp D g t i
    with hbeta
  have ha1 : (0 : ℤ) < (((g.n - t) * D : ℕ) : ℤ) := by exact_mod_cast Nat.mul_pos (by omega) hD
  have hsig0 : (0 : ℤ) ≤ sig := by rw [hsig]; positivity
  set A : ℝ → ℝ := fun x => (((((d + 2) * D * D : ℕ) : ℤ) : ℝ) +
    ((((g.n - t) * D : ℕ) : ℤ) : ℝ) * (x * D)) / (D : ℝ) ^ 2 with hA
  set B : ℝ → ℝ := fun x => ((beta : ℝ) - (sig : ℝ) * (x * D)) / (D : ℝ) ^ 2 with hB
  set s : ℝ := ∑ l, (if 0 < (c l).w then
    ((slc l : ℤ) : ℝ) * (((c l).val : ℝ) / D - y l) / D else 0) with hs
  obtain ⟨hs0, hsS⟩ := credit_le hD hy hc hfit (fun l => (slc l : ℤ)) (fun l => Int.natCast_nonneg _)
  set S' : ℝ := if 0 < ST d Sg c then (ST d Sg c : ℝ) / (D : ℝ) ^ 2 else 1 with hS'
  have hS'0 : 0 < S' := by
    rw [hS']
    split_ifs with h
    · have : (0 : ℝ) < ST d Sg c := by exact_mod_cast h
      positivity
    · exact one_pos
  have hsS' : s ≤ S' := by
    rw [hS']
    split_ifs with h
    · exact hsS
    · have h' : (ST d Sg c : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp h
      have : (ST d Sg c : ℝ) / (D : ℝ) ^ 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg h' (by positivity)
      unfold ST at this
      linarith
  have hcell : ∀ x ∈ Set.Ioo ((cp D g t (i - 1) : ℝ) / D) ((cp D g t i : ℝ) / D),
      (cp D g t (i - 1) : ℝ) < x * D ∧ x * D ≤ cp D g t i := by
    intro x hx
    exact ⟨(div_lt_iff₀ hDr).mp hx.1, ((lt_div_iff₀ hDr).mp hx.2).le⟩
  have hFx : ∀ x ∈ Set.Ioo ((cp D g t (i - 1) : ℝ) / D) ((cp D g t i : ℝ) / D),
      min (A x + 0) (B x + s) ≤ integrandSO D g d uh sg t y x := by
    intro x hx
    obtain ⟨hxa, hxb⟩ := hcell x hx
    have hxim : (cp D g t (im d c) : ℝ) < x * D :=
      lt_of_le_of_lt (by exact_mod_cast him) hxa
    have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt ha0 hx.1)
    unfold integrandSO
    apply min_le_min
    · rw [relaxStop_tail hg htn.le hc hfit hxim, add_zero]
      simp only [hA]
      push_cast
      field_simp
      exact le_rfl
    · rw [cont_tail hg ht1 htn hy hc hfit htf uh sg hxim]
      have htan := tangent_Epen_le hD hcpD hrn hx0 hxb
      have hsl : s ≤ ∑ l, (sg (t + 1) (fun l => (c l).map) l : ℝ) *
          (((c l).val : ℝ) / D - y l) / D := by
        rw [hs]
        apply Finset.sum_le_sum
        intro l _
        split_ifs
        · simp [hslc, hSg]
        · have h1 := fit_delta_nonneg hD hc hfit l
          positivity
      have hBx : B x = ((D : ℝ) * Epen D (cp D g t i) (g.n - t) +
          (((g.n - t) * Epen D (cp D g t i) (g.n - t - 1) : ℕ) : ℝ) * cp D g t i -
          (((g.n - t) * Epen D (cp D g t i) (g.n - t - 1) : ℕ) : ℝ) * (x * D)) / (D : ℝ) ^ 2 +
          (UT D g d N Sg t c : ℝ) / (D : ℝ) ^ 2 := by
        simp only [hB, hbeta, hsig]
        push_cast
        ring
      rw [hBx]
      linarith
  have hMB : ∀ x ∈ Set.Ioo ((cp D g t (i - 1) : ℝ) / D) ((cp D g t i : ℝ) / D),
      (0 : ℝ) ≤ max 0 (B x - A x) := fun _ _ => le_max_left _ _
  have hAc : Continuous A := by rw [hA]; fun_prop
  have hBc : Continuous B := by rw [hB]; fun_prop
  have hFi := intervalIntegrable_integrandSO hg htn hy uh sg ha0 hab.le hb1
  have key := cell_int_le hab.le hFi hAc hBc (N := fun _ => 0) intervalIntegrable_const
    (fun _ _ => le_rfl) hS'0 hs0 hsS' le_rfl hMB hFx
  simp only [min_self, intervalIntegral.integral_zero, add_zero] at key
  have h1 : (RT D g d N Sg t c i : ℝ) / (2 * (D : ℝ) ^ 3) ≤
      ∫ x in (cp D g t (i - 1) : ℝ) / D..(cp D g t i : ℝ) / D, min (A x) (B x) := by
    have := cell2_div_le hDr (Pa := (cp D g t (i - 1) : ℤ)) (Pb := (cp D g t i : ℤ))
      (a0 := (((d + 2) * D * D : ℕ) : ℤ)) (b0 := beta) (by exact_mod_cast hcp) ha1 hsig0
    simpa only [RT, hA, hB, hbeta, hsig, Int.cast_natCast] using this
  have h2 : s * ((QT D g d N Sg t c i : ℝ) / D) ≤
      s * ∫ x in (cp D g t (i - 1) : ℝ) / D..(cp D g t i : ℝ) / D,
        min 1 (max 0 (A x - B x) / S') := by
    by_cases h : 0 < ST d Sg c
    · apply mul_le_mul_of_nonneg_left _ hs0
      have := chord_div_le hDr (Pa := (cp D g t (i - 1) : ℤ)) (Pb := (cp D g t i : ℤ))
        (a0 := (((d + 2) * D * D : ℕ) : ℤ)) (b0 := beta) (by exact_mod_cast hcp) ha1 hsig0 h
      have hQ : QT D g d N Sg t c i = chord (cp D g t (i - 1)) (cp D g t i)
          (((d + 2) * D * D : ℕ) : ℤ) ((g.n - t) * D : ℕ) beta sig (ST d Sg c) := by
        unfold QT
        rw [ite_eq_left h]
      rw [hQ, hS', ite_eq_left h]
      simpa only [hA, hB, Int.cast_natCast] using this
    · have hSn : (ST d Sg c : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp h
      have : (ST d Sg c : ℝ) / (D : ℝ) ^ 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hSn (by positivity)
      have hs00 : s = 0 := by
        apply le_antisymm _ hs0
        unfold ST at this
        linarith
      rw [hs00, zero_mul, zero_mul]
  have hsplit : ∑ l, (if 0 < (c l).w then
        (sg (t + 1) (fun l => (c l).map) l : ℝ) * QT D g d N Sg t c i / (D : ℝ) ^ 2 *
          (((c l).val : ℝ) / D - y l) else 0) =
      s * ((QT D g d N Sg t c i : ℝ) / D) := by
    rw [hs, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs
    · simp only [hslc, hSg, Int.cast_natCast]
      field_simp
    · simp
  rw [hsplit]
  linarith

/-- The exact tail `[p_jT / D, 1]` (8.6), the last record not forgotten, `p_jT < D`: there the stop
cost is above the continuation (`jT_spec`, `le_Epen_add`, `sub_one_sub_pow_mono`), and the
continuation integrates by 8.5 (e). -/
theorem final_seg (hg : ok D g = true) (ht1 : 1 ≤ t) (htn : t < g.n) (hy : IsMemory y)
    (hc : RecOK D g t c) (hfit : Fits D g t c y) (htf : (c (Fin.last d)).forg = false)
    (uh : ℕ → (Fin (d + 1) → ℕ) → ℕ) (sg : ℕ → (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ)
    (hj : cp D g t (jT D g d (uh (t + 1)) (sg (t + 1)) t c) < D) :
    (RE D g d (uh (t + 1)) (sg (t + 1)) t c : ℝ) / (2 * (D : ℝ) ^ 3) +
      ∑ l, (if 0 < (c l).w then
        (sg (t + 1) (fun l => (c l).map) l : ℝ) *
          ((D - cp D g t (jT D g d (uh (t + 1)) (sg (t + 1)) t c) : ℕ) : ℝ) / (D : ℝ) ^ 2 *
          (((c l).val : ℝ) / D - y l) else 0) ≤
      ∫ x in (cp D g t (jT D g d (uh (t + 1)) (sg (t + 1)) t c) : ℝ) / D..1,
        integrandSO D g d uh sg t y x := by
  have hD : 0 < D := g.so_D_pos D hg
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  set N := uh (t + 1) with hN
  set Sg := sg (t + 1) with hSg
  set j := jT D g d N Sg t c with hjdef
  set p := cp D g t j with hp
  set r := g.n - t with hr
  have hrn : 1 ≤ r := by omega
  have hjL : j < g.L t := by
    rcases (jT_le_L N Sg t c).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← hjdef] at h
      rw [hp, h, g.so_cp_L D t] at hj
      exact lt_irrefl _ hj
  have himL : im d c ≤ g.L t := hc.pos_le (Fin.last d)
  have hij : im d c ≤ j := im_le_jT N Sg t c himL
  have hcond := jT_spec N Sg t c hjL
  rw [← hjdef, ← hp, ← hr] at hcond
  have hpD : p ≤ D := hj.le
  have hP : (p : ℝ) / D < 1 := by
    rw [div_lt_one hDr]
    exact_mod_cast hj
  have hP0 : 0 ≤ (p : ℝ) / D := by positivity
  have hpim : (cp D g t (im d c) : ℝ) ≤ p := by exact_mod_cast g.so_cp_mono D hg hij hjL.le
  set slc : Fin (d + 1) → ℕ := Sg (fun l => (c l).map) with hslc
  set K : ℝ := (UT D g d N Sg t c : ℝ) / (D : ℝ) ^ 2 with hK
  set s : ℝ := ∑ l, (if 0 < (c l).w then
    ((slc l : ℤ) : ℝ) * (((c l).val : ℝ) / D - y l) / D else 0) with hs
  obtain ⟨hs0, hsS⟩ := credit_le hD hy hc hfit (fun l => (slc l : ℤ)) (fun l => Int.natCast_nonneg _)
  have hST : ((∑ l, (slc l : ℤ) * (c l).w : ℤ) : ℝ) = (ST d Sg c : ℝ) := by
    unfold ST
    rfl
  rw [hST] at hsS
  -- the stop cost at `p / D` is above the continuation bound
  have hcondR : (D : ℝ) * ((Epen D p r : ℝ) + r) + (UT D g d N Sg t c : ℝ) + ST d Sg c ≤
      ((d : ℝ) + 2) * D * D + (r : ℝ) * D * p := by
    have := hcond
    exact_mod_cast this
  have hEp := le_Epen_add hD hpD r
  have hstop0 : K + s ≤ ((d + 2 : ℕ) : ℝ) + (r : ℝ) * ((p : ℝ) / D) - (1 - (p : ℝ) / D) ^ r := by
    have h1 : K + (ST d Sg c : ℝ) / (D : ℝ) ^ 2 ≤
        ((d : ℝ) + 2) + (r : ℝ) * ((p : ℝ) / D) - ((Epen D p r : ℝ) + r) / D := by
      rw [hK, ← add_div, div_le_iff₀ (by positivity)]
      have e : (((d : ℝ) + 2) + (r : ℝ) * ((p : ℝ) / D) - ((Epen D p r : ℝ) + r) / D) *
          (D : ℝ) ^ 2 = ((d : ℝ) + 2) * D * D + (r : ℝ) * D * p - D * ((Epen D p r : ℝ) + r) := by
        field_simp
      rw [e]
      linarith
    have h2 : (1 - (p : ℝ) / D) ^ r ≤ ((Epen D p r : ℝ) + r) / D := by
      rw [le_div_iff₀ hDr]
      linarith
    push_cast
    linarith
  -- pointwise on the open segment
  have hFx : ∀ x ∈ Set.Ioo ((p : ℝ) / D) 1,
      (1 - x) ^ r + K + s ≤ integrandSO D g d uh sg t y x := by
    intro x hx
    have hxp : (p : ℝ) < x * D := (div_lt_iff₀ hDr).mp hx.1
    have hxim : (cp D g t (im d c) : ℝ) < x * D := lt_of_le_of_lt hpim hxp
    unfold integrandSO
    apply le_min
    · rw [relaxStop_tail hg htn.le hc hfit hxim]
      have hmono := sub_one_sub_pow_mono hP0 hx.1.le hx.2.le r
      rw [← hr]
      linarith
    · rw [cont_tail hg ht1 htn hy hc hfit htf uh sg hxim]
      have hsl : s ≤ ∑ l, (sg (t + 1) (fun l => (c l).map) l : ℝ) *
          (((c l).val : ℝ) / D - y l) / D := by
        rw [hs]
        apply Finset.sum_le_sum
        intro l _
        split_ifs
        · simp [hslc, hSg]
        · have h1 := fit_delta_nonneg hD hc hfit l
          positivity
      rw [← hr, ← hK]
      linarith
  have hlow : (∫ x in (p : ℝ) / D..1, (1 - x) ^ r + K + s) ≤
      ∫ x in (p : ℝ) / D..1, integrandSO D g d uh sg t y x := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hP.le
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
    · exact intervalIntegrable_integrandSO hg htn hy uh sg hP0 hP.le le_rfl
    · exact hFx
  have hint : (∫ x in (p : ℝ) / D..1, (1 - x) ^ r + K + s) =
      (∫ x in (p : ℝ) / D..1, (1 - x) ^ r) + (K + s) * (1 - (p : ℝ) / D) := by
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_const,
      intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul]
    · ring
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  have hE := Epen_succ_div_le_integral hD hpD r
  -- `RE` and the credited sum
  have hRE : (RE D g d N Sg t c : ℝ) / (2 * (D : ℝ) ^ 3) ≤
      (Epen D p (r + 1) : ℝ) / (D * (r + 1)) + (1 - (p : ℝ) / D) * K := by
    have hRE' : RE D g d N Sg t c = ((2 * D * D * Epen D p (r + 1) / (r + 1) : ℕ) : ℤ) +
        2 * ((D - p : ℕ) : ℤ) * UT D g d N Sg t c := by
      unfold RE
      dsimp only
      rw [← hjdef, ← hp, ← hr, ite_eq_left hj]
    rw [hRE']
    push_cast
    rw [Nat.cast_sub hpD, hK]
    have e1 : (2 * (D : ℝ) * D * Epen D p (r + 1)) / ((r : ℝ) + 1) / (2 * (D : ℝ) ^ 3) =
        (Epen D p (r + 1) : ℝ) / (D * (r + 1)) := by
      field_simp
    have e2 : 2 * ((D : ℝ) - p) * (UT D g d N Sg t c : ℝ) / (2 * (D : ℝ) ^ 3) =
        (1 - (p : ℝ) / D) * ((UT D g d N Sg t c : ℝ) / (D : ℝ) ^ 2) := by
      field_simp
    rw [add_div, e2, ← e1]
    gcongr
    have hq := intCast_ediv_le (a := 2 * (D : ℤ) * D * Epen D p (r + 1)) (b := (r : ℤ) + 1)
      (by positivity)
    push_cast at hq
    exact hq
  have hsplit : ∑ l, (if 0 < (c l).w then
        (sg (t + 1) (fun l => (c l).map) l : ℝ) * ((D - p : ℕ) : ℝ) / (D : ℝ) ^ 2 *
          (((c l).val : ℝ) / D - y l) else 0) =
      (1 - (p : ℝ) / D) * s := by
    rw [hs, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs
    · simp only [hslc, hSg, Int.cast_natCast]
      rw [Nat.cast_sub hpD]
      field_simp
    · simp
  rw [hsplit]
  nlinarith

theorem QC_nonneg (hg : ok D g = true) (N : (Fin (d + 1) → ℕ) → ℕ)
    (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) {i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ g.L t) :
    0 ≤ QC D g d N Sg t c i := by
  unfold QC
  split_ifs with h
  · exact chord_nonneg (by exact_mod_cast g.so_cp_mono D hg (by omega : i - 1 ≤ i) hiL) h
  · exact le_rfl

theorem QT_nonneg (hg : ok D g = true) (N : (Fin (d + 1) → ℕ) → ℕ)
    (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) {i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ g.L t) :
    0 ≤ QT D g d N Sg t c i := by
  unfold QT
  dsimp only
  split_ifs with h
  · exact chord_nonneg (by exact_mod_cast g.so_cp_mono D hg (by omega : i - 1 ≤ i) hiL) h
  · exact le_rfl

theorem acc_nonneg (hg : ok D g = true) (hc : RecOK D g t c) (N : (Fin (d + 1) → ℕ) → ℕ)
    (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) (l : Fin (d + 1)) : 0 ≤ acc D g d N Sg t c l := by
  unfold acc
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro i hi
    rw [Finset.mem_Icc] at hi
    exact mul_nonneg (coefC_nonneg Sg t c i l)
      (QC_nonneg hg N Sg hi.1 (hi.2.trans (hc.pos_le (Fin.last d))))
  · have hQT : 0 ≤ ∑ i ∈ Finset.Ioc (im d c) (jT D g d N Sg t c), QT D g d N Sg t c i := by
      apply Finset.sum_nonneg
      intro i hi
      rw [Finset.mem_Ioc] at hi
      exact QT_nonneg hg N Sg (by omega) (hi.2.trans (jT_le_L N Sg t c))
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (Int.natCast_nonneg _) (add_nonneg hQT (Int.natCast_nonneg _))
    · exact mul_nonneg (Int.natCast_nonneg _) (by simpa using hQT)

theorem lam_nonneg (N : (Fin (d + 1) → ℕ) → ℕ) (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ)
    (l : Fin (d + 1)) : 0 ≤ lam D g d N Sg t c l :=
  Finset.sum_nonneg fun i _ => lamC_nonneg N Sg t c i l

/-- `∫ over [0, 1] = sum of the integrals over the cells 1, ..., K + ∫ over [p_K / D, 1]`. -/
theorem integral_split (hg : ok D g = true) (htn : t < g.n) (hy : IsMemory y)
    (uh : ℕ → (Fin (d + 1) → ℕ) → ℕ) (sg : ℕ → (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) {K : ℕ}
    (hK : K ≤ g.L t) :
    ∫ x in (0 : ℝ)..1, integrandSO D g d uh sg t y x =
      ∑ i ∈ Finset.Icc 1 K, (∫ x in (cp D g t (i - 1) : ℝ) / D..(cp D g t i : ℝ) / D,
        integrandSO D g d uh sg t y x) +
      ∫ x in (cp D g t K : ℝ) / D..1, integrandSO D g d uh sg t y x := by
  have hD : 0 < D := g.so_D_pos D hg
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hle1 : ∀ k, (cp D g t k : ℝ) / D ≤ 1 := by
    intro k
    rw [div_le_one hDr]
    exact_mod_cast g.so_cp_le_D D hg t k
  have hcell : ∀ k, k + 1 ≤ g.L t → IntervalIntegrable (integrandSO D g d uh sg t y) volume
      ((cp D g t k : ℝ) / D) ((cp D g t (k + 1) : ℝ) / D) := by
    intro k hk
    apply intervalIntegrable_integrandSO hg htn hy uh sg (by positivity) _ (hle1 _)
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast g.so_cp_mono D hg (Nat.le_succ k) hk) hDr.le
  have h1 := intervalIntegral.sum_integral_adjacent_intervals
    (f := integrandSO D g d uh sg t y) (μ := volume) (a := fun k => (cp D g t k : ℝ) / D) (n := K)
    fun k hk => hcell k (by omega)
  have hsum : ∀ K' : ℕ, ∑ i ∈ Finset.Icc 1 K', (∫ x in (cp D g t (i - 1) : ℝ) / D..
      (cp D g t i : ℝ) / D, integrandSO D g d uh sg t y x) =
      ∑ k ∈ Finset.range K', ∫ x in (cp D g t k : ℝ) / D..(cp D g t (k + 1) : ℝ) / D,
        integrandSO D g d uh sg t y x := by
    intro K'
    induction K' with
    | zero => simp
    | succ K' ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ, Nat.add_sub_cancel]
  rw [hsum K, h1]
  simp only [g.so_cp_zero D t, Nat.cast_zero, zero_div]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_integrandSO hg htn hy uh sg le_rfl (by positivity) (hle1 K))
    (intervalIntegrable_integrandSO hg htn hy uh sg (by positivity) (hle1 K) le_rfl)).symm

/-- The credits of the record `l`, regrouped by cells:
`(acc_l / D ^ 2 + lam_l / D) delta_l` is the sum over the cells of their credits. -/
theorem credit_split (N : (Fin (d + 1) → ℕ) → ℕ) (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ)
    (δ : Fin (d + 1) → ℝ) (l : Fin (d + 1)) :
    (if 0 < (c l).w then
      ((acc D g d N Sg t c l : ℝ) / (D : ℝ) ^ 2 + (lam D g d N Sg t c l : ℝ) / D) * δ l else 0) =
    ∑ i ∈ Finset.Icc 1 (im d c), (if 0 < (c l).w then
      ((coefC D g d Sg t c i l : ℝ) * QC D g d N Sg t c i / (D : ℝ) ^ 2 +
        (lamC D g d N Sg t c i l : ℝ) / D) * δ l else 0) +
    (if (c (Fin.last d)).forg then 0 else
      ∑ i ∈ Finset.Ioc (im d c) (jT D g d N Sg t c), (if 0 < (c l).w then
        (Sg (fun l => (c l).map) l : ℝ) * QT D g d N Sg t c i / (D : ℝ) ^ 2 * δ l else 0) +
      (if 0 < (c l).w then (Sg (fun l => (c l).map) l : ℝ) *
        ((if cp D g t (jT D g d N Sg t c) < D then ((D - cp D g t (jT D g d N Sg t c) : ℕ) : ℤ)
          else 0 : ℤ) : ℝ) / (D : ℝ) ^ 2 * δ l else 0)) := by
  by_cases hw : 0 < (c l).w
  · simp only [hw, ite_true]
    have e1 : ∑ i ∈ Finset.Icc 1 (im d c),
        ((coefC D g d Sg t c i l : ℝ) * QC D g d N Sg t c i / (D : ℝ) ^ 2 +
          (lamC D g d N Sg t c i l : ℝ) / D) * δ l =
        (∑ i ∈ Finset.Icc 1 (im d c), (coefC D g d Sg t c i l : ℝ) * QC D g d N Sg t c i) /
          (D : ℝ) ^ 2 * δ l +
        (∑ i ∈ Finset.Icc 1 (im d c), (lamC D g d N Sg t c i l : ℝ)) / D * δ l := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
      ring
    have e2 : ∑ i ∈ Finset.Ioc (im d c) (jT D g d N Sg t c),
        (Sg (fun l => (c l).map) l : ℝ) * QT D g d N Sg t c i / (D : ℝ) ^ 2 * δ l =
        (Sg (fun l => (c l).map) l : ℝ) *
          (∑ i ∈ Finset.Ioc (im d c) (jT D g d N Sg t c), (QT D g d N Sg t c i : ℝ)) /
          (D : ℝ) ^ 2 * δ l := by
      rw [← Finset.sum_mul, ← Finset.sum_div, ← Finset.mul_sum]
    rw [e1, e2]
    unfold acc lam
    push_cast
    by_cases htf : (c (Fin.last d)).forg = true
    · simp only [htf, ite_true]
      ring
    · simp only [htf, Bool.false_eq_true, ite_false]
      by_cases hcp : cp D g t (jT D g d N Sg t c) < D
      · simp only [hcp, ite_true]
        ring
      · simp only [hcp, ite_false]
        push_cast
        ring
  · simp only [hw, ite_false, Finset.sum_const_zero, add_zero]
    split_ifs <;> simp

/-- 8.6: the bound of one record list. For a record list `c` that the memory `y` fits,
`T0 / D + sum over the credited l of (mu_l / D) delta_l` is at most the integral of the integrand of
(R_t). -/
theorem bound_le_integral (hg : ok D g = true) (ht1 : 1 ≤ t) (htn : t < g.n) (hy : IsMemory y)
    (hc : RecOK D g t c) (hfit : Fits D g t c y) (uh : ℕ → (Fin (d + 1) → ℕ) → ℕ)
    (sg : ℕ → (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) :
    ((bound D g d (uh (t + 1)) (sg (t + 1)) t c).1 : ℝ) / D +
      ∑ l, (if 0 < (c l).w then
        ((bound D g d (uh (t + 1)) (sg (t + 1)) t c).2 l : ℝ) / D * (((c l).val : ℝ) / D - y l)
        else 0) ≤
      ∫ x in Set.Icc (0 : ℝ) 1, integrandSO D g d uh sg t y x := by
  have hD : 0 < D := g.so_D_pos D hg
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  set N := uh (t + 1) with hN
  set Sg := sg (t + 1) with hSg
  set δ : Fin (d + 1) → ℝ := fun l => ((c l).val : ℝ) / D - y l with hδ
  have hδ0 : ∀ l, 0 ≤ δ l := fun l => fit_delta_nonneg hD hc hfit l
  have himL : im d c ≤ g.L t := hc.pos_le (Fin.last d)
  have him1 : 1 ≤ im d c := hc.pos_pos (Fin.last d)
  have hjL : jT D g d N Sg t c ≤ g.L t := jT_le_L N Sg t c
  have hij : im d c ≤ jT D g d N Sg t c := im_le_jT N Sg t c himL
  -- step 1: the floors of 5.5
  have hT0 : ((bound D g d N Sg t c).1 : ℝ) / D ≤
      (Rtot D g d N Sg t c : ℝ) / (2 * (D : ℝ) ^ 3) := by
    have h := intCast_ediv_le (a := Rtot D g d N Sg t c) (b := ((2 * D * D : ℕ) : ℤ))
      (by positivity)
    simp only [bound]
    push_cast at h ⊢
    calc _ ≤ (Rtot D g d N Sg t c : ℝ) / (2 * D * D) / D := div_le_div_of_nonneg_right h hDr.le
      _ = _ := by field_simp
  have hmu : ∀ l, (if 0 < (c l).w then
      ((bound D g d N Sg t c).2 l : ℝ) / D * δ l else 0) ≤
      (if 0 < (c l).w then
        ((acc D g d N Sg t c l : ℝ) / (D : ℝ) ^ 2 + (lam D g d N Sg t c l : ℝ) / D) * δ l
        else 0) := by
    intro l
    split_ifs
    · apply mul_le_mul_of_nonneg_right _ (hδ0 l)
      simp only [bound]
      split_ifs
      · simp only [Int.cast_zero, zero_div]
        have h1 : (0 : ℝ) ≤ acc D g d N Sg t c l := by exact_mod_cast acc_nonneg hg hc N Sg l
        have h2 : (0 : ℝ) ≤ lam D g d N Sg t c l := by exact_mod_cast lam_nonneg N Sg l
        positivity
      · have h := intCast_ediv_le (a := acc D g d N Sg t c l) (b := (D : ℤ)) (by exact_mod_cast hD)
        push_cast at h ⊢
        rw [add_div]
        have : ((acc D g d N Sg t c l / D : ℤ) : ℝ) / D ≤
            (acc D g d N Sg t c l : ℝ) / (D : ℝ) ^ 2 := by
          calc _ ≤ (acc D g d N Sg t c l : ℝ) / D / D := div_le_div_of_nonneg_right h hDr.le
            _ = _ := by field_simp
        linarith
    · exact le_rfl
  -- step 2: regroup by cells
  have hR : (Rtot D g d N Sg t c : ℝ) / (2 * (D : ℝ) ^ 3) =
      ∑ i ∈ Finset.Icc 1 (im d c), (RC D g d N Sg t c i : ℝ) / (2 * (D : ℝ) ^ 3) +
      (if (c (Fin.last d)).forg then 0 else
        ∑ i ∈ Finset.Ioc (im d c) (jT D g d N Sg t c), (RT D g d N Sg t c i : ℝ) / (2 * (D : ℝ) ^ 3) +
        (RE D g d N Sg t c : ℝ) / (2 * (D : ℝ) ^ 3)) := by
    unfold Rtot
    push_cast
    rw [add_div, Finset.sum_div]
    split_ifs
    · simp
    · rw [add_div, Finset.sum_div]
  have hsum := Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) =>
    credit_split (D := D) (g := g) (t := t) (c := c) N Sg δ l
  rw [Finset.sum_add_distrib, Finset.sum_comm] at hsum
  -- step 3: the integral over the cells
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have hhead : ∀ i ∈ Finset.Icc 1 (im d c),
      (RC D g d N Sg t c i : ℝ) / (2 * (D : ℝ) ^ 3) +
        ∑ l, (if 0 < (c l).w then
          ((coefC D g d Sg t c i l : ℝ) * QC D g d N Sg t c i / (D : ℝ) ^ 2 +
            (lamC D g d N Sg t c i l : ℝ) / D) * δ l else 0) ≤
      ∫ x in (cp D g t (i - 1) : ℝ) / D..(cp D g t i : ℝ) / D, integrandSO D g d uh sg t y x := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    exact head_cell hg ht1 htn hy hc hfit uh sg hi.1 hi.2
  by_cases htf : (c (Fin.last d)).forg = true
  · -- the last record forgotten: the cells 1, ..., im = L cover [0, 1]
    have hiL : im d c = g.L t := (hc.forg_iff (Fin.last d)).mp htf
    rw [integral_split hg htn hy uh sg himL, hiL, g.so_cp_L D t, div_self hDr.ne',
      intervalIntegral.integral_same, add_zero, ← hiL]
    have hsum' : ∑ l, (if 0 < (c l).w then
        ((acc D g d N Sg t c l : ℝ) / (D : ℝ) ^ 2 + (lam D g d N Sg t c l : ℝ) / D) * δ l
        else 0) = ∑ i ∈ Finset.Icc 1 (im d c), ∑ l, (if 0 < (c l).w then
          ((coefC D g d Sg t c i l : ℝ) * QC D g d N Sg t c i / (D : ℝ) ^ 2 +
            (lamC D g d N Sg t c i l : ℝ) / D) * δ l else 0) := by
      rw [hsum]
      simp [htf]
    have hR' := hR
    rw [ite_eq_left htf, add_zero] at hR'
    have h3 := Finset.sum_le_sum hhead
    rw [Finset.sum_add_distrib] at h3
    calc _ ≤ (Rtot D g d N Sg t c : ℝ) / (2 * (D : ℝ) ^ 3) + ∑ l, (if 0 < (c l).w then
          ((acc D g d N Sg t c l : ℝ) / (D : ℝ) ^ 2 + (lam D g d N Sg t c l : ℝ) / D) * δ l
          else 0) := add_le_add hT0 (Finset.sum_le_sum fun l _ => hmu l)
      _ = _ := by rw [hR', hsum']
      _ ≤ _ := h3
  · -- the last record not forgotten
    have htf' : (c (Fin.last d)).forg = false := by simpa using htf
    rw [integral_split hg htn hy uh sg hjL]
    have hU : Finset.Icc 1 (jT D g d N Sg t c) =
        Finset.Icc 1 (im d c) ∪ Finset.Ioc (im d c) (jT D g d N Sg t c) := by
      ext i
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    have hdisj : Disjoint (Finset.Icc 1 (im d c)) (Finset.Ioc (im d c) (jT D g d N Sg t c)) := by
      rw [Finset.disjoint_left]
      intro i hi hi'
      rw [Finset.mem_Icc] at hi
      rw [Finset.mem_Ioc] at hi'
      omega
    rw [hU, Finset.sum_union hdisj]
    have htail : ∀ i ∈ Finset.Ioc (im d c) (jT D g d N Sg t c),
        (RT D g d N Sg t c i : ℝ) / (2 * (D : ℝ) ^ 3) +
          ∑ l, (if 0 < (c l).w then
            (Sg (fun l => (c l).map) l : ℝ) * QT D g d N Sg t c i / (D : ℝ) ^ 2 * δ l else 0) ≤
        ∫ x in (cp D g t (i - 1) : ℝ) / D..(cp D g t i : ℝ) / D,
          integrandSO D g d uh sg t y x := by
      intro i hi
      rw [Finset.mem_Ioc] at hi
      exact tail_cell hg ht1 htn hy hc hfit htf' uh sg hi.1 (hi.2.trans hjL)
    have hfin : (RE D g d N Sg t c : ℝ) / (2 * (D : ℝ) ^ 3) +
        ∑ l, (if 0 < (c l).w then (Sg (fun l => (c l).map) l : ℝ) *
          ((if cp D g t (jT D g d N Sg t c) < D then
            ((D - cp D g t (jT D g d N Sg t c) : ℕ) : ℤ) else 0 : ℤ) : ℝ) / (D : ℝ) ^ 2 * δ l
          else 0) ≤
        ∫ x in (cp D g t (jT D g d N Sg t c) : ℝ) / D..1, integrandSO D g d uh sg t y x := by
      by_cases hcp : cp D g t (jT D g d N Sg t c) < D
      · simp only [hcp, ite_true, Int.cast_natCast]
        exact final_seg hg ht1 htn hy hc hfit htf' uh sg hcp
      · have hcpD : cp D g t (jT D g d N Sg t c) = D :=
          le_antisymm (g.so_cp_le_D D hg t _) (not_lt.mp hcp)
        have hRE : RE D g d N Sg t c = 0 := by
          unfold RE
          dsimp only
          rw [ite_eq_right hcp]
        simp only [hcp, ite_false, hRE, Int.cast_zero, zero_div, mul_zero, zero_mul, ite_self,
          Finset.sum_const_zero, add_zero, hcpD, div_self hDr.ne', intervalIntegral.integral_same,
          le_refl, lt_irrefl, Nat.sub_self]
    have hsum' : ∑ l, (if 0 < (c l).w then
        ((acc D g d N Sg t c l : ℝ) / (D : ℝ) ^ 2 + (lam D g d N Sg t c l : ℝ) / D) * δ l
        else 0) = ∑ i ∈ Finset.Icc 1 (im d c), ∑ l, (if 0 < (c l).w then
          ((coefC D g d Sg t c i l : ℝ) * QC D g d N Sg t c i / (D : ℝ) ^ 2 +
            (lamC D g d N Sg t c i l : ℝ) / D) * δ l else 0) +
        (∑ i ∈ Finset.Ioc (im d c) (jT D g d N Sg t c), ∑ l, (if 0 < (c l).w then
            (Sg (fun l => (c l).map) l : ℝ) * QT D g d N Sg t c i / (D : ℝ) ^ 2 * δ l else 0) +
          ∑ l, (if 0 < (c l).w then (Sg (fun l => (c l).map) l : ℝ) *
            ((if cp D g t (jT D g d N Sg t c) < D then
              ((D - cp D g t (jT D g d N Sg t c) : ℕ) : ℤ) else 0 : ℤ) : ℝ) / (D : ℝ) ^ 2 * δ l
            else 0)) := by
      rw [hsum]
      simp only [htf', Bool.false_eq_true, ite_false]
      rw [Finset.sum_add_distrib, Finset.sum_comm (s := Finset.univ)]
    have hR' := hR
    rw [ite_eq_right (by simp [htf'] : ¬ (c (Fin.last d)).forg = true)] at hR'
    have h3 := Finset.sum_le_sum hhead
    have h4 := Finset.sum_le_sum htail
    rw [Finset.sum_add_distrib] at h3 h4
    calc _ ≤ (Rtot D g d N Sg t c : ℝ) / (2 * (D : ℝ) ^ 3) + ∑ l, (if 0 < (c l).w then
          ((acc D g d N Sg t c l : ℝ) / (D : ℝ) ^ 2 + (lam D g d N Sg t c l : ℝ) / D) * δ l
          else 0) := add_le_add hT0 (Finset.sum_le_sum fun l _ => hmu l)
      _ = _ := by rw [hR', hsum']
      _ ≤ _ := by linarith

end Cells

end Robbins.Cert.SO
