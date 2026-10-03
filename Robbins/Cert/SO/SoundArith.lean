import Robbins.Cert.SO.Spec

/-!
# Arithmetic and integral lemmas of the second-order soundness

Section 8 of the specification (Robbins/Cert/SO/Spec.lean): the scalar lemma 8.4, the integral lemmas 8.5 (a) to (e), the
bounds of the penalty `Epen D` (Lemma B.1 of the paper), the tangent bound of
`(1 - x) ^ r` (8.2 (b), 8.3), the monotonicity used for `jT` (8.3), and the rounding of `/` on `ℤ`.
-/

namespace Robbins.Cert.SO

open MeasureTheory intervalIntegral

/-! ## 8.4 The scalar lemma -/

/-- 8.4: `min (A + N) C ≥ min (A, B) + s min (1, (A - B)^+ / S) + min (N, (B - A)^+)` for
`N ≥ 0`, `0 ≤ s ≤ S`, `S > 0`, `C ≥ B + s`. -/
theorem scalar_min {A B C N S s : ℝ} (hN : 0 ≤ N) (hS : 0 < S) (hs0 : 0 ≤ s) (hsS : s ≤ S)
    (hC : B + s ≤ C) :
    min A B + s * min 1 (max 0 (A - B) / S) + min N (max 0 (B - A)) ≤ min (A + N) C := by
  by_cases hle : B ≤ A
  · -- Case B ≤ A
    have hsub : 0 ≤ A - B := sub_nonneg.mpr hle
    have hminAB : min A B = B := min_eq_right hle
    have hmax1 : max 0 (B - A) = 0 := max_eq_left (sub_nonpos.mpr hle)
    have hmax1' : max 0 (A - B) = A - B := max_eq_right hsub
    have hminN : min N 0 = 0 := min_eq_right hN
    have hL : min A B + s * min 1 (max 0 (A - B) / S) + min N (max 0 (B - A)) = B + s * min 1 ((A - B) / S) := by
      simp [hminAB, hmax1, hmax1', hminN]
    rw [hL]
    have hleC : B + s * min 1 ((A - B) / S) ≤ C := by
      have hmin1_le_one : min 1 ((A - B) / S) ≤ 1 := min_le_left _ _
      have h_mul_s_le_s : s * min 1 ((A - B) / S) ≤ s := by
        nlinarith
      nlinarith
    have hleAN : B + s * min 1 ((A - B) / S) ≤ A + N := by
      have hmin1_le_div : min 1 ((A - B) / S) ≤ (A - B) / S := min_le_right _ _
      have h_mul_div_le_sub : s * ((A - B) / S) ≤ A - B := by
        have h1 : s * ((A - B) / S) ≤ S * ((A - B) / S) := by
          have hdiv_nonneg : 0 ≤ (A - B) / S := div_nonneg hsub hS.le
          nlinarith
        have h2 : S * ((A - B) / S) = A - B := by
          field_simp [hS.ne.symm]
        nlinarith
      have h_mul_min_le_sub : s * min 1 ((A - B) / S) ≤ A - B := by
        nlinarith
      nlinarith
    exact le_min hleAN hleC
  · -- Case A < B
    have hlt : A < B := lt_of_not_ge hle
    have hsub : A - B ≤ 0 := sub_nonpos.mpr (le_of_lt hlt)
    have hminAB : min A B = A := min_eq_left (le_of_lt hlt)
    have hmax1 : max 0 (A - B) = 0 := max_eq_left hsub
    have hdiv0 : (0 : ℝ) / S = 0 := zero_div S
    have hmin1 : min 1 (0 : ℝ) = 0 := by
      exact min_eq_right (by norm_num : (0 : ℝ) ≤ 1)
    have hmax2 : max 0 (B - A) = B - A := max_eq_right (sub_nonneg.mpr (le_of_lt hlt))
    have hL : min A B + s * min 1 (max 0 (A - B) / S) + min N (max 0 (B - A)) = A + min N (B - A) := by
      simp [hminAB, hmax1, hdiv0, hmax2]
    rw [hL]
    have hleAN : A + min N (B - A) ≤ A + N := by
      have hminN_le_N : min N (B - A) ≤ N := min_le_left _ _
      nlinarith
    have hleC : A + min N (B - A) ≤ C := by
      have hminN_le_sub : min N (B - A) ≤ B - A := min_le_right _ _
      have hB_le_C : B ≤ C := by
        nlinarith
      nlinarith
    exact le_min hleAN hleC

/-- 8.4 without the slope term (`S = 0`). -/
theorem scalar_min0 {A B C N : ℝ} (hN : 0 ≤ N) (hC : B ≤ C) :
    min A B + min N (max 0 (B - A)) ≤ min (A + N) C := by
  by_cases hAB : A ≤ B
  · -- case A ≤ B
    have hsub : 0 ≤ B - A := sub_nonneg.mpr hAB
    have hmax : max 0 (B - A) = B - A := max_eq_right hsub
    have hminAB : min A B = A := min_eq_left hAB
    rw [hminAB, hmax]
    -- Goal: A + min N (B - A) ≤ min (A + N) C
    calc
      A + min N (B - A) = min N (B - A) + A := by ring
      _ = min (N + A) ((B - A) + A) := by rw [min_add_add_right]
      _ = min (A + N) B := by ring
      _ ≤ min (A + N) C := min_le_min (le_refl _) hC
  · -- case B < A
    have hBA : B ≤ A := le_of_not_ge hAB
    have hsub : B - A ≤ 0 := sub_nonpos.mpr hBA
    have hmax : max 0 (B - A) = 0 := max_eq_left hsub
    have hminAB : min A B = B := min_eq_right hBA
    have hminN : min N 0 = 0 := min_eq_right hN
    rw [hminAB, hmax, hminN, add_zero]
    -- Goal: B ≤ min (A + N) C
    exact le_min (by linarith) hC

/-! ## 8.5 The integral lemmas -/

/-- The integral of an affine function. -/
theorem integral_affine (a b x0 x1 : ℝ) :
    ∫ X in x0..x1, (a + b * X) = a * (x1 - x0) + b * (x1 ^ 2 - x0 ^ 2) / 2 := by
  have hi : IntervalIntegrable (fun X : ℝ => b * X) MeasureTheory.volume x0 x1 :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_add intervalIntegrable_const hi,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id, smul_eq_mul]
  ring

/-- Where `f ≤ g` on `[x0, x1]`, the integral of `min f g` is that of `f`. -/
theorem integral_min_eq_left {f g : ℝ → ℝ} {x0 x1 : ℝ} (hx : x0 ≤ x1)
    (h : ∀ X ∈ Set.Icc x0 x1, f X ≤ g X) :
    ∫ X in x0..x1, min (f X) (g X) = ∫ X in x0..x1, f X := by
  apply intervalIntegral.integral_congr
  intro X hX
  rw [Set.uIcc_of_le hx] at hX
  exact min_eq_left (h X hX)

/-- Where `g ≤ f` on `[x0, x1]`, the integral of `min f g` is that of `g`. -/
theorem integral_min_eq_right {f g : ℝ → ℝ} {x0 x1 : ℝ} (hx : x0 ≤ x1)
    (h : ∀ X ∈ Set.Icc x0 x1, g X ≤ f X) :
    ∫ X in x0..x1, min (f X) (g X) = ∫ X in x0..x1, g X := by
  apply intervalIntegral.integral_congr
  intro X hX
  rw [Set.uIcc_of_le hx] at hX
  exact min_eq_right (h X hX)

/-- Where `g - c ≤ f` on `[x0, x1]`, the integral of `min f g` is at least that of `g`, minus
`c (x1 - x0)`. -/
theorem integral_sub_le_min {f g : ℝ → ℝ} {x0 x1 c : ℝ} (hx : x0 ≤ x1) (hf : Continuous f)
    (hg : Continuous g) (hc : 0 ≤ c) (h : ∀ X ∈ Set.Icc x0 x1, g X - c ≤ f X) :
    (∫ X in x0..x1, g X) - c * (x1 - x0) ≤ ∫ X in x0..x1, min (f X) (g X) := by
  have h1 : (∫ X in x0..x1, g X) - c * (x1 - x0) = ∫ X in x0..x1, (g X - c) := by
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [h1]
  have hi1 : IntervalIntegrable (fun X => g X - c) MeasureTheory.volume x0 x1 :=
    (hg.sub continuous_const).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun X => min (f X) (g X)) MeasureTheory.volume x0 x1 :=
    (hf.min hg).intervalIntegrable _ _
  apply intervalIntegral.integral_mono_on hx hi1 hi2
  intro X hX
  exact le_min (h X hX) (by linarith)

/-- Where `v ≤ 0` on `[x0, x1]`, the integral of `max 0 v` is `0`. -/
theorem integral_max_zero_of_nonpos {v : ℝ → ℝ} {x0 x1 : ℝ} (hx : x0 ≤ x1)
    (h : ∀ X ∈ Set.Icc x0 x1, v X ≤ 0) : ∫ X in x0..x1, max 0 (v X) = 0 := by
  have he : ∫ X in x0..x1, max 0 (v X) = ∫ X in x0..x1, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro X hX
    rw [Set.uIcc_of_le hx] at hX
    exact max_eq_left (h X hX)
  rw [he]
  simp

/-- Where `0 ≤ v` on `[x0, x1]`, the integral of `max 0 v` is that of `v`. -/
theorem integral_max_zero_of_nonneg {v : ℝ → ℝ} {x0 x1 : ℝ} (hx : x0 ≤ x1)
    (h : ∀ X ∈ Set.Icc x0 x1, 0 ≤ v X) : ∫ X in x0..x1, max 0 (v X) = ∫ X in x0..x1, v X := by
  apply intervalIntegral.integral_congr
  intro X hX
  rw [Set.uIcc_of_le hx] at hX
  exact max_eq_right (h X hX)

/-- Where `- c ≤ v` on `[x0, x1]`, `c ≥ 0`, the integral of `max 0 v` is at most that of `v` plus
`c (x1 - x0)`. -/
theorem integral_max_zero_le_add {v : ℝ → ℝ} {x0 x1 c : ℝ} (hx : x0 ≤ x1) (hv : Continuous v)
    (hc : 0 ≤ c) (h : ∀ X ∈ Set.Icc x0 x1, -c ≤ v X) :
    ∫ X in x0..x1, max 0 (v X) ≤ (∫ X in x0..x1, v X) + c * (x1 - x0) := by
  have h1 : (∫ X in x0..x1, v X) + c * (x1 - x0) = ∫ X in x0..x1, (v X + c) := by
    rw [intervalIntegral.integral_add (hv.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [h1]
  have hi1 : IntervalIntegrable (fun X => max 0 (v X)) MeasureTheory.volume x0 x1 :=
    (continuous_const.max hv).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun X => v X + c) MeasureTheory.volume x0 x1 :=
    (hv.add continuous_const).intervalIntegrable _ _
  apply intervalIntegral.integral_mono_on hx hi1 hi2
  intro X hX
  exact max_le (by linarith [h X hX]) (by linarith)

/-- The floor `Z = floor (-da / k)` for `k > 0`: `k Z ≤ -da < k (Z + 1)`. -/
theorem mul_ediv_le_lt {da k : ℤ} (hk : 0 < k) :
    k * ((-da) / k) ≤ -da ∧ -da < k * ((-da) / k + 1) := by
  refine ⟨Int.mul_ediv_self_le hk.ne', ?_⟩
  have := Int.lt_mul_ediv_self_add (x := -da) hk
  linarith [mul_add k ((-da) / k) 1]

/-- 8.5 (a): `cell2` is a lower bound of `2 int over [Pa, Pb] of min (a0 + a1 X, b0 - b1 X)`. -/
theorem cell2_le {Pa Pb a0 a1 b0 b1 : ℤ} (hab : Pa < Pb) (ha1 : 0 < a1) (hb1 : 0 ≤ b1) :
    (cell2 Pa Pb a0 a1 b0 b1 : ℝ) ≤
      2 * ∫ X in (Pa : ℝ)..Pb, min ((a0 : ℝ) + a1 * X) ((b0 : ℝ) - b1 * X) := by
  have hk : 0 < a1 + b1 := by omega
  have hkr : (0 : ℝ) < (a1 : ℝ) + b1 := by exact_mod_cast hk
  have hIA : ∀ x0 x1 : ℝ, 2 * ∫ X in x0..x1, ((a0 : ℝ) + a1 * X) =
      2 * a0 * (x1 - x0) + a1 * (x1 ^ 2 - x0 ^ 2) := by
    intro x0 x1
    rw [integral_affine]
    ring
  have hIB : ∀ x0 x1 : ℝ, 2 * ∫ X in x0..x1, ((b0 : ℝ) - b1 * X) =
      2 * b0 * (x1 - x0) - b1 * (x1 ^ 2 - x0 ^ 2) := by
    intro x0 x1
    have he : (fun X : ℝ => (b0 : ℝ) - b1 * X) = fun X => (b0 : ℝ) + (-(b1 : ℝ)) * X := by
      funext X
      ring
    rw [he, integral_affine]
    ring
  have hPab : (Pa : ℝ) ≤ Pb := by exact_mod_cast hab.le
  have hcont : Continuous fun X : ℝ => min ((a0 : ℝ) + a1 * X) ((b0 : ℝ) - b1 * X) := by
    fun_prop
  unfold cell2
  dsimp only
  split_ifs with h1 h2
  · have h1' : ((a0 : ℝ) - b0 + (a1 + b1) * Pa + (a1 + b1) * (Pb - Pa)) ≤ 0 := by
      exact_mod_cast h1
    rw [integral_min_eq_left hPab, hIA]
    · push_cast
      apply le_of_eq
      ring
    · intro X hX
      have := mul_le_mul_of_nonneg_left hX.2 hkr.le
      nlinarith
  · have h2' : (0 : ℝ) ≤ (a0 : ℝ) - b0 + (a1 + b1) * Pa := by exact_mod_cast h2
    rw [integral_min_eq_right hPab, hIB]
    · push_cast
      apply le_of_eq
      ring
    · intro X hX
      have := mul_le_mul_of_nonneg_left hX.1 hkr.le
      nlinarith
  · obtain ⟨hZ1, hZ2⟩ := mul_ediv_le_lt (da := a0 - b0 + (a1 + b1) * Pa) hk
    set q := (-(a0 - b0 + (a1 + b1) * Pa)) / (a1 + b1) with hq
    have hq0 : 0 ≤ q := Int.ediv_nonneg (by omega) hk.le
    have hqlt : q + 1 ≤ Pb - Pa := by
      by_contra hcon
      have : (a1 + b1) * (Pb - Pa) ≤ (a1 + b1) * q :=
        mul_le_mul_of_nonneg_left (by omega) hk.le
      omega
    have hZ1r : ((a1 : ℝ) + b1) * q ≤ -((a0 : ℝ) - b0 + (a1 + b1) * Pa) := by exact_mod_cast hZ1
    have hZ2r : -((a0 : ℝ) - b0 + (a1 + b1) * Pa) < ((a1 : ℝ) + b1) * (q + 1) := by
      exact_mod_cast hZ2
    have hq0r : (0 : ℝ) ≤ q := by exact_mod_cast hq0
    have hqltr : (q : ℝ) + 1 ≤ Pb - Pa := by exact_mod_cast hqlt
    set z : ℝ := (Pa : ℝ) + q with hz
    have hi : ∀ u v : ℝ, IntervalIntegrable
        (fun X : ℝ => min ((a0 : ℝ) + a1 * X) ((b0 : ℝ) - b1 * X)) MeasureTheory.volume u v :=
      fun u v => hcont.intervalIntegrable u v
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi _ z) (hi z _),
      ← intervalIntegral.integral_add_adjacent_intervals (hi z (z + 1)) (hi (z + 1) _)]
    have e1 : ∫ X in (Pa : ℝ)..z, min ((a0 : ℝ) + a1 * X) ((b0 : ℝ) - b1 * X) =
        ∫ X in (Pa : ℝ)..z, ((a0 : ℝ) + a1 * X) := by
      apply integral_min_eq_left (by linarith)
      intro X hX
      have := mul_le_mul_of_nonneg_left hX.2 hkr.le
      nlinarith
    have e3 : ∫ X in (z + 1)..(Pb : ℝ), min ((a0 : ℝ) + a1 * X) ((b0 : ℝ) - b1 * X) =
        ∫ X in (z + 1)..(Pb : ℝ), ((b0 : ℝ) - b1 * X) := by
      apply integral_min_eq_right (by linarith)
      intro X hX
      have := mul_le_mul_of_nonneg_left hX.1 hkr.le
      nlinarith
    have e2 := integral_sub_le_min (f := fun X : ℝ => (a0 : ℝ) + a1 * X)
      (g := fun X : ℝ => (b0 : ℝ) - b1 * X) (x0 := z) (x1 := z + 1) (c := (a1 : ℝ) + b1)
      (by linarith) (by fun_prop) (by fun_prop) hkr.le (by
        intro X hX
        have := mul_le_mul_of_nonneg_left hX.1 hkr.le
        nlinarith)
    have hA1 := hIA (Pa : ℝ) z
    have hB2 := hIB z (z + 1)
    have hB3 := hIB (z + 1) (Pb : ℝ)
    beta_reduce at e2
    rw [e1, e3]
    push_cast
    rw [← hz]
    have hpoly : 2 * (a0 : ℝ) * (z - Pa) + a1 * (z * z - Pa * Pa) +
        (2 * b0 * (Pb - z) - b1 * (Pb * Pb - z * z)) - 2 * (a1 + b1) =
        (2 * a0 * (z - Pa) + a1 * (z ^ 2 - Pa ^ 2)) +
        (2 * b0 * (z + 1 - z) - b1 * ((z + 1) ^ 2 - z ^ 2)) - 2 * ((a1 + b1) * (z + 1 - z)) +
        (2 * b0 * (Pb - (z + 1)) - b1 * (Pb ^ 2 - (z + 1) ^ 2)) := by ring
    rw [hpoly]
    linarith

/-- Twice the integral of the ramp `da + k (X - Pa) - c` over `[x0, x1]` (the trapezoid rule). -/
theorem integral_ramp {da k c Pa : ℤ} (x0 x1 : ℝ) :
    2 * ∫ X in x0..x1, ((da : ℝ) + k * (X - Pa) - c) =
      (x1 - x0) * (((da : ℝ) + k * (x0 - Pa) - c) + ((da : ℝ) + k * (x1 - Pa) - c)) := by
  have he : (fun X : ℝ => (da : ℝ) + k * (X - Pa) - c) =
      fun X => ((da : ℝ) - c - k * Pa) + (k : ℝ) * X := by
    funext X
    ring
  rw [he, integral_affine]
  ring

/-- 8.5 (b), lower bound: the first component of `pos2` is at most
`2 int over [Pa, Pb] of max (0, da + k (X - Pa) - c)`. -/
theorem pos2_fst_le {Pa Pb da k c : ℤ} (hab : Pa < Pb) (hk : 0 < k) :
    ((pos2 Pa Pb da k c).1 : ℝ) ≤
      2 * ∫ X in (Pa : ℝ)..Pb, max 0 ((da : ℝ) + k * (X - Pa) - c) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hPab : (Pa : ℝ) ≤ Pb := by exact_mod_cast hab.le
  have hV := integral_ramp (da := da) (k := k) (c := c) (Pa := Pa)
  have hcont : Continuous fun X : ℝ => (da : ℝ) + k * (X - Pa) - c := by fun_prop
  have hi : ∀ u v : ℝ, IntervalIntegrable
      (fun X : ℝ => max 0 ((da : ℝ) + k * (X - Pa) - c)) MeasureTheory.volume u v :=
    fun u v => (continuous_const.max hcont).intervalIntegrable u v
  unfold pos2
  dsimp only
  split_ifs with h1 h2
  · have := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) hPab
      (fun X (_ : X ∈ Set.Icc (Pa : ℝ) Pb) => le_max_left 0 ((da : ℝ) + k * (X - Pa) - c))
    push_cast
    linarith
  · have h2' : (0 : ℝ) ≤ (da : ℝ) - c := by exact_mod_cast h2
    rw [integral_max_zero_of_nonneg hPab, hV]
    · push_cast
      apply le_of_eq
      ring
    · intro X hX
      have := mul_le_mul_of_nonneg_left (sub_nonneg.mpr hX.1) hkr.le
      linarith
  · push Not at h1 h2
    obtain ⟨hZ1, hZ2⟩ := mul_ediv_le_lt (da := da - c) hk
    set q := (-(da - c)) / k with hq
    have hqlt : q + 1 ≤ Pb - Pa := by
      by_contra hcon
      have : k * (Pb - Pa) ≤ k * q := mul_le_mul_of_nonneg_left (by omega) hk.le
      omega
    have hq0 : 0 ≤ q := Int.ediv_nonneg (by omega) hk.le
    have hZ2r : -((da : ℝ) - c) < k * (q + 1) := by exact_mod_cast hZ2
    have hq0r : (0 : ℝ) ≤ q := by exact_mod_cast hq0
    have hqltr : (q : ℝ) + 1 ≤ Pb - Pa := by exact_mod_cast hqlt
    set z : ℝ := (Pa : ℝ) + q with hz
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi _ (z + 1)) (hi (z + 1) _),
      integral_max_zero_of_nonneg (x0 := z + 1) (by linarith)]
    · have h0 := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume)
        (a := (Pa : ℝ)) (b := z + 1) (by linarith)
        (fun X (_ : X ∈ Set.Icc (Pa : ℝ) (z + 1)) => le_max_left 0 ((da : ℝ) + k * (X - Pa) - c))
      have hV2 := hV (z + 1) Pb
      push_cast
      rw [← hz]
      nlinarith
    · intro X hX
      have := mul_le_mul_of_nonneg_left hX.1 hkr.le
      nlinarith

/-- 8.5 (b), upper bound: `2 int over [Pa, Pb] of max (0, da + k (X - Pa) - c)` is at most the
second component of `pos2`. -/
theorem le_pos2_snd {Pa Pb da k c : ℤ} (hab : Pa < Pb) (hk : 0 < k) :
    2 * ∫ X in (Pa : ℝ)..Pb, max 0 ((da : ℝ) + k * (X - Pa) - c) ≤ ((pos2 Pa Pb da k c).2 : ℝ) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hPab : (Pa : ℝ) ≤ Pb := by exact_mod_cast hab.le
  have hV := integral_ramp (da := da) (k := k) (c := c) (Pa := Pa)
  have hcont : Continuous fun X : ℝ => (da : ℝ) + k * (X - Pa) - c := by fun_prop
  have hi : ∀ u v : ℝ, IntervalIntegrable
      (fun X : ℝ => max 0 ((da : ℝ) + k * (X - Pa) - c)) MeasureTheory.volume u v :=
    fun u v => (continuous_const.max hcont).intervalIntegrable u v
  unfold pos2
  dsimp only
  split_ifs with h1 h2
  · have h1' : (da : ℝ) - c + k * (Pb - Pa) ≤ 0 := by exact_mod_cast h1
    rw [integral_max_zero_of_nonpos hPab]
    · push_cast
      linarith
    · intro X hX
      have := mul_le_mul_of_nonneg_left (sub_le_sub_right hX.2 (Pa : ℝ)) hkr.le
      linarith
  · have h2' : (0 : ℝ) ≤ (da : ℝ) - c := by exact_mod_cast h2
    rw [integral_max_zero_of_nonneg hPab, hV]
    · push_cast
      apply le_of_eq
      ring
    · intro X hX
      have := mul_le_mul_of_nonneg_left (sub_nonneg.mpr hX.1) hkr.le
      linarith
  · push Not at h1 h2
    obtain ⟨hZ1, hZ2⟩ := mul_ediv_le_lt (da := da - c) hk
    set q := (-(da - c)) / k with hq
    have hqlt : q + 1 ≤ Pb - Pa := by
      by_contra hcon
      have : k * (Pb - Pa) ≤ k * q := mul_le_mul_of_nonneg_left (by omega) hk.le
      omega
    have hq0 : 0 ≤ q := Int.ediv_nonneg (by omega) hk.le
    have hZ1r : (k : ℝ) * q ≤ -((da : ℝ) - c) := by exact_mod_cast hZ1
    have hZ2r : -((da : ℝ) - c) < k * (q + 1) := by exact_mod_cast hZ2
    have hq0r : (0 : ℝ) ≤ q := by exact_mod_cast hq0
    have hqltr : (q : ℝ) + 1 ≤ Pb - Pa := by exact_mod_cast hqlt
    set z : ℝ := (Pa : ℝ) + q with hz
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi _ z) (hi z _),
      ← intervalIntegral.integral_add_adjacent_intervals (hi z (z + 1)) (hi (z + 1) _)]
    have e1 : ∫ X in (Pa : ℝ)..z, max 0 ((da : ℝ) + k * (X - Pa) - c) = 0 := by
      apply integral_max_zero_of_nonpos (by linarith)
      intro X hX
      have := mul_le_mul_of_nonneg_left (sub_le_sub_right hX.2 (Pa : ℝ)) hkr.le
      nlinarith
    have e3 : ∫ X in (z + 1)..(Pb : ℝ), max 0 ((da : ℝ) + k * (X - Pa) - c) =
        ∫ X in (z + 1)..(Pb : ℝ), ((da : ℝ) + k * (X - Pa) - c) := by
      apply integral_max_zero_of_nonneg (by linarith)
      intro X hX
      have := mul_le_mul_of_nonneg_left (sub_le_sub_right hX.1 (Pa : ℝ)) hkr.le
      nlinarith
    have e2 := integral_max_zero_le_add (v := fun X : ℝ => (da : ℝ) + k * (X - Pa) - c)
      (x0 := z) (x1 := z + 1) (c := (k : ℝ)) (by linarith) hcont hkr.le (by
        intro X hX
        have := mul_le_mul_of_nonneg_left (sub_le_sub_right hX.1 (Pa : ℝ)) hkr.le
        nlinarith)
    beta_reduce at e2
    have hV1 := hV z (z + 1)
    have hV2 := hV (z + 1) Pb
    rw [e1, e3]
    push_cast
    rw [← hz]
    nlinarith

/-- `min (1, max (0, v) / S) = (max (0, v) - max (0, v - S)) / S` for `S > 0`. -/
theorem min_one_div_eq {v S : ℝ} (hS : 0 < S) :
    min 1 (max 0 v / S) = (max 0 v - max 0 (v - S)) / S := by
  by_cases hv0 : v ≤ 0
  · -- v ≤ 0
    have hmax1 : max 0 v = 0 := max_eq_left hv0
    have hmax2 : max 0 (v - S) = 0 := by
      have h : v - S ≤ 0 := sub_nonpos.mpr (hv0.trans (by linarith))
      exact max_eq_left h
    have hmin : min 1 (0 / S) = 0 := by
      have h0 : (0 : ℝ) ≤ 1 := by norm_num
      rw [zero_div, min_eq_right h0]
    calc
      min 1 (max 0 v / S) = min 1 (0 / S) := by simp [hmax1]
      _ = 0 := hmin
      _ = (0 - 0) / S := by ring
      _ = (max 0 v - max 0 (v - S)) / S := by simp [hmax1, hmax2]
  · -- 0 < v
    have hv0' : 0 ≤ v := by linarith
    have hmax1 : max 0 v = v := max_eq_right hv0'
    by_cases hvS : v ≤ S
    · -- 0 < v ≤ S
      have hmax2 : max 0 (v - S) = 0 := by
        have h : v - S ≤ 0 := sub_nonpos.mpr hvS
        exact max_eq_left h
      have hdiv : v / S ≤ 1 := (div_le_one hS).mpr hvS
      calc
        min 1 (max 0 v / S) = min 1 (v / S) := by simp [hmax1]
        _ = v / S := min_eq_right hdiv
        _ = (v - 0) / S := by ring
        _ = (max 0 v - max 0 (v - S)) / S := by simp [hmax1, hmax2]
    · -- S < v
      have hmax2 : max 0 (v - S) = v - S := max_eq_right (by linarith)
      have hdiv : 1 ≤ v / S := by
        refine (one_le_div hS).mpr ?_
        exact le_of_lt (lt_of_not_ge hvS)
      calc
        min 1 (max 0 v / S) = min 1 (v / S) := by simp [hmax1]
        _ = 1 := min_eq_left hdiv
        _ = (v - (v - S)) / S := by
          field_simp [ne_of_gt hS]
          ring
        _ = (max 0 v - max 0 (v - S)) / S := by simp [hmax1, hmax2]

/-- 8.5 (c): `chord` is a lower bound of `int over [Pa, Pb] of min (1, max (0, Delta X) / S)`,
`Delta X = a0 - b0 + (a1 + b1) X`. -/
theorem chord_le {Pa Pb a0 a1 b0 b1 S : ℤ} (hab : Pa < Pb) (ha1 : 0 < a1) (hb1 : 0 ≤ b1)
    (hS : 0 < S) :
    (chord Pa Pb a0 a1 b0 b1 S : ℝ) ≤
      ∫ X in (Pa : ℝ)..Pb, min 1 (max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X) / S) := by
  set k := a1 + b1 with hk_def
  set da := a0 - b0 + k * Pa with hda_def
  have hk : 0 < k := by
    omega
  have hkℝ : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h_int : (Pa : ℝ) ≤ (Pb : ℝ) := by exact_mod_cast hab.le
  have hSℝ : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hSℝ_nonneg : (0 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS.le
  dsimp [chord]
  split_ifs with h_db h_S_le_da h_pos
  · -- case db ≤ 0, chord = 0
    have h_nonneg : ∀ X ∈ Set.Icc (Pa : ℝ) (Pb : ℝ), 0 ≤ min 1 (max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X) / S) := by
      intro X hX
      have h_max : 0 ≤ max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X) := le_max_left _ _
      have h_div : 0 ≤ max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X) / S :=
        div_nonneg h_max hSℝ_nonneg
      exact le_min (by norm_num) h_div
    have h_int_nonneg := intervalIntegral.integral_nonneg (μ := volume) h_int h_nonneg
    simpa using h_int_nonneg
  · -- case S ≤ da, chord = Pb - Pa
    have h_integrand_eq_one : ∀ X ∈ Set.uIcc (Pa : ℝ) (Pb : ℝ),
        min 1 (max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X) / S) = (1 : ℝ) := by
      intro X hX
      rw [Set.uIcc_of_le h_int] at hX
      rcases hX with ⟨hXl, hXr⟩
      have h_delta_ge_S : (S : ℝ) ≤ (a0 : ℝ) - b0 + (a1 + b1) * X := by
        calc
          (S : ℝ) ≤ (da : ℝ) := by exact_mod_cast h_S_le_da
          _ = (a0 : ℝ) - b0 + (k : ℝ) * (Pa : ℝ) := by
            dsimp [da]
            push_cast
            ring
          _ ≤ (a0 : ℝ) - b0 + (k : ℝ) * (Pa : ℝ) + (k : ℝ) * (X - (Pa : ℝ)) := by
            nlinarith
          _ = (a0 : ℝ) - b0 + (k : ℝ) * X := by ring
          _ = (a0 : ℝ) - b0 + (a1 + b1) * X := by
            dsimp [k]
            push_cast
            ring
      have h_div_ge_one : (1 : ℝ) ≤ ((a0 : ℝ) - b0 + (a1 + b1) * X) / S := by
        calc
          (1 : ℝ) = (S : ℝ) / S := by field_simp [ne_of_gt hSℝ]
          _ ≤ ((a0 : ℝ) - b0 + (a1 + b1) * X) / S :=
            div_le_div_of_nonneg_right h_delta_ge_S hSℝ_nonneg
      have h_num_pos : 0 ≤ (a0 : ℝ) - b0 + (a1 + b1) * X := by linarith
      have h_max_div_ge_one : (1 : ℝ) ≤ (max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X)) / S := by
        have h_max_eq_expr : max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X) = (a0 : ℝ) - b0 + (a1 + b1) * X :=
          max_eq_right h_num_pos
        rw [h_max_eq_expr]
        exact h_div_ge_one
      exact min_eq_left h_max_div_ge_one
    have h_integral_eq : ∫ X in (Pa : ℝ)..Pb, min 1 (max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X) / S) = ((Pb - Pa : ℤ) : ℝ) := by
      calc
        ∫ X in (Pa : ℝ)..Pb, min 1 (max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X) / S)
            = ∫ X in (Pa : ℝ)..Pb, (1 : ℝ) :=
          intervalIntegral.integral_congr h_integrand_eq_one
        _ = ((Pb : ℝ) - (Pa : ℝ)) • (1 : ℝ) := intervalIntegral.integral_const _
        _ = (Pb : ℝ) - (Pa : ℝ) := by simp
        _ = ((Pb - Pa : ℤ) : ℝ) := by push_cast; ring
    exact h_integral_eq.ge
  · -- case db > 0, S > da, 0 < num', chord = num / (2*S)
    -- goal: ↑(((pos2 ...).1 - (pos2 ...).2) / (2*S)) ≤ integral
    have h_min_eq : ∀ X : ℝ, min 1 (max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X) / S) =
        (max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X) - max 0 (((a0 : ℝ) - b0 + (a1 + b1) * X) - S)) / S := by
      intro X
      exact min_one_div_eq hSℝ
    have h_integral_eq : ∫ X in (Pa : ℝ)..Pb, min 1 (max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X) / S) =
        (∫ X in (Pa : ℝ)..Pb, (max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X) - max 0 (((a0 : ℝ) - b0 + (a1 + b1) * X) - S)) / S) := by
      apply intervalIntegral.integral_congr
      intro X hX
      exact h_min_eq X
    rw [h_integral_eq]
    set Δ := fun X : ℝ => (a0 : ℝ) - b0 + (a1 + b1) * X with hΔ_def
    have hΔ_eq : ∀ X : ℝ, Δ X = (da : ℝ) + (k : ℝ) * (X - (Pa : ℝ)) := by
      intro X
      dsimp [Δ, da, k]
      push_cast
      ring
    have h_int_I : ((pos2 Pa Pb da k 0).1 : ℝ) ≤ 2 * ∫ X in (Pa : ℝ)..Pb, max 0 (Δ X) := by
      have := pos2_fst_le (c := 0) (da := da) hab hk
      simpa [hΔ_eq, sub_zero] using this
    have h_int_J : 2 * ∫ X in (Pa : ℝ)..Pb, max 0 (Δ X - (S : ℝ)) ≤ ((pos2 Pa Pb da k S).2 : ℝ) := by
      have := le_pos2_snd (c := S) (da := da) hab hk
      simpa [hΔ_eq] using this
    -- Split the integral of (max 0 Δ - max 0 (Δ - S)) / S
    have h_int_sub : ∫ X in (Pa : ℝ)..Pb, (max 0 (Δ X) - max 0 (Δ X - (S : ℝ))) / (S : ℝ) =
        ((∫ X in (Pa : ℝ)..Pb, max 0 (Δ X)) - (∫ X in (Pa : ℝ)..Pb, max 0 (Δ X - (S : ℝ)))) / (S : ℝ) := by
      calc
        ∫ X in (Pa : ℝ)..Pb, (max 0 (Δ X) - max 0 (Δ X - (S : ℝ))) / (S : ℝ)
            = (∫ X in (Pa : ℝ)..Pb, (max 0 (Δ X) - max 0 (Δ X - (S : ℝ)))) / (S : ℝ) := by
          rw [intervalIntegral.integral_div]
        _ = ((∫ X in (Pa : ℝ)..Pb, max 0 (Δ X)) - (∫ X in (Pa : ℝ)..Pb, max 0 (Δ X - (S : ℝ)))) / (S : ℝ) := by
          rw [intervalIntegral.integral_sub]
          · have h_cont : Continuous fun X : ℝ => max 0 (Δ X) := by
              have : Continuous Δ := by
                dsimp [Δ]
                fun_prop
              exact Continuous.max continuous_const this
            exact h_cont.intervalIntegrable _ _
          · have h_cont : Continuous fun X : ℝ => max 0 (Δ X - (S : ℝ)) := by
              have : Continuous (fun X : ℝ => Δ X - (S : ℝ)) := by
                dsimp [Δ]
                fun_prop
              exact Continuous.max continuous_const this
            exact h_cont.intervalIntegrable _ _
    rw [h_int_sub]
    have h_num_le : ((pos2 Pa Pb da k 0).1 : ℝ) - ((pos2 Pa Pb da k S).2 : ℝ) ≤
        2 * ((∫ X in (Pa : ℝ)..Pb, max 0 (Δ X)) - (∫ X in (Pa : ℝ)..Pb, max 0 (Δ X - (S : ℝ)))) := by
      linarith
    have h_ediv_bound : (((pos2 Pa Pb da k 0).1 - (pos2 Pa Pb da k S).2) / (2 * S) : ℤ) * (2 * S : ℤ) ≤
        (pos2 Pa Pb da k 0).1 - (pos2 Pa Pb da k S).2 := by
      apply Int.ediv_mul_le
      omega
    have h_ediv_bound_ℝ : ((((pos2 Pa Pb da k 0).1 - (pos2 Pa Pb da k S).2) / (2 * S) : ℤ) : ℝ) * (2 * (S : ℝ)) ≤
        (((pos2 Pa Pb da k 0).1 : ℝ) - ((pos2 Pa Pb da k S).2 : ℝ)) := by
      exact_mod_cast h_ediv_bound
    have h_pos_2S : 0 < (2 : ℝ) * (S : ℝ) := by nlinarith
    have h_div_bound : ((((pos2 Pa Pb da k 0).1 - (pos2 Pa Pb da k S).2) / (2 * S) : ℤ) : ℝ) ≤
        (((pos2 Pa Pb da k 0).1 : ℝ) - ((pos2 Pa Pb da k S).2 : ℝ)) / (2 * (S : ℝ)) := by
      calc
        ((((pos2 Pa Pb da k 0).1 - (pos2 Pa Pb da k S).2) / (2 * S) : ℤ) : ℝ)
            = ((((pos2 Pa Pb da k 0).1 - (pos2 Pa Pb da k S).2) / (2 * S) : ℤ) : ℝ) * (2 * (S : ℝ)) / (2 * (S : ℝ)) := by
          field_simp [ne_of_gt h_pos_2S]
        _ ≤ (((pos2 Pa Pb da k 0).1 : ℝ) - ((pos2 Pa Pb da k S).2 : ℝ)) / (2 * (S : ℝ)) :=
          div_le_div_of_nonneg_right h_ediv_bound_ℝ (by nlinarith)
    apply le_trans h_div_bound ?_
    calc
      (((pos2 Pa Pb da k 0).1 : ℝ) - ((pos2 Pa Pb da k S).2 : ℝ)) / (2 * (S : ℝ))
          ≤ (2 * ((∫ X in (Pa : ℝ)..Pb, max 0 (Δ X)) - (∫ X in (Pa : ℝ)..Pb, max 0 (Δ X - (S : ℝ))))) / (2 * (S : ℝ)) := by
        exact (div_le_div_of_nonneg_right h_num_le (by nlinarith))
      _ = ((∫ X in (Pa : ℝ)..Pb, max 0 (Δ X)) - (∫ X in (Pa : ℝ)..Pb, max 0 (Δ X - (S : ℝ)))) / (S : ℝ) := by
        ring
  · -- case db > 0, S > da, ¬ 0 < num', chord = 0
    -- goal: ↑0 ≤ integral
    have h_nonneg : ∀ X ∈ Set.Icc (Pa : ℝ) (Pb : ℝ), 0 ≤ min 1 (max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X) / S) := by
      intro X hX
      have h_max : 0 ≤ max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X) := le_max_left _ _
      have h_div : 0 ≤ max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X) / S :=
        div_nonneg h_max hSℝ_nonneg
      exact le_min (by norm_num) h_div
    have h_int_nonneg := intervalIntegral.integral_nonneg (μ := volume) h_int h_nonneg
    simpa using h_int_nonneg

/-- 8.5 (d), Abel summation: for values `y_0 ≤ ... ≤ y_{p-1}` in `[a, b]` and `M ≥ 0`,
`int over [a, b] of min (#{q : y_q < x}, M) = sum over q of (min (q + 1, M) - min (q, M)) (b - y_q)`. -/
theorem integral_min_count {p : ℕ} {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M) {y : Fin p → ℝ}
    (hy : Monotone y) (hya : ∀ q, a ≤ y q) (hyb : ∀ q, y q ≤ b) :
    ∫ x in a..b, min ((Finset.univ.filter fun q => y q < x).card : ℝ) M =
      ∑ q : Fin p, (min ((q : ℝ) + 1) M - min (q : ℝ) M) * (b - y q) := by
  -- min 0 M = 0 because M ≥ 0
  have h_min0 : min (0 : ℝ) M = 0 := by
    simp [hM]
  -- Define the telescoping function f(k) = min (k+1) M - min k M
  set f := fun (k : ℕ) => min ((k : ℝ) + 1) M - min (k : ℝ) M with hf_def
  -- Lemma: integral of indicator of (y q, ∞) over [a, b] is b - y q
  have h_indicator_integral (q : Fin p) : ∫ x in a..b, (if y q < x then (1 : ℝ) else 0) = b - y q := by
    have ha_le_yq : a ≤ y q := hya q
    have hyq_le_b : y q ≤ b := hyb q
    have h_indicator_le : ∫ x in a..b, (if x ≤ y q then (1 : ℝ) else 0) = y q - a := by
      calc
        ∫ x in a..b, (if x ≤ y q then (1 : ℝ) else 0) =
            ∫ x in a..b, ({x | x ≤ y q}.indicator (fun _ => (1 : ℝ)) x) := by
          refine intervalIntegral.integral_congr (fun x _ => ?_)
          simp [Set.indicator]
        _ = ∫ x in a..(y q), (fun _ => (1 : ℝ)) x := by
          rw [intervalIntegral.integral_indicator ⟨ha_le_yq, hyq_le_b⟩]
        _ = y q - a := by simp
    have h_eq : (fun x : ℝ => if y q < x then (1 : ℝ) else 0) =
               (fun x => 1 - (if x ≤ y q then (1 : ℝ) else 0)) := by
      ext x
      by_cases h : y q < x
      · have h_not_le : ¬ x ≤ y q := by linarith
        simp [h, h_not_le]
      · have hle : x ≤ y q := by linarith
        simp [h, hle]
    rw [h_eq]
    rw [intervalIntegral.integral_sub]
    · rw [integral_one, h_indicator_le]
      ring
    · exact Continuous.intervalIntegrable continuous_const a b
    · have h_anti : Antitone (fun x : ℝ => if x ≤ y q then (1 : ℝ) else 0) := by
        intro x₁ x₂ hx
        by_cases hx₁ : x₁ ≤ y q
        · simp [hx₁]
          by_cases hx₂ : x₂ ≤ y q
          · simp [hx₂]
          · simp [hx₂]
        · simp [hx₁]
          by_cases hx₂ : x₂ ≤ y q
          · have : x₁ ≤ y q := by linarith
            contradiction
          · simp [hx₂]
      exact h_anti.intervalIntegrable
  -- Key identity for each x: the min equals a sum over Fin p
  have h_telescope (x : ℝ) : min ((Finset.univ.filter fun q => y q < x).card : ℝ) M =
      ∑ q : Fin p, f q * (if y q < x then (1 : ℝ) else 0) := by
    let S := Finset.univ.filter fun q => y q < x
    let c := S.card
    have hc_le_p : c ≤ p := by
      have hS_subset_univ : S ⊆ Finset.univ := Finset.subset_univ _
      have h_card_le : S.card ≤ (Finset.univ : Finset (Fin p)).card :=
        Finset.card_le_card hS_subset_univ
      simpa [c] using h_card_le
    -- Convert Fin sum to range sum
    let g : ℕ → ℝ := fun k =>
      if h : k < p then
        f k * (if y ⟨k, h⟩ < x then (1 : ℝ) else 0)
      else 0
    have h_sum_eq : ∑ q : Fin p, f q * (if y q < x then (1 : ℝ) else 0) = ∑ k ∈ Finset.range p, g k := by
      simpa [g] using Fin.sum_univ_eq_sum_range g p
    -- Claim: for k < p, g k = f k if k < c, and g k = 0 if k ≥ c
    have h_g_eq (k : ℕ) (hk : k < p) : g k = (if k < c then f k else 0) := by
      dsimp [g]
      rw [dif_pos hk]
      have h_iff : y ⟨k, hk⟩ < x ↔ k < c := by
        constructor
        · intro hy_lt
          by_contra! h_ge
          have hS_lower : ∀ q q', q' ≤ q → q ∈ S → q' ∈ S := by
            intro q q' hq'q hqS
            rcases Finset.mem_filter.mp hqS with ⟨hq_univ, hyq⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            have hyq' : y q' ≤ y q := hy hq'q
            linarith
          have h_all_below : ∀ j : ℕ, (hj_le_k : j ≤ k) → (hj_lt_p : j < p) → (⟨j, Nat.lt_of_le_of_lt hj_le_k hk⟩ : Fin p) ∈ S := by
            intro j hj_le_k hj_lt_p
            have hj_lt_p' : j < p := Nat.lt_of_le_of_lt hj_le_k hk
            have hy_j_lt_x : y ⟨j, hj_lt_p'⟩ < x := by
              have h_le : (⟨j, hj_lt_p'⟩ : Fin p) ≤ (⟨k, hk⟩ : Fin p) := Fin.le_def.mpr hj_le_k
              have hy_j_le_y_k : y ⟨j, hj_lt_p'⟩ ≤ y ⟨k, hk⟩ := hy h_le
              linarith
            apply hS_lower (⟨k, hk⟩) (⟨j, hj_lt_p'⟩) (Fin.le_def.mpr hj_le_k)
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy_lt⟩
          have h_card_S_ge : k.succ ≤ S.card := by
            let T := Finset.filter (fun (q : Fin p) => (q : ℕ) ≤ k) Finset.univ
            have hT_subset_S : T ⊆ S := by
              intro q hqT
              rcases Finset.mem_filter.mp hqT with ⟨hq_univ, hq_le_k⟩
              have hq_val_lt_p : (q : ℕ) < p := q.2
              exact h_all_below (q : ℕ) hq_le_k hq_val_lt_p
            have hT_card : T.card = k.succ := by
              have h_eq' : ({q : Fin p | (q : ℕ) ≤ k} : Finset (Fin p)) =
                         ({q : Fin p | (q : ℕ) < k.succ} : Finset (Fin p)) := by
                ext q; simp [Nat.lt_succ_iff]
              have hT_eq : T = ({q : Fin p | (q : ℕ) ≤ k} : Finset (Fin p)) := rfl
              rw [hT_eq, h_eq']
              rw [Fin.card_filter_val_lt]
              exact min_eq_right (Nat.succ_le_of_lt hk)
            have h_card_le : T.card ≤ S.card := Finset.card_le_card hT_subset_S
            rw [hT_card] at h_card_le
            exact h_card_le
          have hc_le_k : c ≤ k := by omega
          have : k.succ ≤ k := by
            calc
              k.succ ≤ S.card := h_card_S_ge
              _ = c := rfl
              _ ≤ k := hc_le_k
          omega
        · intro hk_lt_c
          by_contra! hy_ge
          have hy_ge' : x ≤ y ⟨k, hk⟩ := by linarith
          have hS_subset : S ⊆ Finset.filter (fun (q : Fin p) => (q : ℕ) < k) Finset.univ := by
            intro q hqS
            rcases Finset.mem_filter.mp hqS with ⟨hq_univ, hyq_lt_x⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            by_contra! h_ge
            have hk_le_q : (⟨k, hk⟩ : Fin p) ≤ q := Fin.le_def.mpr h_ge
            have hyk_le_yq : y (⟨k, hk⟩ : Fin p) ≤ y q := hy hk_le_q
            linarith
          have h_filter_card : (Finset.filter (fun (q : Fin p) => (q : ℕ) < k) Finset.univ).card = k := by
            rw [Fin.card_filter_val_lt]
            exact min_eq_right (Nat.le_of_lt hk)
          have h_card_S_le_k : S.card ≤ k := by
            calc
              S.card ≤ (Finset.filter (fun (q : Fin p) => (q : ℕ) < k) Finset.univ).card :=
                Finset.card_le_card hS_subset
              _ = k := h_filter_card
          have : k < S.card := hk_lt_c
          omega
      -- Now use h_iff to rewrite
      by_cases hyq : y ⟨k, hk⟩ < x
      · have hk_lt_c : k < c := (h_iff.mp hyq)
        simp [hyq, hk_lt_c]
      · have h_not_lt_c : ¬ k < c := by
          intro hk_lt_c
          have hyq' : y ⟨k, hk⟩ < x := (h_iff.mpr hk_lt_c)
          exact hyq hyq'
        simp [hyq, h_not_lt_c]
    -- Now combine everything
    calc
      min ((Finset.univ.filter fun q => y q < x).card : ℝ) M = min (c : ℝ) M := by simp [c, S]
      _ = ∑ k ∈ Finset.range c, f k := by
        dsimp [f]
        set g' := fun (k : ℕ) => min (k : ℝ) M with hg'_def
        have h_telescope' : ∑ k ∈ Finset.range c, (g' (k+1) - g' k) = g' c - g' 0 :=
          Finset.sum_range_sub g' c
        have h_eq'' : ∀ k, g' (k+1) - g' k = min ((k : ℝ) + 1) M - min (k : ℝ) M := by
          intro k
          dsimp [g']
          simp
        rw [← Finset.sum_congr rfl (fun k hk => by rw [← h_eq'' k])]
        rw [h_telescope']
        dsimp [g']
        simp [h_min0]
      _ = ∑ k ∈ Finset.range p, (if k < c then f k else 0) := by
        rw [← Finset.sum_filter]
        have h_filter_eq : (Finset.range p).filter (fun k => k < c) = Finset.range c := by
          ext k; constructor <;> simp; intro hk; omega
        rw [h_filter_eq]
      _ = ∑ k ∈ Finset.range p, g k := by
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        rw [h_g_eq k hk]
      _ = ∑ q : Fin p, f q * (if y q < x then (1 : ℝ) else 0) := by
        simpa [g] using (Fin.sum_univ_eq_sum_range g p).symm
  -- Now integrate both sides
  calc
    ∫ x in a..b, min ((Finset.univ.filter fun q => y q < x).card : ℝ) M
        = ∫ x in a..b, ∑ q : Fin p, f q * (if y q < x then (1 : ℝ) else 0) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact h_telescope x
    _ = ∑ q : Fin p, ∫ x in a..b, f q * (if y q < x then (1 : ℝ) else 0) := by
      rw [intervalIntegral.integral_finsetSum]
      intro q hq
      have h_indicator : IntervalIntegrable (fun x : ℝ => if y q < x then (1 : ℝ) else 0) volume a b := by
        have h_eq : (fun x : ℝ => if y q < x then (1 : ℝ) else 0) =
                   (fun x => 1 - (if x ≤ y q then (1 : ℝ) else 0)) := by
          ext x
          by_cases h : y q < x
          · have h_not_le : ¬ x ≤ y q := by linarith
            simp [h, h_not_le]
          · have hle : x ≤ y q := by linarith
            simp [h, hle]
        rw [h_eq]
        apply IntervalIntegrable.sub
        · exact Continuous.intervalIntegrable continuous_const a b
        · have h_anti : Antitone (fun x : ℝ => if x ≤ y q then (1 : ℝ) else 0) := by
            intro x₁ x₂ hx
            by_cases hx₁ : x₁ ≤ y q
            · simp [hx₁]
              by_cases hx₂ : x₂ ≤ y q
              · simp [hx₂]
              · simp [hx₂]
            · simp [hx₁]
              by_cases hx₂ : x₂ ≤ y q
              · have : x₁ ≤ y q := by linarith
                contradiction
              · simp [hx₂]
          exact h_anti.intervalIntegrable
      exact h_indicator.const_mul (f q)
    _ = ∑ q : Fin p, f q * ∫ x in a..b, (if y q < x then (1 : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [intervalIntegral.integral_const_mul]
    _ = ∑ q : Fin p, f q * (b - y q) := by
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [h_indicator_integral q]
    _ = ∑ q : Fin p, (min ((q : ℝ) + 1) M - min (q : ℝ) M) * (b - y q) := by
      simp [f]

/-- `int over [a, 1] of (1 - x) ^ r = (1 - a) ^ (r + 1) / (r + 1)`. -/
theorem integral_one_sub_pow (a : ℝ) (r : ℕ) :
    ∫ x in a..1, (1 - x) ^ r = (1 - a) ^ (r + 1) / (r + 1) := by
  calc
    ∫ x in a..1, (1 - x) ^ r = ∫ x in (1 : ℝ) - 1..(1 : ℝ) - a, x ^ r := by
      rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ r) 1]
    _ = ∫ x in (0 : ℝ)..(1 - a), x ^ r := by
      simp
    _ = ((1 - a) ^ (r + 1) - (0 : ℝ) ^ (r + 1)) / (↑r + 1) := by rw [integral_pow]
    _ = ((1 - a) ^ (r + 1) - 0) / (↑r + 1) := by
      rw [zero_pow (Nat.succ_ne_zero r)]
    _ = (1 - a) ^ (r + 1) / (↑r + 1) := by ring

/-! ## The penalty `Epen D` (Lemma B.1 of the paper) -/

theorem Epen_zero (D z : ℕ) : Epen D z 0 = D := rfl

theorem Epen_succ (D z r : ℕ) : Epen D z (r + 1) = Epen D z r * (D - z) / D := rfl

/-- `Epen D z r ≤ D`. -/
theorem Epen_le_D (D z r : ℕ) : Epen D z r ≤ D := by
  induction' r with r ih
  · rw [Epen_zero]
  · rw [Epen_succ]
    apply le_trans ?_ ih
    apply Nat.div_le_of_le_mul
    calc
      Epen D z r * (D - z) ≤ Epen D z r * D := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = D * Epen D z r := Nat.mul_comm _ _

/-- `Epen D` is nonincreasing in the point. -/
theorem Epen_anti {D z z' : ℕ} (h : z ≤ z') (r : ℕ) : Epen D z' r ≤ Epen D z r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Epen_succ, Epen_succ]
    apply Nat.div_le_div_right
    apply Nat.mul_le_mul ih (Nat.sub_le_sub_left h D)

/-- `Epen D z r ≤ D (1 - z / D) ^ r`. -/
theorem Epen_le {D : ℕ} (hD : 0 < D) {z : ℕ} (hz : z ≤ D) (r : ℕ) :
    (Epen D z r : ℝ) ≤ D * (1 - z / D) ^ r := by
  induction' r with r ih
  · simp [Epen_zero]
  · rw [Epen_succ]
    have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne.symm
    have h_nonneg : 0 ≤ 1 - (z : ℝ) / (D : ℝ) := by
      have hz' : (z : ℝ) ≤ (D : ℝ) := by exact_mod_cast hz
      have h_div : (z : ℝ) / (D : ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hD)).mpr hz'
      linarith
    calc
      ((Epen D z r * (D - z) / D : ℕ) : ℝ) ≤ ((Epen D z r * (D - z) : ℕ) : ℝ) / (D : ℝ) :=
        Nat.cast_div_le
      _ = ((Epen D z r : ℝ) * ((D - z : ℕ) : ℝ)) / (D : ℝ) := by simp
      _ = ((Epen D z r : ℝ) * ((D : ℝ) - (z : ℝ))) / (D : ℝ) := by
        simp [Nat.cast_sub hz]
      _ = (Epen D z r : ℝ) * (((D : ℝ) - (z : ℝ)) / (D : ℝ)) := by
        field_simp [hD']
      _ = (Epen D z r : ℝ) * (1 - (z : ℝ) / (D : ℝ)) := by
        field_simp [hD']
      _ ≤ (D * (1 - (z : ℝ) / (D : ℝ)) ^ r) * (1 - (z : ℝ) / (D : ℝ)) :=
        mul_le_mul_of_nonneg_right ih h_nonneg
      _ = D * (1 - (z : ℝ) / (D : ℝ)) ^ (r + 1) := by
        ring

/-- `D (1 - z / D) ^ r ≤ Epen D z r + r`. -/
theorem le_Epen_add {D : ℕ} (hD : 0 < D) {z : ℕ} (hz : z ≤ D) (r : ℕ) :
    (D : ℝ) * (1 - z / D) ^ r ≤ Epen D z r + r := by
  induction' r with r ih
  · simp [Epen_zero]
  · have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
    have hzleD : (z : ℝ) ≤ D := by exact_mod_cast hz
    have hznonneg : (0 : ℝ) ≤ z := by exact_mod_cast (Nat.zero_le z)
    set q := 1 - (z : ℝ) / D with hq_def
    have hq_nonneg : 0 ≤ q := by
      dsimp [q]
      have hdiv : (z : ℝ) / D ≤ 1 := (div_le_one (by exact_mod_cast hD)).mpr hzleD
      linarith
    have hq_le_one : q ≤ 1 := by
      dsimp [q]
      have hdiv_nonneg : 0 ≤ (z : ℝ) / D := div_nonneg hznonneg (by positivity)
      linarith
    have hEpen_mul_q_lt : (Epen D z r : ℝ) * q < (Epen D z (r + 1) : ℝ) + 1 := by
      have hkey : ∀ a : ℕ, (a : ℝ) / D < ((a / D : ℕ) : ℝ) + 1 := by
        intro a
        have hdivmod := Nat.div_add_mod a D
        have hmodlt : a % D < D := Nat.mod_lt a hD
        calc
          (a : ℝ) / D = (((D * (a / D) + a % D : ℕ) : ℝ) / D) := by
            rw [show (a : ℝ) = ((D * (a / D) + a % D : ℕ) : ℝ) from by rw [hdivmod]]
          _ = (((a / D : ℕ) : ℝ) * (D : ℝ) + ((a % D : ℕ) : ℝ)) / D := by
            push_cast
            ring
          _ = ((a / D : ℕ) : ℝ) + ((a % D : ℕ) : ℝ) / D := by
            rw [add_div]
            field_simp [hDpos.ne']
          _ < ((a / D : ℕ) : ℝ) + 1 := by
            have h : ((a % D : ℕ) : ℝ) / D < 1 := by
              refine (div_lt_one ?_).mpr ?_
              · exact_mod_cast hD
              · exact mod_cast hmodlt
            linarith
      have ha_eq : (Epen D z r * (D - z) : ℝ) / D = (Epen D z r : ℝ) * q := by
        dsimp [q]
        push_cast
        field_simp [hDpos.ne']
      have h_lt_raw := hkey (Epen D z r * (D - z))
      have h_lt : (Epen D z r : ℝ) * q < (Epen D z (r + 1) : ℝ) + 1 := by
        rw [ha_eq.symm]
        simpa [Epen_succ, Nat.cast_sub hz] using h_lt_raw
      exact h_lt
    have h_mul_ineq : (D : ℝ) * q ^ (r + 1) ≤ ((Epen D z r : ℝ) + r) * q := by
      calc
        (D : ℝ) * q ^ (r + 1) = (D : ℝ) * (q ^ r * q) := by ring
        _ = ((D : ℝ) * q ^ r) * q := by ring
        _ ≤ ((Epen D z r : ℝ) + r) * q := by
          nlinarith [ih, hq_nonneg]
    have h_sum_ineq : ((Epen D z r : ℝ) + r) * q ≤ (Epen D z (r + 1) : ℝ) + (r + 1) := by
      have hq_mul_r_le_r : r * q ≤ r := by
        nlinarith
      calc
        ((Epen D z r : ℝ) + r) * q = (Epen D z r : ℝ) * q + r * q := by ring
        _ ≤ ((Epen D z (r + 1) : ℝ) + 1) + r * q := by linarith
        _ ≤ ((Epen D z (r + 1) : ℝ) + 1) + r := by linarith
        _ = (Epen D z (r + 1) : ℝ) + (r + 1) := by ring
    simpa [Nat.cast_succ] using calc
      (D : ℝ) * (1 - (z : ℝ) / D) ^ (r + 1) = (D : ℝ) * q ^ (r + 1) := by simp [q]
      _ ≤ (Epen D z (r + 1) : ℝ) + (r + 1) := le_trans h_mul_ineq h_sum_ineq

/-- 8.5 (e): `E_{t-1} (z) / (D (r + 1)) ≤ int over [z / D, 1] of (1 - x) ^ r`. -/
theorem Epen_succ_div_le_integral {D : ℕ} (hD : 0 < D) {z : ℕ} (hz : z ≤ D) (r : ℕ) :
    (Epen D z (r + 1) : ℝ) / (D * (r + 1)) ≤ ∫ x in (z : ℝ) / D..1, (1 - x) ^ r := by
  have hD_ne : (D : ℝ) ≠ 0 := by exact mod_cast hD.ne.symm
  have hEpen := Epen_le hD hz (r + 1)
  have hint := integral_one_sub_pow ((z : ℝ) / D) r
  calc
    (Epen D z (r + 1) : ℝ) / (D * (r + 1)) ≤ (D * (1 - (z : ℝ) / D) ^ (r + 1)) / (D * (r + 1)) := by
      exact div_le_div_of_nonneg_right hEpen (by positivity)
    _ = (1 - (z : ℝ) / D) ^ (r + 1) / (r + 1) := by
      field_simp [hD_ne]
    _ = ∫ x in (z : ℝ) / D..1, (1 - x) ^ r := by
      rw [hint]

/-! ## Tangent and monotonicity (8.2 (b), 8.3) -/

/-- The tangent of the convex function `(1 - x) ^ r` at `p` lies below it on `[0, 1]`. -/
theorem tangent_le_one_sub_pow {x p : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (r : ℕ) : (1 - p) ^ r + r * (1 - p) ^ (r - 1) * (p - x) ≤ (1 - x) ^ r := by
  set u := 1 - x with hu_def
  set w := 1 - p with hw_def
  have hu : 0 ≤ u := by linarith
  have hw : 0 ≤ w := by linarith
  have h_diff : p - x = u - w := by
    dsimp [u, w]
    ring
  rw [h_diff]
  have h_factor : u ^ r - w ^ r = (∑ i ∈ Finset.range r, u ^ i * w ^ (r - 1 - i)) * (u - w) := by
    rw [← geom_sum₂_mul]
  have h_sum_le (h : u ≤ w) : (∑ i ∈ Finset.range r, u ^ i * w ^ (r - 1 - i)) ≤ r * w ^ (r - 1) := by
    calc
      (∑ i ∈ Finset.range r, u ^ i * w ^ (r - 1 - i)) ≤ (∑ i ∈ Finset.range r, w ^ i * w ^ (r - 1 - i)) := by
        refine Finset.sum_le_sum (λ i hi => ?_)
        have h_pow : u ^ i ≤ w ^ i := pow_le_pow_left₀ hu h i
        have h_nonneg : 0 ≤ w ^ (r - 1 - i) := pow_nonneg hw _
        exact mul_le_mul_of_nonneg_right h_pow h_nonneg
      _ = (∑ _i ∈ Finset.range r, w ^ (r - 1)) := by
        refine Finset.sum_congr rfl (λ i hi => ?_)
        have hi_range : i < r := Finset.mem_range.1 hi
        have h_le : i ≤ r - 1 := by omega
        rw [← pow_add, Nat.add_sub_cancel' h_le]
      _ = r * w ^ (r - 1) := by
        simp [Finset.sum_const]
  have h_sum_ge (h : w ≤ u) : r * w ^ (r - 1) ≤ (∑ i ∈ Finset.range r, u ^ i * w ^ (r - 1 - i)) := by
    calc
      r * w ^ (r - 1) = (∑ _i ∈ Finset.range r, w ^ (r - 1)) := by
        simp [Finset.sum_const]
      _ = (∑ i ∈ Finset.range r, w ^ i * w ^ (r - 1 - i)) := by
        refine Finset.sum_congr rfl (λ i hi => ?_)
        have hi_range : i < r := Finset.mem_range.1 hi
        have h_le : i ≤ r - 1 := by omega
        rw [← pow_add, Nat.add_sub_cancel' h_le]
      _ ≤ (∑ i ∈ Finset.range r, u ^ i * w ^ (r - 1 - i)) := by
        refine Finset.sum_le_sum (λ i hi => ?_)
        have h_pow : w ^ i ≤ u ^ i := pow_le_pow_left₀ hw h i
        have h_nonneg : 0 ≤ w ^ (r - 1 - i) := pow_nonneg hw _
        exact mul_le_mul_of_nonneg_right h_pow h_nonneg
  by_cases h : u ≤ w
  · have h_nonpos : u - w ≤ 0 := by linarith
    have h_main : (r * w ^ (r - 1)) * (u - w) ≤ (∑ i ∈ Finset.range r, u ^ i * w ^ (r - 1 - i)) * (u - w) :=
      mul_le_mul_of_nonpos_right (h_sum_le h) h_nonpos
    have h_goal : r * w ^ (r - 1) * (u - w) ≤ (∑ i ∈ Finset.range r, u ^ i * w ^ (r - 1 - i)) * (u - w) := by
      simpa [mul_assoc] using h_main
    linarith
  · have h_nonneg : 0 ≤ u - w := by linarith
    have h_main : (r * w ^ (r - 1)) * (u - w) ≤ (∑ i ∈ Finset.range r, u ^ i * w ^ (r - 1 - i)) * (u - w) :=
      mul_le_mul_of_nonneg_right (h_sum_ge (by linarith)) h_nonneg
    have h_goal : r * w ^ (r - 1) * (u - w) ≤ (∑ i ∈ Finset.range r, u ^ i * w ^ (r - 1 - i)) * (u - w) := by
      simpa [mul_assoc] using h_main
    linarith

/-- `r x - (1 - x) ^ r` is nondecreasing on `[0, 1]` (the test of `jT`). -/
theorem sub_one_sub_pow_mono {x x' : ℝ} (hx0 : 0 ≤ x) (hxx' : x ≤ x') (hx'1 : x' ≤ 1) (r : ℕ) :
    r * x - (1 - x) ^ r ≤ r * x' - (1 - x') ^ r := by
  set k := 1 - x with hk_def
  set h := 1 - x' with hh_def
  have hk0 : 0 ≤ k := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hkh : h ≤ k := by linarith
  have hk1 : k ≤ 1 := by linarith
  have hh1 : h ≤ 1 := by linarith
  have hsub_nonneg : 0 ≤ k - h := by linarith
  -- core inequality: r*(k-h) ≥ k^r - h^r
  have h_core : (r : ℝ) * (k - h) ≥ k ^ r - h ^ r := by
    induction' r with r ih
    · -- r = 0
      simp
    · -- r → r+1
      have h_rec : k ^ (r + 1) - h ^ (r + 1) = k * (k ^ r - h ^ r) + h ^ r * (k - h) := by
        ring
      rw [h_rec]
      have h1 : k * (k ^ r - h ^ r) ≤ k * ((r : ℝ) * (k - h)) := by
        have : k ^ r - h ^ r ≤ (r : ℝ) * (k - h) := ih
        nlinarith
      have hh_pow_le_one : h ^ r ≤ (1 : ℝ) := by
        have := pow_le_pow_of_le_one hh0 hh1 (Nat.zero_le r)
        simpa using this
      have h2 : h ^ r * (k - h) ≤ 1 * (k - h) := by
        nlinarith
      have h_mul : (r : ℝ) * k + 1 ≤ (r : ℝ) + 1 := by
        nlinarith
      have h_final : ((r : ℝ) * k + 1) * (k - h) ≤ ((r : ℝ) + 1) * (k - h) :=
        mul_le_mul_of_nonneg_right h_mul hsub_nonneg
      calc
        (↑(r + 1) : ℝ) * (k - h) ≥ ((r : ℝ) * k + 1) * (k - h) := by
          -- need to relate ↑(r+1) and (r:ℝ)+1
          simpa [Nat.cast_add, Nat.cast_one] using h_final
        _ = k * ((r : ℝ) * (k - h)) + 1 * (k - h) := by ring
        _ ≥ k * (k ^ r - h ^ r) + h ^ r * (k - h) := by nlinarith
  -- translate back to original goal
  dsimp [k, h] at h_core
  have h_simp : (1 - x) - (1 - x') = x' - x := by ring
  rw [h_simp] at h_core
  dsimp [k, h]
  have h_pow_le : (1 - x') ^ r ≤ (1 - x) ^ r := by
    have h_nonneg : 0 ≤ 1 - x' := by linarith
    have h_le : 1 - x' ≤ 1 - x := by linarith
    exact pow_le_pow_left₀ h_nonneg h_le r
  have h_diff : (r : ℝ) * x' - (1 - x') ^ r - ((r : ℝ) * x - (1 - x) ^ r) = (r : ℝ) * (x' - x) + ((1 - x) ^ r - (1 - x') ^ r) := by ring
  have h_nonneg : 0 ≤ (r : ℝ) * x' - (1 - x') ^ r - ((r : ℝ) * x - (1 - x) ^ r) := by
    rw [h_diff]
    have : (r : ℝ) * (x' - x) ≥ (1 - x) ^ r - (1 - x') ^ r := h_core
    linarith
  linarith

/-! ## Rounding -/

/-- The floor of `a / b` on `ℤ`, cast to `ℝ`, is at most `a / b` (`b > 0`). -/
theorem intCast_ediv_le {a b : ℤ} (hb : 0 < b) : ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  have hb' : 0 < (b : ℝ) := Int.cast_pos.mpr hb
  rw [le_div_iff₀ hb']
  exact_mod_cast Int.ediv_mul_le a hb.ne'

/-- The floor of `a / b` on `ℤ` plus one exceeds `a / b` (`b > 0`). -/
theorem lt_intCast_ediv_add_one {a b : ℤ} (hb : 0 < b) : (a : ℝ) / b < ((a / b : ℤ) : ℝ) + 1 := by
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [div_lt_iff₀ hb']
  have h_int := Int.lt_ediv_add_one_mul_self a hb
  have h_cast : (a : ℝ) < (((a / b + 1) * b : ℤ) : ℝ) := by exact_mod_cast h_int
  simpa [Int.cast_add, Int.cast_mul, Int.cast_one] using h_cast

end Robbins.Cert.SO
