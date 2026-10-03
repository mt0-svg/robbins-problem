import Mathlib
import Robbins.Cert.Grid

/-!
# Arithmetic of the certificate: penalty tables, cell integral, tail

The first-order certificate, sections 3 and 4 of its format. All quantities are
natural numbers; a point value `z` is the numerator of `z / D`, `D = 2 ^ 40`.

* `Epen z r`: the penalty table `E_{n-r}` at a point of value `z`, `E_n = D`,
  `E_{t-1} = floor (E_t (D - z) / D)`; `Epen_le` and `le_Epen_add` are the bounds of 6.1,
  `Epen z r ≤ D (1 - z / D) ^ r ≤ Epen z r + r`, and `Epen_anti` the monotonicity in `z`.
* `jcell r a b alpha C`: the cell integral of D9 in units of `1 / (2 D ^ 2)`; `jcell_le` bounds it by
  `2 D ^ 2 ∫_{a/D}^{b/D} min (alpha + r x) (C / D)`.
* `condT`, `tailT`: condition (T) and the tail term of 4.3; `tailT_le` bounds the tail by
  `2 D ^ 2 ∫_{X/D}^1 ((1 - x) ^ r + U / D)`.
-/

namespace Robbins.Cert

open MeasureTheory intervalIntegral

/-- The penalty table at a point of value `z`: `Epen z r = E_{n-r}[z]`. -/
def Epen (z : Nat) : Nat → Nat
  | 0 => D
  | r + 1 => Epen z r * (D - z) / D

/-- The cell integral (section 4.3 of the format), units `2 ^ -81`. -/
def jcell (r a b alpha C : Nat) : Nat :=
  let S := 2 * D * alpha * (b - a) + r * (b * b - a * a)
  if alpha * D + r * b ≤ C then S
  else if C ≤ alpha * D + r * a then 2 * (b - a) * C
  else
    let F := alpha * D + r * b - C
    S - (F * F + r - 1) / r

/-- Condition (T) at `X`: `U + EX + r ≤ (1 + m) D + r X`. -/
def condT (r m U EX X : Nat) : Bool :=
  U + EX + r ≤ (1 + m) * D + r * X

/-- The tail term: `floor (2 D E1X / (r + 1)) + 2 (D - X) U` if `X < D` and (T) holds, else `0`. -/
def tailT (r m U X EX E1X : Nat) : Nat :=
  if X < D && condT r m U EX X then 2 * D * E1X / (r + 1) + 2 * (D - X) * U else 0

theorem D_pos : 0 < D := by
  unfold D
  norm_num

theorem Epen_zero (z : Nat) : Epen z 0 = D := rfl

theorem Epen_succ (z r : Nat) : Epen z (r + 1) = Epen z r * (D - z) / D := rfl

theorem Epen_le_D (z r : Nat) : Epen z r ≤ D := by
  induction r with
  | zero =>
      rw [Epen_zero]
  | succ r ih =>
      rw [Epen_succ]
      have hDpos : 0 < D := by
        unfold D
        norm_num
      calc
        Epen z r * (D - z) / D ≤ Epen z r * D / D := by
          apply Nat.div_le_div_right
          apply Nat.mul_le_mul_left (Epen z r)
          apply Nat.sub_le
        _ = Epen z r := by
          apply Nat.mul_div_cancel _ hDpos
        _ ≤ D := ih

theorem Epen_anti {z z' : Nat} (h : z ≤ z') (r : Nat) : Epen z' r ≤ Epen z r := by
  induction' r with r IH
  · rfl
  · rw [Epen_succ, Epen_succ]
    have hsub : D - z' ≤ D - z := Nat.sub_le_sub_left h D
    have hmul : Epen z' r * (D - z') ≤ Epen z r * (D - z) := Nat.mul_le_mul IH hsub
    exact Nat.div_le_div_right hmul

/-- 6.1, upper bound. -/
theorem Epen_le (z r : Nat) (hz : z ≤ D) : (Epen z r : ℝ) ≤ D * (1 - z / D) ^ r := by
  have hDpos : 0 < D := by decide
  have hDpos' : 0 < (D : ℝ) := by exact_mod_cast hDpos
  have hDpos'' : (D : ℝ) ≠ 0 := by linarith
  induction' r with r ih
  · simp [Epen_zero]
  · rw [Epen_succ]
    calc
      ((Epen z r * (D - z) / D : ℕ) : ℝ) ≤ ((Epen z r * (D - z) : ℕ) : ℝ) / (D : ℝ) :=
        Nat.cast_div_le
      _ = ((Epen z r : ℝ) * ((D - z : ℕ) : ℝ)) / (D : ℝ) := by simp
      _ = (Epen z r : ℝ) * (((D - z : ℕ) : ℝ) / (D : ℝ)) := by ring
      _ = (Epen z r : ℝ) * (((D : ℝ) - (z : ℝ)) / (D : ℝ)) := by
        simp [Nat.cast_sub hz]
      _ = (Epen z r : ℝ) * ((1 : ℝ) - ((z : ℝ) / (D : ℝ))) := by
        field_simp [hDpos'']
      _ ≤ (D * ((1 : ℝ) - ((z : ℝ) / (D : ℝ))) ^ r) * ((1 : ℝ) - ((z : ℝ) / (D : ℝ))) := by
        have h_nonneg : 0 ≤ (1 : ℝ) - ((z : ℝ) / (D : ℝ)) := by
          have hz_div : (z : ℝ) / (D : ℝ) ≤ 1 := by
            exact (div_le_one (by exact_mod_cast hDpos)).mpr (by exact_mod_cast hz)
          linarith
        exact mul_le_mul_of_nonneg_right ih h_nonneg
      _ = D * (((1 : ℝ) - ((z : ℝ) / (D : ℝ))) ^ r * ((1 : ℝ) - ((z : ℝ) / (D : ℝ)))) := by ring
      _ = D * ((1 : ℝ) - ((z : ℝ) / (D : ℝ))) ^ (r + 1) := by ring

/-- 6.1, lower bound. -/
theorem le_Epen_add (z r : Nat) (hz : z ≤ D) : (D : ℝ) * (1 - z / D) ^ r ≤ Epen z r + r := by
  have hDpos : 0 < (D : ℝ) := by
    have h := D_pos
    exact_mod_cast h
  have hDpos_ne : (D : ℝ) ≠ 0 := by linarith
  have hz_div_nonneg : 0 ≤ (z : ℝ) / (D : ℝ) := by
    positivity
  have hz_div_le_one : (z : ℝ) / (D : ℝ) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by exact_mod_cast hz)
  have hq_nonneg : 0 ≤ 1 - (z : ℝ) / (D : ℝ) := by
    linarith
  have hq_le_one : 1 - (z : ℝ) / (D : ℝ) ≤ 1 := by
    linarith
  -- key lemma: for any a : ℕ, (a : ℝ) / (D : ℝ) < ((a / D : ℕ) : ℝ) + 1
  have h_div_lt_add_one (a : ℕ) : (a : ℝ) / (D : ℝ) < ((a / D : ℕ) : ℝ) + 1 := by
    have hmod := Nat.mod_lt a D_pos
    have hdivmod := Nat.div_add_mod a D
    have ha_eq_nat : a = D * (a / D) + a % D := by
      omega
    have ha_eq : (a : ℝ) = (D : ℝ) * ((a / D : ℕ) : ℝ) + ((a % D : ℕ) : ℝ) := by
      have h := congrArg (fun x : ℕ => (x : ℝ)) ha_eq_nat
      simpa [Nat.cast_add, Nat.cast_mul] using h
    have hmod_lt : ((a % D : ℕ) : ℝ) < (D : ℝ) := by exact mod_cast hmod
    have hdiv_lt_one : ((a % D : ℕ) : ℝ) / (D : ℝ) < 1 :=
      (div_lt_one hDpos).mpr hmod_lt
    calc
      (a : ℝ) / (D : ℝ) = ((D : ℝ) * ((a / D : ℕ) : ℝ) + ((a % D : ℕ) : ℝ)) / (D : ℝ) := by rw [ha_eq]
      _ = ((a / D : ℕ) : ℝ) + ((a % D : ℕ) : ℝ) / (D : ℝ) := by
        field_simp [hDpos_ne]
      _ < ((a / D : ℕ) : ℝ) + 1 := by
        linarith
  induction' r with r ih
  · -- r = 0
    simp [Epen_zero]
  · -- r → r+1
    have h_mul : (D : ℝ) * (1 - (z : ℝ) / (D : ℝ)) ^ (r + 1) =
        ((D : ℝ) * (1 - (z : ℝ) / (D : ℝ)) ^ r) * (1 - (z : ℝ) / (D : ℝ)) := by
      ring
    rw [h_mul]
    have h1 : ((D : ℝ) * (1 - (z : ℝ) / (D : ℝ)) ^ r) * (1 - (z : ℝ) / (D : ℝ))
        ≤ ((Epen z r : ℝ) + (r : ℝ)) * (1 - (z : ℝ) / (D : ℝ)) := by
      nlinarith
    have h2 : ((Epen z r : ℝ) + (r : ℝ)) * (1 - (z : ℝ) / (D : ℝ))
        ≤ (Epen z r : ℝ) * (1 - (z : ℝ) / (D : ℝ)) + (r : ℝ) := by
      nlinarith
    have h_key : (Epen z r : ℝ) * (1 - (z : ℝ) / (D : ℝ)) < (Epen z (r + 1) : ℝ) + 1 := by
      calc
        (Epen z r : ℝ) * (1 - (z : ℝ) / (D : ℝ))
            = ((Epen z r : ℝ) * ((D : ℝ) - (z : ℝ))) / (D : ℝ) := by
          field_simp [hDpos_ne]
        _ = (((Epen z r * (D - z) : ℕ) : ℝ)) / (D : ℝ) := by
          push_cast
          simp [Nat.cast_sub hz]
        _ < (((Epen z r * (D - z) / D : ℕ) : ℝ)) + 1 := h_div_lt_add_one (Epen z r * (D - z))
        _ = (Epen z (r + 1) : ℝ) + 1 := by rw [Epen_succ]
    have h_total : ((D : ℝ) * (1 - (z : ℝ) / (D : ℝ)) ^ r) * (1 - (z : ℝ) / (D : ℝ)) ≤
        (Epen z (r + 1) : ℝ) + ((r + 1 : ℕ) : ℝ) := by
      have htemp : ((D : ℝ) * (1 - (z : ℝ) / (D : ℝ)) ^ r) * (1 - (z : ℝ) / (D : ℝ)) ≤
          (Epen z r : ℝ) * (1 - (z : ℝ) / (D : ℝ)) + (r : ℝ) := by
        linarith
      have htemp2 : (Epen z r : ℝ) * (1 - (z : ℝ) / (D : ℝ)) + (r : ℝ) <
          (Epen z (r + 1) : ℝ) + ((r : ℝ) + 1) := by
        linarith
      have htemp3 : (Epen z (r + 1) : ℝ) + ((r : ℝ) + 1) = (Epen z (r + 1) : ℝ) + ((r + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      linarith
    simpa using h_total

theorem integral_lin (alpha r u v : ℝ) :
    ∫ x in u..v, (alpha + r * x) = alpha * (v - u) + r * (v ^ 2 - u ^ 2) / 2 := by
  calc
    ∫ x in u..v, (alpha + r * x) = (∫ x in u..v, alpha) + (∫ x in u..v, r * x) := by
      apply intervalIntegral.integral_add
      · exact intervalIntegrable_const
      · exact (continuous_const.mul continuous_id).intervalIntegrable (a := u) (b := v)
    _ = ((v - u) • alpha) + (∫ x in u..v, r * x) := by rw [intervalIntegral.integral_const]
    _ = alpha * (v - u) + (∫ x in u..v, r * x) := by rw [smul_eq_mul, mul_comm]
    _ = alpha * (v - u) + r * (∫ x in u..v, x) := by rw [intervalIntegral.integral_const_mul]
    _ = alpha * (v - u) + r * ((v ^ 2 - u ^ 2) / 2) := by rw [integral_id]
    _ = alpha * (v - u) + r * (v ^ 2 - u ^ 2) / 2 := by ring

theorem integral_min_of_le {alpha r c u v : ℝ} (huv : u ≤ v)
    (h : ∀ x ∈ Set.Icc u v, alpha + r * x ≤ c) :
    ∫ x in u..v, min (alpha + r * x) c = alpha * (v - u) + r * (v ^ 2 - u ^ 2) / 2 := by
  have h_eqon : Set.EqOn (fun x => min (alpha + r * x) c) (fun x => alpha + r * x) (Set.uIcc u v) := by
    intro x hx
    rw [Set.uIcc_of_le huv] at hx
    exact min_eq_left (h x hx)
  rw [intervalIntegral.integral_congr h_eqon]
  have hint_const : IntervalIntegrable (fun (_x : ℝ) => alpha) volume u v :=
    intervalIntegrable_const
  have hint_rx : IntervalIntegrable (fun (x : ℝ) => r * x) volume u v :=
    (intervalIntegral.intervalIntegrable_id (μ := volume)).const_mul r
  calc
    ∫ x in u..v, (alpha + r * x) = (∫ x in u..v, alpha) + (∫ x in u..v, r * x) := by
      rw [intervalIntegral.integral_add hint_const hint_rx]
    _ = (∫ x in u..v, alpha) + (r * ∫ x in u..v, x) := by
      rw [intervalIntegral.integral_const_mul r (fun x => x)]
    _ = ((v - u) • alpha) + (r * ((v ^ 2 - u ^ 2) / 2)) := by
      rw [intervalIntegral.integral_const, integral_id]
    _ = alpha * (v - u) + r * (v ^ 2 - u ^ 2) / 2 := by
      simp [smul_eq_mul]
      ring

theorem integral_min_of_ge {alpha r c u v : ℝ} (huv : u ≤ v)
    (h : ∀ x ∈ Set.Icc u v, c ≤ alpha + r * x) :
    ∫ x in u..v, min (alpha + r * x) c = c * (v - u) := by
  have hmin : ∀ x, x ∈ Set.uIcc u v → min (alpha + r * x) c = c := by
    intro x hx
    rw [Set.uIcc_of_le huv] at hx
    exact min_eq_right (h x hx)
  calc
    ∫ x in u..v, min (alpha + r * x) c = ∫ x in u..v, c :=
      intervalIntegral.integral_congr hmin
    _ = (v - u) • c := intervalIntegral.integral_const c
    _ = c * (v - u) := by ring

theorem integral_min_split {alpha r c u s v : ℝ} (hus : u ≤ s) (hsv : s ≤ v) (hr : 0 ≤ r)
    (hs : alpha + r * s = c) :
    ∫ x in u..v, min (alpha + r * x) c =
      (alpha * (s - u) + r * (s ^ 2 - u ^ 2) / 2) + c * (v - s) := by
  have h_cont : Continuous (fun x : ℝ => min (alpha + r * x) c) := by
    refine Continuous.min ?_ ?_
    · exact (continuous_const.add (continuous_const.mul continuous_id))
    · exact continuous_const
  have h_int_us : IntervalIntegrable (fun x : ℝ => min (alpha + r * x) c) volume u s :=
    h_cont.intervalIntegrable u s
  have h_int_sv : IntervalIntegrable (fun x : ℝ => min (alpha + r * x) c) volume s v :=
    h_cont.intervalIntegrable s v
  rw [← intervalIntegral.integral_add_adjacent_intervals h_int_us h_int_sv]
  have h_left : ∫ x in u..s, min (alpha + r * x) c = alpha * (s - u) + r * (s ^ 2 - u ^ 2) / 2 := by
    apply integral_min_of_le hus
    intro x hx
    rcases hx with ⟨hxu, hxs⟩
    nlinarith
  have h_right : ∫ x in s..v, min (alpha + r * x) c = c * (v - s) := by
    apply integral_min_of_ge hsv
    intro x hx
    rcases hx with ⟨hxs, hxv⟩
    nlinarith
  rw [h_left, h_right]

theorem integral_min_nonneg {alpha r c u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (ha : 0 ≤ alpha)
    (hr : 0 ≤ r) (hc : 0 ≤ c) : 0 ≤ ∫ x in u..v, min (alpha + r * x) c := by
  refine intervalIntegral.integral_nonneg huv ?_
  intro x hx
  rcases hx with ⟨hxul, hxur⟩
  have hx_nonneg : 0 ≤ x := le_trans hu hxul
  have h_nonneg : 0 ≤ alpha + r * x := add_nonneg ha (mul_nonneg hr hx_nonneg)
  by_cases h : alpha + r * x ≤ c
  · rw [min_eq_left h]
    exact h_nonneg
  · rw [min_eq_right (by linarith)]
    exact hc

theorem div_le_ceilDiv (F r : Nat) (hr : 0 < r) :
    ((F * F : Nat) : ℝ) / r ≤ ((F * F + r - 1) / r : Nat) := by
  set q := (F * F + r - 1) / r with hq
  have h_lt : F * F + r - 1 < q * r + r := by
    simpa [hq] using Nat.lt_div_mul_add hr (a := F * F + r - 1)
  have h_le : F * F ≤ q * r := by omega
  have h_le' : ((F * F : Nat) : ℝ) ≤ ((q : ℕ) : ℝ) * ((r : ℕ) : ℝ) := by
    have h : ((F * F : ℕ) : ℝ) ≤ ((q * r : ℕ) : ℝ) := by exact_mod_cast h_le
    simpa [Nat.cast_mul] using h
  have h_div : ((F * F : Nat) : ℝ) / (r : ℝ) ≤ ((q : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by exact_mod_cast hr)]
    simpa [Nat.cast_mul] using h_le'
  simpa [hq] using h_div

/-- D9: the cell integral is a lower bound. -/
theorem jcell_le (r a b alpha C : Nat) (hr : 1 ≤ r) (hab : a ≤ b) :
    (jcell r a b alpha C : ℝ) ≤
      2 * (D : ℝ) ^ 2 * ∫ x in (a / D : ℝ)..(b / D), min ((alpha : ℝ) + r * x) ((C : ℝ) / D) := by
  have hD : (0 : ℝ) < D := by exact_mod_cast D_pos
  have hDne : (D : ℝ) ≠ 0 := hD.ne'
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hAB : (a / D : ℝ) ≤ b / D := div_le_div_of_nonneg_right habR hD.le
  have hA0 : (0 : ℝ) ≤ a / D := div_nonneg (Nat.cast_nonneg _) hD.le
  have hS : ((2 * D * alpha * (b - a) + r * (b * b - a * a) : ℕ) : ℝ) =
      2 * D * alpha * ((b : ℝ) - a) + r * ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hab,
      Nat.cast_sub (Nat.mul_le_mul hab hab)]
    push_cast
    ring
  have hlin : 2 * (D : ℝ) ^ 2 * ((alpha : ℝ) * (b / D - a / D) + r * ((b / D : ℝ) ^ 2 - (a / D) ^ 2) / 2) =
      2 * D * alpha * ((b : ℝ) - a) + r * ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) := by
    field_simp
  simp only [jcell]
  split_ifs with h1 h2
  · -- the stop cost is below the continuation on the whole cell
    have h1R : (alpha : ℝ) * D + r * b ≤ C := by exact_mod_cast h1
    rw [integral_min_of_le hAB fun x hx => ?_, hS, hlin]
    rw [le_div_iff₀ hD]
    have : (r : ℝ) * x ≤ r * (b / D) := mul_le_mul_of_nonneg_left hx.2 hr'.le
    have e : (r : ℝ) * (b / D) * D = r * b := by field_simp
    nlinarith
  · have h2R : (C : ℝ) ≤ alpha * D + r * a := by exact_mod_cast h2
    rw [integral_min_of_ge hAB fun x hx => ?_]
    · push_cast [Nat.cast_sub hab]
      field_simp
      ring_nf
      exact le_rfl
    · rw [div_le_iff₀ hD]
      have : (r : ℝ) * (a / D) ≤ r * x := mul_le_mul_of_nonneg_left hx.1 hr'.le
      have e : (r : ℝ) * (a / D) * D = r * a := by field_simp
      nlinarith
  · have h1R : (C : ℝ) < alpha * D + r * b := by
      have : C < alpha * D + r * b := Nat.lt_of_not_le h1
      exact_mod_cast this
    have h2R : (alpha : ℝ) * D + r * a < C := by
      have : alpha * D + r * a < C := Nat.lt_of_not_le h2
      exact_mod_cast this
    set s : ℝ := ((C : ℝ) - alpha * D) / (r * D) with hs_def
    have hfs : (alpha : ℝ) + r * s = C / D := by
      rw [hs_def]; field_simp; ring
    have has : (a / D : ℝ) ≤ s := by
      rw [hs_def, div_le_div_iff₀ hD (mul_pos hr' hD)]; nlinarith
    have hsb : s ≤ b / D := by
      rw [hs_def, div_le_div_iff₀ (mul_pos hr' hD) hD]; nlinarith
    have hint := integral_min_split has hsb hr'.le hfs
    have hval : 2 * (D : ℝ) ^ 2 * ∫ x in (a / D : ℝ)..(b / D), min ((alpha : ℝ) + r * x) ((C : ℝ) / D) =
        (2 * D * alpha * ((b : ℝ) - a) + r * ((b : ℝ) ^ 2 - (a : ℝ) ^ 2)) -
          ((alpha : ℝ) * D + r * b - C) ^ 2 / r := by
      rw [hint, hs_def]
      field_simp
      ring
    have hnn := integral_min_nonneg hA0 hAB (Nat.cast_nonneg alpha) hr'.le
      (div_nonneg (Nat.cast_nonneg C) hD.le)
    have hlt : C < alpha * D + r * b := Nat.lt_of_not_le h1
    have hFR : ((alpha * D + r * b - C : ℕ) : ℝ) = alpha * D + r * b - C := by
      rw [Nat.cast_sub hlt.le]
      push_cast
      ring
    have hceil := div_le_ceilDiv (alpha * D + r * b - C) r (by omega)
    rw [Nat.cast_mul, hFR] at hceil
    rw [hval]
    by_cases hq : ((alpha * D + r * b - C) * (alpha * D + r * b - C) + r - 1) / r ≤
        2 * D * alpha * (b - a) + r * (b * b - a * a)
    · rw [Nat.cast_sub hq, hS]
      have : ((alpha : ℝ) * D + r * b - C) ^ 2 = ((alpha : ℝ) * D + r * b - C) *
          ((alpha : ℝ) * D + r * b - C) := sq _
      rw [this]
      linarith
    · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_le hq), Nat.cast_zero, ← hval]
      exact mul_nonneg (by positivity) hnn

theorem integral_one_sub_pow (u : ℝ) (r : Nat) :
    ∫ x in u..1, (1 - x) ^ r = (1 - u) ^ (r + 1) / (r + 1) := by
  calc
    ∫ x in u..1, (1 - x) ^ r = ∫ x in (1 : ℝ) - 1..(1 : ℝ) - u, x ^ r := by
      rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ r) (1 : ℝ)]
    _ = ∫ x in (0 : ℝ)..(1 - u), x ^ r := by simp
    _ = ((1 - u) ^ (r + 1) - (0 : ℝ) ^ (r + 1)) / (↑r + 1) := by rw [integral_pow]
    _ = ((1 - u) ^ (r + 1) - 0) / (↑r + 1) := by simp
    _ = (1 - u) ^ (r + 1) / (↑r + 1) := by ring
    _ = (1 - u) ^ (r + 1) / (r + 1) := by simp

/-- 6.3: the tail term is a lower bound of the integral of the continuation over `(X / D, 1]`. -/
theorem tailT_le (r m U X EX : Nat) (hX : X < D) :
    (tailT r m U X EX (Epen X (r + 1)) : ℝ) ≤
      2 * (D : ℝ) ^ 2 * ∫ x in (X / D : ℝ)..1, ((1 - x) ^ r + (U : ℝ) / D) := by
  have hDpos : 0 < (D : ℝ) := by
    have : 0 < D := by unfold D; norm_num
    exact_mod_cast this
  have hD_nonneg : 0 ≤ (D : ℝ) := by linarith
  have hXD_le_one : (X : ℝ) / (D : ℝ) ≤ 1 := by
    have hXleD : (X : ℝ) ≤ (D : ℝ) := by exact_mod_cast hX.le
    exact (div_le_one hDpos).mpr hXleD
  unfold tailT
  split_ifs with hcond
  · -- hcond : (decide (X < D) && condT r m U EX X) = true
    have h_and := by simpa using hcond
    rcases h_and with ⟨hX_lt_D, hcondT⟩
    -- Normalize the goal: push Nat.cast inside
    push_cast
    -- Goal: ↑(2 * D * Epen X (r+1) / (r+1)) + 2 * ↑(D-X) * ↑U ≤ 2 * ↑D^2 * ∫ ...
    have h_int_one_sub_pow : ∫ x in (X / D : ℝ)..1, (1 - x) ^ r =
        (1 - (X / D : ℝ)) ^ (r + 1) / ((r : ℝ) + 1) := by
      rw [Robbins.Cert.integral_one_sub_pow]
    have h_int_const : ∫ x in (X / D : ℝ)..1, ((U : ℝ) / (D : ℝ)) =
        (1 - (X / D : ℝ)) * ((U : ℝ) / (D : ℝ)) := by
      rw [intervalIntegral.integral_const]
      simp
    have h_int_add : ∫ x in (X / D : ℝ)..1, ((1 - x) ^ r + (U : ℝ) / (D : ℝ)) =
        (∫ x in (X / D : ℝ)..1, (1 - x) ^ r) + (∫ x in (X / D : ℝ)..1, ((U : ℝ) / (D : ℝ))) := by
      refine intervalIntegral.integral_add ?_ ?_
      · have h_cont : Continuous (fun x : ℝ => (1 - x) ^ r) := by continuity
        exact h_cont.intervalIntegrable _ _
      · have h_cont : Continuous (fun _ : ℝ => (U : ℝ) / (D : ℝ)) := by continuity
        exact h_cont.intervalIntegrable _ _
    have hRHS : 2 * (D : ℝ) ^ 2 * ∫ x in (X / D : ℝ)..1, ((1 - x) ^ r + (U : ℝ) / (D : ℝ)) =
        2 * (D : ℝ) * ((D : ℝ) * (1 - (X : ℝ) / (D : ℝ)) ^ (r + 1)) / ((r : ℝ) + 1) +
        2 * ((D : ℝ) - (X : ℝ)) * (U : ℝ) := by
      rw [h_int_add, h_int_one_sub_pow, h_int_const]
      field_simp [hDpos.ne.symm]
    have h_first_term_le : (↑(2 * D * Epen X (r + 1) / (r + 1)) : ℝ) ≤
        2 * (D : ℝ) * (Epen X (r + 1) : ℝ) / ((r : ℝ) + 1) := by
      simpa [Nat.cast_mul, Nat.cast_add] using
        Nat.cast_div_le (m := 2 * D * Epen X (r + 1)) (n := r + 1)
    have h_second_term_eq : (2 * ↑(D - X) * ↑U : ℝ) = 2 * ((D : ℝ) - (X : ℝ)) * (U : ℝ) := by
      simp [Nat.cast_sub hX.le]
    have h_epen_le : (Epen X (r + 1) : ℝ) ≤ (D : ℝ) * (1 - (X : ℝ) / (D : ℝ)) ^ (r + 1) :=
      Epen_le X (r + 1) hX.le
    have h_first_term_le2 : 2 * (D : ℝ) * (Epen X (r + 1) : ℝ) / ((r : ℝ) + 1) ≤
        2 * (D : ℝ) * ((D : ℝ) * (1 - (X : ℝ) / (D : ℝ)) ^ (r + 1)) / ((r : ℝ) + 1) := by
      have h_nonneg : 0 ≤ (r : ℝ) + 1 := by
        have : 0 ≤ (r : ℝ) := by exact_mod_cast Nat.zero_le r
        linarith
      have h_mul : 2 * (D : ℝ) * (Epen X (r + 1) : ℝ) ≤
          2 * (D : ℝ) * ((D : ℝ) * (1 - (X : ℝ) / (D : ℝ)) ^ (r + 1)) := by
        nlinarith
      exact div_le_div_of_nonneg_right h_mul h_nonneg
    calc
      (↑(2 * D * Epen X (r + 1) / (r + 1)) : ℝ) + 2 * ↑(D - X) * ↑U ≤
          (2 * (D : ℝ) * (Epen X (r + 1) : ℝ) / ((r : ℝ) + 1)) + 2 * ↑(D - X) * ↑U := by
        nlinarith
      _ ≤ (2 * (D : ℝ) * ((D : ℝ) * (1 - (X : ℝ) / (D : ℝ)) ^ (r + 1)) / ((r : ℝ) + 1)) +
          2 * ↑(D - X) * ↑U := by nlinarith
      _ = (2 * (D : ℝ) * ((D : ℝ) * (1 - (X : ℝ) / (D : ℝ)) ^ (r + 1)) / ((r : ℝ) + 1)) +
          2 * ((D : ℝ) - (X : ℝ)) * (U : ℝ) := by rw [h_second_term_eq]
      _ = 2 * (D : ℝ) ^ 2 * ∫ x in (X / D : ℝ)..1, ((1 - x) ^ r + (U : ℝ) / (D : ℝ)) := by rw [hRHS]
  · -- hcond : ¬ (decide (X < D) && condT r m U EX X) = true
    have h_int_nonneg : 0 ≤ ∫ x in (X / D : ℝ)..1, ((1 - x) ^ r + (U : ℝ) / D) := by
      refine intervalIntegral.integral_nonneg hXD_le_one ?_
      intro u hu
      rcases hu with ⟨hu_low, hu_high⟩
      have h1 : 0 ≤ 1 - u := by linarith
      have h2 : 0 ≤ (1 - u) ^ r := pow_nonneg h1 r
      have h3 : 0 ≤ (U : ℝ) / (D : ℝ) :=
        div_nonneg (by exact_mod_cast Nat.zero_le U) hD_nonneg
      nlinarith
    have h_nonneg : 0 ≤ 2 * (D : ℝ) ^ 2 * ∫ x in (X / D : ℝ)..1, ((1 - x) ^ r + (U : ℝ) / D) := by
      nlinarith
    simpa using h_nonneg

end Robbins.Cert
