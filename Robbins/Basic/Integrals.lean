import Mathlib

/-!
# Integrals over `[0, 1]` used by the sanity checks
-/

namespace Robbins

open MeasureTheory Set

theorem integral_Icc_ite_lt {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    ∫ a in Set.Icc (0 : ℝ) 1, (if a < c then (1 : ℝ) else 0) = c := by
  have hc0 : (0 : ℝ) ≤ c := hc.1
  have hc1 : c ≤ 1 := hc.2
  have hmeas : MeasurableSet (Iio c) := measurableSet_Iio
  -- rewrite the integrand as an indicator
  have h_indicator : (fun (a : ℝ) => (if a < c then (1 : ℝ) else 0)) = (Iio c).indicator (fun _ => (1 : ℝ)) := by
    ext a
    simp [Set.indicator, Set.mem_Iio]
  rw [h_indicator]
  -- use setIntegral_indicator to move the indicator outside the integral
  rw [MeasureTheory.setIntegral_indicator hmeas]
  -- now we have ∫ a in (Icc 0 1) ∩ (Iio c), (1 : ℝ)
  -- the intersection is Ico 0 c
  have h_inter : (Icc (0 : ℝ) 1) ∩ Iio c = Ico (0 : ℝ) c := by
    ext x
    constructor
    · rintro ⟨⟨hx0, hx1⟩, hxc⟩
      exact ⟨hx0, hxc⟩
    · rintro ⟨hx0, hxc⟩
      have hx1 : x ≤ 1 := by
        -- x < c and c ≤ 1, so x ≤ 1
        linarith
      exact ⟨⟨hx0, hx1⟩, hxc⟩
  rw [h_inter]
  -- now ∫ a in Ico 0 c, (1 : ℝ)
  rw [MeasureTheory.setIntegral_const (1 : ℝ)]
  -- this gives volume.real (Ico 0 c) • (1 : ℝ) = volume.real (Ico 0 c)
  simp [hc0]

theorem integral_Icc_ite_gt {c : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    ∫ a in Set.Icc (0 : ℝ) 1, (if c < a then (1 : ℝ) else 0) = 1 - c := by
  have hc0 : 0 ≤ c := hc.1
  have hc1 : c ≤ 1 := hc.2
  have h_nonneg : 0 ≤ 1 - c := by linarith
  have h_inter : (Set.Icc (0 : ℝ) 1) ∩ Set.Ioi c = Set.Ioc c 1 := by
    ext x
    constructor
    · intro ⟨⟨hx0, hx1⟩, hx_gt⟩
      exact ⟨hx_gt, hx1⟩
    · intro ⟨hx_gt, hx1⟩
      have hx0 : 0 ≤ x := by linarith
      exact ⟨⟨hx0, hx1⟩, hx_gt⟩
  calc
    ∫ a in Set.Icc (0 : ℝ) 1, (if c < a then (1 : ℝ) else 0)
        = ∫ a in Set.Icc (0 : ℝ) 1, (Set.Ioi c).indicator (fun _ => (1 : ℝ)) a := by
      refine (MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_).symm
      intro a ha
      simp [Set.indicator, Set.mem_Ioi]
    _ = ∫ a in (Set.Icc (0 : ℝ) 1) ∩ Set.Ioi c, (fun _ => (1 : ℝ)) a := by
      rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi]
    _ = ∫ a in Set.Ioc c 1, (1 : ℝ) := by rw [h_inter]
    _ = (volume.real (Set.Ioc c 1)) • (1 : ℝ) := by rw [MeasureTheory.setIntegral_const]
    _ = volume.real (Set.Ioc c 1) := by simp
    _ = (volume (Set.Ioc c 1)).toReal := rfl
    _ = (ENNReal.ofReal (1 - c)).toReal := by rw [Real.volume_Ioc]
    _ = 1 - c := by rw [ENNReal.toReal_ofReal h_nonneg]

theorem integral_min_one_add_two_sub :
    ∫ a in Set.Icc (0 : ℝ) 1, min (1 + a) (2 - a) = 5 / 4 := by
  -- convert Icc integral to interval integral
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  -- integrability from continuity
  have hcont : Continuous (fun (a : ℝ) => min (1 + a) (2 - a)) := by
    refine Continuous.min ?_ ?_
    · exact (continuous_const.add continuous_id)
    · exact (continuous_const.sub continuous_id)
  have hint : IntervalIntegrable (fun (a : ℝ) => min (1 + a) (2 - a)) volume 0 (1/2) :=
    hcont.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun (a : ℝ) => min (1 + a) (2 - a)) volume (1/2) 1 :=
    hcont.intervalIntegrable _ _
  -- split at 1/2
  rw [← intervalIntegral.integral_add_adjacent_intervals hint hint2]
  -- on [0, 1/2], min(1+a, 2-a) = 1+a
  have hleft : ∫ a in (0 : ℝ)..(1/2 : ℝ), min (1 + a) (2 - a) = ∫ a in (0 : ℝ)..(1/2 : ℝ), (1 + a) := by
    refine intervalIntegral.integral_congr ?_
    intro a ha
    have ha' : a ∈ Set.Icc (0 : ℝ) (1/2) := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/2)] at ha
      exact ha
    rcases ha' with ⟨ha0, ha1⟩
    have h : 1 + a ≤ 2 - a := by linarith
    exact min_eq_left h
  -- on [1/2, 1], min(1+a, 2-a) = 2-a
  have hright : ∫ a in (1/2 : ℝ)..(1 : ℝ), min (1 + a) (2 - a) = ∫ a in (1/2 : ℝ)..(1 : ℝ), (2 - a) := by
    refine intervalIntegral.integral_congr ?_
    intro a ha
    have ha' : a ∈ Set.Icc (1/2 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ha
      exact ha
    rcases ha' with ⟨ha0, ha1⟩
    have h : 2 - a ≤ 1 + a := by linarith
    exact min_eq_right h
  rw [hleft, hright]
  -- compute the two integrals
  have h_int_const_01 : IntervalIntegrable (fun (_ : ℝ) => (1 : ℝ)) volume 0 (1/2) :=
    intervalIntegrable_const
  have h_int_id_01 : IntervalIntegrable (fun (x : ℝ) => x) volume 0 (1/2) :=
    intervalIntegral.intervalIntegrable_id
  have h_int_const_12 : IntervalIntegrable (fun (_ : ℝ) => (2 : ℝ)) volume (1/2) 1 :=
    intervalIntegrable_const
  have h_int_id_12 : IntervalIntegrable (fun (x : ℝ) => x) volume (1/2) 1 :=
    intervalIntegral.intervalIntegrable_id
  rw [intervalIntegral.integral_add h_int_const_01 h_int_id_01,
    intervalIntegral.integral_sub h_int_const_12 h_int_id_12]
  rw [intervalIntegral.integral_const, integral_id, intervalIntegral.integral_const, integral_id]
  ring_nf

end Robbins
