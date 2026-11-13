import Robbins.Upper.Defs

/-!
# The arithmetic of the threshold rule

`survive N t = (N - t + 1)(N - t) / ((N + 1) N)` (telescoping product), so each time contributes at
most `4 / N` (`term_le`) and the `N` times at most `4` (`sum_le_four`).
-/

namespace Robbins.Threshold

theorem thr_mem (N t : ℕ) (ht : t < N) : 0 ≤ thr N t ∧ thr N t ≤ 1 := by
  have hNt_succ : t.succ ≤ N := Nat.succ_le_of_lt ht
  have hNt_succ' : (t : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hNt_succ
  have hden_pos : 0 < (N : ℝ) - (t : ℝ) + 1 := by linarith
  have hden_ge_two : 2 ≤ (N : ℝ) - (t : ℝ) + 1 := by linarith
  have h0 : 0 ≤ thr N t := by
    unfold thr
    refine div_nonneg (by norm_num) (by linarith)
  have h1 : thr N t ≤ 1 := by
    unfold thr
    exact ((div_le_one hden_pos).mpr hden_ge_two)
  exact And.intro h0 h1

theorem survive_eq (N t : ℕ) (ht : t + 1 ≤ N) :
    survive N t = ((N : ℝ) - t + 1) * ((N : ℝ) - t) / (((N : ℝ) + 1) * N) := by
  induction' t with t ih
  · -- base t = 0
    simp [survive]
    have hN : (N : ℝ) + 1 ≠ 0 := by
      intro h
      have h' : (N : ℕ) + 1 = (0 : ℕ) := by exact_mod_cast h
      omega
    have hN' : (N : ℝ) ≠ 0 := by
      intro h
      have h' : (N : ℕ) = (0 : ℕ) := by exact_mod_cast h
      omega
    field_simp [hN, hN']
  · -- step: t → t+1
    have ht' : t + 1 ≤ N := by omega
    have hpos : (N : ℝ) - (t : ℝ) + 1 ≠ 0 := by
      intro hzero
      have hpos' : (t : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast ht'
      linarith
    rw [survive, Finset.prod_range_succ]
    rw [← survive]
    rw [ih ht']
    unfold thr
    push_cast
    field_simp [hpos]
    ring_nf

theorem term_le (N t : ℕ) (ht : t < N) :
    ((N : ℝ) - 1) * survive N t * thr N t ^ 2 ≤ 4 / N := by
  have hNpos : (0 : ℝ) < N := by
    have h : 0 < N := Nat.zero_lt_of_lt ht
    exact_mod_cast h
  have ht_le : t + 1 ≤ N := Nat.succ_le_of_lt ht
  have ht_lt_N : (t : ℝ) < N := by exact_mod_cast ht
  rw [survive_eq N t ht_le]
  unfold thr
  set r := (N : ℝ) - (t : ℝ) + 1 with hr
  have hrpos : 0 < r := by linarith
  have hN_ne_zero : (N : ℝ) ≠ 0 := by linarith
  have hNp1_ne_zero : (N : ℝ) + 1 ≠ 0 := by linarith
  have hr_ne_zero : r ≠ 0 := by linarith
  field_simp [hN_ne_zero, hNp1_ne_zero, hr_ne_zero]
  rw [hr]
  nlinarith

theorem sum_le_four (N : ℕ) :
    ∑ t ∈ Finset.range N, ((N : ℝ) - 1) * survive N t * thr N t ^ 2 ≤ 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  calc ∑ t ∈ Finset.range N, ((N : ℝ) - 1) * survive N t * thr N t ^ 2
      ≤ ∑ _t ∈ Finset.range N, (4 : ℝ) / N :=
        Finset.sum_le_sum fun t ht => term_le N t (Finset.mem_range.mp ht)
    _ = 4 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

end Robbins.Threshold
