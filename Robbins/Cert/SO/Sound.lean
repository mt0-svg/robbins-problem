import Robbins.Cert.SO.SoundList
import Robbins.Relax.TheoremB

/-!
# Soundness of second-order tables bounded by the specification

Theorem 4.3 and Corollary B.4 of the paper (section 8 of Robbins/Cert/SO/Spec.lean): integer tables of values `uh t` and nonnegative slopes `sg t`
(units `1 / D`, sorted tuples of local indices of `G_t`) with (last) the values of section 4 as
upper bounds and (step) the bound of every record list of section 6 (Robbins/Cert/SO/Spec.lean) as
an upper bound, give the relaxed sub-solution

`u_t (y) = uh_t (k) / D + sum over l of (sg_t (k)_l / D) (G_l - y_l)`, `k = ceil_t (y)`,
`G_l = pt (glob t (k_l)) / D`,

hence `uh_1 (cnt_1, ..., cnt_1) / D ≤ v n` by Theorem B.

The kernel evaluator proves (last) and (step) for its tables (Robbins/Cert/SO/EvalKChain.lean); this
file proves that they give the relaxed sub-solution.
-/

namespace Robbins.Cert.SO

open MeasureTheory Robbins.Cert

/-- Tables bounded by the specification give a relaxed sub-solution. -/
theorem relaxed_of_tables (D : ℕ) (hD : 0 < D) (g : Grid) (hg : ok D g = true) (d : ℕ)
    (uh : ℕ → (Fin (d + 1) → ℕ) → ℕ) (sg : ℕ → (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ)
    (hlast : ∀ k, g.IsState g.n k → uh g.n k + ∑ l, pt D g (g.glob g.n (k l)) ≤ (d + 2) * D ∧
      ∀ l, sg g.n k l ≤ if k l < g.cnt g.n then D else 0)
    (hstep : ∀ t, 1 ≤ t → t < g.n → ∀ k, g.IsState t k → ∀ x, ValidChoice g t x →
      (uh t k : ℤ) ≤ (bound D g d (uh (t + 1)) (sg (t + 1)) t (recList D g t k x)).1 ∧
        ∀ l, (sg t k l : ℤ) ≤ (bound D g d (uh (t + 1)) (sg (t + 1)) t (recList D g t k x)).2 l) :
    ∃ u : RelaxedSubSolution g.n (d + 1), ∀ t y, u.u t y = uSO D g d uh sg t y := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hstate : ∀ t {y : Fin (d + 1) → ℝ}, IsMemory y →
      g.IsState t (fun l => ceilR D g t (y l)) := fun t y hy =>
    ⟨fun l l' h => g.so_ceilR_mono D t (hy.1 h), fun l => g.so_ceilR_le_cnt D t (y l)⟩
  have hGy : ∀ t {y : Fin (d + 1) → ℝ}, IsMemory y → ∀ l,
      0 ≤ (pt D g (g.glob t (ceilR D g t (y l))) : ℝ) / D - y l := by
    intro t y hy l
    have h := g.so_le_pt_ceilR D hD t (hy.2 l).2
    rw [sub_nonneg, le_div_iff₀ hDr]
    exact h
  refine ⟨{ u := uSO D g d uh sg, measurable := fun t _ _ => measurable_uSO d uh sg t,
            bounded := ?_, last := ?_, step := ?_ }, fun t y => rfl⟩
  · intro t _ _
    obtain ⟨C, _, hC⟩ := abs_uSO_le hg d uh sg t
    exact ⟨C, hC⟩
  · -- (R_n)
    intro y hy
    set k : Fin (d + 1) → ℕ := fun l => ceilR D g g.n (y l) with hk
    obtain ⟨hl1, hl2⟩ := hlast k (hstate g.n hy)
    have hy0 : ∀ l, 0 ≤ y l := fun l => (hy.2 l).1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      integral_relaxStop g.n g.n y hy0 zero_le_one]
    have hmax : ∀ l, max 0 (1 - y l) = 1 - y l :=
      fun l => max_eq_right (by linarith [(hy.2 l).2])
    simp only [hmax, sub_self, zero_mul, zero_div, add_zero]
    show (uh g.n k : ℝ) / D + ∑ l, (sg g.n k l : ℝ) / D *
      ((pt D g (g.glob g.n (k l)) : ℝ) / D - y l) ≤ 1 + ∑ l, (1 - y l)
    have hterm : ∀ l, (sg g.n k l : ℝ) / D * ((pt D g (g.glob g.n (k l)) : ℝ) / D - y l) ≤
        (pt D g (g.glob g.n (k l)) : ℝ) / D - y l := by
      intro l
      have hs : (sg g.n k l : ℝ) / D ≤ 1 := by
        rw [div_le_one hDr]
        have := hl2 l
        split_ifs at this
        · exact_mod_cast this
        · have h0 : sg g.n k l = 0 := by omega
          rw [h0, Nat.cast_zero]
          exact hDr.le
      have hG := hGy g.n hy l
      calc _ ≤ 1 * ((pt D g (g.glob g.n (k l)) : ℝ) / D - y l) :=
            mul_le_mul_of_nonneg_right hs hG
        _ = _ := one_mul _
    have huh : (uh g.n k : ℝ) / D ≤ ((d : ℝ) + 2) - ∑ l, (pt D g (g.glob g.n (k l)) : ℝ) / D := by
      have h : (uh g.n k : ℝ) + ∑ l, (pt D g (g.glob g.n (k l)) : ℝ) ≤ ((d : ℝ) + 2) * D := by
        exact_mod_cast hl1
      rw [← Finset.sum_div, div_le_iff₀ hDr, sub_mul, div_mul_cancel₀ _ hDr.ne']
      linarith
    have hsum := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hterm l
    rw [Finset.sum_sub_distrib] at hsum
    have hcard : ∑ l : Fin (d + 1), (1 - y l) = ((d : ℝ) + 1) - ∑ l, y l := by
      rw [Finset.sum_sub_distrib]
      simp
    rw [hcard]
    linarith
  · -- (R_t)
    intro t ht1 htn y hy
    set k : Fin (d + 1) → ℕ := fun l => ceilR D g t (y l) with hk
    have hks := hstate t hy
    set x : Fin (d + 1) → ℕ := fun l => choiceOf D g t (y l) with hx
    have hxv : ValidChoice g t x := choiceOf_valid hy
    have hc := recList_ok (D := D) hg ht1 htn hks hxv
    have hfit : Fits D g t (recList D g t k x) y := fits_choice hg ht1 htn hy
    have hb := bound_le_integral hg ht1 htn hy hc hfit uh sg
    obtain ⟨hT, hmu⟩ := hstep t ht1 htn k hks x hxv
    -- the forgotten coordinates have slope `0` (the all-`J` choice)
    have hJv : ValidChoice g t (fun _ : Fin (d + 1) => g.J) :=
      ⟨fun _ _ _ => le_rfl, fun _ => Or.inr rfl⟩
    have hzero : ∀ l, k l = g.cnt t → sg t k l = 0 := by
      intro l hl
      have h := (hstep t ht1 htn k hks _ hJv).2 l
      have hJn : g.J ∉ newPts g t := fun hm => lt_irrefl _ ((g.mem_newPts).mp hm).1
      have hrec : recList D g t k (fun _ => g.J) l = locRec D g t (k l) := by
        unfold recList
        rw [ite_eq_right (fun h => hJn h.2)]
      have hforg : (recList D g t k (fun _ => g.J) l).forg = true := by
        rw [hrec]
        simp [locRec, hl]
      simp only [bound, hforg, ite_true] at h
      omega
    show uSO D g d uh sg t y ≤ ∫ x in Set.Icc (0 : ℝ) 1, integrandSO D g d uh sg t y x
    refine le_trans ?_ hb
    unfold uSO
    dsimp only
    apply add_le_add
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hT) hDr.le
    · apply Finset.sum_le_sum
      intro l _
      have hw := recList_w_pos (D := D) (x := x) hg ht1 htn hks l
      by_cases hl : k l < g.cnt t
      · rw [ite_eq_left (hw.mpr hl)]
        have hrec : recList D g t k x l = locRec D g t (k l) := by
          unfold recList
          rw [ite_eq_right (fun h => absurd h.1 hl.ne)]
        rw [hrec]
        simp only [locRec]
        apply mul_le_mul_of_nonneg_right _ (hGy t hy l)
        exact div_le_div_of_nonneg_right (by exact_mod_cast hmu l) hDr.le
      · have hl' : k l = g.cnt t := le_antisymm (hks.2 l) (not_lt.mp hl)
        rw [ite_eq_right (fun h => hl (hw.mp h)), hzero l hl']
        simp

/-- Theorem B for the second-order tables: `uh_1 (cnt_1, ..., cnt_1) / D ≤ v n`. -/
theorem le_v_of_tables (D : ℕ) (hD : 0 < D) (g : Grid) (hg : ok D g = true) (d : ℕ)
    (uh : ℕ → (Fin (d + 1) → ℕ) → ℕ) (sg : ℕ → (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ)
    (hlast : ∀ k, g.IsState g.n k → uh g.n k + ∑ l, pt D g (g.glob g.n (k l)) ≤ (d + 2) * D ∧
      ∀ l, sg g.n k l ≤ if k l < g.cnt g.n then D else 0)
    (hstep : ∀ t, 1 ≤ t → t < g.n → ∀ k, g.IsState t k → ∀ x, ValidChoice g t x →
      (uh t k : ℤ) ≤ (bound D g d (uh (t + 1)) (sg (t + 1)) t (recList D g t k x)).1 ∧
        ∀ l, (sg t k l : ℤ) ≤ (bound D g d (uh (t + 1)) (sg (t + 1)) t (recList D g t k x)).2 l) :
    (uh 1 (fun _ => g.cnt 1) : ℝ) / D ≤ v g.n := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  obtain ⟨u, hu⟩ := relaxed_of_tables D hD g hg d uh sg hlast hstep
  have h := u.val_one_le_v (by have := g.so_ok_two_le_n D hg; omega)
  rw [hu] at h
  unfold uSO at h
  simp only [g.so_ceilR_one D hg 1] at h
  have hpt : (pt D g (g.glob 1 (g.cnt 1)) : ℝ) / D - 1 = 0 := by
    rw [g.glob_of_ge le_rfl, g.so_pt_of_ge D le_rfl, div_self hDr.ne', sub_self]
  simp only [hpt, mul_zero, Finset.sum_const_zero, add_zero] at h
  exact h

end Robbins.Cert.SO
