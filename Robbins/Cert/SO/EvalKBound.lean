import Robbins.Cert.SO.EvalKPre

/-!
# The fields of the packed accumulators are below `2 ^ 128`

For a record list `c` of the specification (`RecOK`) and the tables `uhOf d Nn`, `sgOf d Nn`:
`acc_l < 2 ^ 128` (`acc_lt`) and `lam_l ≤ D` (`lam_le`), with `D = DS = 2 ^ 36`. Every chord lies in
`[0, p_i - p_{i-1}]`, the widths telescope to at most `D`, a coefficient is at most `D ^ 2` (a slope
is below `2 ^ 48`, the last coefficient `r E_{t+1}` is at most `D ^ 2` by `Epen_mul_le`), so
`acc_l ≤ D ^ 3 + 2 ^ 49 D`.
-/

namespace Robbins.Cert.SO.K

open Robbins.Cert Robbins.Cert.K

/-- The chord of the specification is at most the width of the cell. -/
theorem bnd_chord_le_width {Pa Pb a0 a1 b0 b1 S : ℤ} (hab : Pa < Pb) (ha1 : 0 < a1)
    (hb1 : 0 ≤ b1) (hS : 0 < S) : SO.chord Pa Pb a0 a1 b0 b1 S ≤ Pb - Pa := by
  have h1 := SO.chord_le (a0 := a0) (b0 := b0) hab ha1 hb1 hS
  have h2 : ∫ X in (Pa : ℝ)..Pb, min 1 (max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X) / S) ≤
      ∫ _ in (Pa : ℝ)..Pb, (1 : ℝ) := by
    apply intervalIntegral.integral_mono_on (by exact_mod_cast hab.le)
    · apply Continuous.intervalIntegrable; fun_prop
    · exact intervalIntegrable_const
    · intro x _; exact min_le_left _ _
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h2
  exact_mod_cast h1.trans h2

/-- A chord of a cell `i` of `P_t` lies in `[0, p_i - p_{i-1}]`. -/
theorem bnd_chord_cell {g : Grid} (hg : ok DS g = true) {t i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ g.L t)
    {a0 a1 b0 b1 S : ℤ} (ha1 : 0 < a1) (hb1 : 0 ≤ b1) (hS : 0 < S) :
    0 ≤ SO.chord (cp DS g t (i - 1)) (cp DS g t i) a0 a1 b0 b1 S ∧
      SO.chord (cp DS g t (i - 1)) (cp DS g t i) a0 a1 b0 b1 S ≤
        (cp DS g t i : ℤ) - cp DS g t (i - 1) := by
  have hlt : cp DS g t (i - 1) < cp DS g t i := g.so_cp_lt_cp DS hg (by omega) hiL
  exact ⟨so_chord_nonneg (by exact_mod_cast hlt.le) hS,
    bnd_chord_le_width (by exact_mod_cast hlt) ha1 hb1 hS⟩

theorem bnd_DS_pos : 0 < DS := by
  unfold DS
  norm_num

/-- A slope of a table is below `2 ^ 48`. -/
theorem bnd_sgOf_lt (d : ℕ) (Nn : List ℕ) (k : Fin (d + 1) → ℕ) (l : Fin (d + 1)) :
    sgOf d Nn k l < 2 ^ 48 := by
  unfold sgOf
  exact Nat.mod_lt _ (by positivity)

variable {g : Grid} {d t : ℕ} {Nn : List ℕ} {c : Fin (d + 1) → Rec}

/-- `QC_i ∈ [0, p_i - p_{i-1}]`. -/
theorem bnd_QC (hg : ok DS g = true) (htn : t < g.n) {i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ g.L t) :
    0 ≤ QC DS g d (uhOf d Nn) (sgOf d Nn) t c i ∧
      QC DS g d (uhOf d Nn) (sgOf d Nn) t c i ≤ (cp DS g t i : ℤ) - cp DS g t (i - 1) := by
  have hw : (0 : ℤ) ≤ (cp DS g t i : ℤ) - cp DS g t (i - 1) := by
    have := g.so_cp_mono DS hg (Nat.sub_le i 1) hiL
    omega
  have ha1 : (0 : ℤ) < (((g.n - t) * DS : ℕ) : ℤ) := by
    have := bnd_DS_pos
    have : 0 < (g.n - t) * DS := Nat.mul_pos (by omega) this
    exact_mod_cast this
  unfold QC
  split_ifs with hS
  · exact bnd_chord_cell hg hi1 hiL ha1 (by unfold sigmaC; positivity) hS
  · exact ⟨le_rfl, hw⟩

/-- `QT_i ∈ [0, p_i - p_{i-1}]`. -/
theorem bnd_QT (hg : ok DS g = true) (htn : t < g.n) {i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ g.L t) :
    0 ≤ QT DS g d (uhOf d Nn) (sgOf d Nn) t c i ∧
      QT DS g d (uhOf d Nn) (sgOf d Nn) t c i ≤ (cp DS g t i : ℤ) - cp DS g t (i - 1) := by
  have hw : (0 : ℤ) ≤ (cp DS g t i : ℤ) - cp DS g t (i - 1) := by
    have := g.so_cp_mono DS hg (Nat.sub_le i 1) hiL
    omega
  have ha1 : (0 : ℤ) < (((g.n - t) * DS : ℕ) : ℤ) := by
    have := bnd_DS_pos
    have : 0 < (g.n - t) * DS := Nat.mul_pos (by omega) this
    exact_mod_cast this
  unfold QT
  split_ifs with hS
  · exact bnd_chord_cell hg hi1 hiL ha1 (by positivity) hS
  · exact ⟨le_rfl, hw⟩

/-- A coefficient is at most `D ^ 2`. -/
theorem bnd_coefC_le (hg : ok DS g = true) (i : ℕ) (l : Fin (d + 1)) :
    coefC DS g d (sgOf d Nn) t c i l ≤ (DS : ℤ) * DS := by
  have hsl : ∀ (k : Fin (d + 1) → ℕ) (j : Fin (d + 1)), ((sgOf d Nn k j : ℕ) : ℤ) ≤ (DS : ℤ) * DS := by
    intro k j
    have h1 := bnd_sgOf_lt d Nn k j
    have h2 : (2 : ℕ) ^ 48 ≤ DS * DS := by unfold DS; norm_num
    exact_mod_cast (h1.le.trans h2)
  have hD2 : (0 : ℤ) ≤ (DS : ℤ) * DS := by positivity
  unfold coefC
  split_ifs
  · exact hD2
  · have hz1 : 1 ≤ pt DS g (c (Fin.last d)).gi := g.so_pt_pos DS hg _
    have hzD : pt DS g (c (Fin.last d)).gi ≤ DS := g.so_pt_le_D DS hg _
    have hE := Epen_mul_le DS (pt DS g (c (Fin.last d)).gi) (g.n - t - 1) hz1 hzD
    have hr : g.n - t ≤ DS + (g.n - t - 1) := by have := bnd_DS_pos; omega
    have h : (g.n - t) * Epen DS (pt DS g (c (Fin.last d)).gi) (g.n - t - 1) ≤ DS * DS := by
      calc (g.n - t) * Epen DS (pt DS g (c (Fin.last d)).gi) (g.n - t - 1)
          ≤ (DS + (g.n - t - 1)) * Epen DS (pt DS g (c (Fin.last d)).gi) (g.n - t - 1) :=
            Nat.mul_le_mul_right _ hr
        _ = Epen DS (pt DS g (c (Fin.last d)).gi) (g.n - t - 1) * (DS + (g.n - t - 1)) :=
            Nat.mul_comm _ _
        _ ≤ DS * DS := hE
    exact_mod_cast h
  · exact hD2
  · exact hsl _ _
  · exact hD2
  · exact hsl _ _

/-- `jT ≤ L`. -/
theorem bnd_jT_le (hc : RecOK DS g t c) :
    jT DS g d (uhOf d Nn) (sgOf d Nn) t c ≤ g.L t := by
  have him : im d c ≤ g.L t := hc.pos_le (Fin.last d)
  unfold jT
  generalize hf : List.find? _ (List.range' (im d c) (g.L t - im d c)) = o
  cases o with
  | none => exact le_rfl
  | some j =>
    have hm := List.mem_of_find?_eq_some hf
    rw [List.mem_range'_1] at hm
    show j ≤ g.L t
    omega

/-- The sum of the widths of the cells `a + 1, ..., b` is `p_b - p_a`. -/
theorem bnd_sum_width (a b : ℕ) (hab : a ≤ b) :
    ∑ i ∈ Finset.Ioc a b, ((cp DS g t i : ℤ) - cp DS g t (i - 1)) =
      (cp DS g t b : ℤ) - cp DS g t a :=
  sum_Ioc_sub (fun i => (cp DS g t i : ℤ)) hab

/-- `acc_l < 2 ^ 128`: at most `D ^ 2` per unit of the chord, and the chords sum to at most `D`. -/
theorem acc_lt (hg : ok DS g = true) (htn : t < g.n) (hc : RecOK DS g t c) (l : Fin (d + 1)) :
    acc DS g d (uhOf d Nn) (sgOf d Nn) t c l < F128 := by
  have him : im d c ≤ g.L t := hc.pos_le (Fin.last d)
  have hjT := bnd_jT_le (Nn := Nn) hc
  have hD : (0 : ℤ) ≤ DS := by positivity
  have hcpD : ∀ i, (cp DS g t i : ℤ) ≤ DS := fun i => by exact_mod_cast g.so_cp_le_D DS hg t i
  have hcp0 : ∀ i, (0 : ℤ) ≤ cp DS g t i := fun i => by positivity
  -- the cells `1 .. im`
  have h1 : ∑ i ∈ Finset.Icc 1 (im d c),
      coefC DS g d (sgOf d Nn) t c i l * QC DS g d (uhOf d Nn) (sgOf d Nn) t c i ≤
      (DS : ℤ) * DS * DS := by
    calc ∑ i ∈ Finset.Icc 1 (im d c),
          coefC DS g d (sgOf d Nn) t c i l * QC DS g d (uhOf d Nn) (sgOf d Nn) t c i
        ≤ ∑ i ∈ Finset.Icc 1 (im d c),
            (DS : ℤ) * DS * ((cp DS g t i : ℤ) - cp DS g t (i - 1)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
          obtain ⟨hq0, hq1⟩ := bnd_QC (c := c) (Nn := Nn) hg htn hi1 (hi2.trans him)
          exact mul_le_mul (bnd_coefC_le hg i l) hq1 hq0 (by positivity)
      _ = (DS : ℤ) * DS * ((cp DS g t (im d c) : ℤ) - cp DS g t 0) := by
          have hI : Finset.Icc 1 (im d c) = Finset.Ioc 0 (im d c) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
          rw [← Finset.mul_sum, hI, bnd_sum_width 0 (im d c) (Nat.zero_le _)]
      _ ≤ (DS : ℤ) * DS * DS := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := hcp0 0
          linarith [hcpD (im d c)]
  -- the tail
  have hQT : ∑ i ∈ Finset.Ioc (im d c) (jT DS g d (uhOf d Nn) (sgOf d Nn) t c),
      QT DS g d (uhOf d Nn) (sgOf d Nn) t c i ≤ DS := by
    by_cases hij : im d c ≤ jT DS g d (uhOf d Nn) (sgOf d Nn) t c
    · calc ∑ i ∈ Finset.Ioc (im d c) (jT DS g d (uhOf d Nn) (sgOf d Nn) t c),
            QT DS g d (uhOf d Nn) (sgOf d Nn) t c i
          ≤ ∑ i ∈ Finset.Ioc (im d c) (jT DS g d (uhOf d Nn) (sgOf d Nn) t c),
              ((cp DS g t i : ℤ) - cp DS g t (i - 1)) := by
            refine Finset.sum_le_sum fun i hi => ?_
            obtain ⟨hi1, hi2⟩ := Finset.mem_Ioc.mp hi
            exact (bnd_QT (c := c) (Nn := Nn) hg htn (by omega) (hi2.trans hjT)).2
        _ = (cp DS g t (jT DS g d (uhOf d Nn) (sgOf d Nn) t c) : ℤ) - cp DS g t (im d c) :=
            bnd_sum_width _ _ hij
        _ ≤ DS := by linarith [hcpD (jT DS g d (uhOf d Nn) (sgOf d Nn) t c), hcp0 (im d c)]
    · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
      exact hD
  have hE : (if cp DS g t (jT DS g d (uhOf d Nn) (sgOf d Nn) t c) < DS then
      ((DS - cp DS g t (jT DS g d (uhOf d Nn) (sgOf d Nn) t c) : ℕ) : ℤ) else 0) ≤ DS := by
    split_ifs
    · exact_mod_cast Nat.sub_le _ _
    · exact hD
  have h2 : (if (c (Fin.last d)).forg then 0
      else (sgOf d Nn (fun l => (c l).map) l : ℤ) *
        (∑ i ∈ Finset.Ioc (im d c) (jT DS g d (uhOf d Nn) (sgOf d Nn) t c),
            QT DS g d (uhOf d Nn) (sgOf d Nn) t c i +
          if cp DS g t (jT DS g d (uhOf d Nn) (sgOf d Nn) t c) < DS then
            ((DS - cp DS g t (jT DS g d (uhOf d Nn) (sgOf d Nn) t c) : ℕ) : ℤ)
          else 0)) ≤ 2 ^ 48 * (2 * DS) := by
    by_cases hf : (c (Fin.last d)).forg = true
    · rw [ite_eq_left hf]
      positivity
    · rw [ite_eq_right hf]
      have hs : ((sgOf d Nn (fun l => (c l).map) l : ℕ) : ℤ) ≤ 2 ^ 48 := by
        exact_mod_cast (bnd_sgOf_lt d Nn _ l).le
      calc (sgOf d Nn (fun l => (c l).map) l : ℤ) *
            (∑ i ∈ Finset.Ioc (im d c) (jT DS g d (uhOf d Nn) (sgOf d Nn) t c),
                QT DS g d (uhOf d Nn) (sgOf d Nn) t c i +
              if cp DS g t (jT DS g d (uhOf d Nn) (sgOf d Nn) t c) < DS then
                ((DS - cp DS g t (jT DS g d (uhOf d Nn) (sgOf d Nn) t c) : ℕ) : ℤ)
              else 0)
          ≤ (sgOf d Nn (fun l => (c l).map) l : ℤ) * (2 * DS) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ 2 ^ 48 * (2 * DS) := mul_le_mul_of_nonneg_right hs (by positivity)
  have hF : (DS : ℤ) * DS * DS + 2 ^ 48 * (2 * DS) < F128 := by
    unfold DS F128
    norm_num
  unfold acc
  linarith

/-- `lam_l ≤ D`: only the own cell of the record `l` credits it. -/
theorem lam_le (l : Fin (d + 1)) : lam DS g d (uhOf d Nn) (sgOf d Nn) t c l ≤ DS :=
  lam_le_D DS g d (uhOf d Nn) (sgOf d Nn) t c l

end Robbins.Cert.SO.K
