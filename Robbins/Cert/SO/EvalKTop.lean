import Robbins.Cert.SO.EvalKPre
import Robbins.Cert.SO.EvalKBound

/-!
# The kernel evaluator of one record list against `bound`

`checkVar c lk uh sg p top` checks a claimed state `(uh, sg)` against the output of section 5 on the
record list `p.rs ++ [top]` (`evalTop`). For the record list of the kernel records of a record list
`c` of the specification (`RecOK`), with a lookup `lk` that reads the table of time `t + 1` at the
rank of every state of `G_{t+1}`, the accumulators of `evalTop` are `Rtot`, `acc` and `lam` of
Robbins/Cert/SO/Spec.lean (`evalTop_spec`), each field of `acc` and `lam` is below `2 ^ 128`
(`acc_lt`, `lam_le` in EvalKBound.lean), so a passed check gives `uh ≤ T0` and `sg_l ≤ mu_l` (`checkVar_sound`).
-/

namespace Robbins.Cert.SO.K

open Robbins.Cert Robbins.Cert.K

/-! ## Arithmetic -/

/-- The chord of the specification is at most the width of the cell. -/
theorem so_chord_le_sub {Pa Pb a0 a1 b0 b1 S : ℤ} (hab : Pa < Pb) (ha1 : 0 < a1) (hb1 : 0 ≤ b1)
    (hS : 0 < S) : SO.chord Pa Pb a0 a1 b0 b1 S ≤ Pb - Pa := by
  have h1 := SO.chord_le (a0 := a0) (b0 := b0) hab ha1 hb1 hS
  have h2 : ∫ X in (Pa : ℝ)..Pb, min 1 (max 0 ((a0 : ℝ) - b0 + (a1 + b1) * X) / S) ≤
      ∫ _ in (Pa : ℝ)..Pb, (1 : ℝ) := by
    apply intervalIntegral.integral_mono_on (by exact_mod_cast hab.le)
    · apply Continuous.intervalIntegrable; fun_prop
    · exact intervalIntegrable_const
    · intro x _; exact min_le_left _ _
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h2
  exact_mod_cast h1.trans h2

/-! ## The last record -/

section Defs

variable (g : Grid) (d t : ℕ) (Nn : List ℕ) (c : Fin (d + 1) → Rec)

/-- The kernel record of the last record. -/
noncomputable def topOf : SR := toSR g t (c (Fin.last d))

/-- The constants of the last record, as `evalTop` builds them. -/
noncomputable def tpOf : Tp :=
  Tp.mk (Nat.mul DS (topOf g d t c).em)
    (bsel (topOf g d t c).fg 0 (Nat.mul (topOf g d t c).pm (topOf g d t c).dl))
    (bsel (topOf g d t c).fg 0 (Nat.mul (topOf g d t c).pm (mkCtx g t).FT)) (topOf g d t c).pos
    (bsel (topOf g d t c).fg 0 (mkCtx g t).FT)

/-- `Q_i` of a cell `i ≤ im`, as a natural number. -/
noncomputable def QN (i : ℕ) : ℕ := (QC DS g d (uhOf d Nn) (sgOf d Nn) t c i).toNat

/-- The packed coefficients of the cell `i`. -/
noncomputable def cPN (i : ℕ) : ℕ := ∑ l : Fin (d + 1), coefN g d t Nn c i l * F128 ^ (l : ℕ)

/-- The packed own-cell credits of the cell `i`. -/
noncomputable def lamP (i : ℕ) : ℕ :=
  ∑ l : Fin (d + 1), (lamC DS g d (uhOf d Nn) (sgOf d Nn) t c i l).toNat * F128 ^ (l : ℕ)

/-- The packed slopes of the tail state `Hc = map`. -/
noncomputable def slcP : ℕ := ∑ l : Fin (d + 1), sgOf d Nn (fun l => (c l).map) l * F128 ^ (l : ℕ)

/-- The first boundary `j' ≥ j` that passes the test of section 5.4, `L` if there is none
(`jT = jF im`). -/
noncomputable def jF (j : ℕ) : ℕ :=
  (((List.range' j (g.L t - j)).find? fun j =>
    decide ((((d + 2) * DS * DS + (g.n - t) * DS * cp DS g t j : ℕ) : ℤ) ≥
      (DS : ℤ) * (Epen DS (cp DS g t j) (g.n - t) + (g.n - t) : ℕ) +
        UT DS g d (uhOf d Nn) (sgOf d Nn) t c + ST d (sgOf d Nn) c)).getD (g.L t))

/-- The exact tail from the boundary `j` (`RE = REj jT`). -/
noncomputable def REj (j : ℕ) : ℤ :=
  if cp DS g t j < DS then
    ((2 * DS * DS * Epen DS (cp DS g t j) (g.n - t + 1) / (g.n - t + 1) : ℕ) : ℤ) +
      2 * ((DS - cp DS g t j : ℕ) : ℤ) * UT DS g d (uhOf d Nn) (sgOf d Nn) t c
  else 0

/-- `QT_i` of a tail cell, as a natural number. -/
noncomputable def QTN (i : ℕ) : ℕ := (QT DS g d (uhOf d Nn) (sgOf d Nn) t c i).toNat

/-- The chord of the exact tail from the boundary `j`. -/
noncomputable def ExN (j : ℕ) : ℕ := if cp DS g t j < DS then DS - cp DS g t j else 0

end Defs

variable {g : Grid} {d t : ℕ} {Nn : List ℕ} {c : Fin (d + 1) → Rec}

theorem jT_eq : jT DS g d (uhOf d Nn) (sgOf d Nn) t c = jF g d t Nn c (im d c) := rfl

theorem RE_eq : RE DS g d (uhOf d Nn) (sgOf d Nn) t c = REj g d t Nn c (jF g d t Nn c (im d c)) := rfl

/-! ## The cells `1, ..., im` -/

/-- `D > 0`. -/
theorem DS_pos : 0 < DS := by norm_num [DS]

/-- `DS2 = D ^ 2`. -/
theorem DS2_eq : DS2 = DS * DS := by norm_num [DS2, DS]

/-- `coef` of the last record. -/
theorem coefN_last (hc : RecOK DS g t c) (i : ℕ) :
    coefN g d t Nn c i (Fin.last d) =
      if (c (Fin.last d)).forg ∨ i = im d c then 0 else (topOf g d t c).pm := by
  unfold coefN coefC
  rw [dite_eq_left_of_eq_true (by simp)]
  simp only [topOf, toSR, hc.gi_eq]
  split_ifs
  · rfl
  · exact Int.toNat_natCast _

/-- `Nat.beq` of distinct numbers. -/
theorem beq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  rw [Bool.eq_false_iff]; intro h2; exact h (Nat.eq_of_beq_eq_true h2)

/-- The packed coefficients of a cell. -/
theorem cPN_eq (hd : g.m = d + 1) (hc : RecOK DS g t c) (i : ℕ) :
    cPN g d t Nn c i = (pdSpec g d t Nn c i).cp +
      (if Nat.beq i (im d c) = true then 0 else (tpOf g d t c).PmF) := by
  rw [cPN, Fin.sum_univ_castSucc, coefN_last hc]
  simp only [pdSpec, tpOf, Fin.val_last, Fin.val_castSucc, mkCtx_FT, hd, Nat.add_sub_cancel]
  congr 1
  rw [bsel_eq]
  by_cases h1 : i = im d c
  · simp [h1]
  · simp only [beq_false_of_ne h1, h1, or_false]
    simp only [topOf, toSR]
    by_cases hf : (c (Fin.last d)).forg = true <;> simp [hf]


/-- `coef_l` is the natural `coefN`. -/
theorem coefC_eq (i : ℕ) (l : Fin (d + 1)) :
    coefC DS g d (sgOf d Nn) t c i l = (coefN g d t Nn c i l : ℤ) :=
  (Int.toNat_of_nonneg (coefC_nonneg _ _ _ _ _ _ _ _)).symm

/-- `S` of a cell. -/
theorem SC_eq (hc : RecOK DS g t c) (i : ℕ) :
    SO.SC DS g d (sgOf d Nn) t c i = ((if Nat.beq i (im d c) = true then (pdSpec g d t Nn c i).sp
      else (pdSpec g d t Nn c i).sp + (tpOf g d t c).PmW : ℕ) : ℤ) := by
  unfold SO.SC
  simp only [coefC_eq]
  rw [Fin.sum_univ_castSucc, coefN_last hc]
  have hlast : ((if (c (Fin.last d)).forg = true ∨ i = im d c then 0 else (topOf g d t c).pm) *
      (c (Fin.last d)).w : ℕ) = if Nat.beq i (im d c) = true then 0 else (tpOf g d t c).PmW := by
    simp only [tpOf, topOf, toSR, bsel_eq]
    by_cases h1 : i = im d c
    · simp [h1]
    · simp only [beq_false_of_ne h1, h1, or_false]
      by_cases hf : (c (Fin.last d)).forg = true <;> simp [hf, Nat.mul_eq]
  have : ((if Nat.beq i (im d c) = true then (pdSpec g d t Nn c i).sp
      else (pdSpec g d t Nn c i).sp + (tpOf g d t c).PmW : ℕ) : ℤ) =
      ((pdSpec g d t Nn c i).sp : ℤ) + ((if Nat.beq i (im d c) = true then 0 else (tpOf g d t c).PmW : ℕ) : ℤ) := by
    split_ifs <;> push_cast <;> ring
  rw [this, ← hlast]
  simp only [pdSpec]
  push_cast
  rfl

/-- `beta` of a cell. -/
theorem betaC_eq (hg : ok DS g = true) (hc : RecOK DS g t c) (i : ℕ) :
    betaC DS g d (uhOf d Nn) (sgOf d Nn) t c i =
      (Nat.add (pdSpec g d t Nn c i).bet (tpOf g d t c).DEm : ℕ) := by
  unfold betaC
  simp only [pdSpec, tpOf, topOf, toSR, hc.gi_eq, ev_toSR hg hc, Nat.add_eq, Nat.mul_eq]
  push_cast
  ring


/-- `a0` of a cell. -/
theorem a0C_eq (i : ℕ) : a0C DS d c i = ((pdSpec g d t Nn c i).a0 : ℤ) := by
  simp only [a0C, pdSpec, DS2_eq]; push_cast; ring

/-- `sigma` of a cell. -/
theorem sigmaC_eq (i : ℕ) :
    sigmaC g d (sgOf d Nn) t c i = ((pdSpec g d t Nn c i).sig : ℤ) := rfl

/-- `M` of a cell. -/
theorem MC_eq (hg : ok DS g = true) (hc : RecOK DS g t c) (i : ℕ) :
    MC DS g d (uhOf d Nn) (sgOf d Nn) t c i =
      if (pdSpec g d t Nn c i).A1 ≤ Nat.add (pdSpec g d t Nn c i).bet (tpOf g d t c).DEm then
        (((Nat.add (pdSpec g d t Nn c i).bet (tpOf g d t c).DEm - (pdSpec g d t Nn c i).A1) / DS : ℕ) : ℤ)
      else 0 := by
  have hgap : betaC DS g d (uhOf d Nn) (sgOf d Nn) t c i - sigmaC g d (sgOf d Nn) t c i * cp DS g t i -
      a0C DS d c i - (((g.n - t) * DS : ℕ) : ℤ) * cp DS g t i =
      (Nat.add (pdSpec g d t Nn c i).bet (tpOf g d t c).DEm : ℤ) - (pdSpec g d t Nn c i).A1 := by
    rw [betaC_eq hg hc, sigmaC_eq (Nn := Nn), a0C_eq (g := g) (t := t) (Nn := Nn)]
    simp only [pdSpec]; push_cast; ring
  unfold MC
  simp only []
  rw [hgap]
  set B := Nat.add (pdSpec g d t Nn c i).bet (tpOf g d t c).DEm
  set A1 := (pdSpec g d t Nn c i).A1
  by_cases h : A1 ≤ B
  · rw [ite_eq_left h]
    rw [← Nat.cast_sub h]
    split_ifs with h2
    · rw [Int.natCast_div]
    · have : B - A1 = 0 := by omega
      simp [this]
  · rw [ite_eq_right h, ite_eq_right (by omega)]


/-- `Q_i` of a cell is the kernel chord. -/
theorem QN_eq (hg : ok DS g = true) (htn : t < g.n) (hc : RecOK DS g t c) {i : ℕ} (hi1 : 1 ≤ i)
    (hiL : i ≤ g.L t) :
    QN g d t Nn c i =
      if (if Nat.beq i (im d c) = true then (pdSpec g d t Nn c i).sp
          else (pdSpec g d t Nn c i).sp + (tpOf g d t c).PmW) = 0 then 0
      else chord (pdSpec g d t Nn c i).pa (pdSpec g d t Nn c i).pb (pdSpec g d t Nn c i).a0
        ((g.n - t) * DS) (Nat.add (pdSpec g d t Nn c i).bet (tpOf g d t c).DEm)
        (pdSpec g d t Nn c i).sig
        (if Nat.beq i (im d c) = true then (pdSpec g d t Nn c i).sp
          else (pdSpec g d t Nn c i).sp + (tpOf g d t c).PmW) := by
  have hab : (pdSpec g d t Nn c i).pa ≤ (pdSpec g d t Nn c i).pb :=
    g.so_cp_mono DS hg (by omega) hiL
  have ha1 : 0 < (g.n - t) * DS := Nat.mul_pos (by omega) DS_pos
  unfold QN QC
  rw [SC_eq hc, betaC_eq hg hc, sigmaC_eq (Nn := Nn), a0C_eq (g := g) (t := t) (Nn := Nn)]
  set S := if Nat.beq i (im d c) = true then (pdSpec g d t Nn c i).sp
    else (pdSpec g d t Nn c i).sp + (tpOf g d t c).PmW
  by_cases hS : S = 0
  · simp [hS]
  · rw [ite_eq_left (by exact_mod_cast Nat.pos_of_ne_zero hS), ite_eq_right hS]
    have hch := chord_eq (pdSpec g d t Nn c i).pa (pdSpec g d t Nn c i).pb (pdSpec g d t Nn c i).a0
      ((g.n - t) * DS) (Nat.add (pdSpec g d t Nn c i).bet (tpOf g d t c).DEm)
      (pdSpec g d t Nn c i).sig S hab ha1 (Nat.pos_of_ne_zero hS)
    exact (congrArg Int.toNat hch.symm).trans (Int.toNat_natCast _)

/-- The own-cell credits of a cell. -/
theorem lamP_eq (hg : ok DS g = true) (hd : g.m = d + 1) (hc : RecOK DS g t c) (i : ℕ) :
    lamP g d t Nn c i =
      if (pdSpec g d t Nn c i).A1 ≤ Nat.add (pdSpec g d t Nn c i).bet (tpOf g d t c).DEm then
        ownLam ((Nat.add (pdSpec g d t Nn c i).bet (tpOf g d t c).DEm - (pdSpec g d t Nn c i).A1) / DS)
          (pdSpec g d t Nn c i).own (if Nat.beq i (im d c) = true then (tpOf g d t c).topF else 0)
      else 0 := by
  have hM := MC_eq (Nn := Nn) hg hc i
  set B := Nat.add (pdSpec g d t Nn c i).bet (tpOf g d t c).DEm
  set A1 := (pdSpec g d t Nn c i).A1
  unfold lamP
  by_cases h : A1 ≤ B
  · rw [ite_eq_left h] at hM ⊢
    set M := (B - A1) / DS
    let p : Fin (d + 1) → Bool := fun l => decide ((c l).pos = i) && !(c l).forg
    have hl : ∀ l, (lamC DS g d (uhOf d Nn) (sgOf d Nn) t c i l).toNat =
        if p l then dq (Finset.univ.filter fun l' => l' < l ∧ p l' = true).card M else 0 := by
      intro l
      unfold lamC
      simp only [p, hM]
      have hcard : (Finset.univ.filter fun l' : Fin (d + 1) => l' < l ∧ (c l').pos = i ∧ (c l').forg = false) =
          Finset.univ.filter fun l' => l' < l ∧ (decide ((c l').pos = i) && !(c l').forg) = true := by
        apply Finset.filter_congr; intro l' _; simp
      by_cases hl : (c l).pos = i ∧ (c l).forg = false
      · rw [ite_eq_left hl, hcard, ← dq_cast, Int.toNat_natCast]
        simp [hl.1, hl.2]
      · rw [ite_eq_right hl]
        have : (decide ((c l).pos = i) && !(c l).forg) = false := by
          by_cases h1 : (c l).pos = i
          · have h2 : (c l).forg = true := by simpa [h1] using hl
            simp [h1, h2]
          · simp [h1]
        simp [this]
    simp only [hl]
    rw [lamSum_eq p M]
    congr 1
    · have hf : List.filter (fun l => decide ((c l.castSucc).pos = i) && !(c l.castSucc).forg)
          (List.finRange d) = List.filter (fun l => !(c l.castSucc).forg && (c l.castSucc).pos == i)
          (List.finRange d) := List.filter_congr fun l _ => by
            cases (c l.castSucc).forg <;> simp [beq_eq_decide]
      simp only [pdSpec, ownF, p]
      rw [hf]
    · simp only [p, tpOf, topOf, toSR, bsel_eq, mkCtx_FT, hd, Nat.add_sub_cancel, im]
      by_cases h1 : i = (c (Fin.last d)).pos
      · subst h1
        by_cases hf : (c (Fin.last d)).forg = true <;> simp [hf, Nat.beq_refl]
      · simp [beq_false_of_ne h1, Ne.symm h1]
  · rw [ite_eq_right h] at hM ⊢
    apply Finset.sum_eq_zero
    intro l _
    unfold lamC
    simp only [hM]
    split_ifs
    · rw [min_eq_right (by positivity), min_eq_right (by positivity)]; simp
    · simp


/-- The prefix data of `mkPre`. -/
theorem mkPre_pd (hg : ok DS g = true) (hd : g.m = d + 1) (ht1 : 1 ≤ t) (htn : t < g.n)
    {lk : ℕ → SV}
    (hlk : ∀ H : Fin (d + 1) → ℕ, g.IsState (t + 1) H →
      lk (rank H) = ⟨stOf d Nn H % 2 ^ 48, slopes g.m (stOf d Nn H)⟩)
    (hc : RecOK DS g t c) :
    (mkPre (mkCtx g t) lk (rsOf g d t c)).pd =
      (List.range (g.L t)).map fun j => pdSpec g d t Nn c (j + 1) :=
  pdLoop_spec hg hd ht1 htn hlk hc

/-- `topLoop` on a cell `i ≤ im`. -/
theorem topLoop_cons_le (C : Ctx) (lk : ℕ → SV) (p : Pre) (top : SR) (tp : Tp) (pd : PD)
    (rest : List PD) (i : ℕ) (A : Acc) (hi : i ≤ tp.im) :
    topLoop C lk p top tp (pd :: rest) i A =
      topLoop C lk p top tp rest (i + 1) (topCell C.a1 tp pd (Nat.beq i tp.im) (Nat.add pd.bet tp.DEm) A) := by
  show bsel (Nat.ble i tp.im) _ _ = _
  rw [bsel_eq, ite_eq_left (Nat.ble_eq.mpr hi)]
  rfl

/-- `topLoop` on a cell `i > im`. -/
theorem topLoop_cons_gt (C : Ctx) (lk : ℕ → SV) (p : Pre) (top : SR) (tp : Tp) (pd : PD)
    (rest : List PD) (i : ℕ) (A : Acc) (hi : tp.im < i) :
    topLoop C lk p top tp (pd :: rest) i A = bsel top.fg A (tailPart C lk p top pd.from' A) := by
  show bsel (Nat.ble i tp.im) _ _ = _
  rw [bsel_eq, ite_eq_right (by rw [Nat.ble_eq]; omega)]


/-- One cell `i ≤ im` of `topLoop`. -/
theorem topCell_spec (hg : ok DS g = true) (hd : g.m = d + 1) (htn : t < g.n)
    (hc : RecOK DS g t c) {i : ℕ} (hi1 : 1 ≤ i) (hiim : i ≤ im d c) (A A' : Acc)
    (hA' : A' = topCell ((g.n - t) * DS) (tpOf g d t c) (pdSpec g d t Nn c i) (Nat.beq i (im d c))
      (Nat.add (pdSpec g d t Nn c i).bet (tpOf g d t c).DEm) A) :
    (A'.rp : ℤ) - A'.rn = (A.rp : ℤ) - A.rn + RC DS g d (uhOf d Nn) (sgOf d Nn) t c i ∧
      A'.ac = A.ac + QN g d t Nn c i * cPN g d t Nn c i ∧ A'.lm = A.lm + lamP g d t Nn c i := by
  have hiL : i ≤ g.L t := hiim.trans (hc.pos_le _)
  have hab : (pdSpec g d t Nn c i).pa ≤ (pdSpec g d t Nn c i).pb :=
    g.so_cp_mono DS hg (by omega) hiL
  have ha1 : 0 < (g.n - t) * DS := Nat.mul_pos (by omega) DS_pos
  obtain ⟨h1, h2, h3⟩ := topCell_eq ((g.n - t) * DS) (tpOf g d t c) (pdSpec g d t Nn c i)
    (Nat.beq i (im d c)) (Nat.add (pdSpec g d t Nn c i).bet (tpOf g d t c).DEm) A hab ha1 rfl rfl rfl
    rfl rfl rfl rfl
  subst hA'
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]
    unfold RC
    rw [betaC_eq hg hc, sigmaC_eq (Nn := Nn), a0C_eq (g := g) (t := t) (Nn := Nn)]
    rfl
  · rw [h2, QN_eq hg htn hc hi1 hiL, cPN_eq hd hc]
    congr 2
    · split_ifs <;> rfl
  · rw [h3, lamP_eq hg hd hc]



/-- The cells `1, ..., k` (`k ≤ im`) of `topLoop`. -/
theorem topLoop_cells (hg : ok DS g = true) (hd : g.m = d + 1) (ht1 : 1 ≤ t) (htn : t < g.n)
    {lk : ℕ → SV}
    (hlk : ∀ H : Fin (d + 1) → ℕ, g.IsState (t + 1) H →
      lk (rank H) = ⟨stOf d Nn H % 2 ^ 48, slopes g.m (stOf d Nn H)⟩)
    (hc : RecOK DS g t c) {k : ℕ} (hk : k ≤ im d c) :
    ∃ A : Acc, topLoop (mkCtx g t) lk (mkPre (mkCtx g t) lk (rsOf g d t c)) (topOf g d t c)
        (tpOf g d t c) (mkPre (mkCtx g t) lk (rsOf g d t c)).pd 1 (Acc.mk 0 0 0 0) =
      topLoop (mkCtx g t) lk (mkPre (mkCtx g t) lk (rsOf g d t c)) (topOf g d t c)
        (tpOf g d t c) ((mkPre (mkCtx g t) lk (rsOf g d t c)).pd.drop k) (k + 1) A ∧
      (A.rp : ℤ) - A.rn = ∑ i ∈ Finset.Icc 1 k, RC DS g d (uhOf d Nn) (sgOf d Nn) t c i ∧
      A.ac = ∑ i ∈ Finset.Icc 1 k, QN g d t Nn c i * cPN g d t Nn c i ∧
      A.lm = ∑ i ∈ Finset.Icc 1 k, lamP g d t Nn c i := by
  induction k with
  | zero => exact ⟨Acc.mk 0 0 0 0, rfl, by simp, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨A, hA, h1, h2, h3⟩ := ih (by omega)
    have hkL : k < g.L t := by have := hc.pos_le (Fin.last d); unfold im at hk; omega
    have hpd := mkPre_pd (Nn := Nn) hg hd ht1 htn hlk hc
    have hdrop : (mkPre (mkCtx g t) lk (rsOf g d t c)).pd.drop k =
        pdSpec g d t Nn c (k + 1) :: (mkPre (mkCtx g t) lk (rsOf g d t c)).pd.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons (by rw [hpd]; simp; omega)]
      congr 1
      simp [hpd]
    obtain ⟨e1, e2, e3⟩ := topCell_spec (Nn := Nn) hg hd htn hc (i := k + 1) (by omega) hk A _ rfl
    refine ⟨topCell ((g.n - t) * DS) (tpOf g d t c) (pdSpec g d t Nn c (k + 1)) (Nat.beq (k + 1) (im d c))
      (Nat.add (pdSpec g d t Nn c (k + 1)).bet (tpOf g d t c).DEm) A, ?_, ?_, ?_, ?_⟩
    · rw [hA, hdrop, topLoop_cons_le _ _ _ _ _ _ _ _ _ hk]; rfl
    · rw [e1, h1, Finset.sum_Icc_succ_top (by omega)]
    · rw [e2, h2, Finset.sum_Icc_succ_top (by omega)]
    · rw [e3, h3, Finset.sum_Icc_succ_top (by omega)]


/-! ## The tail (section 5.4) -/

/-- The first term of a sum over `(j, k]`. -/
theorem sum_Ioc_first {M : Type*} [AddCommMonoid M] (f : ℕ → M) {j k : ℕ} (h : j + 1 ≤ k) :
    ∑ i ∈ Finset.Ioc j k, f i = f (j + 1) + ∑ i ∈ Finset.Ioc (j + 1) k, f i := by
  rw [← Finset.sum_Ioc_consecutive f (Nat.le_succ j) h, Nat.Ioc_succ_singleton, Finset.sum_singleton]

/-- `tailCells` on a cell. -/
theorem tailCells_cons (r a1 a0 U S slcF : ℕ) (cl : SC) (rest : List SC) (pj etj etmj : ℕ) (A : Acc) :
    tailCells r a1 a0 U S slcF (cl :: rest) pj etj etmj A =
      bsel (Nat.ble (DS * (etj + r) + U + S) (a0 + a1 * pj)) (tailCells.tailEnd r U slcF pj etmj A)
        (tailCells r a1 a0 U S slcF rest cl.pb cl.et cl.etm
          (Acc.mk (cell2 cl.pa cl.pb a0 a1 (DS * cl.et + U + r * cl.e1 * cl.pb) (r * cl.e1) A.rp A.rn).p
            (cell2 cl.pa cl.pb a0 a1 (DS * cl.et + U + r * cl.e1 * cl.pb) (r * cl.e1) A.rp A.rn).n
            (bsel (Nat.beq S 0) A.ac (A.ac + chord cl.pa cl.pb a0 a1 (DS * cl.et + U + r * cl.e1 * cl.pb)
              (r * cl.e1) S * slcF)) A.lm)) := rfl

/-- The exact tail. -/
theorem tailEnd_eq (r U slcF pj etmj : ℕ) (A : Acc) :
    tailCells.tailEnd r U slcF pj etmj A =
      if DS ≤ pj then A else
        Acc.mk (A.rp + (2 * DS2 * etmj / (r + 1) + 2 * (DS - pj) * U)) A.rn
          (A.ac + (DS - pj) * slcF) A.lm := by
  simp only [tailCells.tailEnd, bsel_eq, Nat.ble_eq]
  rfl

/-- The tail cells on abstract data: the cells `j + 1, ..., k` and the exact tail from `k`. -/
theorem tailCells_gen (r a1 a0 U S slcF : ℕ) (F : ℕ → SC) (P E Em E1 : ℕ → ℕ)
    (hpa : ∀ i, (F i).pa = P (i - 1)) (hpb : ∀ i, (F i).pb = P i) (het : ∀ i, (F i).et = E i)
    (hetm : ∀ i, (F i).etm = Em i) (he1 : ∀ i, (F i).e1 = E1 i) (ha1 : 0 < a1)
    {L : ℕ} (hPL : DS ≤ P L) {j k : ℕ} (hjk : j ≤ k) (hkL : k ≤ L)
    (hmono : ∀ i, j < i → i ≤ k → P (i - 1) ≤ P i)
    (hno : ∀ i, j ≤ i → i < k → ¬ DS * (E i + r) + U + S ≤ a0 + a1 * P i)
    (hstop : k < L → DS * (E k + r) + U + S ≤ a0 + a1 * P k)
    (A A' : Acc)
    (hA' : A' = tailCells r a1 a0 U S slcF ((List.range (L - j)).map fun i => F (j + i + 1))
      (P j) (E j) (Em j) A) :
    (A'.rp : ℤ) - A'.rn = (A.rp : ℤ) - A.rn +
        (∑ i ∈ Finset.Ioc j k, SO.cell2 (P (i - 1) : ℤ) (P i : ℤ) (a0 : ℤ) (a1 : ℤ)
          ((DS * E i + U + r * E1 i * P i : ℕ) : ℤ) ((r * E1 i : ℕ) : ℤ) +
        (if P k < DS then ((2 * DS2 * Em k / (r + 1) : ℕ) : ℤ) + 2 * ((DS - P k : ℕ) : ℤ) * U
          else 0)) ∧
      A'.ac = A.ac + slcF *
        (∑ i ∈ Finset.Ioc j k, (if S = 0 then 0 else
          chord (P (i - 1)) (P i) a0 a1 (DS * E i + U + r * E1 i * P i) (r * E1 i) S) +
        (if P k < DS then DS - P k else 0)) ∧
      A'.lm = A.lm := by
  obtain ⟨n, hn⟩ : ∃ n, k = j + n := ⟨k - j, by omega⟩
  induction n generalizing j A with
  | zero =>
    have hkj : k = j := by omega
    rw [hkj] at hstop ⊢
    simp only [Finset.Ioc_self, Finset.sum_empty, zero_add]
    rcases Nat.lt_or_ge j L with hjL | hjL
    · rw [show L - j = (L - (j + 1)) + 1 by omega, List.range_succ_eq_map, List.map_cons,
        tailCells_cons, bsel_eq, ite_eq_left (Nat.ble_eq.mpr (hstop hjL)),
        tailEnd_eq] at hA'
      subst hA'
      split_ifs with h1 h2 h2
      · omega
      · simp
      · refine ⟨?_, ?_, rfl⟩
        · push_cast; ring
        · ring
      · omega
    · rw [show L - j = 0 by omega, List.range_zero, List.map_nil] at hA'
      subst hA'
      have : j = L := by omega
      rw [this]
      simp [Nat.not_lt.mpr hPL]
  | succ n ih =>
    subst hn
    have hjL : j < L := by omega
    rw [show L - j = (L - (j + 1)) + 1 by omega, List.range_succ_eq_map, List.map_cons,
      tailCells_cons, bsel_eq, ite_eq_right (by rw [Nat.ble_eq]; exact hno j le_rfl (by omega))] at hA'
    have hrest : (List.map (fun i => F (j + i + 1)) (List.map Nat.succ (List.range (L - (j + 1))))) =
        (List.range (L - (j + 1))).map fun i => F (j + 1 + i + 1) := by
      rw [List.map_map]
      congr 1
      funext i
      simp only [Function.comp, Nat.succ_eq_add_one]
      congr 1
      omega
    rw [hrest, show j + 0 + 1 = j + 1 by omega, hpb, het, hetm, hpa, he1, Nat.add_sub_cancel] at hA'
    generalize hB : Acc.mk _ _ _ _ = B at hA'
    obtain ⟨e1, e2, e3⟩ := ih (j := j + 1) (by omega)
      (fun i hi hik => hmono i (by omega) hik) (fun i hi hik => hno i (by omega) hik) B hA'
      (by omega)
    have hab : P j ≤ P (j + 1) := by
      have := hmono (j + 1) (by omega) (by omega); simpa using this
    subst hB
    dsimp only at e1 e2 e3
    refine ⟨?_, ?_, e3⟩
    · rw [e1, cell2_eq _ _ _ _ _ _ _ _ hab ha1, sum_Ioc_first _ (by omega : j + 1 ≤ j + (n + 1)),
        Nat.add_sub_cancel]
      ring
    · rw [e2, sum_Ioc_first _ (by omega : j + 1 ≤ j + (n + 1)), Nat.add_sub_cancel]
      simp only [bsel_eq, Nat.beq_eq]
      split_ifs <;> ring

/-- The tail cells on abstract data, with the cell terms and the end terms named. -/
theorem tailCells_gen' (r a1 a0 U S slcF : ℕ) (F : ℕ → SC) (P E Em E1 : ℕ → ℕ)
    (hpa : ∀ i, (F i).pa = P (i - 1)) (hpb : ∀ i, (F i).pb = P i) (het : ∀ i, (F i).et = E i)
    (hetm : ∀ i, (F i).etm = Em i) (he1 : ∀ i, (F i).e1 = E1 i) (ha1 : 0 < a1)
    {L : ℕ} (hPL : DS ≤ P L) {j k : ℕ} (hjk : j ≤ k) (hkL : k ≤ L)
    (hmono : ∀ i, j < i → i ≤ k → P (i - 1) ≤ P i)
    (hno : ∀ i, j ≤ i → i < k → ¬ DS * (E i + r) + U + S ≤ a0 + a1 * P i)
    (hstop : k < L → DS * (E k + r) + U + S ≤ a0 + a1 * P k)
    (Rc : ℕ → ℤ) (Qc : ℕ → ℕ) (ER : ℤ) (EA : ℕ)
    (hRc : ∀ i, j < i → i ≤ k → Rc i = SO.cell2 (P (i - 1) : ℤ) (P i : ℤ) (a0 : ℤ) (a1 : ℤ)
      ((DS * E i + U + r * E1 i * P i : ℕ) : ℤ) ((r * E1 i : ℕ) : ℤ))
    (hQc : ∀ i, j < i → i ≤ k → Qc i = if S = 0 then 0 else
      chord (P (i - 1)) (P i) a0 a1 (DS * E i + U + r * E1 i * P i) (r * E1 i) S)
    (hER : ER = if P k < DS then ((2 * DS2 * Em k / (r + 1) : ℕ) : ℤ) + 2 * ((DS - P k : ℕ) : ℤ) * U
      else 0)
    (hEA : EA = if P k < DS then DS - P k else 0)
    (A A' : Acc)
    (hA' : A' = tailCells r a1 a0 U S slcF ((List.range (L - j)).map fun i => F (j + i + 1))
      (P j) (E j) (Em j) A) :
    (A'.rp : ℤ) - A'.rn = (A.rp : ℤ) - A.rn + (∑ i ∈ Finset.Ioc j k, Rc i + ER) ∧
      A'.ac = A.ac + slcF * (∑ i ∈ Finset.Ioc j k, Qc i + EA) ∧ A'.lm = A.lm := by
  obtain ⟨e1, e2, e3⟩ := tailCells_gen r a1 a0 U S slcF F P E Em E1 hpa hpb het hetm he1 ha1 hPL
    hjk hkL hmono hno hstop A A' hA'
  refine ⟨?_, ?_, e3⟩
  · rw [e1, hER, Finset.sum_congr rfl fun i hi => hRc i (Finset.mem_Ioc.mp hi).1 (Finset.mem_Ioc.mp hi).2]
  · rw [e2, hEA, Finset.sum_congr rfl fun i hi => hQc i (Finset.mem_Ioc.mp hi).1 (Finset.mem_Ioc.mp hi).2]


/-- `jF` at the end. -/
theorem jF_L : jF g d t Nn c (g.L t) = g.L t := by
  simp [jF]

/-- `jF` below the end. -/
theorem jF_of_lt {j : ℕ} (hj : j < g.L t) :
    jF g d t Nn c j = if (((d + 2) * DS * DS + (g.n - t) * DS * cp DS g t j : ℕ) : ℤ) ≥
      (DS : ℤ) * (Epen DS (cp DS g t j) (g.n - t) + (g.n - t) : ℕ) +
        UT DS g d (uhOf d Nn) (sgOf d Nn) t c + ST d (sgOf d Nn) c then j
      else jF g d t Nn c (j + 1) := by
  unfold jF
  rw [show g.L t - j = (g.L t - (j + 1)) + 1 by omega, List.range'_succ, List.find?_cons]
  split_ifs with h1
  · rw [decide_eq_true h1]; rfl
  · rw [decide_eq_false h1]

/-- `j ≤ jF j ≤ L`. -/
theorem jF_mem {j : ℕ} (hj : j ≤ g.L t) : j ≤ jF g d t Nn c j ∧ jF g d t Nn c j ≤ g.L t := by
  obtain ⟨n, hn⟩ : ∃ n, g.L t = j + n := ⟨g.L t - j, by omega⟩
  induction n generalizing j with
  | zero => rw [show j = g.L t by omega, jF_L]; omega
  | succ n ih =>
    rw [jF_of_lt (by omega)]
    split_ifs
    · omega
    · have := ih (j := j + 1) (by omega) (by omega); omega

/-- `jF j` is the first boundary from `j` where the tail is exact. -/
theorem jF_stop {j : ℕ} (hj : j ≤ g.L t) :
    (∀ i, j ≤ i → i < jF g d t Nn c j → ¬ ((((d + 2) * DS * DS + (g.n - t) * DS * cp DS g t i : ℕ) : ℤ) ≥
      (DS : ℤ) * (Epen DS (cp DS g t i) (g.n - t) + (g.n - t) : ℕ) +
        UT DS g d (uhOf d Nn) (sgOf d Nn) t c + ST d (sgOf d Nn) c)) ∧
    (jF g d t Nn c j < g.L t →
      (((d + 2) * DS * DS + (g.n - t) * DS * cp DS g t (jF g d t Nn c j) : ℕ) : ℤ) ≥
        (DS : ℤ) * (Epen DS (cp DS g t (jF g d t Nn c j)) (g.n - t) + (g.n - t) : ℕ) +
          UT DS g d (uhOf d Nn) (sgOf d Nn) t c + ST d (sgOf d Nn) c) := by
  obtain ⟨n, hn⟩ : ∃ n, g.L t = j + n := ⟨g.L t - j, by omega⟩
  induction n generalizing j with
  | zero =>
    have hjL : j = g.L t := by omega
    rw [hjL, jF_L]
    exact ⟨fun i h1 h2 => absurd h2 (by omega), fun h => absurd h (lt_irrefl _)⟩
  | succ n ih =>
    rw [jF_of_lt (by omega)]
    split_ifs with h1
    · exact ⟨fun i h2 h3 => absurd h3 (by omega), fun _ => h1⟩
    · obtain ⟨ih1, ih2⟩ := ih (j := j + 1) (by omega) (by omega)
      refine ⟨fun i h2 h3 => ?_, ih2⟩
      rcases h2.eq_or_lt with h2 | h2
      · rw [← h2]; exact h1
      · exact ih1 i h2 h3

/-- The tail cells from the boundary `j`. -/
theorem tailCells_spec (hg : ok DS g = true) (hd : g.m = d + 1) (ht1 : 1 ≤ t) (htn : t < g.n)
    (_hc : RecOK DS g t c) {U S : ℕ} (hU : (U : ℤ) = UT DS g d (uhOf d Nn) (sgOf d Nn) t c)
    (hS : (S : ℤ) = ST d (sgOf d Nn) c) (slcF : ℕ) {j : ℕ} (hj : j ≤ g.L t) (A A' : Acc)
    (hA' : A' = tailCells (g.n - t) ((g.n - t) * DS) (Nat.mul (Nat.succ g.m) DS2) U S slcF
      ((mkCtx g t).cells.drop j) (cp DS g t j) (Epen DS (cp DS g t j) (g.n - t))
      (Epen DS (cp DS g t j) (g.n - t + 1)) A) :
    (A'.rp : ℤ) - A'.rn = (A.rp : ℤ) - A.rn +
        (∑ i ∈ Finset.Ioc j (jF g d t Nn c j), RT DS g d (uhOf d Nn) (sgOf d Nn) t c i +
          REj g d t Nn c (jF g d t Nn c j)) ∧
      A'.ac = A.ac + slcF * (∑ i ∈ Finset.Ioc j (jF g d t Nn c j), QTN g d t Nn c i +
        ExN g t (jF g d t Nn c j)) ∧
      A'.lm = A.lm := by
  have hcells := mkCtx_cells g hg ht1 htn
  have ha1 : 0 < (g.n - t) * DS := Nat.mul_pos (by omega) DS_pos
  have ha0 : Nat.mul (Nat.succ g.m) DS2 = (d + 2) * DS * DS := by
    rw [hd, DS2_eq]; show (d + 1 + 1) * (DS * DS) = (d + 2) * DS * DS; ring
  have hA0' : ((Nat.mul (Nat.succ g.m) DS2 : ℕ) : ℤ) = (((d + 2) * DS * DS : ℕ) : ℤ) := by rw [ha0]
  have hdrop : (mkCtx g t).cells.drop j =
      (List.range (g.L t - j)).map fun i => toSC g t (j + i + 1) := by
    rw [hcells]
    apply List.ext_getElem
    · simp
    · intro n h1 h2
      simp only [List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [hdrop] at hA'
  obtain ⟨hjj, hjL⟩ := jF_mem (g := g) (d := d) (t := t) (Nn := Nn) (c := c) hj
  obtain ⟨hno, hstop⟩ := jF_stop (g := g) (d := d) (t := t) (Nn := Nn) (c := c) hj
  have hiff : ∀ i, (DS * (Epen DS (cp DS g t i) (g.n - t) + (g.n - t)) + U + S ≤
      Nat.mul (Nat.succ g.m) DS2 + (g.n - t) * DS * cp DS g t i) ↔
      ((((d + 2) * DS * DS + (g.n - t) * DS * cp DS g t i : ℕ) : ℤ) ≥
        (DS : ℤ) * (Epen DS (cp DS g t i) (g.n - t) + (g.n - t) : ℕ) +
          UT DS g d (uhOf d Nn) (sgOf d Nn) t c + ST d (sgOf d Nn) c) := by
    intro i
    rw [← hU, ← hS, ← ha0]
    constructor <;> intro h <;> exact_mod_cast h
  have hbeta : ∀ i, ((DS * Epen DS (cp DS g t i) (g.n - t) + U +
      (g.n - t) * Epen DS (cp DS g t i) (g.n - t - 1) * cp DS g t i : ℕ) : ℤ) =
      (DS : ℤ) * (Epen DS (cp DS g t i) (g.n - t) : ℕ) + UT DS g d (uhOf d Nn) (sgOf d Nn) t c +
        (((g.n - t) * Epen DS (cp DS g t i) (g.n - t - 1) : ℕ) : ℤ) * (cp DS g t i : ℤ) := by
    intro i; rw [← hU]; push_cast; ring
  exact tailCells_gen' (g.n - t) ((g.n - t) * DS) (Nat.mul (Nat.succ g.m) DS2) U S slcF (toSC g t)
    (cp DS g t) (fun i => Epen DS (cp DS g t i) (g.n - t)) (fun i => Epen DS (cp DS g t i) (g.n - t + 1))
    (fun i => Epen DS (cp DS g t i) (g.n - t - 1)) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) ha1 (g.so_cp_L DS t).ge hjj hjL
    (fun i _ hi => g.so_cp_mono DS hg (Nat.sub_le i 1) (by omega))
    (fun i h1 h2 => fun h => hno i h1 h2 ((hiff i).mp h)) (fun h => (hiff _).mpr (hstop h))
    (RT DS g d (uhOf d Nn) (sgOf d Nn) t c) (QTN g d t Nn c) (REj g d t Nn c (jF g d t Nn c j))
    (ExN g t (jF g d t Nn c j))
    (fun i hi1 hi2 => by
      show RT DS g d (uhOf d Nn) (sgOf d Nn) t c i = SO.cell2 (cp DS g t (i - 1) : ℤ) (cp DS g t i : ℤ)
        ((Nat.mul (Nat.succ g.m) DS2 : ℕ) : ℤ) (((g.n - t) * DS : ℕ) : ℤ)
        ((DS * Epen DS (cp DS g t i) (g.n - t) + U +
          (g.n - t) * Epen DS (cp DS g t i) (g.n - t - 1) * cp DS g t i : ℕ) : ℤ)
        (((g.n - t) * Epen DS (cp DS g t i) (g.n - t - 1) : ℕ) : ℤ)
      rw [hA0', hbeta i]; rfl)
    (fun i hi1 hi2 => by
      show QTN g d t Nn c i = if S = 0 then 0 else
        chord (cp DS g t (i - 1)) (cp DS g t i) (Nat.mul (Nat.succ g.m) DS2) ((g.n - t) * DS)
          (DS * Epen DS (cp DS g t i) (g.n - t) + U +
            (g.n - t) * Epen DS (cp DS g t i) (g.n - t - 1) * cp DS g t i)
          ((g.n - t) * Epen DS (cp DS g t i) (g.n - t - 1)) S
      unfold QTN QT
      rw [← hS]
      by_cases hS0 : S = 0
      · simp [hS0]
      · have hab : cp DS g t (i - 1) ≤ cp DS g t i := by
          exact g.so_cp_mono DS hg (Nat.sub_le i 1) (by omega)
        rw [ite_eq_left (by exact_mod_cast Nat.pos_of_ne_zero hS0), ite_eq_right hS0,
          ← Int.toNat_natCast (chord _ _ _ _ _ _ _), chord_eq _ _ _ _ _ _ _ hab ha1 (Nat.pos_of_ne_zero hS0),
          hA0', hbeta])
    (by
      show REj g d t Nn c (jF g d t Nn c j) = if cp DS g t (jF g d t Nn c j) < DS then
        ((2 * DS2 * Epen DS (cp DS g t (jF g d t Nn c j)) (g.n - t + 1) / (g.n - t + 1) : ℕ) : ℤ) +
          2 * ((DS - cp DS g t (jF g d t Nn c j) : ℕ) : ℤ) * U else 0
      unfold REj
      rw [← hU, show 2 * DS2 = 2 * DS * DS by rw [DS2_eq, Nat.mul_assoc]])
    rfl A A' hA'


/-- The slopes of a state as a list over `Fin`. -/
theorem slopes_ofFn (hd : g.m = d + 1) (H : Fin (d + 1) → ℕ) :
    slopes g.m (stOf d Nn H) = List.ofFn fun l : Fin (d + 1) => sgOf d Nn H l := by
  apply List.ext_getElem
  · simp [slopes_eq, hd]
  · intro n h1 h2
    simp only [slopes_eq, List.getElem_map, List.getElem_range, List.getElem_ofFn, sgOf]

/-- `binoms m x` at `l < m`. -/
theorem binoms_getD {m x l : ℕ} (hl : l < m) : (binoms m x).getD l 0 = (x + l).choose (l + 1) := by
  rw [binoms_eq, List.getD_eq_getElem _ _ (by simp; omega)]
  simp

/-- The rank of the tail state from the prefix sum and the last record. -/
theorem rank_map_pre (hd : g.m = d + 1) {lk : ℕ → SV} :
    Nat.add (mkPre (mkCtx g t) lk (rsOf g d t c)).Cpre (topOf g d t c).bsl =
      rank fun l => (c l).map := by
  show Nat.add (llast 0 (rankCs (rsOf g d t c))) (topOf g d t c).bsl = _
  rw [rsOf, llast_rankCs, rank, Fin.sum_univ_castSucc]
  show _ + (binoms g.m (c (Fin.last d)).map).getLastD 0 = _
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    simp only [toSR, Fin.val_castSucc]
    exact binoms_getD (by omega)
  · rw [binoms_eq, List.getLastD_eq_getLast?, List.getLast?_map, List.getLast?_range, hd]
    simp

/-- `U` of the tail: `D N (Hc) + sum over l of sg_l ev_l`. -/
theorem U_tail (hg : ok DS g = true) (hd : g.m = d + 1) (hc : RecOK DS g t c) {lk : ℕ → SV} :
    ((Nat.add (Nat.mul DS (stOf d Nn (fun l => (c l).map) % 2 ^ 48))
      (dot (lapp (mkPre (mkCtx g t) lk (rsOf g d t c)).evs [(topOf g d t c).ev])
        (slopes g.m (stOf d Nn fun l => (c l).map))) : ℕ) : ℤ) =
      UT DS g d (uhOf d Nn) (sgOf d Nn) t c := by
  have hev : lapp (mkPre (mkCtx g t) lk (rsOf g d t c)).evs [(topOf g d t c).ev] =
      List.ofFn fun l : Fin (d + 1) => (toSR g t (c l)).ev := by
    show lapp (lmap SR.ev (rsOf g d t c)) [(toSR g t (c (Fin.last d))).ev] = _
    rw [rsOf, lapp_eq, lmap_eq, List.map_ofFn, List.ofFn_succ' (fun l : Fin (d + 1) => (toSR g t (c l)).ev),
      List.concat_eq_append]
    rfl
  rw [hev, slopes_ofFn hd, dot_ofFn]
  unfold UT
  simp only [Nat.add_eq, Nat.mul_eq, uhOf]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ev_toSR hg hc l]
  ring

/-- `S` of the tail: `sum over l of sg_l w_l`. -/
theorem S_tail (hd : g.m = d + 1) {lk : ℕ → SV} :
    ((dot (lapp (mkPre (mkCtx g t) lk (rsOf g d t c)).dls [(topOf g d t c).dl])
        (slopes g.m (stOf d Nn fun l => (c l).map)) : ℕ) : ℤ) = ST d (sgOf d Nn) c := by
  have hdl : lapp (mkPre (mkCtx g t) lk (rsOf g d t c)).dls [(topOf g d t c).dl] =
      List.ofFn fun l : Fin (d + 1) => (c l).w := by
    show lapp (lmap SR.dl (rsOf g d t c)) [(toSR g t (c (Fin.last d))).dl] = _
    rw [rsOf, lapp_eq, lmap_eq, List.map_ofFn, List.ofFn_succ' (fun l : Fin (d + 1) => (c l).w),
      List.concat_eq_append]
    rfl
  rw [hdl, slopes_ofFn hd, dot_ofFn]
  unfold ST
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- The packed slopes of the tail state. -/
theorem packF_slopes (hd : g.m = d + 1) :
    packF (slopes g.m (stOf d Nn fun l => (c l).map)) = slcP d Nn c := by
  rw [slopes_eq, packF_eq, slcP, hd, ← Fin.sum_univ_eq_sum_range]
  rfl


/-- The tail of a last record not forgotten. -/
theorem tailPart_spec (hg : ok DS g = true) (hd : g.m = d + 1) (ht1 : 1 ≤ t) (htn : t < g.n)
    {lk : ℕ → SV}
    (hlk : ∀ H : Fin (d + 1) → ℕ, g.IsState (t + 1) H →
      lk (rank H) = ⟨stOf d Nn H % 2 ^ 48, slopes g.m (stOf d Nn H)⟩)
    (hc : RecOK DS g t c) (_hfg : (c (Fin.last d)).forg = false) (A A' : Acc)
    (hA' : A' = tailPart (mkCtx g t) lk (mkPre (mkCtx g t) lk (rsOf g d t c)) (topOf g d t c)
      ((mkCtx g t).cells.drop (im d c)) A) :
    (A'.rp : ℤ) - A'.rn = (A.rp : ℤ) - A.rn +
        (∑ i ∈ Finset.Ioc (im d c) (jT DS g d (uhOf d Nn) (sgOf d Nn) t c),
          RT DS g d (uhOf d Nn) (sgOf d Nn) t c i + RE DS g d (uhOf d Nn) (sgOf d Nn) t c) ∧
      A'.ac = A.ac + slcP d Nn c *
        (∑ i ∈ Finset.Ioc (im d c) (jT DS g d (uhOf d Nn) (sgOf d Nn) t c), QTN g d t Nn c i +
          ExN g t (jT DS g d (uhOf d Nn) (sgOf d Nn) t c)) ∧
      A'.lm = A.lm := by
  have hsv := hlk _ (map_isState hc)
  have hval : (topOf g d t c).val = cp DS g t (im d c) := hc.val_eq (Fin.last d)
  have hA2 : A' = tailCells (g.n - t) ((g.n - t) * DS) (Nat.mul (Nat.succ g.m) DS2)
      (Nat.add (Nat.mul DS (stOf d Nn (fun l => (c l).map) % 2 ^ 48))
        (dot (lapp (mkPre (mkCtx g t) lk (rsOf g d t c)).evs [(topOf g d t c).ev])
          (slopes g.m (stOf d Nn fun l => (c l).map))))
      (dot (lapp (mkPre (mkCtx g t) lk (rsOf g d t c)).dls [(topOf g d t c).dl])
        (slopes g.m (stOf d Nn fun l => (c l).map)))
      (packF (slopes g.m (stOf d Nn fun l => (c l).map)))
      ((mkCtx g t).cells.drop (im d c)) (cp DS g t (im d c)) (Epen DS (cp DS g t (im d c)) (g.n - t))
      (Epen DS (cp DS g t (im d c)) (g.n - t + 1)) A := by
    rw [hA', tailPart, rank_map_pre hd, hsv, ← hval]
    rfl
  obtain ⟨e1, e2, e3⟩ := tailCells_spec hg hd ht1 htn hc (U_tail hg hd hc) (S_tail hd) _
    (hc.pos_le (Fin.last d)) A A' hA2
  rw [packF_slopes hd] at e2
  exact ⟨e1, e2, e3⟩


/-! ## The accumulators -/

/-- `QC_i ≥ 0`. -/
theorem QC_nonneg (hg : ok DS g = true) {i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ g.L t) :
    0 ≤ QC DS g d (uhOf d Nn) (sgOf d Nn) t c i := by
  unfold QC
  split_ifs with hS
  · exact so_chord_nonneg (by exact_mod_cast g.so_cp_mono DS hg (by omega) hiL) hS
  · exact le_rfl

/-- `QT_i ≥ 0`. -/
theorem QT_nonneg (hg : ok DS g = true) {i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ g.L t) :
    0 ≤ QT DS g d (uhOf d Nn) (sgOf d Nn) t c i := by
  unfold QT
  split_ifs with hS
  · exact so_chord_nonneg (by exact_mod_cast g.so_cp_mono DS hg (by omega) hiL) hS
  · exact le_rfl

/-- `acc_l` as a natural number. -/
theorem acc_eq_nat (hg : ok DS g = true) (hc : RecOK DS g t c) (l : Fin (d + 1)) :
    acc DS g d (uhOf d Nn) (sgOf d Nn) t c l =
      ((∑ i ∈ Finset.Icc 1 (im d c), coefN g d t Nn c i l * QN g d t Nn c i +
        (if (c (Fin.last d)).forg then 0 else sgOf d Nn (fun l => (c l).map) l *
          (∑ i ∈ Finset.Ioc (im d c) (jT DS g d (uhOf d Nn) (sgOf d Nn) t c), QTN g d t Nn c i +
            ExN g t (jT DS g d (uhOf d Nn) (sgOf d Nn) t c))) : ℕ) : ℤ) := by
  have him : im d c ≤ g.L t := hc.pos_le (Fin.last d)
  have hjT : jT DS g d (uhOf d Nn) (sgOf d Nn) t c ≤ g.L t :=
    (jF_mem (g := g) (d := d) (t := t) (Nn := Nn) (c := c) him).2
  unfold acc
  push_cast
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
    rw [coefC_eq, QN, Int.toNat_of_nonneg (QC_nonneg hg hi1 (hi2.trans him))]
  · by_cases hf : (c (Fin.last d)).forg = true
    · simp [hf]
    · simp only [hf, Bool.false_eq_true, ite_false]
      have hsum : ∑ i ∈ Finset.Ioc (im d c) (jT DS g d (uhOf d Nn) (sgOf d Nn) t c),
          QT DS g d (uhOf d Nn) (sgOf d Nn) t c i =
          ∑ i ∈ Finset.Ioc (im d c) (jT DS g d (uhOf d Nn) (sgOf d Nn) t c), ((QTN g d t Nn c i : ℕ) : ℤ) :=
        Finset.sum_congr rfl fun i hi => by
          obtain ⟨hi1, hi2⟩ := Finset.mem_Ioc.mp hi
          rw [QTN, Int.toNat_of_nonneg (QT_nonneg hg (by omega) (hi2.trans hjT))]
      have hE : (if cp DS g t (jT DS g d (uhOf d Nn) (sgOf d Nn) t c) < DS then
          ((DS - cp DS g t (jT DS g d (uhOf d Nn) (sgOf d Nn) t c) : ℕ) : ℤ) else 0) =
          ((ExN g t (jT DS g d (uhOf d Nn) (sgOf d Nn) t c) : ℕ) : ℤ) := by
        unfold ExN; split_ifs <;> simp
      rw [hsum, hE]

/-- `lam_l` as a natural number. -/
theorem lam_eq_nat (l : Fin (d + 1)) :
    lam DS g d (uhOf d Nn) (sgOf d Nn) t c l =
      ((∑ i ∈ Finset.Icc 1 (im d c), (lamC DS g d (uhOf d Nn) (sgOf d Nn) t c i l).toNat : ℕ) : ℤ) := by
  unfold lam
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.toNat_of_nonneg (lamC_nonneg _ _ _ _ _ _ _ _ _)]

/-- The packed `acc`. -/
theorem ac_pack (hg : ok DS g = true) (hc : RecOK DS g t c) :
    ∑ l : Fin (d + 1), (acc DS g d (uhOf d Nn) (sgOf d Nn) t c l).toNat * F128 ^ (l : ℕ) =
      ∑ i ∈ Finset.Icc 1 (im d c), QN g d t Nn c i * cPN g d t Nn c i +
        (if (c (Fin.last d)).forg then 0 else slcP d Nn c *
          (∑ i ∈ Finset.Ioc (im d c) (jT DS g d (uhOf d Nn) (sgOf d Nn) t c), QTN g d t Nn c i +
            ExN g t (jT DS g d (uhOf d Nn) (sgOf d Nn) t c))) := by
  simp only [acc_eq_nat hg hc, Int.toNat_natCast, add_mul, Finset.sum_add_distrib]
  congr 1
  · unfold cPN
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  · split_ifs
    · simp
    · unfold slcP
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring

/-- The packed `lam`. -/
theorem lm_pack :
    ∑ l : Fin (d + 1), (lam DS g d (uhOf d Nn) (sgOf d Nn) t c l).toNat * F128 ^ (l : ℕ) =
      ∑ i ∈ Finset.Icc 1 (im d c), lamP g d t Nn c i := by
  simp only [lam_eq_nat, Int.toNat_natCast, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl


/-- The accumulators of `evalTop` are `Rtot`, `acc` and `lam` of the specification. -/
theorem evalTop_spec (hg : ok DS g = true) (hd : g.m = d + 1) (ht1 : 1 ≤ t) (htn : t < g.n)
    {lk : ℕ → SV}
    (hlk : ∀ H : Fin (d + 1) → ℕ, g.IsState (t + 1) H →
      lk (rank H) = ⟨stOf d Nn H % 2 ^ 48, slopes g.m (stOf d Nn H)⟩)
    (hc : RecOK DS g t c) :
    ((evalTop (mkCtx g t) lk (mkPre (mkCtx g t) lk (rsOf g d t c)) (topOf g d t c)).rp : ℤ) -
        (evalTop (mkCtx g t) lk (mkPre (mkCtx g t) lk (rsOf g d t c)) (topOf g d t c)).rn =
        Rtot DS g d (uhOf d Nn) (sgOf d Nn) t c ∧
      (evalTop (mkCtx g t) lk (mkPre (mkCtx g t) lk (rsOf g d t c)) (topOf g d t c)).ac =
        ∑ l : Fin (d + 1), (acc DS g d (uhOf d Nn) (sgOf d Nn) t c l).toNat * F128 ^ (l : ℕ) ∧
      (evalTop (mkCtx g t) lk (mkPre (mkCtx g t) lk (rsOf g d t c)) (topOf g d t c)).lm =
        ∑ l : Fin (d + 1), (lam DS g d (uhOf d Nn) (sgOf d Nn) t c l).toNat * F128 ^ (l : ℕ) := by
  have him : im d c ≤ g.L t := hc.pos_le (Fin.last d)
  obtain ⟨A, hA, h1, h2, h3⟩ := topLoop_cells (Nn := Nn) hg hd ht1 htn hlk hc (k := im d c) le_rfl
  have hev : evalTop (mkCtx g t) lk (mkPre (mkCtx g t) lk (rsOf g d t c)) (topOf g d t c) =
      topLoop (mkCtx g t) lk (mkPre (mkCtx g t) lk (rsOf g d t c)) (topOf g d t c) (tpOf g d t c)
        (mkPre (mkCtx g t) lk (rsOf g d t c)).pd 1 (Acc.mk 0 0 0 0) := rfl
  have hpd := mkPre_pd (Nn := Nn) hg hd ht1 htn hlk hc
  rw [hev, hA, ac_pack hg hc, lm_pack]
  unfold Rtot
  by_cases hf : (c (Fin.last d)).forg = true
  · have himL : im d c = g.L t := (hc.forg_iff _).mp hf
    have hnil : (mkPre (mkCtx g t) lk (rsOf g d t c)).pd.drop (im d c) = [] := by
      rw [hpd]; simp [himL]
    rw [hnil]
    simp only [hf, ite_true, add_zero]
    exact ⟨h1, h2, h3⟩
  · have hfg : (c (Fin.last d)).forg = false := by simpa using hf
    have himL : im d c < g.L t := by
      have h1x := hc.pos_le (Fin.last d)
      have h2x := (hc.forg_iff (Fin.last d)).not.mp hf
      show (c (Fin.last d)).pos < g.L t
      omega
    have hcons : (mkPre (mkCtx g t) lk (rsOf g d t c)).pd.drop (im d c) =
        pdSpec g d t Nn c (im d c + 1) :: (mkPre (mkCtx g t) lk (rsOf g d t c)).pd.drop (im d c + 1) := by
      rw [List.drop_eq_getElem_cons (by rw [hpd]; simp; omega)]
      congr 1
      simp [hpd]
    rw [hcons, topLoop_cons_gt _ _ _ _ _ _ _ _ _ (by show im d c < im d c + 1; omega), bsel_eq]
    have htf : (topOf g d t c).fg = false := hfg
    rw [ite_eq_right (by rw [htf]; exact Bool.false_ne_true)]
    have hfrom : (pdSpec g d t Nn c (im d c + 1)).from' = (mkCtx g t).cells.drop (im d c) := by
      show (mkCtx g t).cells.drop (im d c + 1 - 1) = _
      rw [Nat.add_sub_cancel]
    rw [hfrom]
    obtain ⟨e1, e2, e3⟩ := tailPart_spec hg hd ht1 htn hlk hc hfg A _ rfl
    simp only [hf, Bool.false_eq_true, ite_false]
    refine ⟨?_, ?_, ?_⟩
    · rw [e1, h1]
    · rw [e2, h2]
    · rw [e3, h3]


/-- `acc_l ≥ 0`. -/
theorem acc_nonneg (hg : ok DS g = true) (_htn : t < g.n) (hc : RecOK DS g t c) (l : Fin (d + 1)) :
    0 ≤ acc DS g d (uhOf d Nn) (sgOf d Nn) t c l := by
  rw [acc_eq_nat hg hc]; exact Int.natCast_nonneg _

/-- `lam_l ≥ 0`. -/
theorem lam_nonneg (l : Fin (d + 1)) : 0 ≤ lam DS g d (uhOf d Nn) (sgOf d Nn) t c l := by
  rw [lam_eq_nat]; exact Int.natCast_nonneg _

/-! ## The check -/

variable (g) in
/-- A passed `checkVar` on the kernel records of `c`: the claimed state is below `bound`. -/
theorem checkVar_sound (hg : ok DS g = true) {d : ℕ} (_hd1 : 1 ≤ d) (hd : g.m = d + 1) {t : ℕ}
    (ht1 : 1 ≤ t) (htn : t < g.n) {Nn : List ℕ} {lk : ℕ → SV}
    (hlk : ∀ H : Fin (d + 1) → ℕ, g.IsState (t + 1) H →
      lk (rank H) = ⟨stOf d Nn H % 2 ^ 48, slopes g.m (stOf d Nn H)⟩)
    {c : Fin (d + 1) → Rec} (hc : RecOK DS g t c) {uh : ℕ} {sg : List ℕ}
    (h : checkVar (mkCtx g t) lk uh sg
      (mkPre (mkCtx g t) lk (List.ofFn fun l : Fin d => toSR g t (c l.castSucc)))
      (toSR g t (c (Fin.last d))) = true) :
    (uh : ℤ) ≤ (bound DS g d (uhOf d Nn) (sgOf d Nn) t c).1 ∧
      ∀ l : Fin (d + 1), (sg.getD l 0 : ℤ) ≤ (bound DS g d (uhOf d Nn) (sgOf d Nn) t c).2 l := by
  change bsel (Nat.ble (Nat.add (Nat.mul (Nat.mul 2 DS2) uh)
      (evalTop (mkCtx g t) lk (mkPre (mkCtx g t) lk (rsOf g d t c)) (topOf g d t c)).rn)
      (evalTop (mkCtx g t) lk (mkPre (mkCtx g t) lk (rsOf g d t c)) (topOf g d t c)).rp)
    (muOK (lapp (mkPre (mkCtx g t) lk (rsOf g d t c)).rs [topOf g d t c]) sg
      (evalTop (mkCtx g t) lk (mkPre (mkCtx g t) lk (rsOf g d t c)) (topOf g d t c)).ac
      (evalTop (mkCtx g t) lk (mkPre (mkCtx g t) lk (rsOf g d t c)) (topOf g d t c)).lm) false = true at h
  obtain ⟨e1, e2, e3⟩ := evalTop_spec (Nn := Nn) hg hd ht1 htn hlk hc
  generalize evalTop (mkCtx g t) lk (mkPre (mkCtx g t) lk (rsOf g d t c)) (topOf g d t c) = A at h e1 e2 e3
  rw [bsel_eq] at h
  split_ifs at h with hle
  have hle' := Nat.ble_eq.mp hle
  have hrs : lapp (mkPre (mkCtx g t) lk (rsOf g d t c)).rs [topOf g d t c] =
      List.ofFn fun l : Fin (d + 1) => toSR g t (c l) := by
    show lapp (rsOf g d t c) [toSR g t (c (Fin.last d))] = _
    rw [rsOf, lapp_eq, List.ofFn_succ' (fun l : Fin (d + 1) => toSR g t (c l)), List.concat_eq_append]
  rw [hrs, e2, e3] at h
  have hmu := muOK_sound (fun l : Fin (d + 1) => toSR g t (c l)) sg
    (fun l => (acc DS g d (uhOf d Nn) (sgOf d Nn) t c l).toNat)
    (fun l => (lam DS g d (uhOf d Nn) (sgOf d Nn) t c l).toNat)
    (fun l => by
      have h1 := acc_nonneg (Nn := Nn) hg htn hc l
      have h2 := acc_lt (Nn := Nn) hg htn hc l
      omega)
    (fun l => by
      have h1 := lam_nonneg (g := g) (t := t) (Nn := Nn) (c := c) l
      have h2 := lam_le (g := g) (t := t) (Nn := Nn) (c := c) l
      have h3 : (DS : ℤ) < F128 := by norm_num [DS, F128]
      omega)
    h
  refine ⟨?_, fun l => ?_⟩
  · unfold bound
    simp only
    have hpos : (0 : ℤ) < ((2 * DS * DS : ℕ) : ℤ) := by norm_num [DS]
    rw [Int.le_ediv_iff_mul_le hpos, ← e1]
    have h2 : 2 * DS2 = 2 * DS * DS := by rw [DS2_eq, Nat.mul_assoc]
    simp only [Nat.add_eq, Nat.mul_eq, h2] at hle'
    have hle2 : ((2 * DS * DS * uh + A.rn : ℕ) : ℤ) ≤ (A.rp : ℤ) := by exact_mod_cast hle'
    push_cast at hle2 ⊢
    linarith
  · have hl := hmu l
    unfold bound
    simp only
    have hfg : (toSR g t (c l)).fg = (c l).forg := rfl
    rw [hfg] at hl
    split_ifs at hl ⊢ with hf
    · exact_mod_cast hl
    · have h1 := acc_nonneg (Nn := Nn) hg htn hc l
      have h2 := lam_nonneg (g := g) (t := t) (Nn := Nn) (c := c) l
      have h3 : ((((acc DS g d (uhOf d Nn) (sgOf d Nn) t c l).toNat / DS : ℕ) : ℤ)) =
          acc DS g d (uhOf d Nn) (sgOf d Nn) t c l / DS := by
        rw [Int.natCast_ediv, Int.toNat_of_nonneg h1]
      have h4 : (((lam DS g d (uhOf d Nn) (sgOf d Nn) t c l).toNat : ℕ) : ℤ) =
          lam DS g d (uhOf d Nn) (sgOf d Nn) t c l := Int.toNat_of_nonneg h2
      have hl' : (sg.getD l 0 : ℤ) ≤ (((lam DS g d (uhOf d Nn) (sgOf d Nn) t c l).toNat +
          (acc DS g d (uhOf d Nn) (sgOf d Nn) t c l).toNat / DS : ℕ) : ℤ) := by exact_mod_cast hl
      push_cast at hl'
      rw [h4] at hl'
      rw [← h3]
      exact hl'


end Robbins.Cert.SO.K
