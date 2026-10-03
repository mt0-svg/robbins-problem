import Robbins.Cert.SO.LS.TopV
import Robbins.Cert.SO.LS.TailS

/-!
# The lanes step: a tail cell on lanes

`tailCellV` on the lanes of a mask against `tailCell_closed` lane by lane: the masks, the crossing
quotient, the crossing terms, the chord and the additions to the accumulators.
-/

namespace Robbins.Cert.SO.L
open Robbins.Cert Robbins.Cert.K Robbins.Cert.SO.K Robbins.Lanes

/-- The chord of a tail cell on its lanes, from the check of `tailCellV`. -/
theorem ch_factsT (n h pa kk A0 A1 : ℕ) (B S q1 r1 : ℕ → ℕ) (use : ℕ → Prop) [DecidablePred use]
    (Aok : Bool) (ch : ℕ × Bool)
    (hch : ch = if ∃ l < n, use l then
        chordV (mkVC n) h (pack LW n B) (pack LW n S) (pack LW n fun _ => kk) (pack LW n fun _ => A0)
          (pack LW n fun _ => A1) (pack LW n q1) (pack LW n r1)
          (pack LW n fun l => if use l then 2 ^ 143 else 0)
      else (0, true))
    (hhD : h ≤ DS) (hBb : ∀ l < n, B l < 2 ^ 92) (hSb : ∀ l < n, S l < 2 ^ 92)
    (hkk : kk < 2 ^ 50) (hA0b : A0 < 2 ^ 92) (hA1b : A1 < 2 ^ 92)
    (hq1b : ∀ l < n, q1 l < 2 ^ 37) (hr1b : ∀ l < n, r1 l < 2 ^ 92)
    (hA : A1 = A0 + kk * h)
    (huse : ∀ l < n, use l → B l < A1 ∧ A0 < B l + S l ∧ 0 < S l)
    (hq : ∀ l < n, use l → A0 < B l → q1 l = (B l - A0) / kk ∧ r1 l = (B l - A0) % kk)
    (hok : bsel ch.2 Aok false = true) :
    ch.1 = (pack LW n fun l => if use l then chord.chord1 pa (pa + h) (B l) (S l) kk A0 A1 else 0) ∧
      ch.2 = true ∧ Aok = true ∧
      ∀ l < n, use l → chord.chord1 pa (pa + h) (B l) (S l) kk A0 A1 ≤ QMX := by
  subst hch
  obtain ⟨h2, hAok⟩ := bsel_and _ _ hok
  by_cases hE : ∃ l < n, use l
  · rw [ite_eq_left hE] at h2 ⊢
    obtain ⟨e1, e2⟩ := chordV_spec n h pa B S (fun _ => kk) (fun _ => A0) (fun _ => A1) q1 r1 use hhD
      hBb hSb (fun _ _ => hkk) (fun _ _ => hA0b) (fun _ _ => hA1b) hq1b hr1b (fun _ _ _ => hA)
      huse hq h2
    exact ⟨e1, h2, hAok, e2⟩
  · rw [ite_eq_right hE]
    refine ⟨?_, rfl, hAok, fun l hl hc => absurd ⟨l, hl, hc⟩ hE⟩
    exact ((pack_congr _ _ _ _ fun l hl => ite_eq_right fun hc => hE ⟨l, hl, hc⟩).trans
      (pack_zeros n)).symm

theorem tailCellV5_core (n m a1 a0 sig kk A0 A1 : ℕ) (cl : SC) (B Sf q1 r1 : ℕ → ℕ)
    (gf : ℕ → ℕ → ℕ) (cont : ℕ → Prop) [DecidablePred cont] (A : LA) (rpf rnf : ℕ → ℕ)
    (af : ℕ → ℕ → ℕ)
    (hpab : cl.pa ≤ cl.pb) (hpbD : cl.pb ≤ DS) (hh : cl.h = cl.pb - cl.pa)
    (ha1 : a1 < 2 ^ 47) (ha0 : a0 < 2 ^ 80) (hsig : sig < 2 ^ 48) (hkk : kk = a1 + sig)
    (hA0 : A0 = a0 + kk * cl.pa) (hA1 : A1 = a0 + kk * cl.pb) (hA1b : A1 < 2 ^ 90)
    (hBb : ∀ l < n, B l < 2 ^ 90) (hSb : ∀ l < n, Sf l < 2 ^ 91)
    (hgb : ∀ f l, l < n → gf f l < 2 ^ 48)
    (hq1b : ∀ l < n, q1 l < 2 ^ 37) (hr1b : ∀ l < n, r1 l < 2 ^ 92)
    (hq1e : ∀ l < n, cont l → ¬ A1 ≤ B l → A0 < B l →
      q1 l = (B l - A0) / kk ∧ r1 l = (B l - A0) % kk)
    (hArp : A.rp = pack LW n rpf) (hArn : A.rn = pack LW n rnf)
    (hAac : A.ac = (List.range m).map fun q => pack LW n (af q))
    (hok : (tailCellV.tailCellV5 (mkVC n) a1 a0 (pack LW n Sf)
      ((List.range m).map fun f => pack LW n (gf f)) cl (pack LW n fun l => if cont l then 2 ^ 143 else 0)
      A sig (pack LW n B) kk A0 A1 (pack LW n fun l => if A1 ≤ B l then 2 ^ 143 else 0)
      (pack LW n fun l => if B l ≤ A0 then 2 ^ 143 else 0)
      (pack LW n fun l => if cont l ∧ ¬A1 ≤ B l ∧ ¬B l ≤ A0 then 2 ^ 143 else 0)
      (pack LW n fun l => if cont l ∧ Sf l ≠ 0 ∧ ¬A1 ≤ B l ∧ ¬B l + Sf l ≤ A0 then 2 ^ 143 else 0)
      (pack LW n q1, pack LW n r1)).ok = true) :
    tailCellV.tailCellV5 (mkVC n) a1 a0 (pack LW n Sf)
      ((List.range m).map fun f => pack LW n (gf f)) cl (pack LW n fun l => if cont l then 2 ^ 143 else 0)
      A sig (pack LW n B) kk A0 A1 (pack LW n fun l => if A1 ≤ B l then 2 ^ 143 else 0)
      (pack LW n fun l => if B l ≤ A0 then 2 ^ 143 else 0)
      (pack LW n fun l => if cont l ∧ ¬A1 ≤ B l ∧ ¬B l ≤ A0 then 2 ^ 143 else 0)
      (pack LW n fun l => if cont l ∧ Sf l ≠ 0 ∧ ¬A1 ≤ B l ∧ ¬B l + Sf l ≤ A0 then 2 ^ 143 else 0)
      (pack LW n q1, pack LW n r1) = LA.mk
      (pack LW n fun l => rpf l + if cont l then cRP a1 a0 kk A0 A1 cl.pa cl.pb cl.h (B l) else 0)
      (pack LW n fun l => rnf l + if cont l then cRN sig kk A0 A1 cl.pa cl.pb (B l) else 0)
      ((List.range m).map fun q => pack LW n fun l => af q l +
        if cont l ∧ Sf l ≠ 0 then gf q l * chord.chord1 cl.pa cl.pb (B l) (Sf l) kk A0 A1 else 0)
      A.lm A.ok ∧
    ∀ l < n, cont l → Sf l ≠ 0 → chord.chord1 cl.pa cl.pb (B l) (Sf l) kk A0 A1 < 2 ^ 37 := by
  have hDS : DS = 2 ^ 36 := rfl
  have b143 : ∀ {x k : ℕ}, x < 2 ^ k → k ≤ 143 → x < 2 ^ 143 := fun hx hk =>
    lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hk)
  have b144 : ∀ {x k : ℕ}, x < 2 ^ k → k ≤ 144 → x < 2 ^ 144 := fun hx hk =>
    lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hk)
  have hhD : cl.h ≤ DS := by omega
  have hkkb : kk < 2 ^ 50 := by
    have : (2 : ℕ) ^ 47 + 2 ^ 48 ≤ 2 ^ 50 := by norm_num
    omega
  have hA01 : A0 ≤ A1 := by rw [hA0, hA1]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hpab) _
  have hA0b : A0 < 2 ^ 90 := lt_of_le_of_lt hA01 hA1b
  have hAh : A1 = A0 + kk * cl.h := by
    rw [hA1, hA0, hh, Nat.mul_sub, add_assoc, Nat.add_sub_cancel' (Nat.mul_le_mul_left _ hpab)]
  have hpah : cl.pa + cl.h = cl.pb := by omega
  have hdivh : ∀ l < n, ¬ A1 ≤ B l → A0 < B l → 0 < kk ∧ (B l - A0) / kk < cl.h := fun l hl h1 h2 => by
    have hK : 0 < kk := by
      rcases Nat.eq_zero_or_pos kk with h0 | h0
      · rw [h0, zero_mul, add_zero] at hAh; omega
      · exact h0
    refine ⟨hK, (Nat.div_lt_iff_lt_mul hK).2 ?_⟩
    rw [mul_comm]; omega
  unfold tailCellV.tailCellV5 tailCellV.tailCellV6 tailCellV.tailCellV7 at hok ⊢
  rw [bsel_mask_eq, bsel_mask_eq] at hok ⊢
  rw [show ((pack LW n q1, pack LW n r1) : ℕ × ℕ).1 = pack LW n q1 from rfl,
    show ((pack LW n q1, pack LW n r1) : ℕ × ℕ).2 = pack LW n r1 from rfl] at hok ⊢
  rw [crossT_spec n a1 a0 sig kk cl B q1 ha1 ha0 hsig hkkb (by omega) hpbD hhD
    (fun l hl => lt_trans (hBb l hl) (by norm_num)) hq1b] at hok ⊢
  rw [ite_fst, ite_snd] at hok ⊢
  simp only [bc_eq] at hok ⊢
  obtain ⟨eC1, eC2, hAok, hQMX⟩ := ch_factsT n cl.h cl.pa kk A0 A1 B Sf q1 r1
    (fun l => cont l ∧ Sf l ≠ 0 ∧ ¬A1 ≤ B l ∧ ¬B l + Sf l ≤ A0) A.ok _ rfl hhD
    (fun l hl => lt_trans (hBb l hl) (by norm_num)) (fun l hl => lt_trans (hSb l hl) (by norm_num))
    hkkb (lt_trans hA0b (by norm_num)) (lt_trans hA1b (by norm_num)) hq1b hr1b hAh
    (fun l _ hu => ⟨not_le.1 hu.2.2.1, not_le.1 hu.2.2.2, Nat.pos_of_ne_zero hu.2.1⟩)
    (fun l hl hu hlt => hq1e l hl hu.1 hu.2.2.1 hlt) (show bsel _ A.ok false = true from hok)
  rw [hpah] at eC1 hQMX
  rw [eC1, eC2]
  clear hok eC1 eC2
  have hQlt : ∀ l < n, cont l → Sf l ≠ 0 → chord.chord1 cl.pa cl.pb (B l) (Sf l) kk A0 A1 < 2 ^ 37 := by
    intro l hl hc hS
    by_cases h1 : A1 ≤ B l
    · rw [chord1_hi _ _ _ _ _ _ _ h1]; positivity
    · by_cases h3 : B l + Sf l ≤ A0
      · rw [chord1_lo _ _ _ _ _ _ _ h1 h3]; rw [hDS] at hpbD; omega
      · exact lt_of_le_of_lt (hQMX l hl ⟨hc, hS, h1, h3⟩) (by norm_num [QMX])
  refine ⟨?_, hQlt⟩
  have hBS : ∀ l < n, B l + Sf l < 2 ^ 92 := fun l hl => by
    have := hBb l hl; have := hSb l hl
    have : (2 : ℕ) ^ 90 + 2 ^ 91 ≤ 2 ^ 92 := by norm_num
    omega
  have hcrp : ∀ l < n, (a0 + a0 + a1 * (cl.pa + cl.pa + q1 l)) * q1 l + 2 * (B l * (cl.h - q1 l)) <
      2 ^ 131 := fun l hl => crossP_lt _ _ _ _ _ _ ha0 ha1 (by omega) (hq1b l hl)
        (lt_trans (hBb l hl) (by norm_num)) (by omega)
  have hcrn : ∀ l < n, sig * (cl.pb * cl.pb - (cl.pa + q1 l) * ((cl.pa + q1 l) % 2 ^ 37)) + (kk + kk) <
      2 ^ 131 := fun l hl => by
    rw [mul_comm sig]; exact crossN_lt _ _ _ _ _ (by omega) hsig hkkb
  have hhB : ∀ l < n, (cl.h + cl.h) * B l < 2 ^ 144 := fun l hl =>
    mul_lt_pow (show cl.h + cl.h < 2 ^ 38 by omega) (hBb l hl) (by norm_num)
  have hrpHI : cl.h * (a0 + a0 + a1 * (cl.pb + cl.pa)) < 2 ^ 144 := by
    have e1 : a1 * (cl.pb + cl.pa) < 2 ^ 85 :=
      mul_lt_pow ha1 (show cl.pb + cl.pa < 2 ^ 38 by omega) (by norm_num)
    have e2 : a0 + a0 + a1 * (cl.pb + cl.pa) < 2 ^ 86 := by
      have : (2 : ℕ) ^ 80 + 2 ^ 80 + 2 ^ 85 ≤ 2 ^ 86 := by norm_num
      omega
    exact mul_lt_pow (show cl.h < 2 ^ 37 by omega) e2 (by norm_num)
  have hrnLOW : sig * (cl.pb * cl.pb - cl.pa * cl.pa) < 2 ^ 144 := by
    have e1 : cl.pb * cl.pb ≤ 2 ^ 72 := (Nat.mul_le_mul (hpbD.trans (le_of_eq hDS))
      (hpbD.trans (le_of_eq hDS))).trans (by norm_num)
    exact mul_lt_pow hsig (show cl.pb * cl.pb - cl.pa * cl.pa < 2 ^ 73 by omega) (by norm_num)
  rw [LA.mk.injEq]
  set E := ∃ l < n, cont l ∧ ¬A1 ≤ B l ∧ ¬B l ≤ A0 with hE
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · have hX : ∀ l < n, (if E then (a0 + a0 + a1 * (cl.pa + cl.pa + q1 l)) * q1 l +
        2 * (B l * (cl.h - q1 l)) else 0) < 2 ^ 131 := fun l hl => by
      split_ifs
      · exact hcrp l hl
      · norm_num
    simp only [Nat.add_eq, Nat.mul_eq]
    rw [pack_const_mul,
      sl_eq n (fun l => B l ≤ A0) (fun l => (cl.h + cl.h) * B l) (fun l => if E then
        (a0 + a0 + a1 * (cl.pa + cl.pa + q1 l)) * q1 l + 2 * (B l * (cl.h - q1 l)) else 0) hhB
        (fun l hl => b144 (hX l hl) (by norm_num)),
      sl_eq n (fun l => A1 ≤ B l) (fun _ => cl.h * (a0 + a0 + a1 * (cl.pb + cl.pa))) _ (fun _ _ => hrpHI)
        ?_, msk_eq n cont _ ?_, hArp, pack_add]
    · refine pack_congr _ _ _ _ fun l hl => ?_
      congr 1
      by_cases hc : cont l
      · rw [ite_eq_left hc, ite_eq_left hc]
        unfold cRP
        by_cases h1 : A1 ≤ B l
        · rw [ite_eq_left h1, ite_eq_left h1]
        · rw [ite_eq_right h1, ite_eq_right h1]
          by_cases h2 : B l ≤ A0
          · rw [ite_eq_left h2, ite_eq_left h2]
          · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_left ⟨l, hl, hc, h1, h2⟩,
              (hq1e l hl hc h1 (not_le.1 h2)).1]
      · rw [ite_eq_right hc, ite_eq_right hc]
    · intro l hl
      split_ifs <;> first | exact hhB l hl | exact hrpHI | exact hrnLOW | exact b144 (hcrp l hl) (by norm_num) | exact b144 (hcrn l hl) (by norm_num) | norm_num
    · intro l hl
      split_ifs <;> first | exact hhB l hl | exact hrpHI | exact hrnLOW | exact b144 (hcrp l hl) (by norm_num) | exact b144 (hcrn l hl) (by norm_num) | norm_num
  · have hX : ∀ l < n, (if E then sig * (cl.pb * cl.pb - (cl.pa + q1 l) * ((cl.pa + q1 l) % 2 ^ 37)) +
        (kk + kk) else 0) < 2 ^ 131 := fun l hl => by
      split_ifs
      · exact hcrn l hl
      · norm_num
    simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
    rw [sl_eq n (fun l => B l ≤ A0) (fun _ => sig * (cl.pb * cl.pb - cl.pa * cl.pa)) (fun l => if E then
        sig * (cl.pb * cl.pb - (cl.pa + q1 l) * ((cl.pa + q1 l) % 2 ^ 37)) + (kk + kk) else 0)
        (fun _ _ => hrnLOW) (fun l hl => b144 (hX l hl) (by norm_num)),
      sl_zero_eq n (fun l => A1 ≤ B l) _ ?_, msk_eq n cont _ ?_, hArn, pack_add]
    · refine pack_congr _ _ _ _ fun l hl => ?_
      congr 1
      by_cases hc : cont l
      · rw [ite_eq_left hc, ite_eq_left hc]
        unfold cRN
        by_cases h1 : A1 ≤ B l
        · rw [ite_eq_left h1, ite_eq_left h1]
        · rw [ite_eq_right h1, ite_eq_right h1]
          by_cases h2 : B l ≤ A0
          · rw [ite_eq_left h2, ite_eq_left h2]
          · have hlt := (hdivh l hl h1 (not_le.1 h2)).2
            rw [ite_eq_right h2, ite_eq_right h2, ite_eq_left ⟨l, hl, hc, h1, h2⟩,
              (hq1e l hl hc h1 (not_le.1 h2)).1, Nat.mod_eq_of_lt (by omega)]
      · rw [ite_eq_right hc, ite_eq_right hc]
    · intro l hl
      split_ifs <;> first | exact hhB l hl | exact hrpHI | exact hrnLOW | exact b144 (hcrp l hl) (by norm_num) | exact b144 (hcrn l hl) (by norm_num) | norm_num
    · intro l hl
      split_ifs <;> first | exact hhB l hl | exact hrpHI | exact hrnLOW | exact b144 (hcrp l hl) (by norm_num) | exact b144 (hcrn l hl) (by norm_num) | norm_num
  · have eBS : Nat.add (pack LW n B) (pack LW n Sf) = pack LW n fun l => B l + Sf l := by
      rw [Nat.add_eq, pack_add]
    have eQH : sl (pack LW n fun l => if B l + Sf l ≤ A0 then 2 ^ 143 else 0) (pack LW n fun _ => cl.h) 0 =
        pack LW n fun l => if B l + Sf l ≤ A0 then cl.h else 0 := by
      have e := sl_eq n (fun l => B l + Sf l ≤ A0) (fun _ => cl.h) (fun _ => 0)
        (fun _ _ => by omega) (fun _ _ => by norm_num)
      rw [pack_zeros] at e
      exact e
    have hQv : ∀ l < n, (if cont l ∧ Sf l ≠ 0 ∧ ¬A1 ≤ B l then
        (if B l + Sf l ≤ A0 then cl.h else 0) +
          (if cont l ∧ Sf l ≠ 0 ∧ ¬A1 ≤ B l ∧ ¬B l + Sf l ≤ A0 then
            chord.chord1 cl.pa cl.pb (B l) (Sf l) kk A0 A1 else 0) else 0) =
        if cont l ∧ Sf l ≠ 0 ∧ ¬A1 ≤ B l then chord.chord1 cl.pa cl.pb (B l) (Sf l) kk A0 A1 else 0 :=
      fun l hl => by
        by_cases hu : cont l ∧ Sf l ≠ 0 ∧ ¬A1 ≤ B l
        · rw [ite_eq_left hu, ite_eq_left hu]
          by_cases h3 : B l + Sf l ≤ A0
          · rw [ite_eq_left h3, ite_eq_right (fun h => h.2.2.2 h3), add_zero,
              chord1_lo _ _ _ _ _ _ _ hu.2.2 h3, hh]
          · rw [ite_eq_right h3, ite_eq_left ⟨hu.1, hu.2.1, hu.2.2, h3⟩, zero_add]
        · rw [ite_eq_right hu, ite_eq_right hu]
    have hv : ∀ l < n, (if B l + Sf l ≤ A0 then cl.h else 0) +
        (if cont l ∧ Sf l ≠ 0 ∧ ¬A1 ≤ B l ∧ ¬B l + Sf l ≤ A0 then
          chord.chord1 cl.pa cl.pb (B l) (Sf l) kk A0 A1 else 0) < 2 ^ 144 := fun l hl => by
      have e1 : (if B l + Sf l ≤ A0 then cl.h else 0) ≤ 2 ^ 36 := by split_ifs <;> omega
      have e2 : (if cont l ∧ Sf l ≠ 0 ∧ ¬A1 ≤ B l ∧ ¬B l + Sf l ≤ A0 then
          chord.chord1 cl.pa cl.pb (B l) (Sf l) kk A0 A1 else 0) ≤ QMX := by
        split_ifs with hch
        · exact hQMX l hl hch
        · exact Nat.zero_le _
      have : QMX < 2 ^ 37 := by norm_num [QMX]
      omega
    rw [eBS, ge_eq n (fun _ => A0) (fun l => B l + Sf l) (fun _ _ => b143 hA0b (by norm_num))
        (fun l hl => b143 (hBS l hl) (by norm_num)), eQH,
      nz_eq n Sf (fun l hl => b143 (hSb l hl) (by norm_num)), notM_eq, land_gm, land_gm, Nat.add_eq,
      pack_add, msk_eq n _ _ hv,
      pack_congr _ _ _ _ hQv]
    rw [lmap_eq, List.map_map, hAac]
    have eM : ∀ f, mulv (mkVC n) 37 (pack LW n (gf f)) (pack LW n fun l =>
        if cont l ∧ Sf l ≠ 0 ∧ ¬A1 ≤ B l then chord.chord1 cl.pa cl.pb (B l) (Sf l) kk A0 A1 else 0) =
        pack LW n fun l => gf f l *
          (if cont l ∧ Sf l ≠ 0 ∧ ¬A1 ≤ B l then chord.chord1 cl.pa cl.pb (B l) (Sf l) kk A0 A1 else 0) :=
      fun f => mulv_eq' n 37 _ _ (by norm_num)
        (fun l hl j hj => mul_lt_pow (hgb f l hl) (Nat.pow_lt_pow_right (by norm_num) hj) (by omega))
        (fun l hl => by
          split_ifs with hu
          · exact hQlt l hl hu.1 hu.2.1
          · positivity)
    simp only [Function.comp_def, eM]
    rw [addL_map]
    refine List.map_congr_left fun q _ => ?_
    rw [pack_add]
    refine pack_congr _ _ _ _ fun l hl => ?_
    congr 1
    by_cases hc : cont l ∧ Sf l ≠ 0
    · rw [ite_eq_left hc]
      by_cases h1 : A1 ≤ B l
      · rw [ite_eq_right (fun h => h.2.2 h1), chord1_hi _ _ _ _ _ _ _ h1, mul_zero]
      · rw [ite_eq_left ⟨hc.1, hc.2, h1⟩]
    · rw [ite_eq_right hc, ite_eq_right (fun h => hc ⟨h.1, h.2.1⟩), mul_zero]

/-- A tail cell on the lanes of `cont`, from `kk`, `A0`, `A1` (`B` the lanes of `beta`). -/
theorem tailCellV2_core (n m a1 a0 sig kk A0 A1 : ℕ) (cl : SC) (B Sf : ℕ → ℕ) (gf : ℕ → ℕ → ℕ)
    (cont : ℕ → Prop) [DecidablePred cont] (A : LA) (rpf rnf : ℕ → ℕ) (af : ℕ → ℕ → ℕ)
    (hpab : cl.pa ≤ cl.pb) (hpbD : cl.pb ≤ DS) (hh : cl.h = cl.pb - cl.pa)
    (ha1 : a1 < 2 ^ 47) (ha0 : a0 < 2 ^ 80) (hsig : sig < 2 ^ 48) (hkk : kk = a1 + sig)
    (hA0 : A0 = a0 + kk * cl.pa) (hA1 : A1 = a0 + kk * cl.pb) (hA1b : A1 < 2 ^ 90)
    (hBb : ∀ l < n, B l < 2 ^ 90) (hSb : ∀ l < n, Sf l < 2 ^ 91)
    (hgb : ∀ f l, l < n → gf f l < 2 ^ 48)
    (hArp : A.rp = pack LW n rpf) (hArn : A.rn = pack LW n rnf)
    (hAac : A.ac = (List.range m).map fun q => pack LW n (af q))
    (hok : (tailCellV.tailCellV2 (mkVC n) a1 a0 (pack LW n Sf)
      ((List.range m).map fun f => pack LW n (gf f)) cl (pack LW n fun l => if cont l then 2 ^ 143 else 0)
      A sig (pack LW n B) kk A0 A1).ok = true) :
    tailCellV.tailCellV2 (mkVC n) a1 a0 (pack LW n Sf) ((List.range m).map fun f => pack LW n (gf f))
      cl (pack LW n fun l => if cont l then 2 ^ 143 else 0) A sig (pack LW n B) kk A0 A1 = LA.mk
      (pack LW n fun l => rpf l + if cont l then cRP a1 a0 kk A0 A1 cl.pa cl.pb cl.h (B l) else 0)
      (pack LW n fun l => rnf l + if cont l then cRN sig kk A0 A1 cl.pa cl.pb (B l) else 0)
      ((List.range m).map fun q => pack LW n fun l => af q l +
        if cont l ∧ Sf l ≠ 0 then gf q l * chord.chord1 cl.pa cl.pb (B l) (Sf l) kk A0 A1 else 0)
      A.lm A.ok ∧
    ∀ l < n, cont l → Sf l ≠ 0 → chord.chord1 cl.pa cl.pb (B l) (Sf l) kk A0 A1 < 2 ^ 37 := by
  have hDS : DS = 2 ^ 36 := rfl
  have b143 : ∀ {x k : ℕ}, x < 2 ^ k → k ≤ 143 → x < 2 ^ 143 := fun hx hk =>
    lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hk)
  have hhD : cl.h ≤ DS := by omega
  have hkkb : kk < 2 ^ 50 := by
    have : (2 : ℕ) ^ 47 + 2 ^ 48 ≤ 2 ^ 50 := by norm_num
    omega
  have hA01 : A0 ≤ A1 := by rw [hA0, hA1]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hpab) _
  have hA0b : A0 < 2 ^ 90 := lt_of_le_of_lt hA01 hA1b
  have hAh : A1 = A0 + kk * cl.h := by
    rw [hA1, hA0, hh, Nat.mul_sub, add_assoc, Nat.add_sub_cancel' (Nat.mul_le_mul_left _ hpab)]
  have eHI := ge_eq n B (fun _ => A1) (fun l hl => b143 (hBb l hl) (by norm_num))
    (fun _ _ => b143 hA1b (by norm_num))
  have eLOW := ge_eq n (fun _ => A0) B (fun _ _ => b143 hA0b (by norm_num))
    (fun l hl => b143 (hBb l hl) (by norm_num))
  have eBS : Nat.add (pack LW n B) (pack LW n Sf) = pack LW n fun l => B l + Sf l := by
    rw [Nat.add_eq, pack_add]
  have eGE2 := ge_eq n (fun _ => A0) (fun l => B l + Sf l) (fun _ _ => b143 hA0b (by norm_num))
    (fun l hl => b143 (show B l + Sf l < 2 ^ 92 by
      have := hBb l hl; have := hSb l hl
      have : (2 : ℕ) ^ 90 + 2 ^ 91 ≤ 2 ^ 92 := by norm_num
      omega) (by norm_num))
  have eNZ := nz_eq n Sf (fun l hl => b143 (hSb l hl) (by norm_num))
  have eTS := tsub_eq n B (fun _ => A0) (fun l hl => b143 (hBb l hl) (by norm_num))
    (fun _ _ => b143 hA0b (by norm_num))
  have eDQ := divQR_eq n (fun l => B l - A0) (fun _ => kk)
    (fun l hl => b143 (lt_of_le_of_lt (Nat.sub_le _ _) (hBb l hl)) (by norm_num))
    (fun l hl j hj => mul_lt_pow hkkb (Nat.pow_lt_pow_right (by norm_num) hj) (by omega))
  unfold tailCellV.tailCellV2 tailCellV.tailCellV3 tailCellV.tailCellV4 at hok ⊢
  simp only [bc_eq] at hok ⊢
  rw [eHI, eLOW, eBS, eGE2, eNZ] at hok ⊢
  simp only [notM_eq, land_gm, lor_gm] at hok ⊢
  rw [bsel_mask_eq, eTS, eDQ, ite_pack2] at hok ⊢
  refine tailCellV5_core n m a1 a0 sig kk A0 A1 cl B Sf _ _ gf cont A rpf rnf af hpab hpbD hh ha1 ha0
    hsig hkk hA0 hA1 hA1b hBb hSb hgb ?_ ?_ ?_ hArp hArn hAac hok
  · intro l hl
    show _
    split_ifs <;> omega
  · intro l hl
    show _
    split_ifs <;> first
      | exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_le_of_lt (Nat.sub_le _ _)
          (lt_trans (hBb l hl) (by norm_num)))
      | norm_num
  · intro l hl hc h1 h2
    show _
    have hK : 0 < kk := by
      rcases Nat.eq_zero_or_pos kk with h0 | h0
      · rw [h0, zero_mul, add_zero] at hAh; omega
      · exact h0
    have hlt : (B l - A0) / kk < cl.h := (Nat.div_lt_iff_lt_mul hK).2 (by rw [mul_comm]; omega)
    have hmin : min ((B l - A0) / kk) (2 ^ 37 - 1) = (B l - A0) / kk :=
      min_eq_left (by rw [hDS] at hhD; omega)
    rw [ite_eq_right (Nat.pos_iff_ne_zero.1 hK), hmin, ite_eq_left ⟨l, hl, Or.inl ⟨hc, h1, not_le.2 h2⟩⟩,
      ite_eq_left ⟨l, hl, Or.inl ⟨hc, h1, not_le.2 h2⟩⟩, Nat.mod_eq_sub_mul_div]
    exact ⟨rfl, rfl⟩

/-- A tail cell on the lanes of `cont` in the closed form of `tailCell_closed`: `sigma = r e1`,
`beta = D et + U + sigma pb` on each lane. -/
theorem tailCellV_core (n m r a1 a0 : ℕ) (cl : SC) (Uf Sf : ℕ → ℕ) (gf : ℕ → ℕ → ℕ)
    (cont : ℕ → Prop) [DecidablePred cont] (A : LA) (rpf rnf : ℕ → ℕ) (af : ℕ → ℕ → ℕ)
    (hpab : cl.pa ≤ cl.pb) (hpbD : cl.pb ≤ DS) (hh : cl.h = cl.pb - cl.pa) (het : cl.et ≤ DS)
    (he1 : cl.e1 ≤ DS) (hr : r ≤ 1023) (ha1 : a1 = r * DS) (ha0 : a0 < 2 ^ 80)
    (hU : ∀ l < n, Uf l < 2 ^ 85) (hS : ∀ l < n, Sf l < 2 ^ 91) (hg : ∀ f l, l < n → gf f l < 2 ^ 48)
    (hArp : A.rp = pack LW n rpf) (hArn : A.rn = pack LW n rnf)
    (hAac : A.ac = (List.range m).map fun q => pack LW n (af q))
    (hok : (tailCellV (mkVC n) r a1 a0 (pack LW n Uf) (pack LW n Sf)
      ((List.range m).map fun f => pack LW n (gf f)) cl (pack LW n fun l => if cont l then 2 ^ 143 else 0)
      A).ok = true) :
    tailCellV (mkVC n) r a1 a0 (pack LW n Uf) (pack LW n Sf)
      ((List.range m).map fun f => pack LW n (gf f)) cl (pack LW n fun l => if cont l then 2 ^ 143 else 0)
      A = LA.mk
      (pack LW n fun l => rpf l + if cont l then cRP a1 a0 (a1 + r * cl.e1) (a0 + (a1 + r * cl.e1) * cl.pa)
        (a0 + (a1 + r * cl.e1) * cl.pb) cl.pa cl.pb cl.h (DS * cl.et + Uf l + r * cl.e1 * cl.pb) else 0)
      (pack LW n fun l => rnf l + if cont l then cRN (r * cl.e1) (a1 + r * cl.e1)
        (a0 + (a1 + r * cl.e1) * cl.pa) (a0 + (a1 + r * cl.e1) * cl.pb) cl.pa cl.pb
        (DS * cl.et + Uf l + r * cl.e1 * cl.pb) else 0)
      ((List.range m).map fun q => pack LW n fun l => af q l +
        if cont l ∧ Sf l ≠ 0 then gf q l * chord.chord1 cl.pa cl.pb (DS * cl.et + Uf l + r * cl.e1 * cl.pb)
          (Sf l) (a1 + r * cl.e1) (a0 + (a1 + r * cl.e1) * cl.pa) (a0 + (a1 + r * cl.e1) * cl.pb) else 0)
      A.lm A.ok ∧
    ∀ l < n, cont l → Sf l ≠ 0 → chord.chord1 cl.pa cl.pb (DS * cl.et + Uf l + r * cl.e1 * cl.pb)
      (Sf l) (a1 + r * cl.e1) (a0 + (a1 + r * cl.e1) * cl.pa) (a0 + (a1 + r * cl.e1) * cl.pb) < 2 ^ 37 := by
  have hDS : DS = 2 ^ 36 := rfl
  have hr46 : r * DS < 2 ^ 46 := by
    rw [hDS]
    calc r * 2 ^ 36 ≤ 1023 * 2 ^ 36 := Nat.mul_le_mul_right _ hr
      _ < 2 ^ 46 := by norm_num
  have hsg : r * cl.e1 < 2 ^ 46 := lt_of_le_of_lt (Nat.mul_le_mul_left _ he1) hr46
  have ha1b : a1 < 2 ^ 47 := by rw [ha1]; omega
  have hpb36 : cl.pb ≤ 2 ^ 36 := hpbD.trans (le_of_eq hDS)
  have hKpb : (a1 + r * cl.e1) * cl.pb < 2 ^ 85 :=
    mul_lt_pow (show a1 + r * cl.e1 < 2 ^ 48 by rw [ha1]; omega) (show cl.pb < 2 ^ 37 by omega)
      (by norm_num)
  have hA1b : a0 + (a1 + r * cl.e1) * cl.pb < 2 ^ 90 := by
    have : (2 : ℕ) ^ 80 + 2 ^ 85 ≤ 2 ^ 90 := by norm_num
    omega
  have hBb : ∀ l < n, DS * cl.et + Uf l + r * cl.e1 * cl.pb < 2 ^ 90 := fun l hl => by
    have e1 : DS * cl.et ≤ 2 ^ 72 := (Nat.mul_le_mul (le_of_eq hDS) (het.trans (le_of_eq hDS))).trans
      (by norm_num)
    have e2 : r * cl.e1 * cl.pb < 2 ^ 83 := mul_lt_pow hsg (show cl.pb < 2 ^ 37 by omega) (by norm_num)
    have := hU l hl
    have : (2 : ℕ) ^ 72 + 2 ^ 85 + 2 ^ 83 ≤ 2 ^ 90 := by norm_num
    omega
  have hB : (fun l => Uf l + (DS * cl.et + r * cl.e1 * cl.pb)) =
      fun l => DS * cl.et + Uf l + r * cl.e1 * cl.pb := by
    funext l; ring
  rw [tailCellV_top, hB] at hok ⊢
  exact tailCellV2_core n m a1 a0 (r * cl.e1) (a1 + r * cl.e1) _ _ cl
    (fun l => DS * cl.et + Uf l + r * cl.e1 * cl.pb) Sf gf cont A rpf rnf af hpab hpbD hh ha1b ha0
    (by omega) rfl rfl rfl hA1b hBb hS hg hArp hArn hAac hok

end Robbins.Cert.SO.L
