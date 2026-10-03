import Robbins.Cert.SO.LS.Vec
import Robbins.Cert.SO.LS.Kc

/-!
# The lanes step: the leaves of the tail

The tail cells of a top record on lanes (`tailV`) against `tailCells` lane by lane: the scalar closed
forms of `tailCell` and `tailEnd`, the bounds of their additions, the masks of the lanes that stop
and go on, the exact tail on lanes, and the flag `ok` of `tailV`.
-/

namespace Robbins.Cert.SO.L

open Robbins.Cert Robbins.Cert.K Robbins.Cert.SO.K Robbins.Lanes

/-- The addition to `rp` of a tail cell on a lane with `beta = B` (`kk = a1 + sig`, `A0 = a0 + kk pa`,
`A1 = a0 + kk pb`): the three cases of `cell2`. -/
noncomputable def cRP (a1 a0 kk A0 A1 pa pb h B : ℕ) : ℕ :=
  if A1 ≤ B then h * (a0 + a0 + a1 * (pb + pa)) else if B ≤ A0 then (h + h) * B else
    (a0 + a0 + a1 * (pa + pa + (B - A0) / kk)) * ((B - A0) / kk) + 2 * (B * (h - (B - A0) / kk))

/-- The addition to `rn` of a tail cell on a lane with `beta = B`. -/
noncomputable def cRN (sig kk A0 A1 pa pb B : ℕ) : ℕ :=
  if A1 ≤ B then 0 else if B ≤ A0 then sig * (pb * pb - pa * pa) else
    sig * (pb * pb - (pa + (B - A0) / kk) * (pa + (B - A0) / kk)) + (kk + kk)

/-- A tail cell in closed form: `rp`, `rn` grow by `cRP`, `cRN` and `ac` by `chord * slcF` where
`S ≠ 0`, then the continuation. -/
theorem tailCell_closed (r a1 a0 U S slcF : ℕ) (cl : SC) (k : Acc → Acc) (sig beta : ℕ) (A : Acc)
    (hh : cl.h = cl.pb - cl.pa) (hbeta : beta = DS * cl.et + U + sig * cl.pb) :
    tailCells.tailCell r a1 a0 U S slcF cl k sig A = k (Acc.mk
      (A.rp + cRP a1 a0 (a1 + sig) (a0 + (a1 + sig) * cl.pa) (a0 + (a1 + sig) * cl.pb) cl.pa cl.pb
        cl.h beta)
      (A.rn + cRN sig (a1 + sig) (a0 + (a1 + sig) * cl.pa) (a0 + (a1 + sig) * cl.pb) cl.pa cl.pb beta)
      (A.ac + if S = 0 then 0 else chord.chord1 cl.pa cl.pb beta S (a1 + sig)
        (a0 + (a1 + sig) * cl.pa) (a0 + (a1 + sig) * cl.pb) * slcF)
      A.lm) := by
  unfold tailCells.tailCell tailCells.tailCell1 tailCells.tailCell2
  rw [show Nat.add (Nat.add (Nat.mul DS cl.et) U) (Nat.mul sig cl.pb) = beta from hbeta.symm]
  congr 1
  set kk := a1 + sig with hkk
  set A0 := a0 + kk * cl.pa with hA0
  set A1 := a0 + kk * cl.pb with hA1
  have ec : chord cl.pa cl.pb a0 a1 beta sig S = chord.chord1 cl.pa cl.pb beta S kk A0 A1 := rfl
  have eac : bsel (Nat.beq S 0) A.ac (Nat.add A.ac (Nat.mul (chord cl.pa cl.pb a0 a1 beta sig S) slcF)) =
      A.ac + if S = 0 then 0 else chord.chord1 cl.pa cl.pb beta S kk A0 A1 * slcF := by
    rw [ec, bsel_eq]
    by_cases hS : S = 0
    · rw [ite_eq_left (by rw [Nat.beq_eq]; exact hS), ite_eq_left hS, add_zero]
    · rw [ite_eq_right (by rw [Nat.beq_eq]; exact hS), ite_eq_right hS]; rfl
  rw [eac]
  have ecell : cell2 cl.pa cl.pb a0 a1 beta sig A.rp A.rn = PN.mk
      (A.rp + cRP a1 a0 kk A0 A1 cl.pa cl.pb cl.h beta) (A.rn + cRN sig kk A0 A1 cl.pa cl.pb beta) := by
    unfold cell2 cell2.cell2a cell2.cell2b cRP cRN
    show bsel (Nat.ble A1 beta) _ (bsel (Nat.ble beta A0) _ (cell2.cell2z cl.pa cl.pb a0 a1 beta sig A.rp A.rn kk
      (cl.pa + (beta - A0) / kk))) = _
    rw [bsel_eq, bsel_eq]
    by_cases h1 : A1 ≤ beta
    · rw [ite_eq_left (by rw [Nat.ble_eq]; exact h1), ite_eq_left h1, ite_eq_left h1, add_zero, hh]
      show PN.mk (A.rp + (cl.pb - cl.pa) * (2 * a0 + a1 * (cl.pb + cl.pa))) A.rn = _
      congr 1
      ring_nf
    · rw [ite_eq_right (by rw [Nat.ble_eq]; exact h1), ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : beta ≤ A0
      · rw [ite_eq_left (by rw [Nat.ble_eq]; exact h2), ite_eq_left h2, ite_eq_left h2, hh]
        show PN.mk (A.rp + 2 * beta * (cl.pb - cl.pa)) (A.rn + sig * (cl.pb * cl.pb - cl.pa * cl.pa)) = _
        congr 1
        ring
      · rw [ite_eq_right (by rw [Nat.ble_eq]; exact h2), ite_eq_right h2, ite_eq_right h2]
        unfold cell2.cell2z
        set q := (beta - A0) / kk with hq
        show PN.mk (A.rp + ((cl.pa + q - cl.pa) * (2 * a0 + a1 * (cl.pa + q + cl.pa)) +
            2 * beta * (cl.pb - (cl.pa + q))))
          (A.rn + (sig * (cl.pb * cl.pb - (cl.pa + q) * (cl.pa + q)) + 2 * kk)) = _
        rw [Nat.add_sub_cancel_left, ← Nat.sub_sub, ← hh]
        congr 1
        · ring
        · ring
  rw [ecell]

/-- The exact tail in closed form. -/
theorem tailEnd_closed (r U slcF pj etmj : ℕ) (A : Acc) :
    tailCells.tailEnd r U slcF pj etmj A = if DS ≤ pj then A else
      Acc.mk (A.rp + (2 * DS2 * etmj / (r + 1) + 2 * (DS - pj) * U)) A.rn (A.ac + (DS - pj) * slcF)
        A.lm := by
  unfold tailCells.tailEnd
  rw [bsel_eq]
  simp [Nat.ble_eq]
  split_ifs with h
  · rfl
  · rfl

theorem chord1_hi (pa pb B S kk A0 A1 : ℕ) (h : A1 ≤ B) : chord.chord1 pa pb B S kk A0 A1 = 0 := by
  unfold chord.chord1
  simp [bsel_eq, Nat.ble_eq, h]

theorem chord1_lo (pa pb B S kk A0 A1 : ℕ) (h1 : ¬ A1 ≤ B) (h2 : B + S ≤ A0) :
    chord.chord1 pa pb B S kk A0 A1 = pb - pa := by
  unfold chord.chord1
  have h_ble1_val : Nat.ble A1 B = false := by
    apply Bool.eq_false_of_not_eq_true
    rw [Nat.ble_eq]
    exact h1
  have h_ble2_val : Nat.ble (B + S) A0 = true := by
    rw [Nat.ble_eq]
    exact h2
  simp [bsel_eq, h_ble1_val, h_ble2_val]

theorem cRP_lt (a1 a0 sig kk A0 A1 pa pb h B : ℕ) (ha1 : a1 < 2 ^ 47) (ha0 : a0 < 2 ^ 80)
    (_hsig : sig < 2 ^ 48) (_hkk : kk = a1 + sig) (hA0 : A0 = a0 + kk * pa) (hA1 : A1 = a0 + kk * pb)
    (hpab : pa ≤ pb) (hpb : pb ≤ 2 ^ 36) (hh : h = pb - pa) (hB : B < 2 ^ 86) :
    cRP a1 a0 kk A0 A1 pa pb h B < 2 ^ 124 := by
  unfold cRP
  split_ifs with h1 h2
  · -- h1 : A1 ≤ B
    have hh_bound : h ≤ 2 ^ 36 := by
      rw [hh]
      exact le_trans (Nat.sub_le pb pa) hpb
    have hsum : a0 + a0 + a1 * (pb + pa) < 2 ^ 85 := by
      have ha0sum : a0 + a0 < 2 ^ 81 := by omega
      have hprod : a1 * (pb + pa) < 2 ^ 84 := by
        have hpbpa : pb + pa ≤ 2 ^ 37 := by
          have hpb' : pb ≤ 2 ^ 36 := hpb
          have hpa' : pa ≤ 2 ^ 36 := le_trans hpab hpb
          omega
        have h_mul : a1 * (pb + pa) < 2 ^ 47 * 2 ^ 37 :=
          Nat.mul_lt_mul_of_lt_of_le ha1 hpbpa (by positivity)
        have : 2 ^ 47 * 2 ^ 37 = 2 ^ 84 := by norm_num
        omega
      omega
    have hprod_le : h * (a0 + a0 + a1 * (pb + pa)) ≤ 2 ^ 36 * 2 ^ 85 :=
      Nat.mul_le_mul hh_bound (le_of_lt hsum)
    have h_pow : 2 ^ 36 * 2 ^ 85 = 2 ^ 121 := by norm_num
    have h_lt : 2 ^ 121 < 2 ^ 124 := by norm_num
    omega
  · -- h2 : B ≤ A0
    have hh_bound : h + h ≤ 2 ^ 37 := by
      have : h ≤ 2 ^ 36 := by
        rw [hh]
        exact le_trans (Nat.sub_le pb pa) hpb
      omega
    have hprod_le : (h + h) * B ≤ 2 ^ 37 * 2 ^ 86 :=
      Nat.mul_le_mul hh_bound (le_of_lt hB)
    have h_pow : 2 ^ 37 * 2 ^ 86 = 2 ^ 123 := by norm_num
    have h_lt : 2 ^ 123 < 2 ^ 124 := by norm_num
    omega
  · -- crossing case: ¬ A1 ≤ B and ¬ B ≤ A0, so A0 < B < A1
    have hA0ltB : A0 < B := by omega
    have hBltA1 : B < A1 := by omega
    have hkk_pos : kk > 0 := by
      by_contra! hkk0
      have hA0_eq_A1 : A0 = A1 := by
        rw [hA0, hA1]
        have : kk = 0 := by omega
        rw [this]
        simp
      omega
    have hA1_eq_A0_add_kkh : A1 = A0 + kk * h := by
      rw [hA0, hA1, hh]
      have htemp : kk * pb = kk * pa + kk * (pb - pa) := by
        have h_eq : pb = pa + (pb - pa) := by
          omega
        have h_left : kk * pb = kk * (pa + (pb - pa)) := by
          nth_rw 1 [h_eq]
        calc
          kk * pb = kk * (pa + (pb - pa)) := h_left
          _ = kk * pa + kk * (pb - pa) := by rw [Nat.mul_add]
      rw [htemp]
      simp [add_assoc]
    have hB_sub_A0_lt_kk_h : B - A0 < kk * h := by
      have : B < A0 + kk * h := by
        calc
          B < A1 := hBltA1
          _ = A0 + kk * h := hA1_eq_A0_add_kkh
      omega
    set q := (B - A0) / kk with hq_def
    have hq_lt_h : q < h := by
      rw [hq_def]
      have : B - A0 < h * kk := by
        rw [mul_comm]
        exact hB_sub_A0_lt_kk_h
      exact ((Nat.div_lt_iff_lt_mul hkk_pos).mpr this)
    have h_bound_h : h ≤ 2 ^ 36 := by
      rw [hh]
      exact le_trans (Nat.sub_le pb pa) hpb
    have hq_lt_2pow36 : q < 2 ^ 36 := lt_of_lt_of_le hq_lt_h h_bound_h
    have h_first_sum_lt : a0 + a0 + a1 * (pa + pa + q) < 2 ^ 86 := by
      have ha0sum : a0 + a0 < 2 ^ 81 := by omega
      have hprod : a1 * (pa + pa + q) < 3 * 2 ^ 83 := by
        have hsum : pa + pa + q < 3 * 2 ^ 36 := by
          have hpa : pa ≤ 2 ^ 36 := le_trans hpab hpb
          omega
        have h_mul : a1 * (pa + pa + q) < 2 ^ 47 * (3 * 2 ^ 36) :=
          Nat.mul_lt_mul_of_lt_of_le ha1 (le_of_lt hsum) (by positivity)
        have : 2 ^ 47 * (3 * 2 ^ 36) = 3 * 2 ^ 83 := by norm_num
        omega
      have h_total : a0 + a0 + a1 * (pa + pa + q) < 2 ^ 81 + 3 * 2 ^ 83 := by
        apply Nat.add_lt_add ha0sum hprod
      have : 2 ^ 81 + 3 * 2 ^ 83 = 13 * 2 ^ 81 := by ring
      rw [this] at h_total
      have : 13 * 2 ^ 81 < 32 * 2 ^ 81 := by omega
      have : 32 * 2 ^ 81 = 2 ^ 86 := by ring
      rw [this] at this
      omega
    have h_first_term : (a0 + a0 + a1 * (pa + pa + q)) * q < 2 ^ 122 := by
      have h_mul : (a0 + a0 + a1 * (pa + pa + q)) * q < 2 ^ 86 * 2 ^ 36 :=
        Nat.mul_lt_mul_of_lt_of_le h_first_sum_lt (le_of_lt hq_lt_2pow36) (by positivity)
      have h_pow : 2 ^ 86 * 2 ^ 36 = 2 ^ 122 := by norm_num
      omega
    have h_second_term : 2 * (B * (h - q)) < 2 ^ 123 := by
      have hhq_le : h - q ≤ 2 ^ 36 :=
        calc
          h - q ≤ h := Nat.sub_le _ _
          _ ≤ 2 ^ 36 := h_bound_h
      have h_inner : B * (h - q) < 2 ^ 86 * 2 ^ 36 :=
        Nat.mul_lt_mul_of_lt_of_le hB hhq_le (by positivity)
      have h_mul2 : 2 * (B * (h - q)) < 2 * (2 ^ 86 * 2 ^ 36) :=
        Nat.mul_lt_mul_of_pos_left h_inner (by norm_num)
      have h_pow : 2 ^ 86 * 2 ^ 36 = 2 ^ 122 := by norm_num
      rw [h_pow] at h_mul2
      have : 2 * (2 ^ 122) = 2 ^ 123 := by norm_num
      rw [this] at h_mul2
      exact h_mul2
    have h_total : (a0 + a0 + a1 * (pa + pa + q)) * q + 2 * (B * (h - q)) < 2 ^ 122 + 2 ^ 123 :=
      Nat.add_lt_add h_first_term h_second_term
    have h_sum_lt : 2 ^ 122 + 2 ^ 123 < 2 ^ 124 := by
      have : 2 ^ 122 + 2 ^ 123 = 3 * 2 ^ 122 := by ring
      rw [this]
      have : 3 * 2 ^ 122 < 4 * 2 ^ 122 := by omega
      have : 4 * 2 ^ 122 = 2 ^ 124 := by ring
      omega
    omega

theorem cRN_lt (sig kk A0 A1 pa pb B : ℕ) (hsig : sig < 2 ^ 48) (hkk : kk < 2 ^ 50)
    (hpb : pb ≤ 2 ^ 36) : cRN sig kk A0 A1 pa pb B < 2 ^ 121 := by
  unfold cRN
  split_ifs with h1 h2
  · -- A1 ≤ B → cRN = 0
    norm_num
  · -- B ≤ A0 → cRN = sig * (pb * pb - pa * pa)
    have hpb_sq : pb * pb ≤ 2 ^ 72 := by
      calc
        pb * pb ≤ (2 ^ 36) * (2 ^ 36) := Nat.mul_le_mul hpb hpb
        _ = 2 ^ 72 := by norm_num
    have hsub : pb * pb - pa * pa ≤ pb * pb := Nat.sub_le _ _
    have hsub' : pb * pb - pa * pa ≤ 2 ^ 72 := Nat.le_trans hsub hpb_sq
    have hprod : sig * (pb * pb - pa * pa) < 2 ^ 48 * 2 ^ 72 :=
      Nat.mul_lt_mul_of_lt_of_le hsig hsub' (by norm_num : 0 < 2 ^ 72)
    have hpow : 2 ^ 48 * 2 ^ 72 = 2 ^ 120 := by norm_num
    have hlt : sig * (pb * pb - pa * pa) < 2 ^ 120 := by
      simpa [hpow] using hprod
    have hfinal : 2 ^ 120 < 2 ^ 121 :=
      Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)
    exact lt_trans hlt hfinal
  · -- else → cRN = sig * (...) + (kk + kk)
    have hpb_sq : pb * pb ≤ 2 ^ 72 := by
      calc
        pb * pb ≤ (2 ^ 36) * (2 ^ 36) := Nat.mul_le_mul hpb hpb
        _ = 2 ^ 72 := by norm_num
    have hsub : pb * pb - (pa + (B - A0) / kk) * (pa + (B - A0) / kk) ≤ pb * pb := Nat.sub_le _ _
    have hsub' : pb * pb - (pa + (B - A0) / kk) * (pa + (B - A0) / kk) ≤ 2 ^ 72 :=
      Nat.le_trans hsub hpb_sq
    have hprod : sig * (pb * pb - (pa + (B - A0) / kk) * (pa + (B - A0) / kk)) < 2 ^ 48 * 2 ^ 72 :=
      Nat.mul_lt_mul_of_lt_of_le hsig hsub' (by norm_num : 0 < 2 ^ 72)
    have hpow : 2 ^ 48 * 2 ^ 72 = 2 ^ 120 := by norm_num
    have hlt1 : sig * (pb * pb - (pa + (B - A0) / kk) * (pa + (B - A0) / kk)) < 2 ^ 120 := by
      simpa [hpow] using hprod
    have hkk2 : kk + kk < 2 ^ 51 := by
      calc
        kk + kk < 2 ^ 50 + 2 ^ 50 := Nat.add_lt_add hkk hkk
        _ = 2 ^ 51 := by norm_num
    have hsum : sig * (pb * pb - (pa + (B - A0) / kk) * (pa + (B - A0) / kk)) + (kk + kk) <
        2 ^ 120 + 2 ^ 51 :=
      Nat.add_lt_add hlt1 hkk2
    have hfinal : 2 ^ 120 + 2 ^ 51 < 2 ^ 121 := by
      have hsum' : 2 ^ 120 + 2 ^ 120 = 2 ^ 121 := by norm_num
      have hlt_pow : 2 ^ 51 < 2 ^ 120 :=
        Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)
      omega
    exact lt_trans hsum hfinal

theorem tailEndInc_lt (r pj etmj U : ℕ) (hetm : etmj ≤ DS) (hU : U < 2 ^ 85) :
    2 * DS2 * etmj / (r + 1) + 2 * (DS - pj) * U < 2 ^ 123 := by
  have hDS : DS = 2 ^ 36 := rfl
  have hDS2 : DS2 = 2 ^ 72 := rfl
  have h1 : 2 * DS2 * etmj / (r + 1) ≤ 2 * DS2 * etmj := Nat.div_le_self _ _
  have h_pow73 : (2 : ℕ) * 2 ^ 72 = 2 ^ 73 := by norm_num
  have h_pow37 : (2 : ℕ) * 2 ^ 36 = 2 ^ 37 := by norm_num
  have h2 : 2 * DS2 * etmj ≤ 2 ^ 109 := by
    rw [hDS2]
    calc
      2 * (2 ^ 72) * etmj = (2 ^ 73) * etmj := by rw [h_pow73]
      _ ≤ 2 ^ 73 * 2 ^ 36 := Nat.mul_le_mul_left _ hetm
      _ = 2 ^ 109 := by norm_num
  have h3 : 2 * (DS - pj) * U ≤ 2 * DS * U := by
    have hsub : DS - pj ≤ DS := Nat.sub_le _ _
    nlinarith
  have h4 : 2 * DS * U < 2 ^ 122 := by
    rw [hDS]
    calc
      2 * (2 ^ 36) * U = (2 ^ 37) * U := by rw [h_pow37]
      _ < 2 ^ 37 * 2 ^ 85 := Nat.mul_lt_mul_of_pos_left hU (by norm_num : 0 < 2 ^ 37)
      _ = 2 ^ 122 := by norm_num
  have hsum : 2 * DS2 * etmj / (r + 1) + 2 * (DS - pj) * U < 2 * DS2 * etmj + 2 ^ 122 := by
    apply Nat.add_lt_add_of_le_of_lt h1
    exact Nat.lt_of_le_of_lt h3 h4
  have htotal : 2 * DS2 * etmj + 2 ^ 122 < 2 ^ 123 := by
    have hlt : 2 * DS2 * etmj < 2 ^ 122 := by
      apply Nat.lt_of_le_of_lt h2
      exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)
    have hsum' : 2 * DS2 * etmj + 2 ^ 122 < 2 ^ 122 + 2 ^ 122 :=
      Nat.add_lt_add_right hlt (2 ^ 122)
    have h_eq : 2 ^ 122 + 2 ^ 122 = 2 ^ 123 := by norm_num
    rw [h_eq] at hsum'
    exact hsum'
  exact Nat.lt_trans hsum htotal

/-- The lanes that go on: those of `a` that do not stop. -/
theorem mask_sub (n : ℕ) (a b : ℕ → Prop) [DecidablePred a] [DecidablePred b] :
    Nat.sub (pack LW n fun l => if a l then 2 ^ 143 else 0)
        (pack LW n fun l => if a l ∧ b l then 2 ^ 143 else 0) =
      pack LW n fun l => if a l ∧ ¬ b l then 2 ^ 143 else 0 := by
  have hle : ∀ l < n, (if a l ∧ b l then 2 ^ 143 else 0) ≤ (if a l then 2 ^ 143 else 0) := by
    intro l hl
    split_ifs with ha hb
    · rfl
    · exfalso; exact hb ha.1
    · exact Nat.zero_le _
    · rfl
  have hsub := pack_sub LW n (fun l => if a l ∧ b l then 2 ^ 143 else 0) (fun l => if a l then 2 ^ 143 else 0) hle
  have h_eq : (fun l => (if a l then 2 ^ 143 else 0) - (if a l ∧ b l then 2 ^ 143 else 0)) = (fun l => if a l ∧ ¬ b l then 2 ^ 143 else 0) := by
    ext l
    by_cases ha : a l
    · by_cases hb : b l
      · simp [ha, hb]
      · simp [ha, hb]
    · simp [ha]
  rw [h_eq] at hsub
  simpa using hsub

/-- The mask of the lanes that stop at a boundary. -/
theorem endMask_eq (n X Y : ℕ) (act : ℕ → Prop) [DecidablePred act] (Uf Sf : ℕ → ℕ)
    (hX : X < 2 ^ 143) (hb : ∀ l < n, Uf l + Sf l + Y < 2 ^ 143) :
    Nat.land (pack LW n fun l => if act l then 2 ^ 143 else 0)
        (ge (mkVC n) (bc (mkVC n) X) (Nat.add (Nat.add (pack LW n Uf) (pack LW n Sf)) (bc (mkVC n) Y))) =
      pack LW n fun l => if act l ∧ Uf l + Sf l + Y ≤ X then 2 ^ 143 else 0 := by
  rw [bc_eq, bc_eq, Nat.add_eq, Nat.add_eq, pack_add, pack_add, ge_eq n (fun _ => X) (fun l => Uf l + Sf l + Y) (fun _ _ => hX) hb, land_gm]

/-- The exact tail on the lanes of `en`. -/
theorem tailEndV_eq (n m r pj etmj : ℕ) (Uf : ℕ → ℕ) (gf : ℕ → ℕ → ℕ) (en : ℕ → Prop)
    [DecidablePred en] (A : LA) (rpf : ℕ → ℕ) (af : ℕ → ℕ → ℕ) (hetm : etmj ≤ DS)
    (hU : ∀ l < n, Uf l < 2 ^ 85) (hg : ∀ f l, l < n → gf f l < 2 ^ 48)
    (hrp : A.rp = pack LW n rpf) (hac : A.ac = (List.range m).map fun q => pack LW n (af q)) :
    bsel (Nat.ble DS pj) A
        (LA.mk (Nat.add A.rp (msk (pack LW n fun l => if en l then 2 ^ 143 else 0)
            (Nat.add (bc (mkVC n) (Nat.div (Nat.mul (Nat.mul 2 DS2) etmj) (Nat.succ r)))
              (Nat.mul (Nat.mul 2 (Nat.sub DS pj)) (pack LW n Uf))))) A.rn
          (addL A.ac (lmap (fun g => msk (pack LW n fun l => if en l then 2 ^ 143 else 0)
            (Nat.mul (Nat.sub DS pj) g)) ((List.range m).map fun f => pack LW n (gf f)))) A.lm A.ok) =
      LA.mk (pack LW n fun l => rpf l +
          if en l ∧ pj < DS then 2 * DS2 * etmj / (r + 1) + 2 * (DS - pj) * Uf l else 0)
        A.rn ((List.range m).map fun q => pack LW n fun l => af q l +
          if en l ∧ pj < DS then (DS - pj) * gf q l else 0) A.lm A.ok := by
  rw [bsel_eq]
  by_cases hpj : DS ≤ pj
  · rw [ite_eq_left (by rw [Nat.ble_eq]; exact hpj)]
    have h0 : ∀ l, ¬ (en l ∧ pj < DS) := fun l h => absurd h.2 (not_lt.2 hpj)
    cases A with
    | mk rp rn ac lm ok =>
      simp only at hrp hac
      rw [LA.mk.injEq]
      refine ⟨?_, rfl, ?_, rfl, rfl⟩
      · rw [hrp]
        exact pack_congr _ _ _ _ fun l _ => by rw [ite_eq_right (h0 l), add_zero]
      · rw [hac]
        exact List.map_congr_left fun q _ => pack_congr _ _ _ _ fun l _ => by
          rw [ite_eq_right (h0 l), add_zero]
  · have hlt : pj < DS := not_le.1 hpj
    have hDS : DS = 2 ^ 36 := rfl
    rw [ite_eq_right (by rw [Nat.ble_eq]; exact hpj), LA.mk.injEq]
    refine ⟨?_, rfl, ?_, rfl, rfl⟩
    · rw [show Nat.div (Nat.mul (Nat.mul 2 DS2) etmj) (Nat.succ r) = 2 * DS2 * etmj / (r + 1) from rfl,
        bc_eq, show Nat.mul (Nat.mul 2 (Nat.sub DS pj)) (pack LW n Uf) =
          pack LW n fun l => 2 * (DS - pj) * Uf l from pack_const_mul _ _ _ _, Nat.add_eq, Nat.add_eq,
        pack_add,
        msk_eq n en _ (fun l hl => lt_trans (tailEndInc_lt r pj etmj (Uf l) hetm (hU l hl))
          (by norm_num)), hrp, pack_add]
      exact pack_congr _ _ _ _ fun l _ => by
        by_cases he : en l
        · rw [ite_eq_left he, ite_eq_left ⟨he, hlt⟩]
        · rw [ite_eq_right he, ite_eq_right (fun h => he h.1)]
    · have hadd : ∀ F G : ℕ → ℕ, addL ((List.range m).map F) ((List.range m).map G) =
          (List.range m).map fun q => F q + G q := by
        intro F G
        unfold addL
        rw [lzipWith_eq]
        apply List.ext_getElem
        · simp
        · intro i h1 h2
          simp
      have eM : ∀ f, msk (pack LW n fun l => if en l then 2 ^ 143 else 0)
          (Nat.mul (Nat.sub DS pj) (pack LW n (gf f))) =
          pack LW n fun l => if en l then (DS - pj) * gf f l else 0 := fun f => by
        rw [show Nat.mul (Nat.sub DS pj) (pack LW n (gf f)) = pack LW n fun l => (DS - pj) * gf f l from
          pack_const_mul _ _ _ _]
        exact msk_eq n en _ (fun l hl => lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (show DS - pj < 2 ^ 37 by omega) (hg f l hl).le (by positivity)) (by norm_num))
      rw [lmap_eq, List.map_map, hac]
      simp only [Function.comp_def, eM]
      rw [hadd]
      refine List.map_congr_left fun q _ => ?_
      rw [pack_add]
      exact pack_congr _ _ _ _ fun l _ => by
        by_cases he : en l
        · rw [ite_eq_left he, ite_eq_left ⟨he, hlt⟩]
        · rw [ite_eq_right he, ite_eq_right (fun h => he h.1)]

/-- A tail cell keeps a failed check failed. -/
theorem tailCellV_ok (v : VC) (r a1 a0 U S : ℕ) (gs : List ℕ) (cl : SC) (CONT : ℕ) (A : LA)
    (h : (tailCellV v r a1 a0 U S gs cl CONT A).ok = true) : A.ok = true := by
  unfold tailCellV tailCellV.tailCellV1 tailCellV.tailCellV2 tailCellV.tailCellV3 tailCellV.tailCellV4
    tailCellV.tailCellV5 tailCellV.tailCellV6 tailCellV.tailCellV7 at h
  have key : ∀ b : Bool, bsel b A.ok false = true → A.ok = true := fun b hb => by
    cases b
    · exact absurd (show false = true from hb) Bool.false_ne_true
    · exact hb
  exact key _ h

/-- The tail keeps a failed check failed. -/
theorem tailV_ok (v : VC) (r a1 a0 U S : ℕ) (gs : List ℕ) (cs : List SC) (pj etj etmj ACT : ℕ)
    (A : LA) (h : (tailV v r a1 a0 U S gs cs pj etj etmj ACT A).ok = true) : A.ok = true := by
  induction cs generalizing pj etj etmj ACT A with
  | nil => exact h
  | cons cl cs ih =>
    have hA' : ∀ X : LA, X.ok = A.ok → X.ok = true → A.ok = true := fun X e hX => e ▸ hX
    change (tailV.tailV1 v r U gs cl (tailV v r a1 a0 U S gs cs) pj etmj ACT A _ a1 a0 S).ok = true at h
    unfold tailV.tailV1 tailV.tailV2 at h
    generalize hX : bsel (Nat.ble DS pj) A _ = X at h
    have hXok : X.ok = A.ok := by
      rw [← hX]
      cases Nat.ble DS pj <;> rfl
    refine hA' X hXok ?_
    generalize Nat.beq _ 0 = b at h
    cases b
    · exact tailCellV_ok v r a1 a0 U S gs cl _ X (ih _ _ _ _ _ h)
    · exact h

/-- A tail cell with `sigma = r e1`, `beta = U + D et + sigma pb` on lanes. -/
theorem tailCellV_top (n r a1 a0 : ℕ) (Uf Sf : ℕ → ℕ) (gs : List ℕ) (cl : SC) (CONT : ℕ) (A : LA) :
    tailCellV (mkVC n) r a1 a0 (pack LW n Uf) (pack LW n Sf) gs cl CONT A =
      tailCellV.tailCellV2 (mkVC n) a1 a0 (pack LW n Sf) gs cl CONT A (r * cl.e1)
        (pack LW n fun l => Uf l + (DS * cl.et + r * cl.e1 * cl.pb)) (a1 + r * cl.e1)
        (a0 + (a1 + r * cl.e1) * cl.pa) (a0 + (a1 + r * cl.e1) * cl.pb) := by
  simp [tailCellV, tailCellV.tailCellV1, bc_eq, pack_add]

end Robbins.Cert.SO.L
