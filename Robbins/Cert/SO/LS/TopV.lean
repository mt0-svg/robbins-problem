import Robbins.Cert.SO.LS.TopS
import Robbins.Cert.SO.LS.Cell
import Robbins.Cert.SO.LS.Sel

/-!
# The lanes step: a cell of the top record on lanes, in closed form

`topCellV` on `n` lanes in closed form, lane by lane (`topCellV_core`), when its saturation check
passes: the terms that `topCell` adds (`LS/TopS.lean`), on abstract lane data.
-/

namespace Robbins.Cert.SO.L

open Robbins.Cert Robbins.Cert.K Robbins.Cert.SO.K Robbins.Lanes

theorem pack_zeros (n : ℕ) : pack LW n (fun _ => 0) = 0 := by
  simp [pack]

/-- A mask that packs to `0` holds on no lane. -/
theorem mask_zero (n : ℕ) (c : ℕ → Prop) [DecidablePred c]
    (h : pack LW n (fun l => if c l then 2 ^ 143 else 0) = 0) : ∀ l < n, ¬ c l := by
  intro l hl hc
  have e := (pack_inj LW n (fun l => if c l then 2 ^ 143 else 0) (fun _ => 0)
    (fun l _ => by show (if c l then (2 : ℕ) ^ 143 else 0) < 2 ^ 144; split_ifs <;> norm_num)
    (fun _ _ => by show (0 : ℕ) < 2 ^ 144; norm_num)).1 (by rw [h, pack_zeros]) l hl
  simp [hc] at e

theorem beq_pack_mask (n : ℕ) (c : ℕ → Prop) [DecidablePred c]
    (h : ¬ Nat.beq (pack LW n (fun l => if c l then 2 ^ 143 else 0)) 0 = true) :
    pack LW n (fun l => if c l then 2 ^ 143 else 0) ≠ 0 := fun e => h (by rw [e]; rfl)

theorem map_range_snoc {α : Type} (d : ℕ) (F : ℕ → α) (x : α) :
    (List.range d).map F ++ [x] = (List.range (d + 1)).map fun q => if q < d then F q else x := by
  rw [List.range_succ, List.map_append, List.map_singleton]
  congr 1
  · exact List.map_congr_left fun q hq => by rw [ite_eq_left (List.mem_range.1 hq)]
  · simp

theorem addL_map (k : ℕ) (F G : ℕ → ℕ) :
    addL ((List.range k).map F) ((List.range k).map G) = (List.range k).map fun q => F q + G q := by
  unfold addL
  rw [lzipWith_eq]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem sl_zero_eq (n : ℕ) (c : ℕ → Prop) [DecidablePred c] (b : ℕ → ℕ) (hb : ∀ l < n, b l < 2 ^ 144) :
    sl (pack LW n (fun l => if c l then 2 ^ 143 else 0)) 0 (pack LW n b) =
      pack LW n (fun l => if c l then 0 else b l) := by
  have h := sl_eq n c (fun _ => 0) b (fun _ _ => by norm_num) hb
  rw [pack_zeros] at h
  exact h

/-- A mask test as a proposition on the lanes. -/
theorem bsel_mask_eq {α : Type} (n : ℕ) (c : ℕ → Prop) [DecidablePred c] (x y : α) :
    bsel (Nat.beq (pack LW n fun l => if c l then 2 ^ 143 else 0) 0) x y =
      if ∃ l < n, c l then y else x := by
  rw [bsel_ite]
  by_cases hE : ∃ l < n, c l
  · have hne : pack LW n (fun l => if c l then 2 ^ 143 else 0) ≠ 0 := fun h0 => by
      obtain ⟨l, hl, hcl⟩ := hE
      exact mask_zero n c h0 l hl hcl
    have hb : Nat.beq (pack LW n fun l => if c l then 2 ^ 143 else 0) 0 = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hne (Nat.eq_of_beq_eq_true h)
    rw [hb, ite_eq_right Bool.false_ne_true, ite_eq_left hE]
  · have h0 : pack LW n (fun l => if c l then 2 ^ 143 else 0) = 0 := by
      refine (pack_congr _ _ _ _ fun l hl => ?_).trans (pack_zeros n)
      exact ite_eq_right (fun h => hE ⟨l, hl, h⟩)
    rw [h0, ite_eq_left (show Nat.beq 0 0 = true from rfl), ite_eq_right hE]

/-- A pair of packs or zeros, as packs. -/
theorem ite_pack2 (n : ℕ) (E : Prop) [Decidable E] (f g : ℕ → ℕ) :
    (if E then (pack LW n f, pack LW n g) else (0, 0)) =
      (pack LW n fun l => if E then f l else 0, pack LW n fun l => if E then g l else 0) := by
  by_cases hE : E
  · rw [ite_eq_left hE]
    exact Prod.ext (pack_congr _ _ _ _ fun l _ => (ite_eq_left hE).symm)
      (pack_congr _ _ _ _ fun l _ => (ite_eq_left hE).symm)
  · rw [ite_eq_right hE]
    refine Prod.ext ?_ ?_
    · exact ((pack_congr _ _ _ _ fun l _ => ite_eq_right hE).trans (pack_zeros n)).symm
    · exact ((pack_congr _ _ _ _ fun l _ => ite_eq_right hE).trans (pack_zeros n)).symm

theorem dqL_le (q M : ℕ) : dq q M ≤ DS := by
  have e : ∀ a b, nmin2 a b = min a b := fun a b => by
    unfold nmin2
    rw [bsel_ite]
    by_cases h : a ≤ b
    · rw [ite_eq_left (by rw [Nat.ble_eq]; exact h), min_eq_left h]
    · rw [ite_eq_right (by rw [Nat.ble_eq]; exact h), min_eq_right (by omega)]
  unfold dq
  rw [e, e]
  show min ((q + 1) * DS) M - min (q * DS) M ≤ DS
  rw [show (q + 1) * DS = q * DS + DS by ring]
  omega

theorem mul_lt_pow {x y a b k : ℕ} (hx : x < 2 ^ a) (hy : y < 2 ^ b) (hk : a + b ≤ k) :
    x * y < 2 ^ k :=
  calc x * y < 2 ^ a * 2 ^ b := Nat.mul_lt_mul_of_lt_of_le hx hy.le (by positivity)
    _ = 2 ^ (a + b) := (pow_add 2 a b).symm
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

theorem ite_pack1 (n : ℕ) (E : Prop) [Decidable E] (f : ℕ → ℕ) :
    (if E then pack LW n f else 0) = pack LW n fun l => if E then f l else 0 := by
  by_cases hE : E
  · rw [ite_eq_left hE]
    exact pack_congr _ _ _ _ fun l _ => (ite_eq_left hE).symm
  · rw [ite_eq_right hE]
    exact ((pack_congr _ _ _ _ fun l _ => ite_eq_right hE).trans (pack_zeros n)).symm

theorem ite_fst (n : ℕ) (E : Prop) [Decidable E] (f g : ℕ → ℕ) :
    (if E then (pack LW n f, pack LW n g) else ((0 : ℕ), (0 : ℕ))).1 =
      pack LW n fun l => if E then f l else 0 := by
  rw [ite_pack2]

theorem ite_snd (n : ℕ) (E : Prop) [Decidable E] (f g : ℕ → ℕ) :
    (if E then (pack LW n f, pack LW n g) else ((0 : ℕ), (0 : ℕ))).2 =
      pack LW n fun l => if E then g l else 0 := by
  rw [ite_pack2]

theorem chordV_ok (v : VC) (h beta S kk A0 A1 q1 r1 use : ℕ) :
    (chordV v h beta S kk A0 A1 q1 r1 use).2 =
      allGe v.G (bc v QMX) (chordV v h beta S kk A0 A1 q1 r1 use).1 := rfl

/-- The last step of a cell of the top record: the coefficient and credit lists. -/
theorem topCellV6_eq (n d : ℕ) (tv : TV) (cv : CV) (isTop : Bool) (A : LA)
    (STc USc : ℕ → Prop) [DecidablePred STc] [DecidablePred USc] (Qf : ℕ → ℕ) (qok : Bool)
    (rp rn : ℕ) (co : ℕ → ℕ → ℕ) (o : ℕ → ℕ → Prop) [∀ q l, Decidable (o q l)] (M : ℕ → ℕ)
    (topOn : Bool) (af lf : ℕ → ℕ → ℕ)
    (hco : cv.co = (List.range d).map fun q => pack LW n (co q))
    (hAac : A.ac = (List.range (d + 1)).map fun q => pack LW n (af q))
    (hAlm : A.lm = (List.range (d + 1)).map fun q => pack LW n (lf q))
    (hcob : ∀ q l, l < n → co q l < 2 ^ 48) (hPm : tv.Pm < 2 ^ 47) (hQb : ∀ l < n, Qf l < 2 ^ 96) :
    topCellV.topCellV6 (mkVC n) tv cv isTop A (pack LW n fun l => if STc l then 2 ^ 143 else 0)
      (pack LW n fun l => if USc l then 2 ^ 143 else 0) (pack LW n Qf) qok rp rn
      ((List.range d).map (fun q => pack LW n fun l => if o q l then dq (ownBefore o q l) (M l) else 0),
        if topOn then pack LW n (fun l => dq (ownBefore o d l) (M l)) else 0) =
    LA.mk rp rn
      ((List.range (d + 1)).map fun q => pack LW n fun l => af q l +
        (if USc l then (if q < d then co q l * (Qf l % 2 ^ 37) else bsel isTop 0 tv.Pm * Qf l)
          else 0))
      ((List.range (d + 1)).map fun q => pack LW n fun l => lf q l +
        (if STc l then (if q < d then (if o q l then dq (ownBefore o q l) (M l) else 0)
          else if topOn then dq (ownBefore o d l) (M l) else 0) else 0))
      (bsel qok A.ok false) := by
  have hdq : ∀ q M, dq q M < 2 ^ 144 := fun q M =>
    lt_of_le_of_lt (dqL_le q M) (by rw [show DS = 2 ^ 36 from rfl]; norm_num)
  have hPm' : bsel isTop 0 tv.Pm < 2 ^ 47 := by
    rw [bsel_ite]; split_ifs
    · positivity
    · exact hPm
  unfold topCellV.topCellV6
  congr 1
  · rw [hco, lmap_eq, List.map_map, lapp_eq]
    have e1 : List.map ((fun co => msk (pack LW n fun l => if USc l then 2 ^ 143 else 0)
        (mulv (mkVC n) 37 co (pack LW n Qf))) ∘ fun q => pack LW n (co q)) (List.range d) =
        (List.range d).map fun q => pack LW n fun l => if USc l then co q l * (Qf l % 2 ^ 37) else 0 :=
      List.map_congr_left fun q _ => by
        show msk _ (mulv (mkVC n) 37 (pack LW n (co q)) (pack LW n Qf)) = _
        rw [mulv_eq n 37 (co q) Qf (by norm_num)
          (fun l hl j hj => mul_lt_pow (hcob q l hl) (Nat.pow_lt_pow_right (by norm_num) hj) (by omega))
          (fun l hl => lt_trans (hQb l hl) (by norm_num))]
        exact msk_eq n USc _ fun l hl =>
          mul_lt_pow (hcob q l hl) (Nat.mod_lt _ (by positivity)) (by norm_num : 48 + 37 ≤ 144)
    have e2 : msk (pack LW n fun l => if USc l then 2 ^ 143 else 0) (Nat.mul (bsel isTop 0 tv.Pm)
        (pack LW n Qf)) = pack LW n fun l => if USc l then bsel isTop 0 tv.Pm * Qf l else 0 := by
      rw [Nat.mul_eq, pack_const_mul]
      exact msk_eq n USc _ fun l hl => mul_lt_pow hPm' (hQb l hl) (by norm_num)
    rw [e1, e2, map_range_snoc, hAac, addL_map]
    refine List.map_congr_left fun q _ => ?_
    by_cases hq : q < d
    · rw [ite_eq_left hq, pack_add]
      exact pack_congr _ _ _ _ fun l _ => by rw [ite_eq_left hq]
    · rw [ite_eq_right hq, pack_add]
      exact pack_congr _ _ _ _ fun l _ => by rw [ite_eq_right hq]
  · rw [lmap_eq, List.map_map, lapp_eq]
    have e1 : List.map ((msk (pack LW n fun l => if STc l then 2 ^ 143 else 0)) ∘
        fun q => pack LW n fun l => if o q l then dq (ownBefore o q l) (M l) else 0) (List.range d) =
        (List.range d).map fun q => pack LW n fun l =>
          if STc l then (if o q l then dq (ownBefore o q l) (M l) else 0) else 0 :=
      List.map_congr_left fun q _ => msk_eq n STc _ fun l _ => by
        split_ifs
        · exact hdq _ _
        · positivity
    have e2 : msk (pack LW n fun l => if STc l then 2 ^ 143 else 0)
        (if topOn then pack LW n (fun l => dq (ownBefore o d l) (M l)) else 0) =
        pack LW n fun l => if STc l then (if topOn then dq (ownBefore o d l) (M l) else 0) else 0 := by
      rw [ite_pack1]
      exact msk_eq n STc _ fun l _ => by
        split_ifs
        · exact hdq _ _
        · positivity
    rw [e1, e2, map_range_snoc, hAlm, addL_map]
    refine List.map_congr_left fun q _ => ?_
    by_cases hq : q < d
    · rw [ite_eq_left hq, pack_add]
      exact pack_congr _ _ _ _ fun l _ => by rw [ite_eq_left hq]
    · rw [ite_eq_right hq, pack_add]
      exact pack_congr _ _ _ _ fun l _ => by rw [ite_eq_right hq]

theorem bsel_and (b x : Bool) (h : bsel b x false = true) : b = true ∧ x = true := by
  cases b <;> cases x
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact ⟨rfl, rfl⟩

/-- The chord of a cell `i ≤ im` on its lanes, from the check of `topCellV`. -/
theorem ch_facts (n h pa a1 : ℕ) (B S sigf A0f A1f q1 r1 : ℕ → ℕ) (Aok : Bool) (ch : ℕ × Bool)
    (hch : ch = if ∃ l < n, ¬A1f l ≤ B l ∧ S l ≠ 0 ∧ ¬B l + S l ≤ A0f l then
        chordV (mkVC n) h (pack LW n B) (pack LW n S) (pack LW n fun l => a1 + sigf l) (pack LW n A0f)
          (pack LW n A1f) (pack LW n q1) (pack LW n r1)
          (pack LW n fun l => if ¬A1f l ≤ B l ∧ S l ≠ 0 ∧ ¬B l + S l ≤ A0f l then 2 ^ 143 else 0)
      else (0, true))
    (hhD : h ≤ DS) (hBb : ∀ l < n, B l < 2 ^ 92) (hSb : ∀ l < n, S l < 2 ^ 92)
    (hKb : ∀ l < n, a1 + sigf l < 2 ^ 50) (hA0b : ∀ l < n, A0f l < 2 ^ 92)
    (hA1b : ∀ l < n, A1f l < 2 ^ 92) (hq1b : ∀ l < n, q1 l < 2 ^ 37) (hr1b : ∀ l < n, r1 l < 2 ^ 92)
    (hA : ∀ l < n, A1f l = A0f l + (a1 + sigf l) * h)
    (hq : ∀ l < n, ¬ A1f l ≤ B l → A0f l < B l →
      q1 l = (B l - A0f l) / (a1 + sigf l) ∧ r1 l = (B l - A0f l) % (a1 + sigf l))
    (hok : bsel ch.2 Aok false = true) :
    ch.1 = (pack LW n fun l => if ¬A1f l ≤ B l ∧ S l ≠ 0 ∧ ¬B l + S l ≤ A0f l then
        chord.chord1 pa (pa + h) (B l) (S l) (a1 + sigf l) (A0f l) (A1f l) else 0) ∧
      ch.2 = true ∧ Aok = true ∧
      ∀ l < n, ¬A1f l ≤ B l ∧ S l ≠ 0 ∧ ¬B l + S l ≤ A0f l →
        chord.chord1 pa (pa + h) (B l) (S l) (a1 + sigf l) (A0f l) (A1f l) ≤ QMX := by
  subst hch
  obtain ⟨h2, hAok⟩ := bsel_and _ _ hok
  by_cases hE : ∃ l < n, ¬A1f l ≤ B l ∧ S l ≠ 0 ∧ ¬B l + S l ≤ A0f l
  · rw [ite_eq_left hE] at h2 ⊢
    obtain ⟨e1, e2⟩ := chordV_spec n h pa B S (fun l => a1 + sigf l) A0f A1f q1 r1
      (fun l => ¬A1f l ≤ B l ∧ S l ≠ 0 ∧ ¬B l + S l ≤ A0f l) hhD hBb hSb hKb hA0b hA1b hq1b hr1b
      (fun l hl _ => hA l hl)
      (fun l _ hu => ⟨not_le.1 hu.1, not_le.1 hu.2.2, Nat.pos_of_ne_zero hu.2.1⟩)
      (fun l hl hu hlt => hq l hl hu.1 hlt) h2
    exact ⟨e1, h2, hAok, e2⟩
  · rw [ite_eq_right hE]
    refine ⟨?_, rfl, hAok, fun l hl hc => absurd ⟨l, hl, hc⟩ hE⟩
    exact ((pack_congr _ _ _ _ fun l hl => ite_eq_right fun hc => hE ⟨l, hl, hc⟩).trans
      (pack_zeros n)).symm

theorem crossP_lt (a0 a1 pa q1 B h : ℕ) (ha0 : a0 < 2 ^ 80) (ha1 : a1 < 2 ^ 47) (hpa : pa ≤ 2 ^ 36)
    (hq1 : q1 < 2 ^ 37) (hB : B < 2 ^ 92) (hh : h ≤ 2 ^ 36) :
    (a0 + a0 + a1 * (pa + pa + q1)) * q1 + 2 * (B * (h - q1)) < 2 ^ 131 := by
  have e1 : a1 * (pa + pa + q1) < 2 ^ 86 := mul_lt_pow ha1 (show pa + pa + q1 < 2 ^ 39 by omega) (by norm_num)
  have e2 : a0 + a0 + a1 * (pa + pa + q1) < 2 ^ 87 := by
    have : (2 : ℕ) ^ 80 + 2 ^ 80 + 2 ^ 86 ≤ 2 ^ 87 := by norm_num
    omega
  have e3 := mul_lt_pow e2 hq1 (le_refl (87 + 37))
  have e4 := mul_lt_pow hB (show h - q1 < 2 ^ 37 by omega) (le_refl (92 + 37))
  have : (2 : ℕ) ^ (87 + 37) + 2 * 2 ^ (92 + 37) ≤ 2 ^ 131 := by norm_num
  omega

theorem crossN_lt (pb pa q1 sig K : ℕ) (hpb : pb ≤ 2 ^ 36) (hsig : sig < 2 ^ 48) (hK : K < 2 ^ 50) :
    (pb * pb - (pa + q1) * ((pa + q1) % 2 ^ 37)) * sig + (K + K) < 2 ^ 131 := by
  have e1 : pb * pb ≤ 2 ^ 72 := (Nat.mul_le_mul hpb hpb).trans (by norm_num)
  have e2 := mul_lt_pow (show pb * pb - (pa + q1) * ((pa + q1) % 2 ^ 37) < 2 ^ 73 by omega) hsig
    (le_refl (73 + 48))
  have : (2 : ℕ) ^ (73 + 48) + 2 ^ 50 + 2 ^ 50 ≤ 2 ^ 131 := by norm_num
  omega

theorem bsel_and_false (a b : Bool) : bsel a b false = (a && b) := by
  cases a <;> rfl

/-- A cell `i ≤ im` of the top record from its masks and `(q1, r1)`, on abstract lane data. -/
theorem topCellV4_core (n a1 d pa pb h h2 PmL : ℕ) (tv : TV) (cv : CV) (isTop : Bool) (A : LA)
    (B S a0f sigf A0f A1f IAf ssqf q1 r1 : ℕ → ℕ) (co : ℕ → ℕ → ℕ) (o : ℕ → ℕ → Prop)
    [∀ q l, Decidable (o q l)] (rpf rnf : ℕ → ℕ) (af lf : ℕ → ℕ → ℕ)
    (hpa : cv.pa = pa) (hh : cv.h = h) (hh2 : cv.h2 = h2) (hpb2 : cv.pb2 = pb * pb)
    (hhd : h = pb - pa) (hpab : pa ≤ pb) (hpbD : pb ≤ DS) (hh2D : h2 ≤ DS + DS) (ha1 : a1 < 2 ^ 47)
    (hPm : tv.Pm = PmL) (hPmL : PmL < 2 ^ 47)
    (hsig : cv.sig = pack LW n sigf) (ha0 : cv.a0 = pack LW n a0f)
    (hkk : cv.kk = pack LW n fun l => a1 + sigf l)
    (hA0 : cv.A0 = pack LW n A0f) (hA1 : cv.A1 = pack LW n A1f)
    (hIA : cv.IA = pack LW n IAf) (hssq : cv.ssq = pack LW n ssqf)
    (hco : cv.co = (List.range d).map fun q => pack LW n (co q))
    (hown : cv.own = (List.range d).map fun q => pack LW n fun l => if o q l then 2 ^ 143 else 0)
    (hA0e : ∀ l < n, A0f l = a0f l + (a1 + sigf l) * pa)
    (hA1e : ∀ l < n, A1f l = a0f l + (a1 + sigf l) * pb)
    (hBb : ∀ l < n, B l < 2 ^ 90) (hSb : ∀ l < n, S l < 2 ^ 91)
    (hsigb : ∀ l < n, sigf l < 2 ^ 48) (ha0b : ∀ l < n, a0f l < 2 ^ 80)
    (hA0b : ∀ l < n, A0f l < 2 ^ 90) (hA1b : ∀ l < n, A1f l < 2 ^ 90)
    (hIAb : ∀ l < n, IAf l < 2 ^ 126) (hssqb : ∀ l < n, ssqf l < 2 ^ 126)
    (hcob : ∀ q l, l < n → co q l < 2 ^ 48) (hd : d < 2 ^ 90)
    (hq1b : ∀ l < n, q1 l < 2 ^ 37) (hr1b : ∀ l < n, r1 l < 2 ^ 92)
    (hq1e : ∀ l < n, ¬ A1f l ≤ B l → A0f l < B l →
      q1 l = (B l - A0f l) / (a1 + sigf l) ∧ r1 l = (B l - A0f l) % (a1 + sigf l))
    (hArp : A.rp = pack LW n rpf) (hArn : A.rn = pack LW n rnf)
    (hAac : A.ac = (List.range (d + 1)).map fun q => pack LW n (af q))
    (hAlm : A.lm = (List.range (d + 1)).map fun q => pack LW n (lf q))
    (hok : (topCellV.topCellV4 (mkVC n) a1 tv cv isTop A (pack LW n B)
        (pack LW n fun l => if A1f l ≤ B l then 2 ^ 143 else 0)
        (pack LW n fun l => if B l ≤ A0f l then 2 ^ 143 else 0) (pack LW n S)
        (pack LW n fun l => if ¬A1f l ≤ B l ∧ ¬B l ≤ A0f l then 2 ^ 143 else 0)
        (pack LW n fun l => if ¬A1f l ≤ B l ∧ S l ≠ 0 ∧ ¬B l + S l ≤ A0f l then 2 ^ 143 else 0)
        (pack LW n q1, pack LW n r1)).ok = true) :
    topCellV.topCellV4 (mkVC n) a1 tv cv isTop A (pack LW n B)
        (pack LW n fun l => if A1f l ≤ B l then 2 ^ 143 else 0)
        (pack LW n fun l => if B l ≤ A0f l then 2 ^ 143 else 0) (pack LW n S)
        (pack LW n fun l => if ¬A1f l ≤ B l ∧ ¬B l ≤ A0f l then 2 ^ 143 else 0)
        (pack LW n fun l => if ¬A1f l ≤ B l ∧ S l ≠ 0 ∧ ¬B l + S l ≤ A0f l then 2 ^ 143 else 0)
        (pack LW n q1, pack LW n r1) = LA.mk
      (pack LW n fun l => rpf l + (if A1f l ≤ B l then IAf l else if B l ≤ A0f l then h2 * B l else
        (a0f l + a0f l + a1 * (pa + pa + (B l - A0f l) / (a1 + sigf l))) *
            ((B l - A0f l) / (a1 + sigf l)) +
          2 * (B l * (h - (B l - A0f l) / (a1 + sigf l)))))
      (pack LW n fun l => rnf l + (if A1f l ≤ B l then 0 else if B l ≤ A0f l then ssqf l else
        (pb * pb - (pa + (B l - A0f l) / (a1 + sigf l)) * (pa + (B l - A0f l) / (a1 + sigf l))) *
            sigf l + ((a1 + sigf l) + (a1 + sigf l))))
      ((List.range (d + 1)).map fun q => pack LW n fun l => af q l +
        (if ¬ A1f l ≤ B l ∧ S l ≠ 0 then (if q < d then co q l else if isTop = true then 0 else PmL) *
          (if B l + S l ≤ A0f l then h else
            chord.chord1 pa (pa + h) (B l) (S l) (a1 + sigf l) (A0f l) (A1f l))
        else 0))
      ((List.range (d + 1)).map fun q => pack LW n fun l => lf q l +
        (if A1f l ≤ B l then (if q < d then
            (if o q l then dq (ownBefore o q l) ((B l - A1f l) / 2 ^ 36) else 0)
          else if (isTop && tv.topOn) = true then dq (ownBefore o d l) ((B l - A1f l) / 2 ^ 36) else 0)
        else 0))
      A.ok ∧
    ∀ l < n, ¬A1f l ≤ B l ∧ S l ≠ 0 ∧ ¬B l + S l ≤ A0f l →
      chord.chord1 pa (pa + h) (B l) (S l) (a1 + sigf l) (A0f l) (A1f l) ≤ QMX := by
  have hDS : DS = 2 ^ 36 := rfl
  have b143 : ∀ {x k : ℕ}, x < 2 ^ k → k ≤ 143 → x < 2 ^ 143 := fun hx hk =>
    lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hk)
  have b144 : ∀ {x k : ℕ}, x < 2 ^ k → k ≤ 144 → x < 2 ^ 144 := fun hx hk =>
    lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hk)
  have hhD : h ≤ DS := by omega
  have hKb : ∀ l < n, a1 + sigf l < 2 ^ 50 := fun l hl => by
    have := hsigb l hl
    have : (2 : ℕ) ^ 47 + 2 ^ 48 ≤ 2 ^ 50 := by norm_num
    omega
  have hAh : ∀ l < n, A1f l = A0f l + (a1 + sigf l) * h := fun l hl => by
    rw [hA1e l hl, hA0e l hl, hhd, Nat.mul_sub, add_assoc, Nat.add_sub_cancel' (Nat.mul_le_mul_left _ hpab)]
  -- in a lane with `A0 < B < A1`: `K > 0` and `(B - A0) / K < h`
  have hdivh : ∀ l < n, ¬ A1f l ≤ B l → A0f l < B l →
      0 < a1 + sigf l ∧ (B l - A0f l) / (a1 + sigf l) < h := fun l hl h1 h2 => by
    have e := hAh l hl
    have hK : 0 < a1 + sigf l := by
      rcases Nat.eq_zero_or_pos (a1 + sigf l) with h0 | h0
      · rw [h0, zero_mul, add_zero] at e; omega
      · exact h0
    refine ⟨hK, (Nat.div_lt_iff_lt_mul hK).2 ?_⟩
    rw [mul_comm]; omega
  unfold topCellV.topCellV4 topCellV.topCellV5 at hok ⊢
  rw [bsel_mask_eq, bsel_mask_eq] at hok ⊢
  rw [show ((pack LW n q1, pack LW n r1) : ℕ × ℕ).1 = pack LW n q1 from rfl,
    show ((pack LW n q1, pack LW n r1) : ℕ × ℕ).2 = pack LW n r1 from rfl] at hok ⊢
  rw [crossV_spec n a1 cv a0f sigf (fun l => a1 + sigf l) B q1 ha0 hsig hkk ha1 (by rw [hpa]; omega)
    (by rw [hh]; exact hhD)
    (by rw [hpb2]; exact (Nat.mul_le_mul hpbD hpbD).trans (le_of_eq rfl)) ha0b hsigb hKb
    (fun l hl => lt_trans (hBb l hl) (by norm_num)) hq1b] at hok ⊢
  rw [ite_fst, ite_snd] at hok ⊢
  rw [hpa, hh, hpb2, hkk, hA0, hA1] at hok ⊢
  obtain ⟨eC1, eC2, hAok, hQMX⟩ := ch_facts n h pa a1 B S sigf A0f A1f q1 r1 A.ok _ rfl hhD
    (fun l hl => lt_trans (hBb l hl) (by norm_num)) (fun l hl => lt_trans (hSb l hl) (by norm_num))
    hKb (fun l hl => lt_trans (hA0b l hl) (by norm_num)) (fun l hl => lt_trans (hA1b l hl) (by norm_num))
    hq1b hr1b hAh hq1e (show bsel _ A.ok false = true from hok)
  refine ⟨?_, hQMX⟩
  rw [eC1, eC2]
  clear hok eC1 eC2
  have eBS : Nat.add (pack LW n B) (pack LW n S) = pack LW n fun l => B l + S l := by
    rw [Nat.add_eq, pack_add]
  have hBS : ∀ l < n, B l + S l < 2 ^ 92 := fun l hl => by
    have := hBb l hl; have := hSb l hl
    have : (2 : ℕ) ^ 90 + 2 ^ 91 ≤ 2 ^ 92 := by norm_num
    omega
  rw [notM_eq, nz_eq n S (fun l hl => b143 (hSb l hl) (by norm_num)), land_gm, eBS,
    ge_eq n A0f (fun l => B l + S l) (fun l hl => b143 (hA0b l hl) (by norm_num))
      (fun l hl => b143 (hBS l hl) (by norm_num)), bc_eq]
  rw [sl_eq n (fun l => B l + S l ≤ A0f l) (fun _ => h) _ (fun l hl => b144 (lt_of_le_of_lt hhD
    (by rw [hDS]; norm_num)) (le_refl 144)) (fun l hl => by
      split_ifs with hc
      · exact lt_of_le_of_lt (hQMX l hl hc) (by norm_num [QMX])
      · norm_num)]
  have hcrp : ∀ l < n, (a0f l + a0f l + a1 * (pa + pa + q1 l)) * q1 l + 2 * (B l * (h - q1 l)) < 2 ^ 131 :=
    fun l hl => crossP_lt _ _ _ _ _ _ (ha0b l hl) ha1 (by omega) (hq1b l hl)
      (lt_trans (hBb l hl) (by norm_num)) (by omega)
  have hcrn : ∀ l < n, (pb * pb - (pa + q1 l) * ((pa + q1 l) % 2 ^ 37)) * sigf l +
      (a1 + sigf l + (a1 + sigf l)) < 2 ^ 131 :=
    fun l hl => crossN_lt _ _ _ _ _ (by omega) (hsigb l hl) (hKb l hl)
  have hh2B : ∀ l < n, h2 * B l < 2 ^ 144 := fun l hl =>
    mul_lt_pow (show h2 < 2 ^ 38 by omega) (hBb l hl) (by norm_num)
  rw [hIA, hh2, Nat.mul_eq, pack_const_mul,
    sl_eq n (fun l => B l ≤ A0f l) (fun l => h2 * B l) _ hh2B (fun l hl => by
      split_ifs <;> first | exact b144 (hcrp l hl) (by norm_num) | norm_num),
    sl_eq n (fun l => A1f l ≤ B l) IAf _ (fun l hl => b144 (hIAb l hl) (by norm_num)) (fun l hl => by
      split_ifs <;> first | exact hh2B l hl | exact b144 (hcrp l hl) (by norm_num) | norm_num),
    hArp, Nat.add_eq, pack_add]
  rw [hssq, sl_eq n (fun l => B l ≤ A0f l) ssqf _ (fun l hl => b144 (hssqb l hl) (by norm_num))
      (fun l hl => by split_ifs <;> first | exact b144 (hcrn l hl) (by norm_num) | norm_num),
    sl_zero_eq n (fun l => A1f l ≤ B l) _ (fun l hl => by
      split_ifs <;> first | exact b144 (hssqb l hl) (by norm_num) |
        exact b144 (hcrn l hl) (by norm_num) | norm_num),
    hArn, Nat.add_eq, pack_add]
  have hBA1 : ∀ l < n, B l - A1f l < 2 ^ 143 := fun l hl =>
    lt_of_le_of_lt (Nat.sub_le _ _) (b143 (hBb l hl) (by norm_num))
  rw [tsub_eq n B A1f (fun l hl => b143 (hBb l hl) (by norm_num))
      (fun l hl => b143 (hA1b l hl) (by norm_num)),
    shr36_eq n (fun l => B l - A1f l) (fun l hl => lt_trans (hBA1 l hl) (by norm_num)), hown,
    creditV_eq n d o (fun l => (B l - A1f l) / 2 ^ 36) (bsel isTop tv.topOn false) hd
      (fun l hl => lt_of_le_of_lt (Nat.div_le_self _ _) (hBA1 l hl))]
  rw [topCellV6_eq n d tv cv isTop A (fun l => A1f l ≤ B l) (fun l => ¬A1f l ≤ B l ∧ S l ≠ 0)
    (fun l => if B l + S l ≤ A0f l then h else if ¬A1f l ≤ B l ∧ S l ≠ 0 ∧ ¬B l + S l ≤ A0f l then
        chord.chord1 pa (pa + h) (B l) (S l) (a1 + sigf l) (A0f l) (A1f l) else 0)
    true _ _ co o (fun l => (B l - A1f l) / 2 ^ 36) (bsel isTop tv.topOn false) af lf hco hAac hAlm
    hcob (by rw [hPm]; exact hPmL) (fun l hl => by
      split_ifs with h1 h2
      · exact lt_of_le_of_lt hhD (by rw [hDS]; norm_num)
      · exact lt_of_le_of_lt (hQMX l hl h2) (by norm_num [QMX])
      · norm_num)]
  congr 1
  · refine pack_congr _ _ _ _ fun l hl => ?_
    congr 1
    by_cases h1 : A1f l ≤ B l
    · rw [ite_eq_left h1, ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : B l ≤ A0f l
      · rw [ite_eq_left h2, ite_eq_left h2]
      · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_left ⟨l, hl, h1, h2⟩,
          (hq1e l hl h1 (not_le.1 h2)).1]
  · refine pack_congr _ _ _ _ fun l hl => ?_
    congr 1
    by_cases h1 : A1f l ≤ B l
    · rw [ite_eq_left h1, ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : B l ≤ A0f l
      · rw [ite_eq_left h2, ite_eq_left h2]
      · have hlt := (hdivh l hl h1 (not_le.1 h2)).2
        rw [ite_eq_right h2, ite_eq_right h2, ite_eq_left ⟨l, hl, h1, h2⟩,
          (hq1e l hl h1 (not_le.1 h2)).1, Nat.mod_eq_of_lt (by omega)]
  · refine List.map_congr_left fun q _ => pack_congr _ _ _ _ fun l hl => ?_
    congr 1
    by_cases hu : ¬A1f l ≤ B l ∧ S l ≠ 0
    · rw [ite_eq_left hu, ite_eq_left hu]
      have hQ : (if B l + S l ≤ A0f l then h else
          if ¬A1f l ≤ B l ∧ S l ≠ 0 ∧ ¬B l + S l ≤ A0f l then
            chord.chord1 pa (pa + h) (B l) (S l) (a1 + sigf l) (A0f l) (A1f l) else 0) =
          (if B l + S l ≤ A0f l then h else
            chord.chord1 pa (pa + h) (B l) (S l) (a1 + sigf l) (A0f l) (A1f l)) := by
        by_cases h3 : B l + S l ≤ A0f l
        · rw [ite_eq_left h3, ite_eq_left h3]
        · rw [ite_eq_right h3, ite_eq_right h3, ite_eq_left ⟨hu.1, hu.2, h3⟩]
      have hQlt : (if B l + S l ≤ A0f l then h else
          chord.chord1 pa (pa + h) (B l) (S l) (a1 + sigf l) (A0f l) (A1f l)) < 2 ^ 37 := by
        by_cases h3 : B l + S l ≤ A0f l
        · rw [ite_eq_left h3]; exact lt_of_le_of_lt hhD (by rw [hDS]; norm_num)
        · rw [ite_eq_right h3]
          exact lt_of_le_of_lt (hQMX l hl ⟨hu.1, hu.2, h3⟩) (by norm_num [QMX])
      rw [hQ]
      by_cases hq : q < d
      · rw [ite_eq_left hq, ite_eq_left hq, Nat.mod_eq_of_lt hQlt]
      · rw [ite_eq_right hq, ite_eq_right hq, bsel_ite, hPm]
    · rw [ite_eq_right hu, ite_eq_right hu]

/-- The lanes of a cell `i ≤ im` of the top record, on abstract lane data. -/
theorem topCellV_core (n a1 d pa pb h h2 PmL : ℕ) (tv : TV) (cv : CV) (isTop : Bool) (A : LA)
    (B S a0f sigf A0f A1f IAf ssqf : ℕ → ℕ) (co : ℕ → ℕ → ℕ) (o : ℕ → ℕ → Prop)
    [∀ q l, Decidable (o q l)] (rpf rnf : ℕ → ℕ) (af lf : ℕ → ℕ → ℕ)
    (hB : Nat.add cv.bet (bc (mkVC n) tv.DEm) = pack LW n B)
    (hS : bsel isTop cv.sp (Nat.add cv.sp (bc (mkVC n) tv.PmW)) = pack LW n S)
    (hpa : cv.pa = pa) (hh : cv.h = h) (hh2 : cv.h2 = h2) (hpb2 : cv.pb2 = pb * pb)
    (hhd : h = pb - pa) (hpab : pa ≤ pb) (hpbD : pb ≤ DS) (hh2D : h2 ≤ DS + DS) (ha1 : a1 < 2 ^ 47)
    (hPm : tv.Pm = PmL) (hPmL : PmL < 2 ^ 47)
    (hsig : cv.sig = pack LW n sigf) (ha0 : cv.a0 = pack LW n a0f)
    (hkk : cv.kk = pack LW n fun l => a1 + sigf l)
    (hA0 : cv.A0 = pack LW n A0f) (hA1 : cv.A1 = pack LW n A1f)
    (hIA : cv.IA = pack LW n IAf) (hssq : cv.ssq = pack LW n ssqf)
    (hco : cv.co = (List.range d).map fun q => pack LW n (co q))
    (hown : cv.own = (List.range d).map fun q => pack LW n fun l => if o q l then 2 ^ 143 else 0)
    (hA0e : ∀ l < n, A0f l = a0f l + (a1 + sigf l) * pa)
    (hA1e : ∀ l < n, A1f l = a0f l + (a1 + sigf l) * pb)
    (hBb : ∀ l < n, B l < 2 ^ 90) (hSb : ∀ l < n, S l < 2 ^ 91)
    (hsigb : ∀ l < n, sigf l < 2 ^ 48) (ha0b : ∀ l < n, a0f l < 2 ^ 80)
    (hA0b : ∀ l < n, A0f l < 2 ^ 90) (hA1b : ∀ l < n, A1f l < 2 ^ 90)
    (hIAb : ∀ l < n, IAf l < 2 ^ 126) (hssqb : ∀ l < n, ssqf l < 2 ^ 126)
    (hcob : ∀ q l, l < n → co q l < 2 ^ 48) (hd : d < 2 ^ 90)
    (hArp : A.rp = pack LW n rpf) (hArn : A.rn = pack LW n rnf)
    (hAac : A.ac = (List.range (d + 1)).map fun q => pack LW n (af q))
    (hAlm : A.lm = (List.range (d + 1)).map fun q => pack LW n (lf q))
    (hok : (topCellV (mkVC n) a1 tv cv isTop A).ok = true) :
    topCellV (mkVC n) a1 tv cv isTop A = LA.mk
      (pack LW n fun l => rpf l + (if A1f l ≤ B l then IAf l else if B l ≤ A0f l then h2 * B l else
        (a0f l + a0f l + a1 * (pa + pa + (B l - A0f l) / (a1 + sigf l))) *
            ((B l - A0f l) / (a1 + sigf l)) +
          2 * (B l * (h - (B l - A0f l) / (a1 + sigf l)))))
      (pack LW n fun l => rnf l + (if A1f l ≤ B l then 0 else if B l ≤ A0f l then ssqf l else
        (pb * pb - (pa + (B l - A0f l) / (a1 + sigf l)) * (pa + (B l - A0f l) / (a1 + sigf l))) *
            sigf l + ((a1 + sigf l) + (a1 + sigf l))))
      ((List.range (d + 1)).map fun q => pack LW n fun l => af q l +
        (if ¬ A1f l ≤ B l ∧ S l ≠ 0 then (if q < d then co q l else if isTop = true then 0 else PmL) *
          (if B l + S l ≤ A0f l then h else
            chord.chord1 pa (pa + h) (B l) (S l) (a1 + sigf l) (A0f l) (A1f l))
        else 0))
      ((List.range (d + 1)).map fun q => pack LW n fun l => lf q l +
        (if A1f l ≤ B l then (if q < d then
            (if o q l then dq (ownBefore o q l) ((B l - A1f l) / 2 ^ 36) else 0)
          else if (isTop && tv.topOn) = true then dq (ownBefore o d l) ((B l - A1f l) / 2 ^ 36) else 0)
        else 0))
      A.ok ∧
    ∀ l < n, ¬A1f l ≤ B l ∧ S l ≠ 0 ∧ ¬B l + S l ≤ A0f l →
      chord.chord1 pa (pa + h) (B l) (S l) (a1 + sigf l) (A0f l) (A1f l) ≤ QMX := by
  have b143 : ∀ {x k : ℕ}, x < 2 ^ k → k ≤ 143 → x < 2 ^ 143 := fun hx hk =>
    lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hk)
  have hDS : DS = 2 ^ 36 := rfl
  have hhD : h ≤ DS := by omega
  have hKb : ∀ l < n, a1 + sigf l < 2 ^ 50 := fun l hl => by
    have := hsigb l hl
    have : (2 : ℕ) ^ 47 + 2 ^ 48 ≤ 2 ^ 50 := by norm_num
    omega
  have eSTOP := ge_eq n B A1f (fun l hl => b143 (hBb l hl) (by norm_num))
    (fun l hl => b143 (hA1b l hl) (by norm_num))
  have eLOW := ge_eq n A0f B (fun l hl => b143 (hA0b l hl) (by norm_num))
    (fun l hl => b143 (hBb l hl) (by norm_num))
  have eBS : Nat.add (pack LW n B) (pack LW n S) = pack LW n fun l => B l + S l := by
    rw [Nat.add_eq, pack_add]
  have eGE2 := ge_eq n A0f (fun l => B l + S l) (fun l hl => b143 (hA0b l hl) (by norm_num))
    (fun l hl => b143 (show B l + S l < 2 ^ 92 by
      have := hBb l hl; have := hSb l hl
      have : (2 : ℕ) ^ 90 + 2 ^ 91 ≤ 2 ^ 92 := by norm_num
      omega) (by norm_num))
  have eNZ := nz_eq n S (fun l hl => b143 (hSb l hl) (by norm_num))
  have eTS := tsub_eq n B A0f (fun l hl => b143 (hBb l hl) (by norm_num))
    (fun l hl => b143 (hA0b l hl) (by norm_num))
  have eDQ := divQR_eq n (fun l => B l - A0f l) (fun l => a1 + sigf l)
    (fun l hl => b143 (lt_of_le_of_lt (Nat.sub_le _ _) (hBb l hl)) (by norm_num))
    (fun l hl j hj => mul_lt_pow (hKb l hl) (Nat.pow_lt_pow_right (by norm_num) hj) (by omega))
  have hAh : ∀ l < n, A1f l = A0f l + (a1 + sigf l) * h := fun l hl => by
    rw [hA1e l hl, hA0e l hl, hhd, Nat.mul_sub, add_assoc,
      Nat.add_sub_cancel' (Nat.mul_le_mul_left _ hpab)]
  unfold topCellV topCellV.topCellV1 topCellV.topCellV2 topCellV.topCellV3 at hok ⊢
  rw [hB, hS, hA1, hA0, hkk, eSTOP, eLOW, eBS, eGE2, eNZ] at hok ⊢
  simp only [notM_eq, land_gm, lor_gm] at hok ⊢
  rw [bsel_mask_eq, eTS, eDQ, ite_pack2] at hok ⊢
  refine topCellV4_core n a1 d pa pb h h2 PmL tv cv isTop A B S a0f sigf A0f A1f IAf ssqf _ _ co o
    rpf rnf af lf hpa hh hh2 hpb2 hhd hpab hpbD hh2D ha1 hPm hPmL hsig ha0 hkk hA0 hA1 hIA hssq hco
    hown hA0e hA1e hBb hSb hsigb ha0b hA0b hA1b hIAb hssqb hcob hd ?_ ?_ ?_ hArp hArn hAac hAlm hok
  · intro l hl
    show _
    split_ifs <;> omega
  · intro l hl
    show _
    split_ifs <;> first
      | exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_le_of_lt (Nat.sub_le _ _)
          (lt_trans (hBb l hl) (by norm_num)))
      | norm_num
  · intro l hl h1 h2
    show _
    have e := hAh l hl
    have hK : 0 < a1 + sigf l := by
      rcases Nat.eq_zero_or_pos (a1 + sigf l) with h0 | h0
      · rw [h0, zero_mul, add_zero] at e; omega
      · exact h0
    have hlt : (B l - A0f l) / (a1 + sigf l) < h := (Nat.div_lt_iff_lt_mul hK).2 (by rw [mul_comm]; omega)
    have hmin : min ((B l - A0f l) / (a1 + sigf l)) (2 ^ 37 - 1) = (B l - A0f l) / (a1 + sigf l) :=
      min_eq_left (by rw [hDS] at hhD; omega)
    rw [ite_eq_right (Nat.pos_iff_ne_zero.1 hK), hmin, ite_eq_left ⟨l, hl, Or.inl ⟨h1, not_le.2 h2⟩⟩,
      ite_eq_left ⟨l, hl, Or.inl ⟨h1, not_le.2 h2⟩⟩, Nat.mod_eq_sub_mul_div]
    exact ⟨rfl, rfl⟩

/-! ## The scalar terms of `topCell` in the form of `topCellV_core` -/

theorem tRP_lane (a1 : ℕ) (pd : PD) (beta pa h h2 : ℕ) (hpa : pd.pa = pa) (hh : pd.h = h)
    (hh2 : pd.h2 = h2) :
    tRP a1 pd beta = if pd.A1 ≤ beta then pd.IA else if beta ≤ pd.A0 then h2 * beta else
      (pd.a0 + pd.a0 + a1 * (pa + pa + (beta - pd.A0) / (a1 + pd.sig))) *
          ((beta - pd.A0) / (a1 + pd.sig)) +
        2 * (beta * (h - (beta - pd.A0) / (a1 + pd.sig))) := by
  unfold tRP tQ1
  rw [hpa, hh, hh2]

theorem tRN_lane (a1 : ℕ) (pd : PD) (beta pa pb : ℕ) (hpa : pd.pa = pa) (hpb : pd.pb = pb) :
    tRN a1 pd beta = if pd.A1 ≤ beta then 0 else if beta ≤ pd.A0 then pd.ssq else
      (pb * pb - (pa + (beta - pd.A0) / (a1 + pd.sig)) * (pa + (beta - pd.A0) / (a1 + pd.sig))) *
          pd.sig + ((a1 + pd.sig) + (a1 + pd.sig)) := by
  unfold tRN tQ1
  rw [hpa, hpb]

theorem qCont_lane (a1 : ℕ) (pd : PD) (beta S pa h : ℕ) (hpa : pd.pa = pa) (hpb : pd.pb = pa + h)
    (hh : pd.h = h) (hA0 : pd.A0 = pd.a0 + (a1 + pd.sig) * pd.pa)
    (hA1 : pd.A1 = pd.a0 + (a1 + pd.sig) * pd.pb) :
    qCont a1 pd beta S =
      if beta + S ≤ pd.A0 then h else chord.chord1 pa (pa + h) beta S (a1 + pd.sig) pd.A0 pd.A1 := by
  unfold qCont chord
  rw [bsel_ite]
  show (if Nat.ble (beta + S) pd.A0 = true then pd.h else
    chord.chord1 pd.pa pd.pb beta S (a1 + pd.sig) (pd.a0 + (a1 + pd.sig) * pd.pa)
      (pd.a0 + (a1 + pd.sig) * pd.pb)) = _
  rw [← hA0, ← hA1, hpa, hpb, hh]
  by_cases hc : beta + S ≤ pd.A0
  · rw [ite_eq_left (by rw [Nat.ble_eq]; exact hc), ite_eq_left hc]
  · rw [ite_eq_right (by rw [Nat.ble_eq]; exact hc), ite_eq_right hc]

theorem tAC_lane (a1 : ℕ) (tp : Tp) (pd : PD) (isTop : Bool) (beta d : ℕ) (co : ℕ → ℕ)
    (PmL q pa h : ℕ) (hpa : pd.pa = pa) (hpb : pd.pb = pa + h) (hh : pd.h = h)
    (hA0 : pd.A0 = pd.a0 + (a1 + pd.sig) * pd.pa) (hA1 : pd.A1 = pd.a0 + (a1 + pd.sig) * pd.pb) :
    tAC a1 tp pd isTop beta d co PmL q =
      if ¬ pd.A1 ≤ beta ∧ tS tp pd isTop ≠ 0 then
        (if q < d then co q else if isTop = true then 0 else PmL) *
          (if beta + tS tp pd isTop ≤ pd.A0 then h else
            chord.chord1 pa (pa + h) beta (tS tp pd isTop) (a1 + pd.sig) pd.A0 pd.A1)
      else 0 := by
  unfold tAC
  rw [qCont_lane a1 pd beta _ pa h hpa hpb hh hA0 hA1]

theorem tLM_lane (pd : PD) (isTop topOn : Bool) (beta d : ℕ) (o : ℕ → Prop) [DecidablePred o]
    (TO q : ℕ) (hTO : TO = if topOn = true then 1 else 0) :
    tLM pd isTop beta d o TO q =
      if pd.A1 ≤ beta then (if q < d then
          (if o q then dq ((Finset.range q).filter o).card ((beta - pd.A1) / 2 ^ 36) else 0)
        else if (isTop && topOn) = true then
          dq ((Finset.range d).filter o).card ((beta - pd.A1) / 2 ^ 36) else 0)
      else 0 := by
  unfold tLM
  rw [show (2 : ℕ) ^ 36 = DS from rfl, hTO]
  by_cases h1 : pd.A1 ≤ beta
  · rw [ite_eq_left h1, ite_eq_left h1]
    by_cases hq : q < d
    · rw [ite_eq_left hq, ite_eq_left hq]
    · rw [ite_eq_right hq, ite_eq_right hq]
      cases isTop <;> cases topOn
      · rw [ite_eq_right (by decide), ite_eq_right (by decide)]
      · rw [ite_eq_right (by decide), ite_eq_right (by decide)]
      · rw [ite_eq_left (show true = true from rfl), ite_eq_right (by decide), mul_zero,
          ite_eq_right (by decide)]
      · rw [ite_eq_left (show true = true from rfl), ite_eq_left (show true = true from rfl), mul_one,
          ite_eq_left (show (true && true) = true from rfl)]
  · rw [ite_eq_right h1, ite_eq_right h1]

/-! ## Their bounds -/

theorem tRP_le (a1 : ℕ) (pd : PD) (beta : ℕ) (ha1 : a1 < 2 ^ 47) (hbeta : beta < 2 ^ 86)
    (ha0 : pd.a0 < 2 ^ 78) (hpa : pd.pa ≤ 2 ^ 36) (hh : pd.h ≤ 2 ^ 36) (hh2 : pd.h2 ≤ 2 ^ 37)
    (hIA : pd.IA < 2 ^ 126) (hA : pd.A1 = pd.A0 + (a1 + pd.sig) * pd.h) :
    tRP a1 pd beta ≤ 2 ^ 126 := by
  unfold tRP tQ1
  by_cases h1 : pd.A1 ≤ beta
  · rw [ite_eq_left h1]; exact hIA.le
  · rw [ite_eq_right h1]
    by_cases h2 : beta ≤ pd.A0
    · rw [ite_eq_left h2]
      exact (mul_lt_pow (show pd.h2 < 2 ^ 38 by omega) hbeta (le_refl _)).le.trans (by norm_num)
    · rw [ite_eq_right h2]
      have hK : 0 < a1 + pd.sig := by
        rcases Nat.eq_zero_or_pos (a1 + pd.sig) with h0 | h0
        · rw [h0, zero_mul, add_zero] at hA; omega
        · exact h0
      have hq : (beta - pd.A0) / (a1 + pd.sig) < pd.h :=
        (Nat.div_lt_iff_lt_mul hK).2 (by rw [mul_comm]; omega)
      have e1 : a1 * (pd.pa + pd.pa + (beta - pd.A0) / (a1 + pd.sig)) < 2 ^ (47 + 38) :=
        mul_lt_pow ha1 (show pd.pa + pd.pa + (beta - pd.A0) / (a1 + pd.sig) < 2 ^ 38 by omega)
          (le_refl _)
      have e2 : pd.a0 + pd.a0 + a1 * (pd.pa + pd.pa + (beta - pd.A0) / (a1 + pd.sig)) < 2 ^ 86 := by
        have : (2 : ℕ) ^ 78 + 2 ^ 78 + 2 ^ (47 + 38) ≤ 2 ^ 86 := by norm_num
        omega
      have e3 := mul_lt_pow e2 (lt_of_lt_of_le hq (hh.trans (by norm_num : (2 : ℕ) ^ 36 ≤ 2 ^ 37))) (le_refl _)
      have e4 := mul_lt_pow hbeta (lt_of_le_of_lt (Nat.sub_le _ ((beta - pd.A0) / (a1 + pd.sig)))
          (lt_of_le_of_lt hh (by norm_num : (2 : ℕ) ^ 36 < 2 ^ 37)))
        (le_refl _)
      have : (2 : ℕ) ^ (86 + 37) + 2 * 2 ^ (86 + 37) ≤ 2 ^ 126 := by norm_num
      omega

theorem tRN_le (a1 : ℕ) (pd : PD) (beta : ℕ) (ha1 : a1 < 2 ^ 47) (hpb : pd.pb ≤ 2 ^ 36)
    (hsig : pd.sig < 2 ^ 48) (hssq : pd.ssq < 2 ^ 126) : tRN a1 pd beta ≤ 2 ^ 126 := by
  unfold tRN
  by_cases h1 : pd.A1 ≤ beta
  · rw [ite_eq_left h1]; exact Nat.zero_le _
  · rw [ite_eq_right h1]
    by_cases h2 : beta ≤ pd.A0
    · rw [ite_eq_left h2]; exact hssq.le
    · rw [ite_eq_right h2]
      have e1 : pd.pb * pd.pb ≤ 2 ^ 72 := (Nat.mul_le_mul hpb hpb).trans (by norm_num)
      have e2 := mul_lt_pow (show pd.pb * pd.pb - (pd.pa + tQ1 a1 pd beta) * (pd.pa + tQ1 a1 pd beta) <
        2 ^ 73 by omega) hsig (le_refl _)
      have : (2 : ℕ) ^ (73 + 48) + 2 ^ 48 * 4 ≤ 2 ^ 126 := by norm_num
      omega


theorem tAC_le (a1 : ℕ) (tp : Tp) (pd : PD) (isTop : Bool) (beta d : ℕ) (co : ℕ → ℕ)
    (PmL q pa h : ℕ) (hpa : pd.pa = pa) (hpb : pd.pb = pa + h) (hh : pd.h = h)
    (hA0 : pd.A0 = pd.a0 + (a1 + pd.sig) * pd.pa) (hA1 : pd.A1 = pd.a0 + (a1 + pd.sig) * pd.pb)
    (hco : ∀ q, co q < 2 ^ 48) (hPmL : PmL < 2 ^ 47) (hhD : h ≤ 2 ^ 36)
    (hQ : ¬ pd.A1 ≤ beta → tS tp pd isTop ≠ 0 → ¬ beta + tS tp pd isTop ≤ pd.A0 →
      chord.chord1 pa (pa + h) beta (tS tp pd isTop) (a1 + pd.sig) pd.A0 pd.A1 ≤ QMX) :
    tAC a1 tp pd isTop beta d co PmL q ≤ 2 ^ 126 := by
  rw [tAC_lane a1 tp pd isTop beta d co PmL q pa h hpa hpb hh hA0 hA1]
  by_cases hu : ¬ pd.A1 ≤ beta ∧ tS tp pd isTop ≠ 0
  · rw [ite_eq_left hu]
    have hc : (if q < d then co q else if isTop = true then 0 else PmL) < 2 ^ 48 := by
      split_ifs
      · exact hco q
      · norm_num
      · exact lt_trans hPmL (by norm_num)
    have hq : (if beta + tS tp pd isTop ≤ pd.A0 then h else
        chord.chord1 pa (pa + h) beta (tS tp pd isTop) (a1 + pd.sig) pd.A0 pd.A1) < 2 ^ 37 := by
      by_cases h3 : beta + tS tp pd isTop ≤ pd.A0
      · rw [ite_eq_left h3]; exact lt_of_le_of_lt hhD (by norm_num)
      · rw [ite_eq_right h3]
        exact lt_of_le_of_lt (hQ hu.1 hu.2 h3) (by norm_num [QMX])
    exact (mul_lt_pow hc hq (le_refl _)).le.trans (by norm_num)
  · rw [ite_eq_right hu]; exact Nat.zero_le _

theorem tLM_le (pd : PD) (isTop : Bool) (beta d : ℕ) (o : ℕ → Prop) [DecidablePred o] (TO q : ℕ)
    (hTO : TO ≤ 1) : tLM pd isTop beta d o TO q ≤ 2 ^ 126 := by
  have hD : DS ≤ 2 ^ 126 := by rw [show DS = 2 ^ 36 from rfl]; norm_num
  unfold tLM
  by_cases h1 : pd.A1 ≤ beta
  · rw [ite_eq_left h1]
    by_cases hq : q < d
    · rw [ite_eq_left hq]
      by_cases ho : o q
      · rw [ite_eq_left ho]; exact (dqL_le _ _).trans hD
      · rw [ite_eq_right ho]; exact Nat.zero_le _
    · rw [ite_eq_right hq]
      by_cases ht : isTop = true
      · rw [ite_eq_left ht]
        exact (Nat.mul_le_mul (dqL_le _ _) hTO).trans (by rw [mul_one]; exact hD)
      · rw [ite_eq_right ht]; exact Nat.zero_le _
  · rw [ite_eq_right h1]; exact Nat.zero_le _

end Robbins.Cert.SO.L
