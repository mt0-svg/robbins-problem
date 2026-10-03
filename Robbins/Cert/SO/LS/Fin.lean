import Robbins.Cert.SO.LS.Vec
import Robbins.Cert.SO.LS.Kc

/-!
# The lanes step: the final check on lanes

`finCheck` on `n` lanes gives, lane by lane, `2 D^2 uh + rn ≤ rp`, the fields of `acc` and `lam`
below `2 ^ 128` and `sg_q ≤ mu_q`; `muOK` then passes on the packed fields of each lane.
-/

namespace Robbins.Cert.SO.L

open Robbins.Cert Robbins.Cert.K Robbins.Cert.SO.K Robbins.Lanes

/-- `muOK` on the packed fields `a q`, `b q` (below `2 ^ 128`) of `ac`, `lm`. -/
theorem muOK_of (cs : List SR) (sg : List ℕ) (a b : ℕ → ℕ) (hlen : sg.length = cs.length)
    (ha : ∀ q < cs.length, a q < 2 ^ 128) (hb : ∀ q < cs.length, b q < 2 ^ 128)
    (hs : ∀ q (hq : q < cs.length), sg.getD q 0 ≤ if cs[q].fg = true then 0 else b q + a q / DS) :
    muOK cs sg (∑ q ∈ Finset.range cs.length, a q * F128 ^ q)
      (∑ q ∈ Finset.range cs.length, b q * F128 ^ q) = true := by
  have key : ∀ (c : ℕ → ℕ) (L : ℕ), ∑ q ∈ Finset.range (L + 1), c q * F128 ^ q =
      c 0 + (∑ q ∈ Finset.range L, c (q + 1) * F128 ^ q) * 2 ^ 128 := by
    intro c L
    rw [Finset.sum_range_succ', Finset.sum_mul, add_comm]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [pow_succ, show F128 = 2 ^ 128 from rfl]
      ring
  have hlo : ∀ (x T : ℕ), x < 2 ^ 128 → Nat.land (x + T * 2 ^ 128) M128 = x := by
    intro x T hx
    show (x + T * 2 ^ 128) &&& (2 ^ 128 - 1) = x
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  have hhi : ∀ (x T : ℕ), x < 2 ^ 128 → Nat.shiftRight (x + T * 2 ^ 128) 128 = T := by
    intro x T hx
    show (x + T * 2 ^ 128) >>> 128 = T
    rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hx,
      zero_add]
  induction cs generalizing sg a b with
  | nil =>
    cases sg with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons r cs ih =>
    cases sg with
    | nil => simp at hlen
    | cons s sg' =>
      simp only [List.length_cons] at hlen ha hb ⊢
      rw [key a, key b]
      have ha0 := ha 0 (by omega)
      have hb0 := hb 0 (by omega)
      show bsel (Nat.ble s (bsel r.fg 0 (Nat.add (Nat.land _ M128) (Nat.div (Nat.land _ M128) DS))))
        (muOK cs sg' (Nat.shiftRight _ 128) (Nat.shiftRight _ 128)) false = true
      rw [hlo _ _ ha0, hlo _ _ hb0, hhi _ _ ha0, hhi _ _ hb0]
      have hs0 := hs 0 (by simp)
      simp only [List.getD_cons_zero, List.getElem_cons_zero] at hs0
      have hle : Nat.ble s (bsel r.fg 0 (Nat.add (b 0) (Nat.div (a 0) DS))) = true := by
        rw [Nat.ble_eq, bsel_eq]
        exact hs0
      rw [hle]
      exact ih sg' (fun q => a (q + 1)) (fun q => b (q + 1)) (by omega)
        (fun q hq => ha (q + 1) (by omega)) (fun q hq => hb (q + 1) (by omega))
        (fun q hq => by
          have := hs (q + 1) (by simp; omega)
          simpa using this)

theorem finCheck_lanes_aux1 {α β γ : Type} (f : α → β → γ) (m : ℕ) (F : ℕ → α) (G : ℕ → β) :
    lzipWith f ((List.range m).map F) ((List.range m).map G) =
      (List.range m).map fun q => f (F q) (G q) := by
  rw [lzipWith_eq]
  apply List.ext_getElem <;> simp

theorem finCheck_lanes_aux2 (x y : Bool) (h : bsel x y false = true) : x = true ∧ y = true := by
  cases x <;> cases y <;> simp_all [bsel_eq]

theorem finCheck_lanes_aux3 (n : ℕ) (f : ℕ → Bool) :
    pre LW n (Nat.shiftLeft (pack LW n fun l => if f l then 1 else 0) 143) =
      pack LW n fun l => if f l = true then 2 ^ 143 else 0 := by
  show pre LW n ((pack LW n fun l => if f l = true then 1 else 0) <<< 143) = _
  rw [Nat.shiftLeft_eq, mul_comm, pack_const_mul,
    pre_eq n n _ (fun l _ => by split_ifs <;> norm_num) le_rfl]
  exact pack_congr _ _ _ _ fun l _ => by split_ifs <;> simp

/-- `finCheck` on `n` lanes, lane by lane (`m ≥ 1` slots, the forgotten flags `fgf q` of the
first `m - 1` slots and `topFg` of the last). -/
theorem finCheck_lanes (n m : ℕ) (hm : 1 ≤ m) (pv : PV) (fgf : ℕ → ℕ → Bool) (topFg : Bool)
    (hfg : pv.fg = (List.range (m - 1)).map fun q => pack LW n fun l => if fgf q l then 1 else 0)
    (uf : ℕ → ℕ) (sf : ℕ → ℕ → ℕ) (huf : ∀ l < n, uf l < 2 ^ 48)
    (hsf : ∀ f l, l < n → sf f l < 2 ^ 48) (A : LA) (rp rn : ℕ → ℕ) (af lf : ℕ → ℕ → ℕ)
    (hrp : A.rp = pack LW n rp) (hrn : A.rn = pack LW n rn)
    (hac : A.ac = (List.range m).map fun q => pack LW n (af q))
    (hlm : A.lm = (List.range m).map fun q => pack LW n (lf q))
    (hB : ∀ l < n, rp l < 2 ^ 142 ∧ rn l < 2 ^ 142 ∧ ∀ q < m, af q l < 2 ^ 142 ∧ lf q l < 2 ^ 142)
    (h : finCheck (mkVC n) pv (pack LW n uf) ((List.range m).map fun f => pack LW n (sf f)) topFg A =
      true) :
    ∀ l < n, 2 * DS2 * uf l + rn l ≤ rp l ∧ ∀ q < m, af q l < 2 ^ 128 ∧ lf q l < 2 ^ 128 ∧
      sf q l ≤ if (if q < m - 1 then fgf q l else topFg) = true then 0 else lf q l + af q l / DS := by
  have hm' : m - 1 + 1 = m := by omega
  have hDS : DS = 2 ^ 36 := rfl
  unfold finCheck at h
  obtain ⟨-, h⟩ := finCheck_lanes_aux2 _ _ h
  obtain ⟨hge, h⟩ := finCheck_lanes_aux2 _ _ h
  have e1 : Nat.add (Nat.mul (Nat.mul 2 DS2) (pack LW n uf)) (pack LW n rn) =
      pack LW n fun l => 2 * DS2 * uf l + rn l := by
    show 2 * DS2 * pack LW n uf + pack LW n rn = _
    rw [pack_const_mul, pack_add]
  rw [hrp, hrn, e1, allGe_eq n rp _ (fun l hl => lt_trans (hB l hl).1 (by norm_num))
    (fun l hl => by
      have h1 : 2 * DS2 * uf l ≤ 2 * DS2 * 2 ^ 48 := Nat.mul_le_mul_left _ (huf l hl).le
      have h2 := (hB l hl).2.1
      have h3 : 2 * DS2 * 2 ^ 48 + 2 ^ 142 < 2 ^ 143 := by norm_num [DS2]
      omega)] at hge
  have hFL : lapp (lmap (fun F => pre LW (mkVC n).n (Nat.shiftLeft F 143)) pv.fg)
      [bsel topFg (mkVC n).G 0] = (List.range m).map fun q =>
        pack LW n fun l => if (if q < m - 1 then fgf q l else topFg) = true then 2 ^ 143 else 0 := by
    rw [lapp_eq, lmap_eq, hfg, List.map_map, mkVC_n]
    have hr : List.range m = List.range (m - 1) ++ [m - 1] := by
      rw [← List.range_succ, Nat.succ_eq_add_one, hm']
    rw [hr, List.map_append, List.map_singleton]
    congr 1
    · refine List.map_congr_left fun q hq => ?_
      have hq' : q < m - 1 := List.mem_range.1 hq
      simp only [Function.comp_apply, hq', ↓reduceIte]
      exact finCheck_lanes_aux3 n (fgf q)
    · rw [mkVC_G]
      simp only [lt_irrefl, ↓reduceIte]
      cases topFg <;> simp [bsel_eq, pack]
  rw [hFL, hac, hlm] at h
  simp only [finCheck_lanes_aux1] at h
  rw [lall_iff] at h
  intro l hl
  refine ⟨hge l hl, fun q hq => ?_⟩
  have hv := h _ (List.mem_map.2 ⟨q, List.mem_range.2 hq, rfl⟩)
  obtain ⟨ha, hv⟩ := finCheck_lanes_aux2 _ _ hv
  obtain ⟨hb, hc⟩ := finCheck_lanes_aux2 _ _ hv
  have hM : M128' < 2 ^ 143 := by norm_num [M128']
  rw [bc_eq, allGe_eq n _ _ (fun _ _ => hM) (fun l hl => lt_trans ((hB l hl).2.2 q hq).1
    (by norm_num))] at ha
  rw [bc_eq, allGe_eq n _ _ (fun _ _ => hM) (fun l hl => lt_trans ((hB l hl).2.2 q hq).2
    (by norm_num))] at hb
  have haf : af q l < 2 ^ 128 := by
    have := ha l hl; have e : M128' = 2 ^ 128 - 1 := rfl; rw [e] at this; omega
  have hlf : lf q l < 2 ^ 128 := by
    have := hb l hl; have e : M128' = 2 ^ 128 - 1 := rfl; rw [e] at this; omega
  refine ⟨haf, hlf, ?_⟩
  have e2 : Nat.add (pack LW n (lf q)) (shr36 (pack LW n (af q)) (mkVC n)) =
      pack LW n fun l => lf q l + af q l / 2 ^ 36 := by
    rw [shr36_eq n _ (fun l hl => lt_trans ((hB l hl).2.2 q hq).1 (by norm_num))]
    exact pack_add _ _ _ _
  rw [notM_eq, e2, msk_eq n _ _ (fun l hl => by
    have h1 := ((hB l hl).2.2 q hq).2
    have h2 : af q l / 2 ^ 36 ≤ af q l := Nat.div_le_self _ _
    have h3 := ((hB l hl).2.2 q hq).1
    have h4 : (2 : ℕ) ^ 142 + 2 ^ 142 = 2 ^ 143 := by norm_num
    omega), allGe_eq n _ _ (fun l hl => by
      have h1 := ((hB l hl).2.2 q hq).2
      have h2 : af q l / 2 ^ 36 ≤ af q l := Nat.div_le_self _ _
      have h3 := ((hB l hl).2.2 q hq).1
      have h4 : (2 : ℕ) ^ 142 + 2 ^ 142 = 2 ^ 143 := by norm_num
      split_ifs <;> omega)
    (fun l hl => lt_trans (hsf q l hl) (by norm_num))] at hc
  have := hc l hl
  rw [hDS]
  split_ifs at this ⊢ <;> simp_all

end Robbins.Cert.SO.L
