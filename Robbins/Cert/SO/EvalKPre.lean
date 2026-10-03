import Robbins.Cert.SO.EvalKCtx
import Robbins.Cert.SO.SoundCell

/-!
# The prefix data of the kernel evaluator against the specification

`mkPre c lk rs` computes, for the first `m - 1` records `rs` of a record list, the data `PD` of every
cell `i = 1, ..., L` that does not involve the last record (section 5.3): the lookup of `H_i`,
`sigma`, `beta - D Em`, `S` and the packed coefficients less the last one, the own-cell fields.
For the kernel records of a record list `c` of the specification (`RecOK`), and a lookup that reads
the table of time `t + 1` at the rank of every state of `G_{t+1}`, this is `pdSpec g d t Nn c i`
(`pdLoop_spec`), whose fields are the quantities of Robbins/Cert/SO/Spec.lean.
-/

namespace Robbins.Cert.SO.K

open Robbins.Cert Robbins.Cert.K

/-! ## The prefix data of the specification -/

variable (g : Grid) (d t : ℕ) (Nn : List ℕ) (c : Fin (d + 1) → Rec)

/-- The kernel prefix records of `c`. -/
noncomputable def rsOf : List SR := List.ofFn fun l : Fin d => toSR g t (c l.castSucc)

/-- `coef_l` of the cell `i`, as a natural number. -/
noncomputable def coefN (i : ℕ) (l : Fin (d + 1)) : ℕ := (coefC DS g d (sgOf d Nn) t c i l).toNat

/-- The fields `F ^ l` of the prefix records of the own cell `i`, not forgotten, increasing. -/
noncomputable def ownF (i : ℕ) : List ℕ :=
  ((List.finRange d).filter fun l => !(c l.castSucc).forg && (c l.castSucc).pos == i).map
    fun l => F128 ^ (l : ℕ)

/-- The prefix data of the cell `i`, from the specification. -/
noncomputable def pdSpec (i : ℕ) : PD :=
  let H := Hc g d t c i
  let sig := sgOf d Nn H (belowF d c i)
  let a0 := (below d c i + 1) * DS2
  let pa := SO.cp DS g t (i - 1)
  let pb := SO.cp DS g t i
  let kk := (g.n - t) * DS + sig
  { pa := pa, pb := pb, h := pb - pa, h2 := 2 * (pb - pa), a0 := a0, sig := sig,
    bet := DS * uhOf d Nn H + sig * SO.pt DS g (g.glob (t + 1) (g.nxt t i)) +
      ∑ l : Fin d, sgOf d Nn H (slot d c i l) * (toSR g t (c l.castSucc)).ev,
    sp := ∑ l : Fin d, coefN g d t Nn c i l.castSucc * (c l.castSucc).w,
    cp := ∑ l : Fin d, coefN g d t Nn c i l.castSucc * F128 ^ (l : ℕ),
    A0 := a0 + kk * pa, A1 := a0 + kk * pb,
    IA := 2 * (pb - pa) * a0 + (g.n - t) * DS * (pb * pb - pa * pa),
    ssq := sig * (pb * pb - pa * pa),
    own := ownF d c i, hasOwn := !(ownF d c i).isEmpty,
    from' := (mkCtx g t).cells.drop (i - 1) }

/-! ## States of `G_{t+1}` -/

variable {g d t Nn c}

/-- `ceil_t` is monotone on the global indices `≤ J`. -/
theorem ceilG_mono' (t : ℕ) {j j' : ℕ} (h : j ≤ j') (hj' : j' ≤ g.J) :
    g.ceilG t j ≤ g.ceilG t j' := by
  have hs := g.s_add_cnt_le t
  simp only [Grid.cnt, Grid.J] at hs hj'
  simp only [Grid.ceilG, ceilLocal, Grid.J, Bool.or_eq_true, beq_iff_eq]
  split_ifs <;> omega

/-- `nxt` is monotone on the cells. -/
theorem nxt_mono' (t : ℕ) {i i' : ℕ} (hi : 1 ≤ i) (h : i ≤ i') (hi' : i' ≤ g.L t) :
    g.nxt t i ≤ g.nxt t i' := by
  unfold Grid.nxt
  apply ceilG_mono'
  · rcases Nat.lt_or_eq_of_le h with h | h
    · exact (g.cellPts_getD_lt (by omega) (by omega)).le
    · rw [h]
  · exact ((g.mem_cellPts).mp (g.cellPts_getD_mem (by omega))).1

/-- `H_i` is a state of `G_{t+1}`. -/
theorem Hc_isState (hc : RecOK DS g t c) {i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ g.L t) :
    g.IsState (t + 1) (Hc g d t c i) := by
  have hmono := hc.pos_mono
  set b := below d c i with hb
  let P : Fin (d + 1) → ℕ := fun l =>
    if (l : ℕ) < b then (c l).pos else if (l : ℕ) = b then i else (c ⟨l - 1, by omega⟩).pos
  have hHP : ∀ l, Hc g d t c i l = g.nxt t (P l) := by
    intro l
    simp only [Hc, P, ← hb]
    split_ifs with h1 h2
    · exact hc.map_eq l
    · rfl
    · exact hc.map_eq _
  have hlt : ∀ l : Fin (d + 1), (l : ℕ) < b → (c l).pos < i := by
    intro l hl
    have hl' : (l : ℕ) < d := lt_of_lt_of_le hl (below_le d c i)
    have := (lt_below_iff hmono i ⟨l, hl'⟩).mp hl
    simpa using this
  have hge : ∀ l : Fin (d + 1), b ≤ (l : ℕ) → (l : ℕ) < d → i ≤ (c l).pos := by
    intro l hl hld
    have := (lt_below_iff hmono i ⟨l, hld⟩).not.mp (by simp only; omega)
    simp at this; simpa using this
  have hP1 : ∀ l, 1 ≤ P l := by
    intro l; simp only [P]; split_ifs
    · exact hc.pos_pos l
    · exact hi1
    · exact hc.pos_pos _
  have hPL : ∀ l, P l ≤ g.L t := by
    intro l; simp only [P]; split_ifs
    · exact hc.pos_le l
    · exact hiL
    · exact hc.pos_le _
  have hPm : Monotone P := by
    intro l1 l2 h12
    have h12' : (l1 : ℕ) ≤ l2 := h12
    have hfin : ∀ a b : Fin (d + 1), (a : ℕ) ≤ b → (c a).pos ≤ (c b).pos :=
      fun a b hab => hmono hab
    simp only [P]
    split_ifs with a1 a2 a3 a4 a5 a6 a7 a8
    all_goals first
      | omega
      | exact hmono h12
      | exact (hlt l1 a1).le
      | exact hfin _ _ (by simp only; omega)
      | exact le_refl _
      | exact hge ⟨_, by omega⟩ (by simp only; omega) (by simp only; omega)
  refine ⟨fun l1 l2 h => ?_, fun l => ?_⟩
  · rw [hHP, hHP]; exact nxt_mono' t (hP1 _) (hPm h) (hPL _)
  · rw [hHP]; exact g.ceilG_le_cnt _ _

/-- The tuple of the maps is a state of `G_{t+1}`. -/
theorem map_isState (hc : RecOK DS g t c) : g.IsState (t + 1) fun l => (c l).map := by
  refine ⟨fun l1 l2 h => ?_, fun l => ?_⟩
  · simp only [hc.map_eq]
    exact nxt_mono' t (hc.pos_pos _) (hc.pos_mono h) (hc.pos_le _)
  · simp only [hc.map_eq]; exact g.ceilG_le_cnt _ _

/-- `ev` of the specification is the natural `ev` of the kernel record. -/
theorem ev_toSR (hg : ok DS g = true) (hc : RecOK DS g t c) (l : Fin (d + 1)) :
    ev DS g d t c l = ((toSR g t (c l)).ev : ℤ) := by
  simp only [ev, toSR]
  split_ifs with hf
  · simp
  · have hp := hc.pos_pos l
    have hpl := hc.pos_le l
    have hj : (g.cellPts t).getD ((c l).pos - 1) 0 ≤ g.J :=
      ((g.mem_cellPts).mp (g.cellPts_getD_mem (by omega))).1
    have hle := (g.so_ceilG_spec DS hg (t + 1) hj).1
    have hv : (c l).val ≤ SO.pt DS g (g.glob (t + 1) (c l).map) := by
      rw [hc.val_eq l, hc.map_eq l, g.so_cp_of_pos DS hp]; exact hle
    rw [Nat.cast_sub hv]

/-! ## The prefix data of the kernel -/

/-- The slot index of the record `l` in the cell `i`, against `below_i`. -/
theorem slot_val (hc : RecOK DS g t c) (i : ℕ) (l : Fin d) :
    ((slot d c i l : Fin (d + 1)) : ℕ) = if (l : ℕ) < below d c i then (l : ℕ) else (l : ℕ) + 1 := by
  have h := lt_below_iff hc.pos_mono i l
  unfold slot
  by_cases hi : i ≤ (c l.castSucc).pos
  · rw [ite_eq_left hi, ite_eq_right (by rw [h]; omega)]; simp
  · rw [ite_eq_right hi, ite_eq_left (by rw [h]; omega)]; simp

/-- The rank sum of the prefix and the term of `nxt_i` make the rank of `H_i`. -/
theorem rank_pre (hd : g.m = d + 1) (i : ℕ) :
    (rankCs (rsOf g d t c)).getD (below d c i) 0 + lget (toSC g t i).cb (below d c i) =
      rank (Hc g d t c i) := by
  have hb := below_le d c i
  rw [rank_Hc, rsOf, rankCs_eq, List.getD_eq_getElem _ _ (by simp; omega), lget_eq]
  simp only [List.getElem_map, List.getElem_range, toSC, toSR, binoms_eq, hd]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega)]; simp
  · rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega)]
    simp only [List.getElem_map, List.getElem_range]; congr 1


/-- The slope of the slot of the record `l` is the one the pass reads. -/
theorem slopes_slot (hd : g.m = d + 1) (hc : RecOK DS g t c) (i : ℕ) (H : Fin (d + 1) → ℕ)
    (l : Fin d) :
    (slopes g.m (stOf d Nn H)).getD (if (l : ℕ) < below d c i then (l : ℕ) else (l : ℕ) + 1) 0 =
      sgOf d Nn H (slot d c i l) := by
  rw [← slot_val hc i l, slopes_getD g hd]

/-- `coef_l` of a prefix record: `0` if forgotten or of the own cell, else the slope of its slot. -/
theorem coefN_eq (i : ℕ) (l : Fin d) :
    coefN g d t Nn c i l.castSucc = if (c l.castSucc).forg || (c l.castSucc).pos == i then 0
      else sgOf d Nn (Hc g d t c i) (slot d c i l) := by
  unfold coefN coefC
  rw [dite_eq_right (by simp only [Fin.val_castSucc]; omega)]
  simp only [slot]
  by_cases hf : (c l.castSucc).forg = true
  · simp [hf]
  · simp only [hf, Bool.false_or, ite_false, Bool.false_eq_true]
    rcases lt_trichotomy i (c l.castSucc).pos with h | h | h
    · rw [ite_eq_left h, ite_eq_right (by simp; omega), ite_eq_left h.le]
      simp only [Int.toNat_natCast]; rfl
    · rw [ite_eq_right (by omega), ite_eq_left h.symm, ite_eq_left (by simp; omega)]; simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by simp; omega),
        ite_eq_right (by omega)]
      simp only [Int.toNat_natCast]; rfl

/-- The cell `i` of `pdLoop` is `pdSpec i`. -/
theorem pdCell_spec (hd : g.m = d + 1) {lk : ℕ → SV}
    (hlk : ∀ H : Fin (d + 1) → ℕ, g.IsState (t + 1) H →
      lk (rank H) = ⟨stOf d Nn H % 2 ^ 48, slopes g.m (stOf d Nn H)⟩)
    (hc : RecOK DS g t c) {i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ g.L t) :
    pdCell ((g.n - t) * DS) lk (rsOf g d t c) (toSC g t i) ((mkCtx g t).cells.drop (i - 1)) i
      (below d c i) ((rankCs (rsOf g d t c)).getD (below d c i) 0) = pdSpec g d t Nn c i := by
  have hb := below_le d c i
  have hsv := hlk _ (Hc_isState hc hi1 hiL)
  have hsig : lget (slopes g.m (stOf d Nn (Hc g d t c i))) (below d c i) =
      sgOf d Nn (Hc g d t c i) (belowF d c i) := by
    rw [lget_eq, ← slopes_getD g hd]; rfl
  unfold pdCell pdCell.pdCell1 pdCell.pdCell2
  have hr : Nat.add ((rankCs (rsOf g d t c)).getD (below d c i) 0) (lget (toSC g t i).cb (below d c i)) =
      rank (Hc g d t c i) := rank_pre hd i
  rw [hr, hsv]
  simp only [hsig]
  rw [rsOf, pass_eq]
  unfold mkPD mkPD.mkPD1 pdSpec
  dsimp only
  congr 1
  · change DS * uhOf d Nn (Hc g d t c i) + sgOf d Nn (Hc g d t c i) (belowF d c i) *
        SO.pt DS g (g.glob (t + 1) (g.nxt t i)) + ∑ l : Fin d,
        (slopes g.m (stOf d Nn (Hc g d t c i))).getD (if (l : ℕ) < below d c i then (l : ℕ) else (l : ℕ) + 1) 0 *
          (toSR g t (c l.castSucc)).ev = _
    congr 1
    exact Finset.sum_congr rfl fun l _ => by rw [slopes_slot hd hc]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [coefN_eq, slopes_slot hd hc, ite_mul, zero_mul]
    rfl
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [coefN_eq, slopes_slot hd hc, ite_mul, zero_mul]
    rfl
  · change @List.rec ℕ (fun _ => Bool) false (fun _ _ _ => true) (ownF d c i) = _
    cases ownF d c i <;> rfl

/-- `takeWhile` and `dropWhile` of a list whose first `n` entries are those `< i`. -/
theorem takeWhile_lt_of_iff (P : List ℕ) (i n : ℕ) (hn : n ≤ P.length)
    (h : ∀ j (hj : j < P.length), P[j] < i ↔ j < n) :
    P.takeWhile (fun p => decide (p < i)) = P.take n ∧
      P.dropWhile (fun p => decide (p < i)) = P.drop n := by
  induction P generalizing n with
  | nil => simp at hn; subst hn; simp
  | cons p P ih =>
    rcases n with _ | n
    · have := (h 0 (by simp)).not.mpr (by omega)
      simp only [List.getElem_cons_zero] at this
      simp [this]
    · have hp := (h 0 (by simp)).mpr (by omega)
      simp only [List.getElem_cons_zero] at hp
      have ih' := ih n (by simp at hn; omega) fun j hj => by
        have := h (j + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [this]; omega
      simp [hp, ih'.1, ih'.2]

/-- `below` is monotone in the cell. -/
theorem below_mono_succ (k : ℕ) : below d c k ≤ below d c (k + 1) := by
  unfold below
  apply Finset.card_le_card
  intro l; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega

/-- The head of `l.drop b` is `l[b]`. -/
theorem headD_drop (l : List ℕ) (b : ℕ) : (l.drop b).headD 0 = l.getD b 0 := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih => cases b <;> simp

/-- One step of `pdLoop` on a cons. -/
theorem pdLoop_cons (a1 : ℕ) (lk : ℕ → SV) (rs : List SR) (cl : SC) (rest : List SC)
    (i b : ℕ) (cuts Cs : List ℕ) :
    pdLoop a1 lk rs (cl :: rest) i b cuts Cs = adv i cuts Cs b fun b cuts Cs =>
      pdCell a1 lk rs cl (cl :: rest) i b (hd Cs) :: pdLoop a1 lk rs rest (i + 1) b cuts Cs := rfl

/-- The prefix data of all cells. -/
theorem pdLoop_spec (hg : ok DS g = true) (hd : g.m = d + 1) (ht1 : 1 ≤ t) (htn : t < g.n)
    {lk : ℕ → SV}
    (hlk : ∀ H : Fin (d + 1) → ℕ, g.IsState (t + 1) H →
      lk (rank H) = ⟨stOf d Nn H % 2 ^ 48, slopes g.m (stOf d Nn H)⟩)
    (hc : RecOK DS g t c) :
    pdLoop ((g.n - t) * DS) lk (rsOf g d t c) (mkCtx g t).cells 1 0
        (lmap SR.pos (rsOf g d t c)) (rankCs (rsOf g d t c)) =
      (List.range (g.L t)).map fun j => pdSpec g d t Nn c (j + 1) := by
  set P : List ℕ := List.ofFn fun l : Fin d => (c l.castSucc).pos with hP
  have hPl : lmap SR.pos (rsOf g d t c) = P := by
    rw [lmap_eq, rsOf, List.map_ofFn]; rfl
  have hcells := mkCtx_cells g hg ht1 htn
  set Cs := rankCs (rsOf g d t c)
  have key : ∀ n k, n + k = g.L t →
      pdLoop ((g.n - t) * DS) lk (rsOf g d t c) ((mkCtx g t).cells.drop k) (k + 1) (below d c k)
          (P.drop (below d c k)) (Cs.drop (below d c k)) =
        (List.range n).map fun j => pdSpec g d t Nn c (k + j + 1) := by
    intro n
    induction n with
    | zero =>
      intro k hk
      rw [List.drop_eq_nil_of_le (by rw [hcells]; simp; omega)]
      rfl
    | succ n ih =>
      intro k hk
      have hlen : k < (mkCtx g t).cells.length := by rw [hcells]; simp; omega
      rw [List.drop_eq_getElem_cons hlen, pdLoop_cons, adv_eq]
      have hb0 := below_mono_succ (c := c) k
      have hb1 := below_le d c (k + 1)
      have htw := takeWhile_lt_of_iff (P.drop (below d c k)) (k + 1) (below d c (k + 1) - below d c k)
        (by simp [hP]; omega) fun j hj => by
          simp only [List.length_drop, hP, List.length_ofFn] at hj
          simp only [hP, List.getElem_drop, List.getElem_ofFn]
          have := (lt_below_iff hc.pos_mono (k + 1) ⟨below d c k + j, by omega⟩).symm
          simp only at this
          rw [this]; omega
      have hlt : ((P.drop (below d c k)).take (below d c (k + 1) - below d c k)).length =
          below d c (k + 1) - below d c k := by simp [hP]; omega
      rw [htw.1, htw.2, hlt, List.drop_drop, List.drop_drop,
        show below d c k + (below d c (k + 1) - below d c k) = below d c (k + 1) by omega,
        ← List.drop_eq_getElem_cons hlen]
      have hck : (mkCtx g t).cells[k] = toSC g t (k + 1) := by simp [hcells]
      rw [hck, hd_eq, headD_drop]
      have hcell := pdCell_spec hd hlk hc (i := k + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hcell
      rw [hcell, ih (k + 1) (by omega), List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      refine List.map_congr_left fun j _ => ?_
      simp only [Function.comp_apply]; congr 1; omega
  have := key (g.L t) 0 (by simp)
  simp only [List.drop_zero, zero_add] at this
  have hb0 : below d c 0 = 0 := by unfold below; simp
  rw [hb0, List.drop_zero, List.drop_zero] at this
  rw [hPl, this]

end Robbins.Cert.SO.K
