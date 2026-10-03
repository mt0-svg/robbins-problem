import Robbins.Cert.SO.LanesSound
import Robbins.Cert.SO.LanesWin

/-!
# Windows of lanes imply the scalar step

`checkStep_of_lanesParts` is the statement the chain uses for a fixed-window step cut into
windows: parts (ranges of top records or windows of lanes of one top) whose states cover the table
from the state `0` (`lpCover`), each passed by its check, give `checkStep`. Its
inputs are `lanesRange_StOK` (Robbins/Cert/SO/LanesSound.lean) and `lanesWin_StOK`, the states of a
window: the lanes `[a, a + w)` of the top `j` are the states `[cnt m j + a, cnt m j + a + w)`.
-/

namespace Robbins.Cert.SO.L

open Robbins.Cert Robbins.Cert.K Robbins.Cert.SO.K Robbins.Lanes

/-- The cell of a window by `mkCVw` against the scalar cell, as `mkCV_rep`: the lookups from the
first rank `s0` give the same lanes as the lookups from `0`. -/
theorem mkCVw_rep (c : Ctx) (hc : ctxOK c = true) (hx : CtxX c) (lk : ℕ → SV) (hi : ℕ)
    (hhi : hi ≤ c.recs.length) (a np : ℕ) (hnp : a + np ≤ cnt (Nat.sub c.m 1) hi) (pv : PV)
    (hpv : PVRep c a np pv) (NS : ℕ) (hNS : NS ≤ B32)
    (hlk : ∀ s < NS, (lk s).V < 2 ^ 48 ∧ ∀ f < c.m, lget (lk s).sl f < 2 ^ 48)
    (FV : ℕ) (hFV : FV = pack LW NS fun s => (lk s).V) (FS : List ℕ)
    (hFS : FS = (List.range c.m).map fun f => pack LW NS fun s => lget (lk s).sl f)
    (i : ℕ) (hi1 : 1 ≤ i) (hii : i ≤ hi)
    (hok : (mkCVw (mkVC np) pv NS c.a1 FV FS i (cellS c i)).ok = true) :
    CVRep c lk a np i (mkCVw (mkVC np) pv NS c.a1 FV FS i (cellS c i)) := by
  obtain ⟨hB, hI, hidx⟩ := mkCV_BI c hc hx hi hhi a np hnp pv hpv i hi1 hii
  have hB32 : B32 = 2 ^ 32 := by unfold B32; norm_num
  set cv := mkCVw (mkVC np) pv NS c.a1 FV FS i (cellS c i) with hcv
  have hIp : cv.idx = pack LW np fun l => idxS c (a + l) i := hI
  set s0 := pre LW 1 cv.idx with hs0def
  have hs0 : s0 < 2 ^ 143 := by
    rcases Nat.eq_zero_or_pos np with h0 | h0
    · have e : (pack LW np fun l => idxS c (a + l) i) = 0 := by rw [h0]; simp [pack]
      rw [hs0def, hIp, e]
      unfold pre
      simp
    · rw [hs0def, hIp, pre_pack LW np 1 _ (fun l hl => lt_trans (hidx l hl) (by norm_num [LW])) h0]
      have e : (pack LW 1 fun l => idxS c (a + l) i) = idxS c (a + 0) i := by simp [pack]
      rw [e]
      exact lt_trans (hidx 0 h0) (by norm_num)
  have e : cv.ok = bsel (allGe (mkVC np).G cv.idx (bc (mkVC np) s0))
      (mkRt (Nat.sub NS s0) (mkVC np).n (Nat.sub cv.idx (bc (mkVC np) s0))).ok false := rfl
  rw [e, bsel_false, Bool.and_eq_true, hIp] at hok
  obtain ⟨hge, hrt⟩ := hok
  obtain ⟨hidxNS, hroute⟩ := route_spec_off NS np s0 (fun l => idxS c (a + l) i)
    (lt_of_le_of_lt hNS (by rw [hB32]; norm_num)) hidx hs0 hge hrt
  have hgv : cv.gv = pack LW np fun l => (lk (idxS c (a + l) i)).V := by
    show route (mkRt (Nat.sub NS s0) (mkVC np).n (Nat.sub cv.idx (bc (mkVC np) s0)))
      (drp LW s0 FV) = _
    rw [hIp, hFV]
    exact hroute (fun s => (lk s).V) (fun s hs => lt_trans (hlk s hs).1 (by norm_num))
  have hgs : cv.gs = (List.range c.m).map fun f =>
      pack LW np fun l => lget (lk (idxS c (a + l) i)).sl f := by
    show lmap (route (mkRt (Nat.sub NS s0) (mkVC np).n (Nat.sub cv.idx (bc (mkVC np) s0))))
      (lmap (drp LW s0) FS) = _
    rw [hIp, hFS, lmap_eq, lmap_eq, List.map_map, List.map_map]
    apply List.map_congr_left
    intro f hf
    rw [List.mem_range] at hf
    exact hroute (fun s => lget (lk s).sl f)
      (fun s hs => lt_trans ((hlk s hs).2 f hf) (by norm_num))
  exact mkCV4_rep c hc hx lk hi hhi a np hnp pv hpv i hi1 hii cv.B cv.idx hB hI cv.ok cv.gv cv.gs
    hgv hgs fun l hl => hlk _ (hidxNS l hl)

/-- A window of lanes passed by `lanesWin` gives the states of its lanes. -/
theorem lanesWin_StOK (g : Grid) (t : ℕ) (Nn Nt : List ℕ) (j a w : ℕ)
    (h : lanesWin g t Nn Nt j a w = true) :
    2 ≤ g.m ∧ litsOK (Wm g.m) Nt = true ∧ (decS g.m Nt).length = (stsS g t Nn).length ∧
      ∀ k, cnt g.m j + a ≤ k → k < cnt g.m j + a + w → StOK g t Nn Nt k := by
  have hx : CtxX (mkCtx g t) := mkCtx_X g t
  unfold lanesWin lanesWin.lanesWin1 at h
  rw [bsel_false, bsel_false, bsel_false, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨hc, hNn, hNt, h⟩ := h
  have hok := cok_of_ctxOK _ hc
  have hm2 : 2 ≤ g.m := hok.m2
  have hW : 0 < Wm g.m := by show 0 < 48 * (g.m + 1); positivity
  change lanesWin.lanesWin2 (mkCtx g t) (litCat (Wm g.m) Nn) (litCat (Wm g.m) Nt) (Wm g.m) j a w
    (mkCtx g t).recs.length = true at h
  rw [litCat_spec _ hW Nn hNn, litCat_spec _ hW Nt hNt] at h
  have eNn : lfoldr (decLit (Wm g.m) (2 ^ Wm g.m - 1)) [] Nn = decS g.m Nn := rfl
  have eNt : lfoldr (decLit (Wm g.m) (2 ^ Wm g.m - 1)) [] Nt = decS g.m Nt := rfl
  rw [eNn, eNt] at h
  set c := mkCtx g t with hcdef
  set R := c.recs.length with hR
  set sn : ℕ → ℕ := fun k => (decS g.m Nn).getD k 0 with hsn
  set st : ℕ → ℕ := fun k => (decS g.m Nt).getD k 0 with hst
  have hsnb : ∀ k, sn k < 2 ^ Wm g.m := fun k => decAll_getD_lt _ hW Nn k
  have hstb : ∀ k, st k < 2 ^ Wm g.m := fun k => decAll_getD_lt _ hW Nt k
  unfold lanesWin.lanesWin2 at h
  dsimp only at h
  rw [bsel_false, bsel_false, bsel_false, bsel_false, bsel_false, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq,
    Nat.ble_eq, Nat.ble_eq, Nat.ble_eq] at h
  obtain ⟨⟨hTt, hTtB⟩, ⟨hjR, haw⟩, hNS, h⟩ := h
  have hlenS : (stsS g t Nn).length = cnt g.m R := stsS_length g t Nn hm2
  refine ⟨hm2, hNt, by rw [hlenS, hTt]; rfl, fun k hk1 hk2 => ?_⟩
  obtain ⟨m', hm'⟩ : ∃ m', c.m = m' + 1 := ⟨c.m - 1, by have := hok.m2; omega⟩
  have hsucc : cnt c.m (j + 1) = cnt c.m j + cnt (c.m - 1) (j + 1) := by
    rw [hm', cnt_succ]; rfl
  have hjR' : j + 1 ≤ R := hjR
  have haw' : a + w ≤ cnt (c.m - 1) (j + 1) := haw
  have hjRn : cnt c.m (j + 1) ≤ cnt c.m R := cnt_mono _ hjR'
  have hjRn1 : cnt (c.m - 1) (j + 1) ≤ cnt (c.m - 1) R := cnt_mono _ hjR'
  have hTt' : (decS g.m Nt).length = cnt c.m R := hTt
  -- the tables as packs
  have ePn : preS (Wm c.m) (cnt c.m (j + 1)) (pack (Wm c.m) (decS g.m Nn).length sn) =
      pack (Wm c.m) (cnt c.m (j + 1)) sn :=
    pre_pack _ _ _ sn (fun l _ => hsnb l) hNS
  have ePt : preS (Wm c.m) w
      (Nat.shiftRight (pack (Wm c.m) (decS g.m Nt).length st)
        (Nat.mul (Wm c.m) (Nat.add (cnt c.m j) a))) =
      pack (Wm c.m) w (fun l => st (l + (cnt c.m j + a))) := by
    show pre _ _ (drp (Wm c.m) (cnt c.m j + a) (pack _ _ st)) = _
    rw [drp_pack (Wm c.m) _ _ st (fun l _ => hstb l)]
    exact pre_pack (Wm c.m) _ _ _ (fun l _ => hstb _) (by rw [hTt']; omega)
  rw [show Wm g.m = Wm c.m from rfl, ePn, ePt] at h
  unfold lanesWin.lanesWin3 at h
  rw [bsel_false, bsel_false, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨hFn, hFt, h⟩ := h
  have hmc : c.m ≤ 32 := hok.m32
  have hNSB : cnt c.m (j + 1) ≤ B32 := le_trans hjRn (by rw [← hTt']; exact hTtB)
  set NS := cnt c.m (j + 1) with hNSdef
  have hwB : w ≤ B32 := by omega
  obtain ⟨eFn1, eFn2⟩ := fields_spec c.m NS hNSB hmc sn (fun s _ => hsnb s) hFn
  obtain ⟨eFt1, eFt2⟩ := fields_spec c.m w hwB hmc (fun l => st (l + (cnt c.m j + a)))
    (fun s _ => hstb _) hFt
  set Fn := fields c.m (pack (Wm c.m) NS sn) NS with hFndef
  set Ft := fields c.m (pack (Wm c.m) w fun l => st (l + (cnt c.m j + a))) w with hFtdef
  -- the prefix vectors of the window
  set N := cnt (Nat.sub c.m 1) R with hNdef
  have haN : a + w ≤ N := le_trans haw' hjRn1
  have hpvW := PVRep_win c hc 0 N a w haN (by rw [Nat.zero_add]; exact le_rfl) _
    (mkPV_rep c hc N le_rfl)
  rw [Nat.zero_add] at hpvW
  set pv := PV.mk (winL a w (mkPV c.recs (Nat.sub c.m 1)).pos)
    (winL a w (mkPV c.recs (Nat.sub c.m 1)).dl) (winL a w (mkPV c.recs (Nat.sub c.m 1)).fg)
    (winL a w (mkPV c.recs (Nat.sub c.m 1)).cs) with hpvdef
  have hpv : PVRep c a w pv := by
    have e : ∀ L, winL a w L = preL w (lmap (drp LW a) (preL N L)) := fun L =>
      (winL_preL L N a w haN).symm
    rw [hpvdef, e, e, e, e]
    exact hpvW
  unfold lanesWin.lanesWin4 lanesWin.lanesWin5 at h
  rw [bsel_false, Bool.and_eq_true, lall_iff] at h
  obtain ⟨hcvs, htop⟩ := h
  set cvs := lmapIdx (fun i cl => mkCVw (mkVC w) pv NS c.a1 Fn.1 Fn.2.1 (Nat.succ i) cl) 0
    (ltake (j + 1) c.cells) with hcvsdef
  set lk := lkS g Nn with hlkdef
  have hcellsH : j + 1 ≤ c.cells.length := by rw [hok.len]; exact hjR'
  have hcvslen : cvs.length = j + 1 := by
    rw [hcvsdef, lmapIdx_length, ltake_eq, List.length_take]
    omega
  -- the lookups
  have hFV : Fn.1 = pack LW NS fun s => (lk s).V := by
    rw [eFn1]
    refine pack_congr _ _ _ _ fun s hs => ?_
    rw [hlkdef, lkS_eq g Nn hNn s (by omega)]
  have hFS : Fn.2.1 = (List.range c.m).map fun f => pack LW NS fun s => lget (lk s).sl f := by
    rw [eFn2]
    refine List.map_congr_left fun f hf => pack_congr _ _ _ _ fun s hs => ?_
    rw [hlkdef, lkS_eq g Nn hNn s (by omega), lget_eq]
    have hf' : f < g.m := List.mem_range.1 hf
    rw [List.getD_eq_getElem _ _ (by simpa using hf')]
    simp only [List.getElem_map, List.getElem_range]
    rfl
  have hcv : ∀ i, 1 ≤ i → i ≤ j + 1 → CVRep c lk a w i (cget cvs (i - 1)) := by
    intro i hi1 hiH
    have hi' : i - 1 < cvs.length := by omega
    have e0 := lmapIdx_getElem (fun i cl => mkCVw (mkVC w) pv NS c.a1 Fn.1 Fn.2.1 (Nat.succ i) cl) 0
      (ltake (j + 1) c.cells) (i - 1) hi'
    rw [cget_of_lt _ _ hi', show cvs[i - 1] = _ from e0]
    have hcell : (ltake (j + 1) c.cells)[i - 1]'(by rw [ltake_eq, List.length_take]; omega) =
        cellS c i := by
      unfold cellS
      simp only [ltake_eq, List.getElem_take]
      rw [List.headD_eq_head?_getD, List.head?_drop, List.getElem?_eq_getElem (by omega)]
      rfl
    have e1 : Nat.succ (0 + (i - 1)) = i := by omega
    simp only [e1, hcell]
    refine mkCVw_rep c hc hx lk (j + 1) hjR' a w haw' pv hpv NS hNSB
      (fun s _ => ⟨(lkS_bound g Nn s).1, fun f _ => (lkS_bound g Nn s).2 f⟩) Fn.1 hFV Fn.2.1 hFS i
      hi1 hiH ?_
    have hmem := hcvs (cvs[i - 1]'hi') (List.getElem_mem hi')
    rw [show cvs[i - 1] = _ from e0] at hmem
    simpa only [e1, hcell] using hmem
  -- the state `k`: the lane `l` of the window, the prefix `a + l` of the top `j`
  have hk1' : cnt c.m j + a ≤ k := hk1
  have hk2' : k < cnt c.m j + a + w := hk2
  set l := k - (cnt c.m j + a) with hldef
  have hl : l < w := by omega
  have hal : a + l < cnt (g.m - 1) (j + 1) := by
    show a + l < cnt (c.m - 1) (j + 1)
    omega
  have hkl : k = cnt g.m j + (a + l) := by
    show k = cnt c.m j + (a + l)
    omega
  intro hk
  have hget := stsS_get g t Nn hm2 j (a + l) hjR' hal
  rw [← hkl, List.getElem?_eq_getElem hk, Option.some_inj] at hget
  rw [hget, checkState_eq c hok.newp]
  dsimp only
  have htop' : topCheck.topCheck1 c pv cvs (pack LW w fun s => st (s + (cnt c.m j + a)) % 2 ^ 48)
      ((List.range c.m).map fun f =>
        pack LW w fun s => st (s + (cnt c.m j + a)) / 2 ^ (48 * (f + 1)) % 2 ^ 48)
      (rget c.recs j) w 0 = true := by
    rw [← eFt1, ← eFt2]
    exact htop
  have := topCheck1_sound c hc hx lk (fun idx => lkS_bound g Nn idx)
    (fun idx => lkS_length g Nn idx) (j + 1) hjR' a w w le_rfl haN pv hpv cvs hcvslen hcv w hwB
    (fun s => st (s + (cnt c.m j + a)) % 2 ^ 48)
    (fun f s => st (s + (cnt c.m j + a)) / 2 ^ (48 * (f + 1)) % 2 ^ 48)
    (fun s _ => Nat.mod_lt _ (by norm_num)) (fun f s _ => Nat.mod_lt _ (by norm_num))
    0 j (by omega) (by omega) htop' l hl
  have e2 : 0 + l + (cnt c.m j + a) = k := by omega
  simp only [e2] at this
  exact this

/-- A part passed by its check gives the states of the part. -/
theorem LPart.StOK_of_check (g : Grid) (t : ℕ) (Nn Nt : List ℕ) (p : LPart)
    (h : p.check g t Nn Nt = true) :
    2 ≤ g.m ∧ litsOK (Wm g.m) Nt = true ∧ (decS g.m Nt).length = (stsS g t Nn).length ∧
      ∀ k, p.first g.m ≤ k → k < p.last g.m (mkCtx g t).recs.length → StOK g t Nn Nt k := by
  cases p with
  | rng lo hi => exact lanesRange_StOK g t Nn Nt lo hi h
  | win j a w => exact lanesWin_StOK g t Nn Nt j a w h

/-- The parts of a cover from `s` cover every state from `s` to `cnt m R`. -/
theorem lpCover_spec (m R : ℕ) : ∀ (ps : List LPart) (s : ℕ), lpCover m R s ps = true →
    ∀ k, s ≤ k → k < cnt m R → ∃ p ∈ ps, p.first m ≤ k ∧ k < p.last m R := by
  intro ps
  induction ps with
  | nil =>
    intro s h k hk hkR
    have : cnt m R ≤ s := Nat.ble_eq.mp h
    omega
  | cons p ps ih =>
    intro s h k hk hkR
    have h' : bsel (Nat.ble (p.first m) s) (lpCover m R (Nat.max s (p.last m R)) ps) false = true :=
      h
    rw [bsel_false, Bool.and_eq_true] at h'
    obtain ⟨h1, h2⟩ := h'
    have hf : p.first m ≤ s := Nat.ble_eq.mp h1
    by_cases hkl : k < p.last m R
    · exact ⟨p, List.mem_cons_self .., by omega, hkl⟩
    · obtain ⟨q, hq, hq'⟩ := ih _ h2 k (show max s _ ≤ k from max_le hk (by omega)) hkR
      exact ⟨q, List.mem_cons_of_mem _ hq, hq'⟩

/-- The lanes check of a fixed-window step in parts (ranges of top records and windows of lanes)
whose states cover the table gives the scalar check. -/
theorem checkStep_of_lanesParts (g : Grid) (t : ℕ) (Nn Nt : List ℕ) (ps : List LPart)
    (hcov : lpCover g.m (mkCtx g t).recs.length 0 ps = true)
    (h : ∀ i, i < ps.length → (ps.getD i (LPart.rng 0 0)).check g t Nn Nt = true) :
    checkStep g t Nn Nt = true := by
  set R := (mkCtx g t).recs.length with hRdef
  have hR1 : 1 ≤ R := mkCtx_recs_pos g t
  have hmem : ∀ p ∈ ps, p.check g t Nn Nt = true := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    have := h i hi
    rwa [List.getD_eq_getElem _ _ hi] at this
  have hcnt : 1 ≤ cnt g.m R := by
    rw [cnt_eq]
    exact Nat.choose_pos (by omega)
  obtain ⟨p0, hp0, -⟩ := lpCover_spec g.m R ps 0 hcov 0 le_rfl (by omega)
  obtain ⟨hm, hlits, hlen, -⟩ := LPart.StOK_of_check g t Nn Nt p0 (hmem p0 hp0)
  refine checkStep_of_StOK g t Nn Nt hlits hlen fun k => ?_
  by_cases hk : k < cnt g.m R
  · obtain ⟨p, hp, hk1, hk2⟩ := lpCover_spec g.m R ps 0 hcov k (Nat.zero_le _) hk
    exact (LPart.StOK_of_check g t Nn Nt p (hmem p hp)).2.2.2 k hk1 hk2
  · intro hk'
    rw [stsS_length g t Nn hm] at hk'
    exact absurd hk' hk

end Robbins.Cert.SO.L
