import Robbins.Cert.SO.EvalKSound
import Robbins.Cert.SO.EvalKDefs
import Robbins.Cert.SO.SoundRec

/-!
# The data of a kernel step against the specification

The step evaluator `checkStep g t Nn Nt` of Robbins/Cert/SO/EvalK.lean builds its data once per
step (`mkCtx`): the cells of `P_t`, the records of the local points of `G_t` and of the new points,
and a lookup `lkOf g Nn` into the table of time `t + 1`. Here:

* `toSR g t c`, `toSC g t i`: the kernel record of a record `c` of the specification and the kernel
  cell `i`, from the quantities of Robbins/Cert/SO/Spec.lean;
* `mkCtx_cells`, `mkCtx_recs`, `mkCtx_newp`: the lists of `mkCtx` are those of the specification
  (`mkRec_eq`: a record built by `mkCtx` is `toSR` of its global index);
* `slopes_getD`: the slopes of a packed state are `sgOf`.
-/

namespace Robbins.Cert.SO.K

open Robbins.Cert Robbins.Cert.K

variable (g : Grid)

/-- The kernel record of a record `c` of the specification at time `t`. -/
noncomputable def toSR (t : ℕ) (c : Rec) : SR where
  pos := c.pos
  val := c.val
  cm := c.map
  dl := c.w
  fg := c.forg
  ev := if c.forg then 0 else SO.pt DS g (g.glob (t + 1) c.map) - c.val
  em := SO.Epen DS c.val (g.n - t)
  pm := (g.n - t) * SO.Epen DS c.val (g.n - t - 1)
  etm := SO.Epen DS c.val (g.n - t + 1)
  bs := binoms g.m c.map
  bsl := (binoms g.m c.map).getLastD 0

/-- The kernel cell `i` of `P_t`. -/
noncomputable def toSC (t i : ℕ) : K.SC where
  pa := SO.cp DS g t (i - 1)
  pb := SO.cp DS g t i
  pn := SO.pt DS g (g.glob (t + 1) (g.nxt t i))
  cb := binoms g.m (g.nxt t i)
  et := SO.Epen DS (SO.cp DS g t i) (g.n - t)
  e1 := SO.Epen DS (SO.cp DS g t i) (g.n - t - 1)
  etm := SO.Epen DS (SO.cp DS g t i) (g.n - t + 1)
  h := SO.cp DS g t i - SO.cp DS g t (i - 1)
  h2 := 2 * (SO.cp DS g t i - SO.cp DS g t (i - 1))
  sqd := SO.cp DS g t i * SO.cp DS g t i - SO.cp DS g t (i - 1) * SO.cp DS g t (i - 1)
  a1sq := (g.n - t) * DS *
    (SO.cp DS g t i * SO.cp DS g t i - SO.cp DS g t (i - 1) * SO.cp DS g t (i - 1))

/-- The lookup of the step evaluator into the table `Nn` of time `t + 1`. -/
noncomputable def lkOf (Nn : List ℕ) : ℕ → SV :=
  lkF (lk0 (bld (depth Nn.length) Nn) (depth Nn.length) g.m (Nat.mul 48 (Nat.succ g.m))
    (Nat.sub (Nat.shiftLeft 1 (Nat.mul 48 (Nat.succ g.m))) 1))

/-! ## The step data -/

theorem mkCtx_m (t : ℕ) : (mkCtx g t).m = g.m := rfl

theorem mkCtx_r (t : ℕ) : (mkCtx g t).r = g.n - t := rfl

theorem mkCtx_a1 (t : ℕ) : (mkCtx g t).a1 = (g.n - t) * DS := rfl

theorem mkCtx_FT (t : ℕ) : (mkCtx g t).FT = F128 ^ (g.m - 1) := rfl

/-- `checkStep` with the lookup `lkOf`. -/
theorem checkStep_eq (t : ℕ) (Nn Nt : List ℕ) :
    checkStep g t Nn Nt =
      chunkCheck (checkState (mkCtx g t) (lkOf g Nn)) (Nat.mul 48 (Nat.succ g.m))
        (Nat.sub (Nat.shiftLeft 1 (Nat.mul 48 (Nat.succ g.m))) 1) Nt
        (states (mkCtx g t).recs (lmap (lmap fun tp => mkPre (mkCtx g t) (lkOf g Nn) (lrevOnto tp []))
          (tupG (Nat.sub g.m 2) (mkCtx g t).recs))) := rfl

theorem winAt_eq (t : ℕ) : winAt g t = g.wt t := rfl

theorem Eback_succ (gptD : List ℕ) (q : ℕ) : Eback gptD (q + 1) = nextE gptD (Eback gptD q) := rfl

/-- The values with the point `1` read as `pt`. -/
theorem gptD_getD {j : ℕ} (hj : j ≤ g.J) : (g.gpt ++ [DS]).getD j 0 = SO.pt DS g j := by
  unfold SO.pt
  split_ifs with h
  · rw [List.getD_append _ _ _ _ h]
  · have hj' : j = g.gpt.length := by simp only [Grid.J] at h hj; omega
    subst hj'
    simp

/-- The endpoints of the cells built by `mkCtx` are `cellPts`. -/
theorem kpts_eq (t : ℕ) :
    (List.filter (fun j => decide ((winAt g t).s ≤ j) && decide (j < (winAt g t).s + (winAt g t).cnt) ||
        decide ((winAt g (t + 1)).s ≤ j) && decide (j < (winAt g (t + 1)).s + (winAt g (t + 1)).cnt))
      (List.range g.gpt.length) ++ [g.gpt.length]) = g.cellPts t := by
  unfold Grid.cellPts
  rw [show g.J + 1 = g.gpt.length + 1 from rfl, List.range_succ, List.filter_append]
  congr 1
  · apply List.filter_congr
    intro j hj
    rw [List.mem_range] at hj
    have hne : (j == g.J) = false := by simp [Grid.J]; omega
    simp only [hne, Bool.false_or, Grid.inWin, winAt_eq]
    rfl
  · simp [Grid.J]

/-- A record built by `mkCtx` is the kernel record of its global index. -/
theorem mkRec_eq {t gi : ℕ} (hgi : gi ≤ g.J) (dl : ℕ) (fg : Bool) :
    mkRec g.m g.gpt.length (g.n - t) (winAt g (t + 1)) (g.gpt ++ [DS]) (Eback (g.gpt ++ [DS]) (g.n - t))
        (Eback (g.gpt ++ [DS]) (g.n - t - 1)) (Eback (g.gpt ++ [DS]) (g.n - t + 1)) (g.cellPts t) gi dl fg =
      toSR g t ⟨(g.cellPts t).idxOf gi + 1, SO.pt DS g gi, gi, g.ceilG (t + 1) gi, dl, fg⟩ := by
  have hlen : gi < (g.gpt ++ [DS]).length := by simp [Grid.J] at hgi ⊢; omega
  have hglob : glob g.gpt.length (winAt g (t + 1)) (ceilLocal g.gpt.length (winAt g (t + 1)) gi) =
      g.glob (t + 1) (g.ceilG (t + 1) gi) := rfl
  unfold mkRec toSR
  simp only [hglob, gptD_getD g (g.glob_le_J _ _), Eback_getD _ _ _ hlen, gptD_getD g hgi]
  rfl

/-- `ceil_{t+1}` of a new point. -/
theorem ceilG_newPt {t j : ℕ} (hj : j ∈ newPts g t) : g.ceilG (t + 1) j = j - (g.wt (t + 1)).s := by
  have hm := (List.mem_filter.mp hj)
  rw [List.mem_range] at hm
  obtain ⟨hJ, hw⟩ := hm
  simp only [Bool.and_eq_true, Grid.inWin, decide_eq_true_eq] at hw
  unfold Grid.ceilG ceilLocal
  have h1 : (j == g.J) = false := by simp; omega
  have h2 : ((g.wt (t + 1)).cnt == 0) = false := by simp; omega
  simp only [h1, h2, Bool.false_or, Bool.false_eq_true, ite_false]
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]

/-- The cells of the step: `toSC g t i` for `i = 1, ..., L`. -/
theorem mkCtx_cells (_hg : ok DS g = true) {t : ℕ} (_ht1 : 1 ≤ t) (htn : t < g.n) :
    (mkCtx g t).cells = (List.range (g.L t)).map fun i => toSC g t (i + 1) := by
  simp only [mkCtx]
  rw [kpts_eq]
  have hr : g.n - t - 1 + 1 = g.n - t := by omega
  rw [← Eback_succ, hr, ← Eback_succ]
  have hmemJ : ∀ j ∈ g.cellPts t, j ≤ g.J := fun j hj => ((g.mem_cellPts).mp hj).1
  rw [List.map_congr_left (fun j hj => gptD_getD g (hmemJ j hj))]
  apply List.ext_getElem
  · simp [Grid.L]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_zip, List.getElem_range]
    have hiL : i < g.L t := by simpa using h2
    have hiL' : i < (g.cellPts t).length := hiL
    have hget : (g.cellPts t)[i] = (g.cellPts t).getD i 0 := (List.getD_eq_getElem _ _ hiL').symm
    have hj : (g.cellPts t)[i] ≤ g.J := hmemJ _ (List.getElem_mem _)
    have hpb : SO.pt DS g (g.cellPts t)[i] = SO.cp DS g t (i + 1) := by
      rw [g.so_cp_of_pos DS (by omega), Nat.add_sub_cancel, hget]
    have hpa : (0 :: List.map (fun j => SO.pt DS g j) (g.cellPts t))[i]'(by simp; omega) = SO.cp DS g t i := by
      cases i with
      | zero => simp [SO.cp]
      | succ k =>
        rw [List.getElem_cons_succ, List.getElem_map, g.so_cp_of_pos DS (by omega), Nat.add_sub_cancel,
          List.getD_eq_getElem _ _ (by omega)]
    have hglob : glob g.gpt.length (winAt g (t + 1)) (ceilLocal g.gpt.length (winAt g (t + 1)) (g.cellPts t)[i]) =
        g.glob (t + 1) (g.nxt t (i + 1)) := by
      simp only [Grid.nxt, Grid.ceilG, Nat.add_sub_cancel, hget]; rfl
    have hceil : ceilLocal g.gpt.length (winAt g (t + 1)) (g.cellPts t)[i] = g.nxt t (i + 1) := by
      simp only [Grid.nxt, Grid.ceilG, Nat.add_sub_cancel, hget]; rfl
    have hlen : (g.cellPts t)[i] < (g.gpt ++ [DS]).length := by simp [Grid.J] at hj ⊢; omega
    rw [hpa, hpb, hglob, hceil, gptD_getD g (g.glob_le_J _ _), Eback_getD _ _ _ hlen, Eback_getD _ _ _ hlen,
      Eback_getD _ _ _ hlen, gptD_getD g hj, hpb]
    simp only [toSC, Nat.add_sub_cancel]

/-- The records of the local points `0, ..., cnt_t` of `G_t`. -/
theorem mkCtx_recs (_hg : ok DS g = true) {t : ℕ} (_ht1 : 1 ≤ t) (htn : t < g.n) :
    (mkCtx g t).recs = (List.range (g.cnt t + 1)).map fun k => toSR g t (locRec DS g t k) := by
  simp only [mkCtx]
  rw [kpts_eq]
  have hr : g.n - t - 1 + 1 = g.n - t := by omega
  rw [← Eback_succ, hr, ← Eback_succ]
  rw [List.range_succ, List.map_append, List.map_singleton]
  congr 1
  · apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    have hk' : k < g.cnt t := hk
    have hglob : g.glob t k = (winAt g t).s + k := by simp [Grid.glob, hk', winAt_eq]
    rw [← hglob, mkRec_eq g (g.glob_le_J _ _)]
    congr 2
    · unfold width
      rw [ite_eq_left hk', gptD_getD g (g.glob_le_J _ _)]
      congr 1
      split_ifs with h0
      · rfl
      · have hg1 : g.glob t k - 1 = g.glob t (k - 1) := by
          simp [Grid.glob, hk', show k - 1 < g.cnt t by omega]; omega
        rw [hg1, gptD_getD g (g.glob_le_J _ _)]
    · exact (decide_eq_false (by omega)).symm
  · have hglob : g.glob t (g.cnt t) = g.gpt.length := g.glob_of_ge le_rfl
    rw [mkRec_eq g (t := t) (gi := g.gpt.length) le_rfl 0 true]
    simp only [locRec, Grid.pos, Grid.mapL, hglob, width, lt_irrefl, ite_false, decide_true]

/-- The records of the new points. -/
theorem mkCtx_newp (_hg : ok DS g = true) {t : ℕ} (_ht1 : 1 ≤ t) (htn : t < g.n) :
    (mkCtx g t).newp = (newPts g t).map fun j => toSR g t (newRec DS g t j) := by
  simp only [mkCtx]
  rw [kpts_eq]
  have hr : g.n - t - 1 + 1 = g.n - t := by omega
  rw [← Eback_succ, hr, ← Eback_succ]
  have hl : List.filter (fun j => decide ((winAt g t).s + (winAt g t).cnt ≤ j))
      (List.map (fun x => (winAt g (t + 1)).s + x) (List.range (winAt g (t + 1)).cnt)) = newPts g t := by
    apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
    · rw [← List.range'_eq_map_range]
      exact (List.pairwise_lt_range').filter _
    · exact List.pairwise_lt_range.filter _
    · intro j
      have hs := g.s_add_cnt_le (t + 1)
      simp only [List.mem_filter, List.mem_map, List.mem_range, newPts, Grid.inWin, winAt_eq,
        Bool.and_eq_true, decide_eq_true_eq, Grid.cnt] at hs ⊢
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, h2⟩
        exact ⟨by omega, ⟨by omega, by omega⟩, of_decide_eq_true h2⟩
      · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
        exact ⟨⟨j - (g.wt (t + 1)).s, by omega, by omega⟩, decide_eq_true h4⟩
  rw [hl]
  apply List.map_congr_left
  intro j hj
  have hJ : j ≤ g.J := by
    have := (List.mem_filter.mp hj).1
    rw [List.mem_range] at this; omega
  rw [mkRec_eq g hJ, ceilG_newPt g hj]
  rfl

/-- The slopes of a state are `sgOf`. -/
theorem slopes_getD {d : ℕ} (hd : g.m = d + 1) (T : List ℕ) (H : Fin (d + 1) → ℕ) (l : Fin (d + 1)) :
    (slopes g.m (stOf d T H)).getD l 0 = sgOf d T H l := by
  rw [slopes_eq, List.getD_eq_getElem _ _ (by simp [hd]; omega)]
  simp [sgOf]

end Robbins.Cert.SO.K
