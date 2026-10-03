import Robbins.Cert.SO.LS.Kc
import Robbins.Cert.SO.LS.Vec

/-!
# The lanes step: a cell of the top record in closed form

`topCell` adds `tRP`, `tRN` to `rp`, `rn` and `tAC q`, `tLM q` to the field `q` of `acc`, `lam`;
`ownLam` is a sum over the own slots.
-/

namespace Robbins.Cert.SO.L

open Robbins.Cert Robbins.Cert.K Robbins.Cert.SO.K Robbins.Lanes

/-- `ownLam` from the slot counter `k`. -/
noncomputable def ownLamK (M : ℕ) (own : List ℕ) (topF k : ℕ) : ℕ :=
  @List.rec ℕ (fun _ => ℕ → ℕ) (fun q => Nat.mul (dq q M) topF)
    (fun s _ ih q => Nat.add (Nat.mul (dq q M) s) (ih (Nat.succ q))) own k

theorem ownLam_eqK (M : ℕ) (own : List ℕ) (topF : ℕ) : ownLam M own topF = ownLamK M own topF 0 := rfl

theorem ownLamK_eq (M topF : ℕ) (L : List ℕ) : ∀ k, ownLamK M L topF k =
    ∑ j ∈ Finset.range L.length, dq (k + j) M * L.getD j 0 + dq (k + L.length) M * topF := by
  induction L with
  | nil => intro k; simp; rfl
  | cons s L ih =>
    intro k
    show Nat.add (Nat.mul (dq k M) s) (ownLamK M L topF (k + 1)) = _
    rw [ih (k + 1), List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    have e1 : ∀ j, k + 1 + j = k + (j + 1) := fun j => by omega
    simp only [e1]
    rw [show k + (L.length + 1) = k + 1 + L.length by omega]
    show dq k M * s + _ = _
    ring

theorem filter_range_card (o : ℕ → Prop) [DecidablePred o] (d : ℕ) :
    ((List.range d).filter fun q => decide (o q)).length = ((Finset.range d).filter o).card := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.range_add_one,
      Finset.filter_insert]
    by_cases h : o d
    · simp only [h, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp)]
      simp [h]
    · simp only [h, ↓reduceIte]
      simp [h]

theorem ownSum_eq (M : ℕ) (o : ℕ → Prop) [DecidablePred o] (d : ℕ) :
    ∑ j ∈ Finset.range (((List.range d).filter fun q => decide (o q)).map (F128 ^ ·)).length,
        dq j M * (((List.range d).filter fun q => decide (o q)).map (F128 ^ ·)).getD j 0 =
      ∑ q ∈ Finset.range d, (if o q then dq ((Finset.range q).filter o).card M else 0) * F128 ^ q := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Finset.sum_range_succ, ← ih]
    set L := (List.range d).filter fun q => decide (o q) with hL
    have e : (List.range (d + 1)).filter (fun q => decide (o q)) = L ++ if o d then [d] else [] := by
      rw [List.range_succ, List.filter_append]
      by_cases h : o d <;> simp [h, L]
    rw [e, List.map_append, List.length_append]
    have hg : ∀ j < (L.map (F128 ^ ·)).length, ((L.map (F128 ^ ·)) ++
        (if o d then [d] else []).map (F128 ^ ·)).getD j 0 = (L.map (F128 ^ ·)).getD j 0 :=
      fun j hj => List.getD_append _ _ _ _ hj
    by_cases h : o d
    · simp only [h, ↓reduceIte, List.map_cons, List.map_nil, List.length_singleton]
      rw [Finset.sum_range_succ]
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun j hj => by rw [List.getD_append _ _ _ _ (Finset.mem_range.1 hj)]) ?_
      rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero, List.length_map,
          filter_range_card]
    · simp only [h, ↓reduceIte, List.map_nil, List.length_nil, List.append_nil, zero_mul, add_zero]

/-- `ownLam` of the own slots `o` of `d` slots, in closed form. -/
theorem ownLam_closed (M : ℕ) (o : ℕ → Prop) [DecidablePred o] (d topF : ℕ) :
    ownLam M (((List.range d).filter fun q => decide (o q)).map (F128 ^ ·)) topF =
      ∑ q ∈ Finset.range d, (if o q then dq ((Finset.range q).filter o).card M else 0) * F128 ^ q +
        dq ((Finset.range d).filter o).card M * topF := by
  rw [ownLam_eqK, ownLamK_eq]
  simp only [Nat.zero_add]
  rw [ownSum_eq, List.length_map, filter_range_card]

/-- `S` of a cell of the top record: `S'`, plus `Pm w` below the top cell. -/
noncomputable def tS (tp : Tp) (pd : PD) (isTop : Bool) : ℕ :=
  if isTop = true then pd.sp else pd.sp + tp.PmW

/-- The crossing quotient `(beta - A0) / kk`. -/
noncomputable def tQ1 (a1 : ℕ) (pd : PD) (beta : ℕ) : ℕ := (beta - pd.A0) / (a1 + pd.sig)

/-- The addition to `rp` of a cell of the top record. -/
noncomputable def tRP (a1 : ℕ) (pd : PD) (beta : ℕ) : ℕ :=
  if pd.A1 ≤ beta then pd.IA else if beta ≤ pd.A0 then pd.h2 * beta else
    (pd.a0 + pd.a0 + a1 * (pd.pa + pd.pa + tQ1 a1 pd beta)) * tQ1 a1 pd beta +
      2 * (beta * (pd.h - tQ1 a1 pd beta))

/-- The addition to `rn` of a cell of the top record. -/
noncomputable def tRN (a1 : ℕ) (pd : PD) (beta : ℕ) : ℕ :=
  if pd.A1 ≤ beta then 0 else if beta ≤ pd.A0 then pd.ssq else
    (pd.pb * pd.pb - (pd.pa + tQ1 a1 pd beta) * (pd.pa + tQ1 a1 pd beta)) * pd.sig +
      ((a1 + pd.sig) + (a1 + pd.sig))

/-- The addition to the field `q` of `acc` of a cell of the top record (`d + 1` fields). -/
noncomputable def tAC (a1 : ℕ) (tp : Tp) (pd : PD) (isTop : Bool) (beta d : ℕ) (co : ℕ → ℕ)
    (PmL q : ℕ) : ℕ :=
  if ¬ pd.A1 ≤ beta ∧ tS tp pd isTop ≠ 0 then
    (if q < d then co q else if isTop = true then 0 else PmL) * qCont a1 pd beta (tS tp pd isTop)
  else 0

/-- The addition to the field `q` of `lam` of a cell of the top record (`d + 1` fields). -/
noncomputable def tLM (pd : PD) (isTop : Bool) (beta d : ℕ) (o : ℕ → Prop) [DecidablePred o]
    (TO q : ℕ) : ℕ :=
  if pd.A1 ≤ beta then
    (if q < d then (if o q then dq ((Finset.range q).filter o).card ((beta - pd.A1) / DS) else 0)
      else if isTop = true then dq ((Finset.range d).filter o).card ((beta - pd.A1) / DS) * TO else 0)
  else 0

theorem bsel_ite {α : Type} (b : Bool) (x y : α) : bsel b x y = if b = true then x else y := by
  cases b <;> rfl

theorem bsel_tt {α : Type} (x y : α) : bsel true x y = x := rfl

theorem bsel_ff {α : Type} (x y : α) : bsel false x y = y := rfl

theorem tcStop_lm (tp : Tp) (pd : PD) (isTop : Bool) (beta : ℕ) (A : Acc) (d : ℕ)
    (o : ℕ → Prop) [DecidablePred o] (TO : ℕ) (hs : pd.A1 ≤ beta)
    (hown : pd.own = ((List.range d).filter fun q => decide (o q)).map (F128 ^ ·))
    (hhas : pd.hasOwn = (List.range d).any fun q => decide (o q))
    (htopF : tp.topF = TO * F128 ^ d) :
    bsel (bsel isTop true pd.hasOwn)
      (Nat.add A.lm (ownLam ((beta - pd.A1) / DS) pd.own (bsel isTop tp.topF 0))) A.lm =
      A.lm + ∑ q ∈ Finset.range (d + 1), tLM pd isTop beta d o TO q * F128 ^ q := by
  rw [hown, ownLam_closed, Finset.sum_range_succ]
  have hlm : ∀ q ∈ Finset.range d, tLM pd isTop beta d o TO q * F128 ^ q =
      (if o q then dq ((Finset.range q).filter o).card ((beta - pd.A1) / DS) else 0) * F128 ^ q :=
    fun q hq => by simp [tLM, hs, Finset.mem_range.1 hq]
  rw [Finset.sum_congr rfl hlm]
  have hd : tLM pd isTop beta d o TO d = if isTop = true then
      dq ((Finset.range d).filter o).card ((beta - pd.A1) / DS) * TO else 0 := by simp [tLM, hs]
  rw [hd]
  cases isTop
  · cases hho : pd.hasOwn
    · have hno : ∀ q < d, ¬ o q := by
        intro q hq hoq
        rw [hhas] at hho
        have : ((List.range d).any fun q => decide (o q)) = true :=
          List.any_eq_true.2 ⟨q, List.mem_range.2 hq, by simpa using hoq⟩
        rw [this] at hho
        exact Bool.noConfusion hho
      have hz : ∑ q ∈ Finset.range d,
          (if o q then dq ((Finset.range q).filter o).card ((beta - pd.A1) / DS) else 0) * F128 ^ q = 0 :=
        Finset.sum_eq_zero fun q hq => by simp [hno q (Finset.mem_range.1 hq)]
      rw [hz, bsel_ff, bsel_ff]
      simp
    · rw [bsel_ff, bsel_tt, bsel_ff, Nat.add_eq]
      simp
  · rw [bsel_tt, bsel_tt, bsel_tt, htopF, Nat.add_eq, ite_eq_left rfl]
    ring



/-- A cell `i ≤ im` of the top record in closed form: `rp`, `rn` and every field of `acc`, `lam`
grow by `tRP`, `tRN`, `tAC`, `tLM`. -/
theorem topCell_closed (a1 : ℕ) (tp : Tp) (pd : PD) (isTop : Bool) (beta : ℕ) (A : Acc) (d : ℕ)
    (co : ℕ → ℕ) (o : ℕ → Prop) [DecidablePred o] (PmL TO : ℕ)
    (hh : pd.h = pd.pb - pd.pa)
    (hA0 : pd.A0 = pd.a0 + (a1 + pd.sig) * pd.pa) (hA1 : pd.A1 = pd.a0 + (a1 + pd.sig) * pd.pb)
    (hcp : pd.cp = ∑ q ∈ Finset.range d, co q * F128 ^ q)
    (hPmF : tp.PmF = PmL * F128 ^ d)
    (hown : pd.own = ((List.range d).filter fun q => decide (o q)).map (F128 ^ ·))
    (hhas : pd.hasOwn = (List.range d).any fun q => decide (o q))
    (htopF : tp.topF = TO * F128 ^ d) :
    topCell a1 tp pd isTop beta A = Acc.mk (A.rp + tRP a1 pd beta) (A.rn + tRN a1 pd beta)
      (A.ac + ∑ q ∈ Finset.range (d + 1), tAC a1 tp pd isTop beta d co PmL q * F128 ^ q)
      (A.lm + ∑ q ∈ Finset.range (d + 1), tLM pd isTop beta d o TO q * F128 ^ q) := by
  have hble : ∀ a b : ℕ, (Nat.ble a b = true) ↔ a ≤ b := fun a b => by rw [Nat.ble_eq]
  unfold topCell
  rw [bsel_ite]
  by_cases hs : pd.A1 ≤ beta
  · rw [ite_eq_left ((hble _ _).2 hs)]
    unfold tcStop
    have ediv : Nat.div (Nat.sub beta pd.A1) DS = (beta - pd.A1) / DS := rfl
    rw [ediv, Acc.mk.injEq]
    refine ⟨by simp [tRP, hs], by simp [tRN, hs], ?_, ?_⟩
    · have : ∀ q, tAC a1 tp pd isTop beta d co PmL q = 0 := fun q => by simp [tAC, hs]
      simp [this]
    · exact tcStop_lm tp pd isTop beta A d o TO hs hown hhas htopF
  · rw [ite_eq_right (fun h => hs ((hble _ _).1 h))]
    unfold topCell.tcRest
    have eS : bsel isTop pd.sp (Nat.add pd.sp tp.PmW) = tS tp pd isTop := by
      cases isTop <;> rfl
    have eAC : accAdd a1 pd beta (bsel isTop pd.sp (Nat.add pd.sp tp.PmW))
        (bsel isTop pd.cp (Nat.add pd.cp tp.PmF)) A.ac =
        A.ac + ∑ q ∈ Finset.range (d + 1), tAC a1 tp pd isTop beta d co PmL q * F128 ^ q := by
      rw [eS]
      unfold accAdd
      rw [bsel_ite]
      by_cases hS0 : tS tp pd isTop = 0
      · rw [ite_eq_left (by rw [hS0]; rfl)]
        have : ∀ q, tAC a1 tp pd isTop beta d co PmL q = 0 := fun q => by simp [tAC, hS0]
        simp [this]
      · rw [ite_eq_right (fun h => hS0 (by simpa using h))]
        show A.ac + _ * _ = _
        congr 1
        rw [Finset.sum_range_succ]
        have hac : ∀ q ∈ Finset.range d, tAC a1 tp pd isTop beta d co PmL q * F128 ^ q =
            qCont a1 pd beta (tS tp pd isTop) * (co q * F128 ^ q) := fun q hq => by
          simp only [tAC, hs, hS0, not_false_eq_true, ne_eq, and_self, ↓reduceIte,
            Finset.mem_range.1 hq]
          ring
        rw [Finset.sum_congr rfl hac, ← Finset.mul_sum, ← hcp]
        simp only [tAC, hs, hS0, not_false_eq_true, ne_eq, and_self, ↓reduceIte, lt_irrefl]
        cases isTop
        · simp only [bsel_ff, Bool.false_eq_true, ↓reduceIte]
          rw [hPmF, Nat.add_eq]
          ring
        · simp only [bsel_tt, ↓reduceIte]
          ring
    rw [bsel_ite]
    by_cases hl : beta ≤ pd.A0
    · rw [ite_eq_left ((hble _ _).2 hl), Acc.mk.injEq, eAC]
      refine ⟨by simp [tRP, hs, hl], by simp [tRN, hs, hl], rfl, by simp [tLM, hs]⟩
    · rw [ite_eq_right (fun h => hl ((hble _ _).1 h))]
      unfold topCell.tcCross cell2 cell2.cell2a cell2.cell2b
      have e1 : Nat.add pd.a0 (Nat.mul (Nat.add a1 pd.sig) pd.pb) = pd.A1 := by rw [hA1]; rfl
      have e0 : Nat.add pd.a0 (Nat.mul (Nat.add a1 pd.sig) pd.pa) = pd.A0 := by rw [hA0]; rfl
      rw [e1, e0, bsel_ite, ite_eq_right (fun h => hs ((hble _ _).1 h)), bsel_ite,
        ite_eq_right (fun h => hl ((hble _ _).1 h))]
      unfold cell2.cell2z
      rw [Acc.mk.injEq, eAC]
      refine ⟨?_, ?_, rfl, by simp [tLM, hs]⟩
      · simp only [tRP, hs, hl, ↓reduceIte]
        set q1 := tQ1 a1 pd beta with hq1
        show A.rp + ((pd.pa + q1 - pd.pa) * (2 * pd.a0 + a1 * (pd.pa + q1 + pd.pa)) +
          2 * beta * (pd.pb - (pd.pa + q1))) = _
        rw [Nat.add_sub_cancel_left, ← Nat.sub_sub, ← hh]
        ring
      · simp only [tRN, hs, hl, ↓reduceIte]
        set q1 := tQ1 a1 pd beta with hq1
        show A.rn + (pd.sig * (pd.pb * pd.pb - (pd.pa + q1) * (pd.pa + q1)) + 2 * (a1 + pd.sig)) = _
        ring

end Robbins.Cert.SO.L
