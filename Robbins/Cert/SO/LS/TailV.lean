import Robbins.Cert.SO.LS.Tail

/-!
# The lanes step: the tail of a top record on lanes

`tailV` on the lanes of a mask against `tailCells` lane by lane (`tailV_lanes`), by induction over
the cells: at each boundary the lanes that stop take the exact tail (`tailEndV_eq`), the others go
through one tail cell (`tailCellV_core`). The accumulator lanes are given unpacked (`rp`, `rn` and the
fields of `ac` as functions of the lane), so that `LanesSound.tailV_rep` only repacks them.
-/

namespace Robbins.Cert.SO.L

open Robbins.Cert Robbins.Cert.K Robbins.Cert.SO.K Robbins.Lanes

/-- The growth of an accumulator lane over `k` tail cells and the exact tail. -/
def tailD (k : ℕ) : ℕ := k * 2 ^ 125 + 2 ^ 123

/-- `packF` of `f 0, .., f (m - 1)`. -/
theorem packF_sum_range (m : ℕ) (f : ℕ → ℕ) :
    packF ((List.range m).map f) = ∑ q ∈ Finset.range m, f q * F128 ^ q := by
  induction m generalizing f with
  | zero => simp [packF, lfoldr_eq]
  | succ m ih =>
    have hcons : packF ((List.range (m + 1)).map f) =
        f 0 + packF ((List.range m).map fun l => f (l + 1)) * F128 := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      unfold packF
      rw [lfoldr_eq, lfoldr_eq, List.foldr_cons]
      rfl
    rw [hcons, ih, Finset.sum_range_succ', Finset.sum_mul]
    rw [pow_zero, mul_one, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [pow_succ, Nat.mul_assoc]

/-- One boundary of the scalar tail. -/
theorem tailCells_cons (r a1 a0 U S slcF : ℕ) (cl : SC) (cs : List SC) (pj etj etmj : ℕ) (A : Acc) :
    tailCells r a1 a0 U S slcF (cl :: cs) pj etj etmj A =
      if U + S + DS * (etj + r) ≤ a0 + a1 * pj then tailCells.tailEnd r U slcF pj etmj A
      else tailCells.tailCell r a1 a0 U S slcF cl (tailCells r a1 a0 U S slcF cs cl.pb cl.et cl.etm)
        (r * cl.e1) A := by
  have e : Nat.add (Nat.add (Nat.mul DS (Nat.add etj r)) U) S = U + S + DS * (etj + r) := by
    simp only [Nat.add_eq, Nat.mul_eq]; ring
  show bsel (Nat.ble (Nat.add (Nat.add (Nat.mul DS (Nat.add etj r)) U) S) (Nat.add a0 (Nat.mul a1 pj)))
    _ _ = _
  rw [bsel_eq, e]
  by_cases h : U + S + DS * (etj + r) ≤ a0 + a1 * pj
  · rw [ite_eq_left h, ite_eq_left (by rw [Nat.ble_eq]; exact h)]
  · rw [ite_eq_right h, ite_eq_right (by rw [Nat.ble_eq]; exact h)]
    rfl

/-- One boundary of the tail on lanes, with the mask `END` of the lanes that stop, the
accumulators `A1` after the exact tail on them and the mask `CONT` of the lanes that go on. -/
theorem tailV_cons_eq (v : VC) (r a1 a0 U S : ℕ) (gs : List ℕ) (cl : SC) (cs : List SC)
    (pj etj etmj ACT : ℕ) (A : LA) (END : ℕ)
    (hEND : Nat.land ACT (ge v (bc v (a0 + a1 * pj)) (Nat.add (Nat.add U S) (bc v (DS * (etj + r))))) =
      END)
    (A1 : LA)
    (hA1 : bsel (Nat.ble DS pj) A
        (LA.mk (Nat.add A.rp (msk END (Nat.add (bc v (Nat.div (Nat.mul (Nat.mul 2 DS2) etmj) (Nat.succ r)))
            (Nat.mul (Nat.mul 2 (Nat.sub DS pj)) U)))) A.rn
          (addL A.ac (lmap (fun g => msk END (Nat.mul (Nat.sub DS pj) g)) gs)) A.lm A.ok) = A1)
    (CONT : ℕ) (hC : Nat.sub ACT END = CONT) :
    tailV v r a1 a0 U S gs (cl :: cs) pj etj etmj ACT A =
      bsel (Nat.beq CONT 0) A1
        (tailV v r a1 a0 U S gs cs cl.pb cl.et cl.etm CONT (tailCellV v r a1 a0 U S gs cl CONT A1)) := by
  subst hEND hA1 hC
  rfl

theorem grow_two {a b c d T : ℕ} (h : a ≤ b + c + d + T) (hc : c < 2 ^ 124) (hd : d < 2 ^ 124) :
    a ≤ b + (T + 2 ^ 125) := by omega

theorem grow_one {a b d T : ℕ} (h : a ≤ b + d + T) (hd : d < 2 ^ 124) : a ≤ b + (T + 2 ^ 125) := by
  omega

/-- The exact tail on one lane, `ac` given by its fields. -/
theorem tailEnd_acc (m r pj etmj U : ℕ) (g a : ℕ → ℕ) (s : Acc)
    (hac : s.ac = ∑ q ∈ Finset.range m, a q * F128 ^ q) :
    tailCells.tailEnd r U (packF ((List.range m).map g)) pj etmj s =
      Acc.mk (s.rp + if pj < DS then 2 * DS2 * etmj / (r + 1) + 2 * (DS - pj) * U else 0) s.rn
        (∑ q ∈ Finset.range m, (a q + if pj < DS then (DS - pj) * g q else 0) * F128 ^ q) s.lm := by
  rw [tailEnd_closed]
  by_cases hp : DS ≤ pj
  · rw [ite_eq_left hp, ite_eq_right (by omega), Nat.add_zero]
    simp only [ite_eq_right (show ¬ pj < DS by omega), Nat.add_zero, ← hac]
  · rw [ite_eq_right hp, ite_eq_left (by omega)]
    simp only [ite_eq_left (show pj < DS by omega)]
    congr 1
    rw [hac, packF_sum_range, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring

/-- The accumulators after one tail cell on one lane, `ac` given by its fields `a` and `slcF` by `g`. -/
noncomputable def cellAcc (m r a1 a0 U S : ℕ) (g a : ℕ → ℕ) (cl : SC) (s : Acc) : Acc := Acc.mk
      (s.rp + cRP a1 a0 (a1 + r * cl.e1) (a0 + (a1 + r * cl.e1) * cl.pa) (a0 + (a1 + r * cl.e1) * cl.pb)
        cl.pa cl.pb cl.h (DS * cl.et + U + r * cl.e1 * cl.pb))
      (s.rn + cRN (r * cl.e1) (a1 + r * cl.e1) (a0 + (a1 + r * cl.e1) * cl.pa)
        (a0 + (a1 + r * cl.e1) * cl.pb) cl.pa cl.pb (DS * cl.et + U + r * cl.e1 * cl.pb))
      (∑ q ∈ Finset.range m, (a q + if S ≠ 0 then g q * chord.chord1 cl.pa cl.pb
        (DS * cl.et + U + r * cl.e1 * cl.pb) S (a1 + r * cl.e1) (a0 + (a1 + r * cl.e1) * cl.pa)
        (a0 + (a1 + r * cl.e1) * cl.pb) else 0) * F128 ^ q) s.lm

/-- A tail cell on one lane, `ac` given by its fields. -/
theorem tailCell_acc (m r a1 a0 U S : ℕ) (g a : ℕ → ℕ) (cl : SC) (k : Acc → Acc) (s : Acc)
    (hh : cl.h = cl.pb - cl.pa) (hac : s.ac = ∑ q ∈ Finset.range m, a q * F128 ^ q) :
    tailCells.tailCell r a1 a0 U S (packF ((List.range m).map g)) cl k (r * cl.e1) s =
      k (cellAcc m r a1 a0 U S g a cl s) := by
  unfold cellAcc
  rw [tailCell_closed r a1 a0 U S _ cl k (r * cl.e1) (DS * cl.et + U + r * cl.e1 * cl.pb) s hh rfl]
  congr 2
  rw [hac, packF_sum_range]
  by_cases hS : S = 0
  · rw [ite_eq_left hS, Nat.add_zero]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [ite_eq_right (by simpa using hS), Nat.add_zero]
  · rw [ite_eq_right hS, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [ite_eq_left hS]
    ring

/-- The tail of a top record on the lanes of `act`, lane by lane: `tailCells` on the lanes of `act`,
the others unchanged, each accumulator lane growing by at most `tailD` of the number of cells. -/
theorem tailV_lanes (n m r a1 a0 : ℕ) (Uf Sf : ℕ → ℕ) (gf : ℕ → ℕ → ℕ)
    (hr : r ≤ 1023) (ha1 : a1 = r * DS) (ha0 : a0 < 2 ^ 80)
    (hU : ∀ l < n, Uf l < 2 ^ 85) (hS : ∀ l < n, Sf l < 2 ^ 91) (hg : ∀ f l, l < n → gf f l < 2 ^ 48) :
    ∀ (cs : List SC), (∀ cl ∈ cs, cl.pa ≤ cl.pb ∧ cl.pb ≤ DS ∧ cl.h = cl.pb - cl.pa ∧ cl.et ≤ DS ∧
      cl.e1 ≤ DS ∧ cl.etm ≤ DS) →
    ∀ (pj etj etmj : ℕ), pj ≤ DS → etj ≤ DS → etmj ≤ DS →
    ∀ (act : ℕ → Prop) [DecidablePred act] (A : LA) (rpf rnf : ℕ → ℕ) (af : ℕ → ℕ → ℕ),
    A.rp = pack LW n rpf → A.rn = pack LW n rnf →
    A.ac = (List.range m).map (fun q => pack LW n (af q)) →
    (tailV (mkVC n) r a1 a0 (pack LW n Uf) (pack LW n Sf) ((List.range m).map fun f => pack LW n (gf f))
      cs pj etj etmj (pack LW n fun l => if act l then 2 ^ 143 else 0) A).ok = true →
    ∃ (rpf' rnf' : ℕ → ℕ) (af' : ℕ → ℕ → ℕ),
      tailV (mkVC n) r a1 a0 (pack LW n Uf) (pack LW n Sf) ((List.range m).map fun f => pack LW n (gf f))
        cs pj etj etmj (pack LW n fun l => if act l then 2 ^ 143 else 0) A =
        LA.mk (pack LW n rpf') (pack LW n rnf') ((List.range m).map fun q => pack LW n (af' q)) A.lm
          true ∧
      (∀ l < n, ∀ s : Acc, s.rp = rpf l → s.rn = rnf l → s.ac = ∑ q ∈ Finset.range m, af q l * F128 ^ q →
        (if act l then tailCells r a1 a0 (Uf l) (Sf l) (packF ((List.range m).map fun f => gf f l)) cs
          pj etj etmj s else s) =
          Acc.mk (rpf' l) (rnf' l) (∑ q ∈ Finset.range m, af' q l * F128 ^ q) s.lm) ∧
      (∀ l < n, rpf' l ≤ rpf l + tailD cs.length ∧ rnf' l ≤ rnf l + tailD cs.length ∧
        ∀ q < m, af' q l ≤ af q l + tailD cs.length) := by
  have hDS : DS = 2 ^ 36 := rfl
  have hDS2 : DS2 = 2 ^ 72 := rfl
  have hrDS : r * DS < 2 ^ 46 := by
    rw [hDS]
    calc r * 2 ^ 36 ≤ 1023 * 2 ^ 36 := Nat.mul_le_mul_right _ hr
      _ < 2 ^ 46 := by norm_num
  have ha1b : a1 < 2 ^ 47 := by rw [ha1]; omega
  intro cs
  induction cs with
  | nil =>
    intro _ pj etj etmj _ _ _ act _ A rpf rnf af hArp hArn hAac hok
    refine ⟨rpf, rnf, af, ?_, ?_, ?_⟩
    · have hok' : A.ok = true := hok
      show A = _
      cases A with
      | mk rp rn ac lm ok =>
        simp only at hArp hArn hAac hok' ⊢
        rw [hArp, hArn, hAac, hok']
    · intro l _ s h1 h2 h3
      have hs : s = Acc.mk (rpf l) (rnf l) (∑ q ∈ Finset.range m, af q l * F128 ^ q) s.lm := by
        cases s
        simp only at h1 h2 h3 ⊢
        rw [h1, h2, h3]
      split
      · exact hs
      · exact hs
    · intro l _
      exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, fun q _ => Nat.le_add_right _ _⟩
  | cons cl cs ih =>
    intro hcs pj etj etmj hpj hetj hetm act _ A rpf rnf af hArp hArn hAac hok
    obtain ⟨hpab, hpbD, hh, het, he1, hetm1⟩ := hcs cl List.mem_cons_self
    have hcs' : ∀ c ∈ cs, c.pa ≤ c.pb ∧ c.pb ≤ DS ∧ c.h = c.pb - c.pa ∧ c.et ≤ DS ∧ c.e1 ≤ DS ∧
        c.etm ≤ DS := fun c hc => hcs c (List.mem_cons_of_mem _ hc)
    have hX : a0 + a1 * pj < 2 ^ 143 := by
      have : a1 * pj < 2 ^ 84 := mul_lt_pow ha1b (show pj < 2 ^ 37 by rw [hDS] at hpj; omega)
        (by norm_num)
      omega
    have hY : ∀ l < n, Uf l + Sf l + DS * (etj + r) < 2 ^ 143 := by
      intro l hl
      have h1 := hU l hl
      have h2 := hS l hl
      have h3 : DS * (etj + r) < 2 ^ 74 :=
        mul_lt_pow (show DS < 2 ^ 37 by rw [hDS]; norm_num) (show etj + r < 2 ^ 37 by rw [hDS] at hetj; omega)
          (by norm_num)
      omega
    have hEND := endMask_eq n (a0 + a1 * pj) (DS * (etj + r)) act Uf Sf hX hY
    have hA1 := tailEndV_eq n m r pj etmj Uf gf
      (fun l => act l ∧ Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj) A rpf af hetm hU hg hArp hAac
    have hC := mask_sub n act (fun l => Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj)
    rw [tailV_cons_eq _ _ _ _ _ _ _ cl cs pj etj etmj _ A _ hEND _ hA1 _ hC] at hok ⊢
    -- the exact tail on one lane
    have hEndLane : ∀ l < n, ∀ s : Acc, act l → Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj →
        s.rp = rpf l → s.rn = rnf l → s.ac = ∑ q ∈ Finset.range m, af q l * F128 ^ q →
        tailCells r a1 a0 (Uf l) (Sf l) (packF ((List.range m).map fun f => gf f l)) (cl :: cs) pj etj
          etmj s =
        Acc.mk (rpf l + if (act l ∧ Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj) ∧ pj < DS then
            2 * DS2 * etmj / (r + 1) + 2 * (DS - pj) * Uf l else 0) (rnf l)
          (∑ q ∈ Finset.range m, (af q l + if (act l ∧ Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj) ∧
            pj < DS then (DS - pj) * gf q l else 0) * F128 ^ q) s.lm := by
      intro l _ s ha hst h1 h2 h3
      rw [tailCells_cons, ite_eq_left (by omega),
        tailEnd_acc m r pj etmj (Uf l) (fun f => gf f l) (fun q => af q l) s h3, h1, h2]
      simp only [ha, hst, true_and]
    have hD : tailD (cl :: cs).length = tailD cs.length + 2 ^ 125 := by
      simp only [tailD, List.length_cons]; ring
    have hE : ∀ l < n, (if (act l ∧ Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj) ∧ pj < DS then
        2 * DS2 * etmj / (r + 1) + 2 * (DS - pj) * Uf l else 0) < 2 ^ 123 := by
      intro l hl
      split_ifs
      · exact tailEndInc_lt r pj etmj (Uf l) hetm (hU l hl)
      · norm_num
    have hEa : ∀ q l, l < n → (if (act l ∧ Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj) ∧ pj < DS then
        (DS - pj) * gf q l else 0) < 2 ^ 85 := by
      intro q l hl
      split_ifs
      · exact mul_lt_pow (show DS - pj < 2 ^ 37 by rw [hDS]; omega) (hg q l hl) (by norm_num)
      · norm_num
    set P := (pack LW n fun l =>
      if act l ∧ ¬(Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj) then 2 ^ 143 else 0) with hP
    by_cases hz : P = 0
    · -- no lane goes on
      have hno := mask_zero n _ hz
      rw [hz] at hok ⊢
      simp only [show Nat.beq 0 0 = true from rfl, bsel_true] at hok ⊢
      have hok' : A.ok = true := hok
      refine ⟨fun l => rpf l + if (act l ∧ Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj) ∧ pj < DS then
          2 * DS2 * etmj / (r + 1) + 2 * (DS - pj) * Uf l else 0, rnf,
        fun q l => af q l + if (act l ∧ Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj) ∧ pj < DS then
          (DS - pj) * gf q l else 0, ?_, ?_, ?_⟩
      · rw [hArn, hok']
      · intro l hl s h1 h2 h3
        by_cases ha : act l
        · have hst : Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj := by
            by_contra hst; exact hno l hl ⟨ha, hst⟩
          rw [ite_eq_left ha]
          exact hEndLane l hl s ha hst h1 h2 h3
        · rw [ite_eq_right ha]
          simp only [ha, false_and, ite_false, Nat.add_zero]
          cases s
          simp only at h1 h2 h3 ⊢
          rw [h1, h2, h3]
      · intro l hl
        have e1 := hE l hl
        beta_reduce
        refine ⟨by rw [hD]; unfold tailD; omega, by omega, fun q _ => ?_⟩
        have e2 := hEa q l hl
        rw [hD]; unfold tailD; omega
    · -- some lane goes on
      have hb : Nat.beq P 0 = false := by
        cases h : Nat.beq P 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hz
      rw [hb] at hok ⊢
      simp only [bsel_false] at hok ⊢
      have hokC := tailV_ok _ _ _ _ _ _ _ _ _ _ _ _ _ hok
      have hcore := tailCellV_core n m r a1 a0 cl Uf Sf gf
        (fun l => act l ∧ ¬(Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj))
        (LA.mk (pack LW n fun l => rpf l + if (act l ∧ Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj) ∧
          pj < DS then 2 * DS2 * etmj / (r + 1) + 2 * (DS - pj) * Uf l else 0) A.rn
          ((List.range m).map fun q => pack LW n fun l => af q l + if (act l ∧ Uf l + Sf l +
            DS * (etj + r) ≤ a0 + a1 * pj) ∧ pj < DS then (DS - pj) * gf q l else 0) A.lm A.ok)
        (fun l => rpf l + if (act l ∧ Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj) ∧ pj < DS then
          2 * DS2 * etmj / (r + 1) + 2 * (DS - pj) * Uf l else 0) rnf
        (fun q l => af q l + if (act l ∧ Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj) ∧ pj < DS then
          (DS - pj) * gf q l else 0) hpab hpbD hh het he1 hr ha1 ha0 hU hS hg rfl hArn rfl hokC
      rw [hcore.1] at hok ⊢
      obtain ⟨rpf', rnf', af', hT, hL, hG⟩ := ih hcs' cl.pb cl.et cl.etm hpbD het hetm1
        (fun l => act l ∧ ¬(Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj)) _ _ _ _ rfl rfl rfl hok
      refine ⟨rpf', rnf', af', hT, ?_, ?_⟩
      · intro l hl s h1 h2 h3
        by_cases ha : act l
        · rw [ite_eq_left ha]
          by_cases hst : Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj
          · have e := hL l hl (tailCells r a1 a0 (Uf l) (Sf l) (packF ((List.range m).map fun f => gf f l))
                (cl :: cs) pj etj etmj s)
              (by rw [hEndLane l hl s ha hst h1 h2 h3]; simp [ha, hst])
              (by rw [hEndLane l hl s ha hst h1 h2 h3]; simp [ha, hst])
              (by
                rw [hEndLane l hl s ha hst h1 h2 h3]
                dsimp only
                refine Finset.sum_congr rfl fun q _ => ?_
                simp [ha, hst])
            rw [ite_eq_right (fun h => h.2 hst)] at e
            rw [e, hEndLane l hl s ha hst h1 h2 h3]
          · rw [tailCells_cons, ite_eq_right (by omega),
              tailCell_acc m r a1 a0 (Uf l) (Sf l) (fun f => gf f l) (fun q => af q l) cl _ s hh h3]
            have e := hL l hl (cellAcc m r a1 a0 (Uf l) (Sf l) (fun f => gf f l) (fun q => af q l) cl s)
              (by simp [cellAcc, ha, hst, h1]) (by simp [cellAcc, ha, hst, h2])
              (by
                simp only [cellAcc]
                refine Finset.sum_congr rfl fun q _ => ?_
                simp [ha, hst])
            rw [ite_eq_left ⟨ha, hst⟩] at e
            exact e
        · rw [ite_eq_right ha]
          have e := hL l hl s (by simp [ha, h1]) (by simp [ha, h2])
            (by rw [h3]; refine Finset.sum_congr rfl fun q _ => ?_; simp [ha])
          rw [ite_eq_right (fun h => ha h.1)] at e
          exact e
      · intro l hl
        obtain ⟨g1, g2, g3⟩ := hG l hl
        have e1 := hE l hl
        have hsg : r * cl.e1 < 2 ^ 46 :=
          lt_of_le_of_lt (Nat.mul_le_mul_left _ he1) hrDS
        have hpb36 : cl.pb ≤ 2 ^ 36 := hpbD.trans (le_of_eq hDS)
        have hBb : DS * cl.et + Uf l + r * cl.e1 * cl.pb < 2 ^ 86 := by
          have b1 : DS * cl.et ≤ 2 ^ 72 :=
            (Nat.mul_le_mul (le_of_eq hDS) (het.trans (le_of_eq hDS))).trans (by norm_num)
          have b2 : r * cl.e1 * cl.pb < 2 ^ 83 :=
            mul_lt_pow hsg (show cl.pb < 2 ^ 37 by omega) (by norm_num)
          have := hU l hl
          omega
        have hcR : (if act l ∧ ¬(Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj) then
            cRP a1 a0 (a1 + r * cl.e1) (a0 + (a1 + r * cl.e1) * cl.pa) (a0 + (a1 + r * cl.e1) * cl.pb)
              cl.pa cl.pb cl.h (DS * cl.et + Uf l + r * cl.e1 * cl.pb) else 0) < 2 ^ 124 := by
          split_ifs
          · exact cRP_lt a1 a0 (r * cl.e1) _ _ _ cl.pa cl.pb cl.h _ ha1b ha0 (by omega) rfl rfl rfl hpab
              hpb36 hh hBb
          · norm_num
        have hcN : (if act l ∧ ¬(Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj) then
            cRN (r * cl.e1) (a1 + r * cl.e1) (a0 + (a1 + r * cl.e1) * cl.pa) (a0 + (a1 + r * cl.e1) * cl.pb)
              cl.pa cl.pb (DS * cl.et + Uf l + r * cl.e1 * cl.pb) else 0) < 2 ^ 121 := by
          split_ifs
          · exact cRN_lt _ _ _ _ cl.pa cl.pb _ (by omega) (by omega) hpb36
          · norm_num
        have hcA : ∀ q, (if (act l ∧ ¬(Uf l + Sf l + DS * (etj + r) ≤ a0 + a1 * pj)) ∧ Sf l ≠ 0 then
            gf q l * chord.chord1 cl.pa cl.pb (DS * cl.et + Uf l + r * cl.e1 * cl.pb) (Sf l)
              (a1 + r * cl.e1) (a0 + (a1 + r * cl.e1) * cl.pa) (a0 + (a1 + r * cl.e1) * cl.pb) else 0) <
            2 ^ 85 := by
          intro q
          split_ifs with hc
          · exact mul_lt_pow (hg q l hl) (hcore.2 l hl hc.1 hc.2) (by norm_num)
          · norm_num
        rw [hD]
        exact ⟨grow_two g1 (e1.trans (by norm_num)) hcR, grow_one g2 (hcN.trans (by norm_num)),
          fun q hq => grow_two (g3 q hq) ((hEa q l hl).trans (by norm_num)) ((hcA q).trans (by norm_num))⟩

end Robbins.Cert.SO.L
