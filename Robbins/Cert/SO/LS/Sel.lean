import Robbins.Cert.SO.LS.Vec

/-!
# The lanes step: selections by lane counts

`pickB` (the vector `b` of a list on the lanes where `B = b`), `slotS` (the slot slopes of the
prefix records), `dqV` and `creditV` (the own-cell credits), on packs.
-/

namespace Robbins.Cert.SO.L

open Robbins.Cert Robbins.Cert.K Robbins.Cert.SO.K Robbins.Lanes

-- Helper lemmas about hd/tl of mapped ranges
lemma hd_map_range_succ (d : ℕ) (f : ℕ → ℕ) : K.hd ((List.range (d + 1)).map f) = f 0 := by
  unfold K.hd
  induction' d with d ih
  · simp
  · rw [List.range_succ_eq_map]
    simp

lemma tl_map_range_succ (d : ℕ) (f : ℕ → ℕ) : K.tl ((List.range (d + 1)).map f) = (List.range d).map (f ∘ Nat.succ) := by
  unfold K.tl
  induction' d with d ih
  · simp
  · rw [List.range_succ_eq_map]
    simp

-- The invariant lemma for pickB
lemma pickB_inv (n r b : ℕ) (Bf : ℕ → ℕ) (X : ℕ → ℕ → ℕ)
    (hX : ∀ b' < b + r, ∀ l < n, X b' l < 2 ^ 144)
    (hBf_lt : ∀ l < n, Bf l < 2 ^ 143)
    (hb_lt : b + r < 2 ^ 143) :
    List.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
      (fun x _ ih b' acc' => ih (b' + 1) (sl (ge (mkVC n) (pack LW n Bf) (bc (mkVC n) b')) x acc'))
      ((List.range r).map (fun j => pack LW n (X (b + j)))) b
      (pack LW n (fun l => if Bf l < b then X (Bf l) l else X (b - 1) l)) =
    pack LW n (fun l => if Bf l < b + r then X (Bf l) l else X (b + r - 1) l) := by
  induction' r with r ih generalizing b
  · -- r = 0
    simp
  · -- r → r+1
    -- Express the list: (List.range (r+1)).map f = f 0 :: (List.range r).map (f ∘ Nat.succ)
    have hlist : (List.range (r + 1)).map (fun j => pack LW n (X (b + j))) =
        pack LW n (X b) :: (List.range r).map (fun j => pack LW n (X ((b + 1) + j))) := by
      rw [List.range_succ_eq_map, List.map_cons]
      simp
      intro a ha
      simp [add_comm, add_left_comm]
    rw [hlist]
    -- Expand List.rec on (x :: xs)
    simp
    -- Goal: List.rec ... ((List.range r).map ...) (b+1) (sl (ge ...) (pack LW n (X b)) (pack LW n (fun l => if Bf l < b then X (Bf l) l else X (b - 1) l)))
    --   = pack LW n (fun l => if Bf l < b + (r+1) then X (Bf l) l else X (b + (r+1) - 1) l)

    -- Compute sl (ge ...) (pack LW n (X b)) (pack LW n (fun l => if Bf l < b then X (Bf l) l else X (b - 1) l))
    -- First, compute ge (mkVC n) (pack LW n Bf) (bc (mkVC n) b)
    have hbc : bc (mkVC n) b = pack LW n (fun _ => b) := by
      rw [bc_eq]
    have hb_lt' : b < 2 ^ 143 := by omega
    have hge : ge (mkVC n) (pack LW n Bf) (bc (mkVC n) b) = pack LW n (fun l => if b ≤ Bf l then 2 ^ 143 else 0) := by
      rw [hbc, ge_eq n Bf (fun _ => b) hBf_lt (fun _ _ => hb_lt')]
    rw [hge]
    -- Now we have: sl (pack LW n (fun l => if b ≤ Bf l then 2 ^ 143 else 0)) (pack LW n (X b)) (pack LW n (fun l => if Bf l < b then X (Bf l) l else X (b - 1) l))
    -- Use sl_eq
    have hXb : ∀ l < n, X b l < 2 ^ 144 := by
      intro l hl
      exact hX b (by omega) l hl
    have haccval : ∀ l < n, (fun l' => if Bf l' < b then X (Bf l') l' else X (b - 1) l') l < 2 ^ 144 := by
      intro l hl
      by_cases hBl : Bf l < b
      · have hBf_lt_144 : X (Bf l) l < 2 ^ 144 := by
          apply hX (Bf l)
          · apply lt_of_lt_of_le hBl; omega
          · exact hl
        simpa [hBl] using hBf_lt_144
      · have hb1_lt_144 : X (b - 1) l < 2 ^ 144 := by
          apply hX (b - 1)
          · -- need: b-1 < b + (r+1)
            by_cases hb0 : b = 0
            · subst hb0; simp
            · have h : b - 1 < b := Nat.sub_lt (Nat.pos_of_ne_zero hb0) (by omega)
              omega
          · exact hl
        simpa [hBl] using hb1_lt_144
    rw [sl_eq n (fun l => b ≤ Bf l) (X b) (fun l => if Bf l < b then X (Bf l) l else X (b - 1) l) hXb haccval]
    -- Now we have: pack LW n (fun l => if b ≤ Bf l then X b l else (if Bf l < b then X (Bf l) l else X (b - 1) l))
    -- Simplify: this equals pack LW n (fun l => if Bf l < b + 1 then X (Bf l) l else X b l)
    have hacc' : pack LW n (fun l => if b ≤ Bf l then X b l else (if Bf l < b then X (Bf l) l else X (b - 1) l)) =
        pack LW n (fun l => if Bf l < b + 1 then X (Bf l) l else X b l) := by
      apply pack_congr
      intro l hl
      by_cases hBle : b ≤ Bf l
      · -- b ≤ Bf l, so ¬ (Bf l < b)
        have h_not_lt : ¬ Bf l < b := by omega
        by_cases h_lt : Bf l < b + 1
        · -- Bf l = b (since b ≤ Bf l < b+1)
          have heq : Bf l = b := by omega
          simp [heq]
        · -- Bf l ≥ b+1, so ¬ (Bf l < b+1)
          simp [hBle, h_lt]
      · -- ¬ b ≤ Bf l, so Bf l < b
        have h_lt : Bf l < b + 1 := by omega
        simp [hBle, h_lt]
    rw [hacc']

    -- Now the goal is:
    -- (List.rec ... ((List.range r).map ...)) (b+1) (pack LW n (fun l => if Bf l < b + 1 then X (Bf l) l else X b l))
    -- = pack LW n (fun l => if Bf l < b + (r+1) then X (Bf l) l else X (b + (r+1) - 1) l)

    -- The acc in the goal is: pack LW n (fun l => if Bf l < b + 1 then X (Bf l) l else X b l)
    -- The acc expected by ih (b+1) is: pack LW n (fun l => if Bf l < (b+1) then X (Bf l) l else X ((b+1) - 1) l)
    -- Note: X ((b+1) - 1) l = X b l (since (b+1) - 1 = b when b+1 ≥ 1, which is always true)
    -- So we need to rewrite X b l to X ((b+1) - 1) l
    have hacc_eq : pack LW n (fun l => if Bf l < b + 1 then X (Bf l) l else X b l) =
        pack LW n (fun l => if Bf l < (b + 1) then X (Bf l) l else X ((b + 1) - 1) l) := by
      apply pack_congr
      intro l hl
      by_cases h : Bf l < b + 1
      · simp [h]
      · simp [h]
    rw [hacc_eq]

    -- Apply induction hypothesis with b' = b+1
    have hX' : ∀ b' < (b + 1) + r, ∀ l < n, X b' l < 2 ^ 144 := by
      intro b' hb' l hl
      apply hX b'
      · omega
      · exact hl
    have hb_lt_sum : (b + 1) + r < 2 ^ 143 := by omega

    rw [ih (b + 1) hX' hb_lt_sum]
    -- Now RHS: pack LW n (fun l => if Bf l < (b+1) + r then X (Bf l) l else X ((b+1) + r - 1) l)
    -- Goal RHS: pack LW n (fun l => if Bf l < b + (r+1) then X (Bf l) l else X (b + (r+1) - 1) l)
    -- These are equal by associativity of addition
    simp [add_comm, add_left_comm]

/-- `pickB`: on the lane `l`, the vector `B l` of the list. -/
theorem pickB_eq (n d : ℕ) (Bf : ℕ → ℕ) (X : ℕ → ℕ → ℕ) (hB : ∀ l < n, Bf l ≤ d) (hd : d < 2 ^ 100)
    (hX : ∀ b ≤ d, ∀ l < n, X b l < 2 ^ 144) :
    pickB (mkVC n) (pack LW n Bf) ((List.range (d + 1)).map fun b => pack LW n (X b)) =
      pack LW n fun l => X (Bf l) l := by
  -- We need the bounds for ge_eq
  have hBf_lt : ∀ l < n, Bf l < 2 ^ 143 := by
    intro l hl
    have h := hB l hl
    have hd' : d < 2 ^ 143 := by
      apply lt_of_lt_of_le hd
      norm_num
    omega
  -- We need hX for b' < 1 + d
  have hX' : ∀ b' < 1 + d, ∀ l < n, X b' l < 2 ^ 144 := by
    intro b' hb' l hl
    have : b' ≤ d := by omega
    exact hX b' this l hl
  have hb_lt : 1 + d < 2 ^ 143 := by
    have hd' : d < 2 ^ 143 := by
      apply lt_of_lt_of_le hd
      norm_num
    omega
  have h := pickB_inv n d 1 Bf X hX' hBf_lt hb_lt
  -- h: List.rec ... ((List.range d).map (fun j => pack LW n (X (1 + j)))) 1 (pack LW n (fun l => if Bf l < 1 then X (Bf l) l else X (1 - 1) l))
  --   = pack LW n (fun l => if Bf l < 1 + d then X (Bf l) l else X (1 + d - 1) l)

  -- Connect pickB to the List.rec in h
  unfold pickB
  have hhd : K.hd ((List.range (d + 1)).map fun b => pack LW n (X b)) = pack LW n (X 0) := by
    rw [hd_map_range_succ]
  have htl : K.tl ((List.range (d + 1)).map fun b => pack LW n (X b)) = (List.range d).map (fun j => pack LW n (X (1 + j))) := by
    rw [tl_map_range_succ]
    simp [Function.comp, add_comm]
  rw [hhd, htl]
  -- Now the goal is: List.rec ... ((List.range d).map ...) 1 (pack LW n (X 0)) = pack LW n (fun l => X (Bf l) l)

  -- Compare with h: the acc in h is pack LW n (fun l => if Bf l < 1 then X (Bf l) l else X (1 - 1) l)
  -- We need to relate pack LW n (X 0) to this
  have hacc : pack LW n (X 0) = pack LW n (fun l => if Bf l < 1 then X (Bf l) l else X (1 - 1) l) := by
    apply pack_congr
    intro l hl
    by_cases hBl : Bf l < 1
    · have hBl0 : Bf l = 0 := by omega
      simp [hBl0]
    · simp [hBl]
  rw [← hacc] at h
  -- Now h: List.rec ... ((List.range d).map ...) 1 (pack LW n (X 0)) = pack LW n (fun l => if Bf l < 1 + d then X (Bf l) l else X (1 + d - 1) l)
  -- RHS simplifies: 1 + d = d + 1, 1 + d - 1 = d
  -- Since Bf l ≤ d < d+1, we have Bf l < d+1 = 1+d always, so the condition is always true
  -- Thus RHS = pack LW n (fun l => X (Bf l) l)
  rw [h]
  apply pack_congr
  intro l hl
  have hBl := hB l hl
  have hlt : Bf l < 1 + d := by omega
  simp [hlt]

/-- `mapIdxFrom` on a mapped `List.range'`. -/
theorem sel_mapIdxFrom_range {α β : Type} (f : ℕ → α → β) (u : ℕ → α) (k n : ℕ) :
    mapIdxFrom f k ((List.range' k n).map u) = (List.range' k n).map fun i => f i (u i) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => rw [List.range'_succ, List.map_cons, List.map_cons, mapIdxFrom, ih]

/-- `lmapIdx` from `0` on a mapped `List.range`. -/
theorem sel_lmapIdx_range {α β : Type} (f : ℕ → α → β) (u : ℕ → α) (n : ℕ) :
    lmapIdx f 0 ((List.range n).map u) = (List.range n).map fun i => f i (u i) := by
  rw [lmapIdx_eq, List.range_eq_range', sel_mapIdxFrom_range]

/-- `slotS`: the slot `q` takes `gs[q]` on the lanes with `q < B`, else `gs[q + 1]`. -/
theorem slotS_eq (n d : ℕ) (Bf : ℕ → ℕ) (G : ℕ → ℕ → ℕ) (hB : ∀ l < n, Bf l < 2 ^ 100) (hd : d < 2 ^ 100)
    (hG : ∀ f ≤ d, ∀ l < n, G f l < 2 ^ 144) :
    slotS (mkVC n) (pack LW n Bf) ((List.range (d + 1)).map fun f => pack LW n (G f)) =
      (List.range d).map fun q => pack LW n fun l => if q < Bf l then G q l else G (q + 1) l := by
  set g : ℕ → ℕ := fun f => pack LW n (G f) with hg
  have ht : ((List.range (d + 1)).map g).tail = (List.range d).map fun q => g (q + 1) := by
    rw [List.range_succ_eq_map, List.map_cons, List.tail_cons, List.map_map]
    rfl
  have hz : lzipWith Prod.mk ((List.range (d + 1)).map g) (tl ((List.range (d + 1)).map g)) =
      (List.range d).map fun q => (g q, g (q + 1)) := by
    rw [lzipWith_eq, tl_eq, ht]
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp
  unfold slotS
  rw [hz, sel_lmapIdx_range]
  apply List.map_congr_left
  intro q hq
  rw [List.mem_range] at hq
  simp only [hg]
  rw [bc_eq, ge_eq n Bf (fun _ => q.succ) (fun l hl => lt_trans (hB l hl) (by norm_num))
    (fun _ _ => by show q + 1 < 2 ^ 143; omega)]
  rw [sl_eq n (fun l => q.succ ≤ Bf l) (G q) (G (q + 1)) (hG q (by omega)) (hG (q + 1) (by omega))]
  apply pack_congr
  intro l _
  simp only [Nat.succ_le_iff]

/-- `dqV` on lanes is `dq`. -/
theorem dqV_eq (n : ℕ) (Q M : ℕ → ℕ) (hQ : ∀ l < n, Q l < 2 ^ 100) (hM : ∀ l < n, M l < 2 ^ 143) :
    dqV (mkVC n) (pack LW n Q) (pack LW n M) = pack LW n fun l => dq (Q l) (M l) := by
  unfold dqV dq
  rw [mkVC_O]
  simp [pack_add, pack_const_mul]
  have hDSQ : ∀ l < n, DS * Q l < 2 ^ 143 := by
    intro l hl
    have hQl := hQ l hl
    have hDS : DS = 2 ^ 36 := rfl
    have hQbound : Q l ≤ 2 ^ 100 - 1 := by omega
    have hmax : 2 ^ 36 * (2 ^ 100 - 1) < 2 ^ 143 := by
      have h1 : 2 ^ 36 * (2 ^ 100 - 1) < 2 ^ 36 * 2 ^ 100 :=
        Nat.mul_lt_mul_of_pos_left (by omega) (by norm_num : 0 < 2 ^ 36)
      have h2 : 2 ^ 36 * 2 ^ 100 = 2 ^ 136 := by ring
      have h3 : 2 ^ 136 < 2 ^ 143 := by norm_num
      rw [h2] at h1
      exact lt_trans h1 h3
    have hle : DS * Q l ≤ DS * (2 ^ 100 - 1) := Nat.mul_le_mul_left DS hQbound
    rw [hDS] at hle
    have : DS * Q l < 2 ^ 143 := lt_of_le_of_lt hle hmax
    exact this
  have hDSQ1 : ∀ l < n, DS * (Q l + 1) < 2 ^ 143 := by
    intro l hl
    have hQl := hQ l hl
    have hsum : DS * (Q l + 1) = DS * Q l + DS := by ring
    rw [hsum]
    have hQbound' : Q l + 1 ≤ 2 ^ 100 := by omega
    have hmax' : DS * (2 ^ 100) < 2 ^ 143 := by
      have : DS * 2 ^ 100 = 2 ^ 136 := by
        have : DS = 2 ^ 36 := rfl
        rw [this]
        ring
      rw [this]
      norm_num
    have hle' : DS * (Q l + 1) ≤ DS * 2 ^ 100 := Nat.mul_le_mul_left DS hQbound'
    exact lt_of_le_of_lt hle' hmax'
  rw [lmin_eq n (fun l => DS * (Q l + 1)) M hDSQ1 hM,
    lmin_eq n (fun l => DS * Q l) M (hDSQ) hM]
  -- Goal: (pack ... min (DS*(Q+1)) M) - (pack ... min (DS*Q) M) = pack ... (nmin2 ((Q+1)*DS) (M) - nmin2 (Q*DS) (M))
  -- Use pack_sub to combine the subtraction on the LHS
  have hsub : (pack LW n (fun l => min (DS * (Q l + 1)) (M l))) - (pack LW n (fun l => min (DS * Q l) (M l)))
      = pack LW n (fun l => min (DS * (Q l + 1)) (M l) - min (DS * Q l) (M l)) := by
    apply pack_sub LW n (fun l => min (DS * Q l) (M l)) (fun l => min (DS * (Q l + 1)) (M l))
    intro l hl
    -- Need: min (DS * Q l) (M l) ≤ min (DS * (Q l + 1)) (M l)
    refine min_le_min ?_ (le_refl _)
    exact Nat.mul_le_mul_left DS (by omega)
  rw [hsub]
  -- Now the goal is: pack ... (min (DS*(Q+1)) M - min (DS*Q) M) = pack ... (nmin2 ((Q+1)*DS) (M) - nmin2 (Q*DS) (M))
  -- Use pack_congr to reduce to pointwise equality
  refine pack_congr LW n (fun l => min (DS * (Q l + 1)) (M l) - min (DS * Q l) (M l))
    (fun l => nmin2 (Nat.mul (Nat.succ (Q l)) DS) (M l) - nmin2 (Nat.mul (Q l) DS) (M l))
    (fun l hl => ?_)
  -- Pointwise equality
  have h_nmin2_eq_min : ∀ a b : ℕ, nmin2 a b = min a b := by
    intro a b
    unfold nmin2
    rw [bsel_eq]
    split_ifs with h
    · -- h : a.ble b = true, i.e., a ≤ b
      have ha_le_b : a ≤ b := by
        simpa [Nat.ble_eq] using h
      rw [min_eq_left ha_le_b]
    · -- h : ¬ a.ble b = true, i.e., b < a
      have hb_lt_a : b ≤ a := by
        have : ¬ a ≤ b := by simpa [Nat.ble_eq] using h
        omega
      rw [min_eq_right hb_lt_a]
  have h1 : nmin2 (Nat.mul (Nat.succ (Q l)) DS) (M l) = min (DS * (Q l + 1)) (M l) := by
    rw [h_nmin2_eq_min]
    simp [mul_comm, Nat.succ_eq_add_one]
  have h2 : nmin2 (Nat.mul (Q l) DS) (M l) = min (DS * Q l) (M l) := by
    rw [h_nmin2_eq_min]
    simp [mul_comm]
  rw [h1, h2]

/-- The number of the slots `q' < q` with `o q' l`. -/
def ownBefore (o : ℕ → ℕ → Prop) [∀ q l, Decidable (o q l)] (q l : ℕ) : ℕ :=
  ((Finset.range q).filter fun q' => o q' l).card

/-- At most the slots before. -/
theorem ownBefore_le (o : ℕ → ℕ → Prop) [∀ q l, Decidable (o q l)] (q l : ℕ) : ownBefore o q l ≤ q := by
  unfold ownBefore
  exact le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_range])

/-- One more slot. -/
theorem ownBefore_succ (o : ℕ → ℕ → Prop) [∀ q l, Decidable (o q l)] (q l : ℕ) :
    ownBefore o (q + 1) l = ownBefore o q l + if o q l then 1 else 0 := by
  unfold ownBefore
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun hm => by simp at hm)]
  · rfl

/-- The credit is at most `M`. -/
theorem dq_le_M (q M : ℕ) : dq q M ≤ M := by
  unfold dq nmin2
  refine le_trans (Nat.sub_le _ _) ?_
  rw [bsel_eq]
  split_ifs with h
  · exact Nat.le_of_ble_eq_true h
  · exact le_rfl

/-- The credits from the slot `a` on. -/
theorem creditV_aux (n d : ℕ) (o : ℕ → ℕ → Prop) [∀ q l, Decidable (o q l)] (M : ℕ → ℕ) (topOn : Bool)
    (hd : d < 2 ^ 90) (hM : ∀ l < n, M l < 2 ^ 143) (m : ℕ) : ∀ a, a + m ≤ d →
    @List.rec ℕ (fun _ => ℕ → List ℕ × ℕ)
      (fun Q => ([], bsel topOn (dqV (mkVC n) Q (pack LW n M)) 0))
      (fun o' _ ih Q => creditV.creditV1 (msk o' (dqV (mkVC n) Q (pack LW n M)))
        (ih (Nat.add Q (ind LW o'))))
      ((List.range m).map fun i => pack LW n fun l => if o (a + i) l then 2 ^ 143 else 0)
      (pack LW n fun l => ownBefore o a l) =
    ((List.range m).map fun i => pack LW n fun l =>
        if o (a + i) l then dq (ownBefore o (a + i) l) (M l) else 0,
      if topOn then pack LW n (fun l => dq (ownBefore o (a + m) l) (M l)) else 0) := by
  have hQ : ∀ a, a ≤ d → ∀ l < n, ownBefore o a l < 2 ^ 100 := fun a ha l _ =>
    lt_of_le_of_lt (ownBefore_le o a l) (by omega)
  induction m with
  | zero =>
    intro a ha
    simp only [List.range_zero, List.map_nil]
    show (([] : List ℕ), bsel topOn (dqV (mkVC n) _ (pack LW n M)) 0) = _
    rw [bsel_eq, dqV_eq n _ M (hQ a (by omega)) hM]
    cases topOn <;> simp
  | succ m ih =>
    intro a ha
    rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map, List.map_map]
    show creditV.creditV1 _ (List.rec _ _ _ _) = _
    have hst : Nat.add (pack LW n fun l => ownBefore o a l)
        (ind LW (pack LW n fun l => if o (a + 0) l then 2 ^ 143 else 0)) =
        pack LW n fun l => ownBefore o (a + 1) l := by
      rw [ind_eq n (fun l => o (a + 0) l)]
      show pack LW n _ + pack LW n _ = _
      rw [pack_add]
      apply pack_congr
      intro l _
      rw [ownBefore_succ, add_zero]
    have hl1 : ((fun i => pack LW n fun l => if o (a + i) l then 2 ^ 143 else 0) ∘ Nat.succ) =
        fun i => pack LW n fun l => if o (a + 1 + i) l then 2 ^ 143 else 0 := by
      funext i
      simp only [Function.comp, Nat.succ_eq_add_one, show a + (i + 1) = a + 1 + i by omega]
    have hl2 : ((fun i => pack LW n fun l => if o (a + i) l then dq (ownBefore o (a + i) l) (M l) else 0) ∘
        Nat.succ) = fun i => pack LW n fun l =>
          if o (a + 1 + i) l then dq (ownBefore o (a + 1 + i) l) (M l) else 0 := by
      funext i
      simp only [Function.comp, Nat.succ_eq_add_one, show a + (i + 1) = a + 1 + i by omega]
    rw [hst, hl1, hl2, ih (a + 1) (by omega), show a + 1 + m = a + (m + 1) by omega]
    unfold creditV.creditV1
    congr 2
    rw [dqV_eq n _ M (hQ a (by omega)) hM,
      msk_eq n (fun l => o (a + 0) l) _ (fun l hl => lt_of_le_of_lt (dq_le_M _ _)
        (lt_trans (hM l hl) (by norm_num)))]
    simp only [add_zero]

/-- `creditV`: slot `q` gets `dq (number of own slots before it) M` where it is own, the top gets
`dq (number of own slots) M` when `topOn`. -/
theorem creditV_eq (n d : ℕ) (o : ℕ → ℕ → Prop) [∀ q l, Decidable (o q l)] (M : ℕ → ℕ) (topOn : Bool)
    (hd : d < 2 ^ 90) (hM : ∀ l < n, M l < 2 ^ 143) :
    creditV (mkVC n) (pack LW n M)
        ((List.range d).map fun q => pack LW n fun l => if o q l then 2 ^ 143 else 0) topOn =
      ((List.range d).map fun q => pack LW n fun l => if o q l then dq (ownBefore o q l) (M l) else 0,
        if topOn then pack LW n (fun l => dq (ownBefore o d l) (M l)) else 0) := by
  have h0 : (pack LW n fun l => ownBefore o 0 l) = 0 := by
    unfold pack ownBefore
    simp
  have := creditV_aux n d o M topOn hd hM d 0 (by omega)
  simp only [zero_add, h0] at this
  unfold creditV
  exact this

end Robbins.Cert.SO.L
