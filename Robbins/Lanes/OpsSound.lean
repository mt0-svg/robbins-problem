import Robbins.Lanes.Pack

/-!
# Packed lanes: the specifications of the kernel operations

Each operation of Robbins/Lanes/Ops.lean applied to packs (Robbins/Lanes/Pack.lean) is the pack
of the lanewise operation, under the lane bounds that keep every lane inside its `W` bits (and
below the guard bit `2 ^ (W - 1)` where a compare is involved).
-/

namespace Robbins.Lanes

/-! ## Combinators -/

theorem cnd_eq {α : Type} (b : Bool) (x y : α) : cnd b x y = if b then x else y := by
  cases b <;> rfl

theorem frc2_eq {α : Type} (a b : ℕ) (k : ℕ → ℕ → α) : frc2 a b k = k a b := by
  simp only [frc2, cnd_eq]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]

/-! ## Lanes, prefixes, concatenation -/

/-- A pack of `n + 1` lanes: the first lane, then the rest shifted by one lane. -/
theorem pack_cons (W n : ℕ) (g : ℕ → ℕ) :
    pack W (n + 1) g = g 0 + pack W n (fun j => g (j + 1)) * 2 ^ W := by
  have h : ∀ j, g (j + 1) * 2 ^ (W * (j + 1)) = g (j + 1) * 2 ^ (W * j) * 2 ^ W := fun j => by
    rw [mul_assoc, ← pow_add, mul_add, mul_one]
  unfold pack
  rw [Finset.sum_range_succ', Finset.sum_congr rfl (fun j _ => h j), Finset.sum_mul]
  simp [add_comm]

/-- A lane by its definition. -/
theorem lane_eq (W P l : ℕ) : lane W P l = P / 2 ^ (W * l) % 2 ^ W := by
  show (P >>> (W * l)) &&& (1 <<< W - 1) = _
  rw [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem lane_pack (W L : ℕ) (f : ℕ → ℕ) (hf : ∀ l < L, f l < 2 ^ W) (l : ℕ) (hl : l < L) :
    lane W (pack W L f) l = f l := by
  rw [lane_eq, pack_div_mod W L f hf l hl]

/-- A pack splits after its first `n` lanes. -/
theorem pack_split (W L n : ℕ) (f : ℕ → ℕ) (hn : n ≤ L) :
    pack W L f = pack W n f + pack W (L - n) (fun l => f (l + n)) * 2 ^ (W * n) := by
  unfold pack
  conv_lhs => rw [show L = n + (L - n) by omega]
  rw [Finset.sum_range_add, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [add_comm n l, mul_assoc, ← pow_add, mul_add, add_comm (W * l)]

theorem pre_pack (W L n : ℕ) (f : ℕ → ℕ) (hf : ∀ l < L, f l < 2 ^ W) (hn : n ≤ L) :
    pre W n (pack W L f) = pack W n f := by
  show pack W L f &&& (1 <<< (W * n) - 1) = _
  rw [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod, pack_split W L n f hn,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (pack_lt W n f (fun l hl => hf l (by omega)))]

theorem drp_pack (W L a : ℕ) (f : ℕ → ℕ) (hf : ∀ l < L, f l < 2 ^ W) :
    drp W a (pack W L f) = pack W (L - a) (fun l => f (l + a)) := by
  show pack W L f >>> (W * a) = _
  rw [Nat.shiftRight_eq_div_pow]
  by_cases h : L ≤ a
  · rw [show L - a = 0 by omega, pack_zero, Nat.div_eq_of_lt]
    exact lt_of_lt_of_le (pack_lt W L f hf) (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ h))
  · rw [pack_split W L a f (by omega), Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (pack_lt W a f (fun l hl => hf l (by omega))), zero_add]

theorem app_pack (W a L : ℕ) (f g : ℕ → ℕ) :
    app W a (pack W a f) (pack W L g) = pack W (a + L) (fun l => if l < a then f l else g (l - a)) := by
  show pack W a f + pack W L g <<< (W * a) = _
  rw [Nat.shiftLeft_eq]
  unfold pack
  rw [Finset.sum_range_add, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun l hl => ?_
    dsimp only
    simp only [Finset.mem_range.1 hl, ↓reduceIte]
  · refine Finset.sum_congr rfl fun l _ => ?_
    dsimp only
    have : ¬ (a + l < a) := by omega
    simp only [this, ↓reduceIte, Nat.add_sub_cancel_left]
    rw [mul_assoc, ← pow_add]
    congr 2
    ring

/-- The gather from any word: lane `j` is the lane `idx[j]` of `src`. -/
theorem gath_lane (W src : ℕ) (idx : List ℕ) :
    gath W src idx = pack W idx.length (fun j => lane W src (idx.getD j 0)) := by
  induction idx with
  | nil => simp [gath, pack]
  | cons i t ih =>
    show lane W src i + gath W src t <<< W = _
    rw [ih, Nat.shiftLeft_eq, List.length_cons, pack_cons]
    simp

theorem gath_pack (W L : ℕ) (f : ℕ → ℕ) (hf : ∀ l < L, f l < 2 ^ W) (idx : List ℕ)
    (hidx : ∀ i ∈ idx, i < L) :
    gath W (pack W L f) idx = pack W idx.length (fun j => f (idx.getD j 0)) := by
  rw [gath_lane]
  refine pack_congr _ _ _ _ fun j hj => ?_
  apply lane_pack W L f hf
  rw [List.getD_eq_getElem _ _ hj]
  exact hidx _ (List.getElem_mem hj)

/-! ## Compare, masks, select -/

theorem geMask_pack (W L : ℕ) (a b : ℕ → ℕ) (hW : 0 < W) (ha : ∀ l < L, a l < 2 ^ (W - 1))
    (hb : ∀ l < L, b l < 2 ^ (W - 1)) :
    geMask (guard W L) (pack W L a) (pack W L b) =
      pack W L (fun l => if b l ≤ a l then 2 ^ (W - 1) else 0) := by
  have hp : 2 ^ W = 2 ^ (W - 1) + 2 ^ (W - 1) := by
    rw [← two_mul, ← pow_succ', Nat.sub_add_cancel hW]
  rw [guard_eq W L hW]
  show (pack W L a + pack W L (fun _ => 2 ^ (W - 1)) - pack W L b) &&& pack W L (fun _ => 2 ^ (W - 1)) = _
  rw [pack_add, pack_sub W L _ _ (fun l hl => by have := hb l hl; omega),
    land_guard W L _ hW (fun l hl => by have := ha l hl; omega)]
  exact pack_congr _ _ _ _ fun l hl => by
    have := ha l hl; have := hb l hl
    split_ifs <;> omega

theorem allGe_iff (W L : ℕ) (a b : ℕ → ℕ) (hW : 0 < W) (ha : ∀ l < L, a l < 2 ^ (W - 1))
    (hb : ∀ l < L, b l < 2 ^ (W - 1)) :
    allGe (guard W L) (pack W L a) (pack W L b) = true ↔ ∀ l < L, b l ≤ a l := by
  have hlt : 2 ^ (W - 1) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hne : 2 ^ (W - 1) ≠ 0 := by positivity
  show Nat.beq _ _ = true ↔ _
  rw [Nat.beq_eq, geMask_pack W L a b hW ha hb, guard_eq W L hW,
    pack_inj W L _ _ (fun l _ => by split_ifs <;> [exact hlt; exact Nat.two_pow_pos W]) (fun _ _ => hlt)]
  refine forall_congr' fun l => imp_congr_right fun _ => ?_
  split_ifs with hc
  · simp [hc]
  · simp only [hc, iff_false]
    exact fun e => hne e.symm

theorem ind_pack (W L : ℕ) (c : ℕ → Prop) [DecidablePred c] (hW : 0 < W) :
    ind W (pack W L (fun l => if c l then 2 ^ (W - 1) else 0)) =
      pack W L (fun l => if c l then 1 else 0) := by
  have e : pack W L (fun l => if c l then 2 ^ (W - 1) else 0) =
      2 ^ (W - 1) * pack W L (fun l => if c l then 1 else 0) := by
    rw [pack_const_mul]
    exact pack_congr _ _ _ _ fun l _ => by split_ifs <;> simp
  show _ >>> (W - 1) = _
  rw [e, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]

theorem full_pack (W L : ℕ) (c : ℕ → Prop) [DecidablePred c] (hW : 0 < W) :
    full W (pack W L (fun l => if c l then 2 ^ (W - 1) else 0)) =
      pack W L (fun l => if c l then 2 ^ W - 1 else 0) := by
  have hp : 2 ^ W = 2 ^ (W - 1) + 2 ^ (W - 1) := by
    rw [← two_mul, ← pow_succ', Nat.sub_add_cancel hW]
  have h1 := ind_pack W L c hW
  show _ + _ - ind W _ = _
  rw [h1, pack_add, pack_sub W L _ _ (fun l _ => by
    have := Nat.two_pow_pos (W - 1); split_ifs <;> omega)]
  exact pack_congr _ _ _ _ fun l _ => by split_ifs <;> omega

theorem sel_pack (W L : ℕ) (c : ℕ → Prop) [DecidablePred c] (a b : ℕ → ℕ) (hW : 0 < W)
    (ha : ∀ l < L, a l < 2 ^ W) (hb : ∀ l < L, b l < 2 ^ W) :
    sel (pack W L (fun l => if c l then 2 ^ W - 1 else 0)) (pack W L a) (pack W L b) =
      pack W L (fun l => if c l then a l else b l) := by
  have hpw : (2 : ℕ) ^ W - 1 < 2 ^ W := Nat.sub_lt (Nat.two_pow_pos W) one_pos
  show pack W L b ^^^ ((pack W L a ^^^ pack W L b) &&& _) = _
  rw [xor_pack W L a b hW ha hb,
    land_pack W L _ _ hW (fun l hl => Nat.xor_lt_two_pow (ha l hl) (hb l hl))
      (fun l _ => by split_ifs <;> [exact hpw; exact Nat.two_pow_pos W]),
    xor_pack W L _ _ hW hb (fun l _ => Nat.and_lt_two_pow _ (by
      split_ifs <;> [exact hpw; exact Nat.two_pow_pos W]))]
  refine pack_congr _ _ _ _ fun l hl => ?_
  split_ifs
  · rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (ha l hl) (hb l hl)),
      ← Nat.xor_assoc, Nat.xor_comm (b l) (a l), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · simp

theorem lmin_pack (W L : ℕ) (a b : ℕ → ℕ) (hW : 0 < W) (ha : ∀ l < L, a l < 2 ^ (W - 1))
    (hb : ∀ l < L, b l < 2 ^ (W - 1)) :
    lmin W (guard W L) (pack W L a) (pack W L b) = pack W L (fun l => min (a l) (b l)) := by
  have hlt : (2 : ℕ) ^ (W - 1) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  show sel (full W (geMask (guard W L) (pack W L a) (pack W L b))) (pack W L b) (pack W L a) = _
  rw [geMask_pack W L a b hW ha hb, full_pack W L (fun l => b l ≤ a l) hW,
    sel_pack W L (fun l => b l ≤ a l) b a hW (fun l hl => (hb l hl).trans hlt)
      (fun l hl => (ha l hl).trans hlt)]
  exact pack_congr _ _ _ _ fun l _ => by split_ifs <;> omega

theorem lmax_pack (W L : ℕ) (a b : ℕ → ℕ) (hW : 0 < W) (ha : ∀ l < L, a l < 2 ^ (W - 1))
    (hb : ∀ l < L, b l < 2 ^ (W - 1)) :
    lmax W (guard W L) (pack W L a) (pack W L b) = pack W L (fun l => max (a l) (b l)) := by
  have hlt : (2 : ℕ) ^ (W - 1) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  show sel (full W (geMask (guard W L) (pack W L a) (pack W L b))) (pack W L a) (pack W L b) = _
  rw [geMask_pack W L a b hW ha hb, full_pack W L (fun l => b l ≤ a l) hW,
    sel_pack W L (fun l => b l ≤ a l) a b hW (fun l hl => (ha l hl).trans hlt)
      (fun l hl => (hb l hl).trans hlt)]
  exact pack_congr _ _ _ _ fun l _ => by split_ifs <;> omega

theorem nzMask_pack (W L : ℕ) (t : ℕ → ℕ) (hW : 2 ≤ W) (ht : ∀ l < L, t l < 2 ^ (W - 1)) :
    nzMask (guard W L) (ones W L) (pack W L t) =
      pack W L (fun l => if t l = 0 then 0 else 2 ^ (W - 1)) := by
  rw [guard_eq W L (by omega), ones_eq W L (by omega)]
  exact zero_mask W L t hW ht

theorem shrL_pack (W L s : ℕ) (a : ℕ → ℕ) (hs : s ≤ W) (ha : ∀ l < L, a l < 2 ^ W) :
    shrL (pack W L (fun _ => 2 ^ (W - s) - 1)) s (pack W L a) = pack W L (fun l => a l / 2 ^ s) := by
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW
    have hs0 : s = 0 := by omega
    subst hs0
    have h0 : ∀ l < L, a l = 0 := fun l hl => by have := ha l hl; simp at this; exact this
    show (pack 0 L a >>> 0) &&& pack 0 L (fun _ => 2 ^ (0 - 0) - 1) = _
    simp only [Nat.shiftRight_zero, Nat.sub_self, pow_zero, Nat.sub_self, Nat.div_one]
    rw [pack_congr 0 L a (fun _ => 0) h0]
    simp [pack]
  have hM : ∀ l < L, (fun _ => 2 ^ (W - s) - 1) l < 2 ^ W := fun _ _ =>
    lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) one_pos) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hR : ∀ l < L, (fun l => a l / 2 ^ s) l < 2 ^ W := fun l hl =>
    lt_of_le_of_lt (Nat.div_le_self _ _) (ha l hl)
  apply Nat.eq_of_testBit_eq
  intro n
  show ((pack W L a >>> s) &&& pack W L _).testBit n = _
  rw [Nat.testBit_land, Nat.testBit_shiftRight, testBit_pack W L _ hW ha, testBit_pack W L _ hW hM,
    testBit_pack W L _ hW hR]
  obtain ⟨l, i, hi, rfl⟩ : ∃ l i, i < W ∧ n = W * l + i :=
    ⟨n / W, n % W, Nat.mod_lt _ hW, (Nat.div_add_mod n W).symm⟩
  have d1 : (W * l + i) / W = l := by rw [Nat.mul_add_div hW, Nat.div_eq_of_lt hi, add_zero]
  have m1 : (W * l + i) % W = i := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  rw [d1, m1, Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases hl : l < L
  · by_cases hc : i < W - s
    · have d2 : (s + (W * l + i)) / W = l := by
        rw [show s + (W * l + i) = W * l + (s + i) by ring, Nat.mul_add_div hW,
          Nat.div_eq_of_lt (by omega), add_zero]
      have m2 : (s + (W * l + i)) % W = s + i := by
        rw [show s + (W * l + i) = W * l + (s + i) by ring, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      rw [d2, m2]
      simp [hl, hc, add_comm]
    · have hf : (a l).testBit (i + s) = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (ha l hl) (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hl, hc, hf]
  · simp [hl]

/-! ## Products -/

/-- Bit `j` of every lane, as a lane unit. -/
theorem bits_pack (W L j : ℕ) (b : ℕ → ℕ) (hW : 0 < W) (hb : ∀ l < L, b l < 2 ^ W) (hj : j < W) :
    Nat.land (Nat.shiftRight (pack W L b) j) (ones W L) =
      pack W L (fun l => if (b l).testBit j then 1 else 0) := by
  rw [ones_eq W L hW]
  have h1 : ∀ l < L, (fun _ => 1) l < 2 ^ W := fun _ _ => Nat.one_lt_two_pow (by omega)
  have h2 : ∀ l < L, (fun l => if (b l).testBit j then 1 else 0) l < 2 ^ W := fun l _ => by
    dsimp only; split_ifs <;> [exact Nat.one_lt_two_pow (by omega); exact Nat.two_pow_pos W]
  apply Nat.eq_of_testBit_eq
  intro n
  show ((pack W L b >>> j) &&& pack W L (fun _ => 1)).testBit n = _
  rw [Nat.testBit_land, Nat.testBit_shiftRight, testBit_pack W L _ hW hb, testBit_pack W L _ hW h1,
    testBit_pack W L _ hW h2]
  by_cases hn : n % W = 0
  · have e1 : (j + n) / W = n / W := by
      have := Nat.div_add_mod n W
      rw [hn, add_zero] at this
      rw [← this, Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hj, zero_add, Nat.mul_div_cancel_left _ hW]
    have e2 : (j + n) % W = j := by
      have := Nat.div_add_mod n W
      rw [hn, add_zero] at this
      rw [← this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    rw [e1, e2, hn]
    split_ifs <;> simp_all
  · have : (1 : ℕ).testBit (n % W) = false := by
      rw [Nat.testBit_one_eq_true_iff_self_eq_zero.not.mpr hn |> Bool.eq_false_iff.mpr]
    split_ifs <;> simp_all

/-- The sum of the shifted multiplicands over the set bits of the multiplier. -/
theorem sum_testBit_mul (a b k : ℕ) :
    ∑ j ∈ Finset.range k, (if b.testBit j then a * 2 ^ j else 0) = a * (b % 2 ^ k) := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (b / 2 ^ k) with h | h <;> simp [h] <;> ring

/-- One step of the lanewise shift and add product. -/
theorem lamTerm_pack (W L j : ℕ) (a b : ℕ → ℕ) (hW : 0 < W) (hj : j < W)
    (ha : ∀ l < L, a l * 2 ^ j < 2 ^ W) (hb : ∀ l < L, b l < 2 ^ W) :
    Nat.land (Nat.shiftLeft (pack W L a) j)
        (Nat.mul (Nat.land (Nat.shiftRight (pack W L b) j) (ones W L)) (lmask W)) =
      pack W L (fun l => if (b l).testBit j then a l * 2 ^ j else 0) := by
  rw [bits_pack W L j b hW hb hj, lmask_eq]
  have hA : Nat.shiftLeft (pack W L a) j = pack W L (fun l => a l * 2 ^ j) := by
    show pack W L a <<< j = _
    rw [Nat.shiftLeft_eq, mul_comm, pack_const_mul]
    exact pack_congr _ _ _ _ fun l _ => mul_comm _ _
  have hM : Nat.mul (pack W L (fun l => if (b l).testBit j then 1 else 0)) (2 ^ W - 1) =
      pack W L (fun l => if (b l).testBit j then 2 ^ W - 1 else 0) := by
    show (_ : ℕ) * (_ : ℕ) = _
    rw [mul_comm, pack_const_mul]
    exact pack_congr _ _ _ _ fun l _ => by split_ifs <;> simp
  rw [hA, hM]
  show (_ : ℕ) &&& (_ : ℕ) = _
  have hpw : (2 : ℕ) ^ W - 1 < 2 ^ W := Nat.sub_lt (Nat.two_pow_pos W) one_pos
  rw [land_pack W L _ _ hW ha (fun l _ => by
    split_ifs <;> [exact hpw; exact Nat.two_pow_pos W])]
  refine pack_congr _ _ _ _ fun l hl => ?_
  split_ifs
  · exact Nat.and_two_pow_sub_one_of_lt_two_pow (ha l hl)
  · simp

/-- The partial products of the shift and add product. -/
theorem mulStep (a b i : ℕ) :
    a * (b % 2 ^ i) + (if b.testBit i then a * 2 ^ i else 0) = a * (b % 2 ^ (i + 1)) := by
  rw [← sum_testBit_mul, ← sum_testBit_mul, Finset.sum_range_succ]

theorem lamportMul_pack (W L k : ℕ) (a b : ℕ → ℕ) (hW : 0 < W) (hk : k ≤ W)
    (ha : ∀ l < L, ∀ j < k, a l * 2 ^ j < 2 ^ W) (hb : ∀ l < L, b l < 2 ^ k) :
    lamportMul k (pack W L a) (pack W L b) (ones W L) (lmask W) = pack W L (fun l => a l * b l) := by
  have hb' : ∀ l < L, b l < 2 ^ W := fun l hl =>
    lt_of_lt_of_le (hb l hl) (Nat.pow_le_pow_right (by norm_num) hk)
  have key : ∀ i ≤ k, (Nat.rec (motive := fun _ => ℕ × ℕ) (0, 0)
      (fun _ p => (Nat.add p.1 (Nat.land (Nat.shiftLeft (pack W L a) p.2)
        (Nat.mul (Nat.land (Nat.shiftRight (pack W L b) p.2) (ones W L)) (lmask W))),
          Nat.add p.2 1)) i) = (pack W L (fun l => a l * (b l % 2 ^ i)), i) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine Prod.ext ?_ rfl
      show 0 = _
      simp [pack, Nat.mod_one]
    | succ i ih =>
      intro hi
      show (Nat.add (Prod.fst _) _, Nat.add (Prod.snd _) 1) = _
      rw [ih (by omega)]
      refine Prod.ext ?_ rfl
      show pack W L _ + _ = _
      rw [lamTerm_pack W L i a b hW (by omega) (fun l hl => ha l hl i (by omega)) hb', pack_add]
      exact pack_congr _ _ _ _ fun l _ => mulStep (a l) (b l) i
  show (Nat.rec (motive := fun _ => ℕ × ℕ) (0, 0) _ k).1 = _
  rw [key k le_rfl]
  exact pack_congr _ _ _ _ fun l hl => by rw [Nat.mod_eq_of_lt (hb l hl)]

/-- One step of the product by doublings. -/
theorem lamDTerm_pack (W L i : ℕ) (a b : ℕ → ℕ) (hW : 0 < W) (hi : i < W)
    (ha : ∀ l < L, a l * 2 ^ i < 2 ^ W) (hb : ∀ l < L, b l < 2 ^ W) :
    Nat.land (pack W L a * 2 ^ i)
        (Nat.mul (Nat.land (pack W L b) (pack W L (fun _ => 1) * 2 ^ i)) ((2 ^ W - 1) / 2 ^ i)) =
      pack W L (fun l => if (b l).testBit i then a l * 2 ^ i else 0) := by
  have hWi : 2 ^ W = 2 ^ (W - i) * 2 ^ i := by rw [← pow_add, Nat.sub_add_cancel hi.le]
  have hpi : 0 < 2 ^ i := Nat.two_pow_pos i
  have hF : (2 ^ W - 1) / 2 ^ i = 2 ^ (W - i) - 1 := by
    have h1 : 1 ≤ 2 ^ (W - i) := Nat.one_le_two_pow
    apply Nat.div_eq_of_lt_le
    · rw [hWi, Nat.sub_mul, one_mul]; exact Nat.sub_le_sub_left hpi _
    · rw [hWi, Nat.sub_add_cancel h1]; exact Nat.sub_lt (by positivity) one_pos
  have hA : pack W L a * 2 ^ i = pack W L (fun l => a l * 2 ^ i) := by
    rw [mul_comm, pack_const_mul]; exact pack_congr _ _ _ _ fun l _ => mul_comm _ _
  have hO : pack W L (fun _ => 1) * 2 ^ i = pack W L (fun _ => 2 ^ i) := by
    rw [mul_comm, pack_const_mul]; exact pack_congr _ _ _ _ fun l _ => mul_one _
  have hpw : (2 : ℕ) ^ i < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) hi
  have hB : Nat.land (pack W L b) (pack W L (fun _ => 2 ^ i)) =
      pack W L (fun l => if (b l).testBit i then 2 ^ i else 0) := by
    show (_ : ℕ) &&& (_ : ℕ) = _
    rw [land_pack W L _ _ hW hb (fun _ _ => hpw)]
    exact pack_congr _ _ _ _ fun l _ => by rw [Nat.and_two_pow]; cases (b l).testBit i <;> simp
  have hM : Nat.mul (pack W L (fun l => if (b l).testBit i then 2 ^ i else 0)) (2 ^ (W - i) - 1) =
      pack W L (fun l => if (b l).testBit i then 2 ^ i * (2 ^ (W - i) - 1) else 0) := by
    show (_ : ℕ) * (_ : ℕ) = _
    rw [mul_comm, pack_const_mul]
    exact pack_congr _ _ _ _ fun l _ => by split_ifs <;> simp [mul_comm]
  rw [hA, hO, hB, hF, hM]
  show (_ : ℕ) &&& (_ : ℕ) = _
  have hlt : 2 ^ i * (2 ^ (W - i) - 1) < 2 ^ W := by
    rw [hWi, Nat.mul_sub, mul_one, mul_comm]; exact Nat.sub_lt (by positivity) hpi
  rw [land_pack W L _ _ hW ha (fun l _ => by split_ifs <;> [exact hlt; exact Nat.two_pow_pos W])]
  refine pack_congr _ _ _ _ fun l hl => ?_
  split_ifs
  · have hal : a l < 2 ^ (W - i) := by
      have := ha l hl; rw [hWi] at this; exact Nat.lt_of_mul_lt_mul_right this
    rw [mul_comm (2 ^ i), ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_and_distrib,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hal]
  · simp

theorem lamD_pack (W L k : ℕ) (a b : ℕ → ℕ) (hW : 0 < W) (hk : k ≤ W)
    (ha : ∀ l < L, ∀ j < k, a l * 2 ^ j < 2 ^ W) (hb : ∀ l < L, b l < 2 ^ k) :
    lamD k (ones W L) (pack W L a) (pack W L b) (lmask W) = pack W L (fun l => a l * b l) := by
  have hb' : ∀ l < L, b l < 2 ^ W := fun l hl =>
    lt_of_lt_of_le (hb l hl) (Nat.pow_le_pow_right (by norm_num) hk)
  rw [ones_eq W L hW, lmask_eq]
  have key : ∀ i ≤ k, (Nat.rec (motive := fun _ => ℕ × ℕ × ℕ × ℕ)
      (0, pack W L a, pack W L (fun _ => 1), 2 ^ W - 1)
      (fun _ p => (Nat.add p.1 (Nat.land p.2.1 (Nat.mul (Nat.land (pack W L b) p.2.2.1) p.2.2.2)),
        Nat.add p.2.1 p.2.1, Nat.add p.2.2.1 p.2.2.1, Nat.shiftRight p.2.2.2 1)) i) =
      (pack W L (fun l => a l * (b l % 2 ^ i)), pack W L a * 2 ^ i, pack W L (fun _ => 1) * 2 ^ i,
        (2 ^ W - 1) / 2 ^ i) := by
    intro i
    induction i with
    | zero =>
      intro _
      simp only [pow_zero, mul_one, Nat.div_one, Nat.mod_one, mul_zero]
      refine Prod.ext ?_ rfl
      show 0 = _
      simp [pack]
    | succ i ih =>
      intro hi
      show (Nat.add (Prod.fst _) _, Nat.add _ _, Nat.add _ _, Nat.shiftRight _ 1) = _
      rw [ih (by omega)]
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
      · show pack W L _ + _ = _
        rw [lamDTerm_pack W L i a b hW (by omega) (fun l hl => ha l hl i (by omega)) hb', pack_add]
        exact pack_congr _ _ _ _ fun l _ => mulStep (a l) (b l) i
      · show (_ : ℕ) + _ = _
        rw [pow_succ]; ring
      · show (_ : ℕ) + _ = _
        rw [pow_succ]; ring
      · show (_ : ℕ) >>> 1 = (2 ^ W - 1) / 2 ^ (i + 1)
        rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]
  show (Nat.rec (motive := fun _ => ℕ × ℕ × ℕ × ℕ) _ _ k).1 = _
  rw [key k le_rfl]
  exact pack_congr _ _ _ _ fun l hl => by rw [Nat.mod_eq_of_lt (hb l hl)]

/-- A bit of the bit-serial product: the spread of the bits by a shift and a subtraction. -/
theorem mulBit_eq (W L1 B Qd k P : ℕ) (ih : ℕ → ℕ) :
    mulBit W L1 B Qd k P ih = ih (P + Nat.land (Nat.shiftLeft B k)
      (Nat.mul (Nat.land (Nat.shiftRight Qd k) L1) (lmask W))) := by
  have e : ∀ x : ℕ, Nat.sub (Nat.shiftLeft x W) x = Nat.mul x (lmask W) := fun x => by
    show x <<< W - x = x * lmask W
    rw [Nat.shiftLeft_eq, lmask_eq, Nat.mul_sub_one]
  show frc2 (Nat.add P (Nat.land (Nat.shiftLeft B k) (Nat.sub (Nat.shiftLeft
    (Nat.land (Nat.shiftRight Qd k) L1) W) (Nat.land (Nat.shiftRight Qd k) L1)))) 1 (fun P _ => ih P) = _
  rw [e, frc2_eq]
  rfl

theorem mulBS_pack (W L Q : ℕ) (b q : ℕ → ℕ) (hW : 0 < W) (hQ : Q ≤ W)
    (hb : ∀ l < L, ∀ j < Q, b l * 2 ^ j < 2 ^ W) (hq : ∀ l < L, q l < 2 ^ Q) :
    mulBS W Q (ones W L) (pack W L b) (pack W L q) = pack W L (fun l => b l * q l) := by
  have hq' : ∀ l < L, q l < 2 ^ W := fun l hl =>
    lt_of_lt_of_le (hq l hl) (Nat.pow_le_pow_right (by norm_num) hQ)
  have key : ∀ i ≤ Q, ∀ P, (@Nat.rec (fun _ => ℕ → ℕ) (fun P => P)
      (fun k ih P => mulBit W (ones W L) (pack W L b) (pack W L q) k P ih) i) P =
      P + pack W L (fun l => b l * (q l % 2 ^ i)) := by
    intro i
    induction i with
    | zero => intro _ P; simp [pack, Nat.mod_one]
    | succ i ih =>
      intro hi P
      show mulBit W (ones W L) (pack W L b) (pack W L q) i P _ = _
      rw [mulBit_eq, ih (by omega),
        lamTerm_pack W L i b q hW (by omega) (fun l hl => hb l hl i (by omega)) hq', add_assoc, pack_add]
      congr 1
      exact pack_congr _ _ _ _ fun l _ => by rw [← mulStep (b l) (q l) i]; ring
  show (@Nat.rec (fun _ => ℕ → ℕ) (fun P => P)
      (fun k ih P => mulBit W (ones W L) (pack W L b) (pack W L q) k P ih) Q) 0 = _
  rw [key Q le_rfl, zero_add]
  exact pack_congr _ _ _ _ fun l hl => by rw [Nat.mod_eq_of_lt (hq l hl)]

/-- The bit-serial product reads the low `Q` bits of each multiplier lane: for lanes below `2 ^ W`, the
product by the multiplier modulo `2 ^ Q`. -/
theorem mulBS_pack_mod (W L Q : ℕ) (b q : ℕ → ℕ) (hW : 0 < W) (hQ : Q ≤ W)
    (hb : ∀ l < L, ∀ j < Q, b l * 2 ^ j < 2 ^ W) (hq : ∀ l < L, q l < 2 ^ W) :
    mulBS W Q (ones W L) (pack W L b) (pack W L q) = pack W L (fun l => b l * (q l % 2 ^ Q)) := by
  have key : ∀ i ≤ Q, ∀ P, (@Nat.rec (fun _ => ℕ → ℕ) (fun P => P)
      (fun k ih P => mulBit W (ones W L) (pack W L b) (pack W L q) k P ih) i) P =
      P + pack W L (fun l => b l * (q l % 2 ^ i)) := by
    intro i
    induction i with
    | zero => intro _ P; simp [pack, Nat.mod_one]
    | succ i ih =>
      intro hi P
      show mulBit W (ones W L) (pack W L b) (pack W L q) i P _ = _
      rw [mulBit_eq, ih (by omega),
        lamTerm_pack W L i b q hW (by omega) (fun l hl => hb l hl i (by omega)) hq, add_assoc, pack_add]
      congr 1
      exact pack_congr _ _ _ _ fun l _ => by rw [← mulStep (b l) (q l) i]; ring
  show (@Nat.rec (fun _ => ℕ → ℕ) (fun P => P)
      (fun k ih P => mulBit W (ones W L) (pack W L b) (pack W L q) k P ih) Q) 0 = _
  rw [key Q le_rfl, zero_add]

/-! ## Divisions -/


/-- The greedy quotient of the restoring division on `i` bits. -/
def gq (i b r : ℕ) : ℕ := if b = 0 then 2 ^ i - 1 else min (r / b) (2 ^ i - 1)

theorem gq_succ (i b r : ℕ) :
    gq (i + 1) b r = (if b * 2 ^ i ≤ r then 2 ^ i else 0) +
      gq i b (if b * 2 ^ i ≤ r then r - b * 2 ^ i else r) := by
  unfold gq
  have hp := Nat.two_pow_pos i
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    simp only [zero_mul, zero_le, ↓reduceIte, pow_succ]
    omega
  · have hb' : b ≠ 0 := by omega
    simp only [hb', ↓reduceIte]
    by_cases hc : b * 2 ^ i ≤ r
    · simp only [hc, ↓reduceIte]
      have h1 : (r - b * 2 ^ i) / b = r / b - 2 ^ i := Nat.sub_mul_div r b (2 ^ i)
      have h2 : 2 ^ i ≤ r / b := (Nat.le_div_iff_mul_le hb).2 (by rw [mul_comm]; exact hc)
      rw [h1, pow_succ]
      omega
    · simp only [hc, ↓reduceIte, zero_add]
      have h2 : r / b < 2 ^ i := (Nat.div_lt_iff_lt_mul hb).2 (by rw [mul_comm]; omega)
      rw [pow_succ]
      omega

/-- One step of the restoring division on packs. -/
theorem divBit_pack {α : Type} (W L k : ℕ) (b r qa : ℕ → ℕ) (ih : ℕ → ℕ → α) (hW : 0 < W) (hk : k < W)
    (hr : ∀ l < L, r l < 2 ^ (W - 1)) (hb : ∀ l < L, b l * 2 ^ k < 2 ^ (W - 1)) :
    divBit W (guard W L) (pack W L b) k (pack W L r) (pack W L qa) ih =
      ih (pack W L (fun l => if b l * 2 ^ k ≤ r l then r l - b l * 2 ^ k else r l))
        (pack W L (fun l => qa l + if b l * 2 ^ k ≤ r l then 2 ^ k else 0)) := by
  have hlt : (2 : ℕ) ^ (W - 1) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hpw : (2 : ℕ) ^ W - 1 < 2 ^ W := Nat.sub_lt (Nat.two_pow_pos W) one_pos
  have hT : Nat.shiftLeft (pack W L b) k = pack W L (fun l => b l * 2 ^ k) := by
    show pack W L b <<< k = _
    rw [Nat.shiftLeft_eq, mul_comm, pack_const_mul]
    exact pack_congr _ _ _ _ fun l _ => mul_comm _ _
  have hge : Nat.land (Nat.sub (Nat.add (pack W L r) (guard W L)) (pack W L fun l => b l * 2 ^ k))
      (guard W L) = pack W L (fun l => if b l * 2 ^ k ≤ r l then 2 ^ (W - 1) else 0) :=
    geMask_pack W L r (fun l => b l * 2 ^ k) hW hr hb
  have hfull := full_pack W L (fun l => b l * 2 ^ k ≤ r l) hW
  have hland : Nat.land (pack W L fun l => b l * 2 ^ k)
      (pack W L (fun l => if b l * 2 ^ k ≤ r l then 2 ^ W - 1 else 0)) =
      pack W L (fun l => if b l * 2 ^ k ≤ r l then b l * 2 ^ k else 0) := by
    show (_ : ℕ) &&& (_ : ℕ) = _
    rw [land_pack W L _ _ hW (fun l hl => lt_trans (hb l hl) hlt)
      (fun l _ => by split_ifs <;> [exact hpw; exact Nat.two_pow_pos W])]
    refine pack_congr _ _ _ _ fun l hl => ?_
    split_ifs
    · rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (lt_trans (hb l hl) hlt)]
    · simp
  have hsub : Nat.sub (pack W L r) (pack W L (fun l => if b l * 2 ^ k ≤ r l then b l * 2 ^ k else 0)) =
      pack W L (fun l => if b l * 2 ^ k ≤ r l then r l - b l * 2 ^ k else r l) := by
    show (_ : ℕ) - (_ : ℕ) = _
    rw [pack_sub W L _ _ (fun l _ => by split_ifs <;> omega)]
    exact pack_congr _ _ _ _ fun l _ => by split_ifs <;> omega
  have hshr : Nat.shiftRight (pack W L (fun l => if b l * 2 ^ k ≤ r l then 2 ^ (W - 1) else 0))
      (Nat.sub (Nat.sub W 1) k) = pack W L (fun l => if b l * 2 ^ k ≤ r l then 2 ^ k else 0) := by
    show _ >>> (W - 1 - k) = _
    have e : pack W L (fun l => if b l * 2 ^ k ≤ r l then 2 ^ (W - 1) else 0) =
        2 ^ (W - 1 - k) * pack W L (fun l => if b l * 2 ^ k ≤ r l then 2 ^ k else 0) := by
      rw [pack_const_mul]
      refine pack_congr _ _ _ _ fun l _ => ?_
      split_ifs
      · rw [← pow_add]; congr 1; omega
      · simp
    rw [e, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
  have hadd : Nat.add (pack W L qa) (pack W L (fun l => if b l * 2 ^ k ≤ r l then 2 ^ k else 0)) =
      pack W L (fun l => qa l + if b l * 2 ^ k ≤ r l then 2 ^ k else 0) := pack_add _ _ _ _
  show frc2 (Nat.sub (pack W L r) (Nat.land (Nat.shiftLeft (pack W L b) k)
      (full W (Nat.land (Nat.sub (Nat.add (pack W L r) (guard W L)) (Nat.shiftLeft (pack W L b) k))
        (guard W L)))))
    (Nat.add (pack W L qa) (Nat.shiftRight (Nat.land (Nat.sub (Nat.add (pack W L r) (guard W L))
      (Nat.shiftLeft (pack W L b) k)) (guard W L)) (Nat.sub (Nat.sub W 1) k))) ih = _
  rw [frc2_eq, hT, hge, hfull, hland, hsub, hshr, hadd]

/-- The loop of the restoring division on packs, for any final continuation `K` (applied to the
remainder and quotient lanes). -/
theorem divLoop_pack {α : Type} (W L Q : ℕ) (b : ℕ → ℕ) (K : ℕ → ℕ → α) (hW : 0 < W) (hQ : Q ≤ W)
    (hb : ∀ l < L, ∀ j < Q, b l * 2 ^ j < 2 ^ (W - 1)) :
    ∀ i ≤ Q, ∀ r qa : ℕ → ℕ, (∀ l < L, r l < 2 ^ (W - 1)) →
      (@Nat.rec (fun _ => ℕ → ℕ → α) K
        (fun k ih R Qa => divBit W (guard W L) (pack W L b) k R Qa ih) i) (pack W L r) (pack W L qa) =
      K (pack W L (fun l => r l - b l * gq i (b l) (r l)))
        (pack W L (fun l => qa l + gq i (b l) (r l))) := by
  intro i
  induction i with
  | zero =>
    intro _ r qa _
    show K (pack W L r) (pack W L qa) = _
    congr 1 <;> exact pack_congr _ _ _ _ fun l _ => by simp [gq]
  | succ i ih =>
    intro hi r qa hr
    show divBit W (guard W L) (pack W L b) i (pack W L r) (pack W L qa)
      (@Nat.rec (fun _ => ℕ → ℕ → α) K
        (fun k ih R Qa => divBit W (guard W L) (pack W L b) k R Qa ih) i) = _
    rw [divBit_pack W L i b r qa _ hW (by omega) hr (fun l hl => hb l hl i (by omega)),
      ih (by omega) _ _ (fun l hl => by have := hr l hl; split_ifs <;> omega)]
    congr 1
    · refine pack_congr _ _ _ _ fun l _ => ?_
      rw [gq_succ]
      split_ifs <;> simp only [mul_add, zero_add, Nat.sub_sub]
    · refine pack_congr _ _ _ _ fun l _ => ?_
      rw [gq_succ]
      split_ifs <;> omega

/-- The restoring division on every lane: the quotient saturates at `2 ^ Q - 1`, and a divisor
`0` gives `2 ^ Q - 1`. -/
theorem divBS_pack_min (W L Q : ℕ) (a b : ℕ → ℕ) (hW : 0 < W) (hQ : Q ≤ W)
    (ha : ∀ l < L, a l < 2 ^ (W - 1)) (hb : ∀ l < L, ∀ j < Q, b l * 2 ^ j < 2 ^ (W - 1)) :
    divBS W Q (guard W L) (pack W L a) (pack W L b) =
      pack W L (fun l => if b l = 0 then 2 ^ Q - 1 else min (a l / b l) (2 ^ Q - 1)) := by
  have h := divLoop_pack W L Q b (fun _ Qa => Qa) hW hQ hb Q le_rfl a (fun _ => 0) ha
  have h0 : pack W L (fun _ => 0) = 0 := by simp [pack]
  rw [h0] at h
  show (@Nat.rec (fun _ => ℕ → ℕ → ℕ) (fun _ Qa => Qa)
    (fun k ih R Qa => divBit W (guard W L) (pack W L b) k R Qa ih) Q) (pack W L a) 0 = _
  rw [h]
  exact pack_congr _ _ _ _ fun l _ => by simp [gq]

/-- The restoring division with its remainder, on every lane. -/
theorem divQR_pack (W L Q : ℕ) (a b : ℕ → ℕ) (hW : 0 < W) (hQ : Q ≤ W)
    (ha : ∀ l < L, a l < 2 ^ (W - 1)) (hb : ∀ l < L, ∀ j < Q, b l * 2 ^ j < 2 ^ (W - 1)) :
    divQR W Q (guard W L) (pack W L a) (pack W L b) =
      (pack W L (fun l => if b l = 0 then 2 ^ Q - 1 else min (a l / b l) (2 ^ Q - 1)),
        pack W L (fun l => a l - b l * (if b l = 0 then 2 ^ Q - 1 else min (a l / b l) (2 ^ Q - 1)))) := by
  have h := divLoop_pack W L Q b (fun R Qa => (Qa, R)) hW hQ hb Q le_rfl a (fun _ => 0) ha
  have h0 : pack W L (fun _ => 0) = 0 := by simp [pack]
  rw [h0] at h
  show (@Nat.rec (fun _ => ℕ → ℕ → ℕ × ℕ) (fun R Qa => (Qa, R))
    (fun k ih R Qa => divBit W (guard W L) (pack W L b) k R Qa ih) Q) (pack W L a) 0 = _
  rw [h]
  refine Prod.ext ?_ ?_ <;> exact pack_congr _ _ _ _ fun l _ => by simp [gq]

/-- The restoring division on lanes whose quotient fits in `Q` bits. -/
theorem divBS_pack (W L Q : ℕ) (a b : ℕ → ℕ) (hW : 0 < W) (hQ : Q ≤ W)
    (ha : ∀ l < L, a l < 2 ^ (W - 1)) (hb : ∀ l < L, ∀ j < Q, b l * 2 ^ j < 2 ^ (W - 1))
    (hq : ∀ l < L, a l < b l * 2 ^ Q) :
    divBS W Q (guard W L) (pack W L a) (pack W L b) = pack W L (fun l => a l / b l) := by
  have hb2 : ∀ l < L, ∀ j < Q, b l * 2 ^ j < 2 ^ (W - 1) := hb
  rw [divBS_pack_min W L Q a b hW hQ ha hb2]
  refine pack_congr _ _ _ _ fun l hl => ?_
  have h1 := hq l hl
  have hb0 : b l ≠ 0 := by rintro e; rw [e] at h1; simp at h1
  have h2 : a l / b l < 2 ^ Q := (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hb0)).2 (by rw [mul_comm]; exact h1)
  simp only [hb0, ↓reduceIte]
  exact min_eq_left (by omega)

theorem chkP_iff (W L : ℕ) (a b p : ℕ → ℕ) (hW : 0 < W) (ha : ∀ l < L, a l < 2 ^ (W - 1))
    (hpb : ∀ l < L, p l + b l < 2 ^ (W - 1)) :
    chkP (guard W L) (ones W L) (pack W L a) (pack W L b) (pack W L p) = true ↔
      ∀ l < L, p l ≤ a l ∧ a l < p l + b l := by
  have hp : 2 ^ W = 2 ^ (W - 1) + 2 ^ (W - 1) := by
    rw [← two_mul, ← pow_succ', Nat.sub_add_cancel hW]
  have key : ∀ (b1 b2 : Bool), ((if b1 = true then b2 else false) = true) ↔ (b1 = true ∧ b2 = true) := by
    decide
  have e1 : pack W L a + pack W L (fun _ => 2 ^ (W - 1)) - pack W L p =
      pack W L (fun l => a l + 2 ^ (W - 1) - p l) := by
    rw [pack_add, pack_sub W L _ _ (fun l hl => by have := hpb l hl; show p l ≤ a l + 2 ^ (W - 1); omega)]
  have e2 : pack W L p + pack W L b + pack W L (fun _ => 2 ^ (W - 1)) - (pack W L a + pack W L (fun _ => 1)) =
      pack W L (fun l => p l + b l + 2 ^ (W - 1) - (a l + 1)) := by
    rw [pack_add, pack_add, pack_add, pack_sub W L _ _ (fun l hl => by
      have := ha l hl; show a l + 1 ≤ p l + b l + 2 ^ (W - 1); omega)]
  rw [guard_eq W L hW, ones_eq W L hW]
  show cnd (Nat.beq ((pack W L a + pack W L (fun _ => 2 ^ (W - 1)) - pack W L p) &&&
      pack W L (fun _ => 2 ^ (W - 1))) (pack W L (fun _ => 2 ^ (W - 1))))
    (Nat.beq ((pack W L p + pack W L b + pack W L (fun _ => 2 ^ (W - 1)) -
      (pack W L a + pack W L (fun _ => 1))) &&& pack W L (fun _ => 2 ^ (W - 1)))
      (pack W L (fun _ => 2 ^ (W - 1)))) false = true ↔ _
  rw [cnd_eq, key, Nat.beq_eq, Nat.beq_eq, e1, e2,
    land_guard_eq_iff W L _ hW (fun l hl => by have := ha l hl; omega),
    land_guard_eq_iff W L _ hW (fun l hl => by have := hpb l hl; omega)]
  constructor
  · rintro ⟨h1, h2⟩ l hl
    have := h1 l hl; have := h2 l hl; have := ha l hl; have := hpb l hl
    constructor <;> omega
  · intro h
    constructor <;> intro l hl <;> have := h l hl <;> have := ha l hl <;> have := hpb l hl <;> omega

theorem chkQ_iff (W L k : ℕ) (a b q : ℕ → ℕ) (hW : 0 < W) (hk : k ≤ W)
    (hb : ∀ l < L, ∀ j < k, b l * 2 ^ j < 2 ^ W) (hq : ∀ l < L, q l < 2 ^ k)
    (ha : ∀ l < L, a l < 2 ^ (W - 1)) (hbq : ∀ l < L, b l * q l + b l < 2 ^ (W - 1)) :
    chkQ W k (guard W L) (ones W L) (pack W L a) (pack W L b) (pack W L q) = true ↔
      ∀ l < L, b l * q l ≤ a l ∧ a l < b l * q l + b l := by
  show chkP (guard W L) (ones W L) (pack W L a) (pack W L b)
      (mulBS W k (ones W L) (pack W L b) (pack W L q)) = true ↔ _
  rw [mulBS_pack W L k b q hW hk hb hq]
  exact chkP_iff W L a b (fun l => b l * q l) hW ha hbq

/-- A quotient witness that passes the check is the quotient. -/
theorem chkQ_sound (W L k : ℕ) (a b q : ℕ → ℕ) (hW : 0 < W) (hk : k ≤ W)
    (hb : ∀ l < L, ∀ j < k, b l * 2 ^ j < 2 ^ W) (hq : ∀ l < L, q l < 2 ^ k)
    (ha : ∀ l < L, a l < 2 ^ (W - 1)) (hbq : ∀ l < L, b l * q l + b l < 2 ^ (W - 1))
    (h : chkQ W k (guard W L) (ones W L) (pack W L a) (pack W L b) (pack W L q) = true) :
    ∀ l < L, q l = a l / b l := by
  intro l hl
  obtain ⟨h1, h2⟩ := (chkQ_iff W L k a b q hW hk hb hq ha hbq).1 h l hl
  have hb0 : 0 < b l := by
    rcases Nat.eq_zero_or_pos (b l) with e | e
    · rw [e] at h1 h2; omega
    · exact e
  symm
  apply Nat.div_eq_of_lt_le
  · rw [mul_comm]; exact h1
  · rw [add_mul, one_mul, mul_comm]; exact h2

/-- Division by an invariant integer by multiplication and shift (Granlund and Montgomery). -/
theorem gm_div (x d s : ℕ) (hd : 0 < d) (hx : x * d ≤ 2 ^ s) :
    x * ((2 ^ s + d - 1) / d) / 2 ^ s = x / d := by
  set M := (2 ^ s + d - 1) / d with hM
  have hps := Nat.two_pow_pos s
  have h1 : 2 ^ s ≤ d * M := by
    have := Nat.div_add_mod (2 ^ s + d - 1) d
    have := Nat.mod_lt (2 ^ s + d - 1) hd
    rw [← hM] at *
    omega
  have h2 : d * M + 1 ≤ 2 ^ s + d := by
    have h3 := Nat.mul_div_le (2 ^ s + d - 1) d
    rw [← hM] at h3
    have : 2 ^ s + d - 1 + 1 = 2 ^ s + d := by omega
    omega
  set q := x / d with hq
  have hq1 : d * q ≤ x := Nat.mul_div_le x d
  have hq2 : x + 1 ≤ d * (q + 1) := by
    have := Nat.lt_mul_div_succ x hd
    rw [← hq] at this
    linarith
  apply Nat.div_eq_of_lt_le
  · nlinarith [Nat.mul_le_mul_left q h1, Nat.mul_le_mul_right M hq1]
  · rcases Nat.eq_zero_or_pos x with hx0 | hx0
    · subst hx0; simp
    · have A : x * (d * M) + x ≤ (x + 1) * 2 ^ s := by nlinarith
      have B : (x + 1) * 2 ^ s ≤ d * (q + 1) * 2 ^ s := Nat.mul_le_mul_right _ hq2
      by_contra hc
      push Not at hc
      have C : d * ((q + 1) * 2 ^ s) ≤ d * (x * M) := Nat.mul_le_mul_left _ hc
      nlinarith

theorem divC_pack (W L s d : ℕ) (x : ℕ → ℕ) (hs : s ≤ W) (hd : 0 < d)
    (hx : ∀ l < L, x l * d ≤ 2 ^ s) (hM : ∀ l < L, x l * ((2 ^ s + d - 1) / d) < 2 ^ W) :
    divC (pack W L (fun _ => 2 ^ (W - s) - 1)) s ((2 ^ s + d - 1) / d) (pack W L x) =
      pack W L (fun l => x l / d) := by
  have e : Nat.mul ((2 ^ s + d - 1) / d) (pack W L x) =
      pack W L (fun l => x l * ((2 ^ s + d - 1) / d)) := by
    show (_ : ℕ) * _ = _
    rw [pack_const_mul]
    exact pack_congr _ _ _ _ fun l _ => mul_comm _ _
  show shrL _ s (Nat.mul ((2 ^ s + d - 1) / d) (pack W L x)) = _
  rw [e, shrL_pack W L s _ hs hM]
  exact pack_congr _ _ _ _ fun l hl => gm_div (x l) d s hd (hx l hl)

/-! ## Fields of the claimed tables -/

/-- The states of one literal: at most `k`, of `Ws` bits each, read from the low end while the
rest exceeds `1` (the leading `1`). -/
def litStates (Ws : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, x => if x ≤ 1 then [] else x % 2 ^ Ws :: litStates Ws k (x / 2 ^ Ws)

/-- The states of the literals, in order. -/
def allStates (Ws : ℕ) (lits : List ℕ) : List ℕ := lits.flatMap (litStates Ws 16)

/-- The loop of `litChunk` with `k` steps. -/
theorem litChunk_rec (W Ws fo F : ℕ) (k : ℕ) : ∀ x c i,
    (@Nat.rec (fun _ => ℕ → ℕ → ℕ → ℕ × ℕ) (fun _ c i => (c, i))
      (fun _ ih x c i => cnd (Nat.ble x 1) (c, i)
        (ih (Nat.shiftRight x Ws)
          (Nat.add c (Nat.shiftLeft (Nat.land (Nat.shiftRight (Nat.land x (lmask Ws)) fo) (lmask F))
            (Nat.mul W i)))
          (Nat.succ i))) k) x c i =
      (c + pack W (litStates Ws k x).length
          (fun j => (litStates Ws k x).getD j 0 / 2 ^ fo % 2 ^ F) * 2 ^ (W * i),
        i + (litStates Ws k x).length) := by
  induction k with
  | zero => intro x c i; simp [litStates, pack]
  | succ k ih =>
    intro x c i
    show cnd (Nat.ble x 1) (c, i) (_ : ℕ × ℕ) = _
    rw [cnd_eq]
    by_cases hx : x ≤ 1
    · have : Nat.ble x 1 = true := by rw [Nat.ble_eq]; exact hx
      simp [this, litStates, hx, pack]
    · have : Nat.ble x 1 = false := Bool.eq_false_iff.2 fun h => hx (by rw [Nat.ble_eq] at h; exact h)
      rw [this]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      have e1 : Nat.shiftRight x Ws = x / 2 ^ Ws := Nat.shiftRight_eq_div_pow x Ws
      have e2 : Nat.land (Nat.shiftRight (Nat.land x (lmask Ws)) fo) (lmask F) = x % 2 ^ Ws / 2 ^ fo % 2 ^ F := by
        show ((x &&& lmask Ws) >>> fo) &&& lmask F = _
        rw [lmask_eq, lmask_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
          Nat.and_two_pow_sub_one_eq_mod]
      have e3 : ∀ f : ℕ, Nat.shiftLeft f (Nat.mul W i) = f * 2 ^ (W * i) := fun f => Nat.shiftLeft_eq f _
      rw [e1, e2, e3]
      simp only [litStates, hx, ↓reduceIte, List.length_cons]
      rw [pack_cons]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      refine Prod.ext ?_ ?_
      · show c + _ + _ * 2 ^ (W * (i + 1)) = c + (_ + _ * 2 ^ W) * 2 ^ (W * i)
        rw [mul_add, mul_one, pow_add]
        ring
      · show i + 1 + _ = i + (_ + 1)
        omega

theorem app_pack' (W a L : ℕ) (f g : ℕ → ℕ) :
    app W a (pack W a f) (pack W L g) = pack W (a + L) (fun l => if l < a then f l else g (l - a)) := by
  show pack W a f + pack W L g <<< (W * a) = _
  rw [Nat.shiftLeft_eq]
  unfold pack
  rw [Finset.sum_range_add, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun l hl => ?_
    dsimp only
    simp only [Finset.mem_range.1 hl, ↓reduceIte]
  · refine Finset.sum_congr rfl fun l _ => ?_
    dsimp only
    have : ¬ (a + l < a) := by omega
    simp only [this, ↓reduceIte, Nat.add_sub_cancel_left]
    rw [mul_assoc, ← pow_add]
    congr 2
    ring

theorem litChunk_eq (W Ws fo F x : ℕ) :
    litChunk W Ws (lmask Ws) fo (lmask F) x =
      (pack W (litStates Ws 16 x).length (fun i => (litStates Ws 16 x).getD i 0 / 2 ^ fo % 2 ^ F),
        (litStates Ws 16 x).length) := by
  show (@Nat.rec (fun _ => ℕ → ℕ → ℕ → ℕ × ℕ) (fun _ c i => (c, i))
      (fun _ ih x c i => cnd (Nat.ble x 1) (c, i)
        (ih (Nat.shiftRight x Ws)
          (Nat.add c (Nat.shiftLeft (Nat.land (Nat.shiftRight (Nat.land x (lmask Ws)) fo) (lmask F))
            (Nat.mul W i)))
          (Nat.succ i))) 16) x 0 0 = _
  rw [litChunk_rec]
  simp

theorem fieldPackP_eq (W Ws fo F : ℕ) (lits : List ℕ) :
    fieldPackP W Ws (lmask Ws) fo (lmask F) lits =
      (pack W (allStates Ws lits).length (fun i => (allStates Ws lits).getD i 0 / 2 ^ fo % 2 ^ F),
        (allStates Ws lits).length) := by
  induction lits with
  | nil => simp [fieldPackP, allStates, pack]
  | cons x t ih =>
    show fieldPackP.fieldCons W (litChunk W Ws (lmask Ws) fo (lmask F) x)
      (fieldPackP W Ws (lmask Ws) fo (lmask F) t) = _
    rw [litChunk_eq, ih]
    have hs : allStates Ws (x :: t) = litStates Ws 16 x ++ allStates Ws t := by
      simp [allStates, List.flatMap_cons]
    refine Prod.ext ?_ ?_
    · show app W _ _ _ = _
      rw [app_pack, hs, List.length_append]
      refine pack_congr _ _ _ _ fun j hj => ?_
      split_ifs with h
      · rw [List.getD_append _ _ _ _ h]
      · rw [List.getD_append_right _ _ _ _ (by omega)]
    · show (_ : ℕ) + _ = _
      rw [hs, List.length_append]

theorem fieldPack_eq (W Ws fo F : ℕ) (lits : List ℕ) :
    fieldPack W Ws fo F lits =
      pack W (allStates Ws lits).length (fun i => (allStates Ws lits).getD i 0 / 2 ^ fo % 2 ^ F) := by
  rw [fieldPack, fieldPackP_eq]

end Robbins.Lanes
