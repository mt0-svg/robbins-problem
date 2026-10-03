import Mathlib
import Robbins.Lanes.Ops

/-!
# Packed lanes: `pack` and the lanewise lemmas

`pack W L f = Σ_{l < L} f l 2 ^ (W l)`: `L` lanes of `W` bits. Sums, truncated differences under
lanewise `≤` and constant multiples of packs are lanewise; `&&&`, `^^^` and `|||` are lanewise
for lanes below `2 ^ W`; a lane is read back by a shift and a mask; the guard-bit compare and the
zero test. The kernel constants of Robbins/Lanes/Ops.lean (`ones`, `guard`, `lmask`, `bcast`)
are packs.

The lemmas `pack_succ`, `pack_congr`, `pack_add`, `pack_sub`, `pack_const_mul`, `pack_lt`, `pack_div_mod`,
`testBit_pack`, `land_pack`, `xor_pack`, `land_two_pow`, `land_guard`, `pack_inj`,
`land_guard_eq_iff`, `zero_mask`, `pack_mul_pow`, `ones_div`, with the guard word written as a
pack, `lor_pack`, and the bridges to the kernel constants.
-/

namespace Robbins.Lanes

/-- `L` lanes of `W` bits: `pack W L f = Σ_{l < L} f l 2 ^ (W l)`. -/
def pack (W L : ℕ) (f : ℕ → ℕ) : ℕ := ∑ l ∈ Finset.range L, f l * 2 ^ (W * l)

theorem pack_zero (W : ℕ) (f : ℕ → ℕ) : pack W 0 f = 0 := by
  simp [pack]

theorem pack_succ (W L : ℕ) (f : ℕ → ℕ) : pack W (L + 1) f = pack W L f + f L * 2 ^ (W * L) := by
  unfold pack
  rw [Finset.sum_range_succ]

theorem pack_congr (W L : ℕ) (f g : ℕ → ℕ) (h : ∀ l < L, f l = g l) : pack W L f = pack W L g := by
  unfold pack
  refine Finset.sum_congr rfl ?_
  intro l hl
  rw [h l (Finset.mem_range.1 hl)]

theorem pack_add (W L : ℕ) (f g : ℕ → ℕ) : pack W L f + pack W L g = pack W L (fun l => f l + g l) := by
  unfold pack
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← add_mul]

theorem pack_sub (W L : ℕ) (f g : ℕ → ℕ) (h : ∀ l < L, f l ≤ g l) :
    pack W L g - pack W L f = pack W L (fun l => g l - f l) := by
  apply Nat.sub_eq_of_eq_add
  calc pack W L g = pack W L (fun l => (g l - f l) + f l) := by
        apply pack_congr W L g (fun l => (g l - f l) + f l)
        intro l hl
        rw [Nat.sub_add_cancel (h l hl)]
    _ = pack W L (fun l => g l - f l) + pack W L f := by rw [← pack_add]

theorem pack_const_mul (W L k : ℕ) (f : ℕ → ℕ) : k * pack W L f = pack W L (fun l => k * f l) := by
  simp [pack, Finset.mul_sum, mul_assoc]

/-- Lanes below `2^W` pack below `2^(W L)`. -/
theorem pack_lt (W L : ℕ) (f : ℕ → ℕ) (h : ∀ l < L, f l < 2 ^ W) : pack W L f < 2 ^ (W * L) := by
  induction L with
  | zero => simp [pack]
  | succ L ih =>
    rw [pack_succ]
    have h1 := ih (fun l hl => h l (Nat.lt_succ_of_lt hl))
    have h2 : f L + 1 ≤ 2 ^ W := h L (Nat.lt_succ_self L)
    have h3 : 2 ^ (W * (L + 1)) = 2 ^ W * 2 ^ (W * L) := by
      rw [mul_add, mul_one, pow_add, mul_comm]
    rw [h3]
    calc pack W L f + f L * 2 ^ (W * L) < 2 ^ (W * L) + f L * 2 ^ (W * L) := by omega
      _ = (f L + 1) * 2 ^ (W * L) := by ring
      _ ≤ 2 ^ W * 2 ^ (W * L) := Nat.mul_le_mul_right _ h2

/-- Lane `l` of a packed number with lanes below `2^W` is read back by a shift and a mask. -/
theorem pack_div_mod (W L : ℕ) (f : ℕ → ℕ) (h : ∀ l < L, f l < 2 ^ W) (l : ℕ) (hl : l < L) :
    pack W L f / 2 ^ (W * l) % 2 ^ W = f l := by
  induction L with
  | zero => omega
  | succ L ih =>
    rw [pack_succ]
    have hpos : 0 < 2 ^ (W * l) := Nat.pos_of_ne_zero (by positivity)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hlt | heq
    · have hih := ih (fun m hm => h m (Nat.lt_succ_of_lt hm)) hlt
      have hsplit : 2 ^ (W * L) = 2 ^ (W * l) * (2 ^ W * 2 ^ (W * (L - l - 1))) := by
        rw [← pow_add, ← pow_add]
        congr 1
        have : L = l + 1 + (L - l - 1) := by omega
        conv_lhs => rw [this]
        ring
      rw [hsplit, show f L * (2 ^ (W * l) * (2 ^ W * 2 ^ (W * (L - l - 1)))) =
          f L * (2 ^ W * 2 ^ (W * (L - l - 1))) * 2 ^ (W * l) by ring, Nat.add_mul_div_right _ _ hpos,
        show f L * (2 ^ W * 2 ^ (W * (L - l - 1))) = 2 ^ W * (f L * 2 ^ (W * (L - l - 1))) by ring,
        Nat.add_mul_mod_self_left, hih]
    · subst heq
      have hA := pack_lt W l f (fun m hm => h m (Nat.lt_succ_of_lt hm))
      rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hA, zero_add]
      exact Nat.mod_eq_of_lt (h l (Nat.lt_succ_self l))

/-- Bit `n` of a packed number is bit `n % W` of lane `n / W` (lanes below `2^W`). -/
theorem testBit_pack (W L : ℕ) (f : ℕ → ℕ) (hW : 0 < W) (h : ∀ l < L, f l < 2 ^ W) (n : ℕ) :
    (pack W L f).testBit n = if n / W < L then (f (n / W)).testBit (n % W) else false := by
  split_ifs with hn
  · have hmod : n % W < W := Nat.mod_lt _ hW
    have e : n = n % W + W * (n / W) := by rw [Nat.add_comm, Nat.div_add_mod]
    rw [← pack_div_mod W L f h (n / W) hn, Nat.testBit_mod_two_pow, decide_eq_true hmod, Bool.true_and,
      Nat.testBit_div_two_pow, ← e]
  · have hle : W * L ≤ n := by
      have := (Nat.le_div_iff_mul_le hW).1 (not_lt.1 hn)
      linarith [mul_comm L W]
    exact Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le (pack_lt W L f h) (Nat.pow_le_pow_right (by norm_num) hle))

/-- `&&&` of two packed numbers is lane by lane. -/
theorem land_pack (W L : ℕ) (f g : ℕ → ℕ) (hW : 0 < W) (hf : ∀ l < L, f l < 2 ^ W)
    (hg : ∀ l < L, g l < 2 ^ W) : pack W L f &&& pack W L g = pack W L (fun l => f l &&& g l) := by
  have hfg : ∀ l < L, (f l &&& g l) < 2 ^ W := fun l hl => Nat.and_lt_two_pow _ (hg l hl)
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_land, testBit_pack W L f hW hf, testBit_pack W L g hW hg, testBit_pack W L _ hW hfg]
  split_ifs <;> simp

/-- `^^^` of two packed numbers is lane by lane. -/
theorem xor_pack (W L : ℕ) (f g : ℕ → ℕ) (hW : 0 < W) (hf : ∀ l < L, f l < 2 ^ W)
    (hg : ∀ l < L, g l < 2 ^ W) : pack W L f ^^^ pack W L g = pack W L (fun l => f l ^^^ g l) := by
  have hfg : ∀ l < L, (f l ^^^ g l) < 2 ^ W := fun l hl => Nat.xor_lt_two_pow (hf l hl) (hg l hl)
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_xor, testBit_pack W L f hW hf, testBit_pack W L g hW hg, testBit_pack W L _ hW hfg]
  split_ifs <;> simp [Nat.testBit_xor]

/-- `|||` of two packed numbers is lane by lane. -/
theorem lor_pack (W L : ℕ) (f g : ℕ → ℕ) (hW : 0 < W) (hf : ∀ l < L, f l < 2 ^ W)
    (hg : ∀ l < L, g l < 2 ^ W) : pack W L f ||| pack W L g = pack W L (fun l => f l ||| g l) := by
  have hfg : ∀ l < L, (f l ||| g l) < 2 ^ W := fun l hl => Nat.or_lt_two_pow (hf l hl) (hg l hl)
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_lor, testBit_pack W L f hW hf, testBit_pack W L g hW hg, testBit_pack W L _ hW hfg]
  split_ifs <;> simp

/-- The top bit of a `W`-bit number, masked: `2^(W-1)` if the number is at least `2^(W-1)`, else `0`. -/
theorem land_two_pow (W z : ℕ) (hW : 0 < W) (hz : z < 2 ^ W) :
    z &&& 2 ^ (W - 1) = if 2 ^ (W - 1) ≤ z then 2 ^ (W - 1) else 0 := by
  have hp : 2 ^ W = 2 ^ (W - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hW]
  have hbit : z.testBit (W - 1) = decide (2 ^ (W - 1) ≤ z) := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have h2 : z / 2 ^ (W - 1) < 2 := (Nat.div_lt_iff_lt_mul (by positivity)).2 (by rw [mul_comm, ← hp]; exact hz)
    by_cases hc : 2 ^ (W - 1) ≤ z
    · have : 1 ≤ z / 2 ^ (W - 1) := (Nat.le_div_iff_mul_le (by positivity)).2 (by simpa using hc)
      simp [hc, Nat.mod_eq_of_lt h2]; omega
    · have : z / 2 ^ (W - 1) = 0 := Nat.div_eq_of_lt (not_le.1 hc)
      simp [hc, this]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land, Nat.testBit_two_pow]
  by_cases hi : W - 1 = i
  · subst hi
    split_ifs with hc <;> simp [hbit, hc]
  · split_ifs <;> simp [hi]

/-- Masking with the guard word keeps the top bit of every lane. -/
theorem land_guard (W L : ℕ) (f : ℕ → ℕ) (hW : 0 < W) (h : ∀ l < L, f l < 2 ^ W) :
    pack W L f &&& pack W L (fun _ => 2 ^ (W - 1)) =
      pack W L (fun l => if 2 ^ (W - 1) ≤ f l then 2 ^ (W - 1) else 0) := by
  have hg : ∀ l < L, (fun _ => 2 ^ (W - 1)) l < 2 ^ W := fun _ _ =>
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [land_pack W L f _ hW h hg]
  exact pack_congr W L _ _ fun l hl => land_two_pow W (f l) hW (h l hl)

/-- Packing lanes below `2^W` is injective on the first `L` lanes. -/
theorem pack_inj (W L : ℕ) (f g : ℕ → ℕ) (hf : ∀ l < L, f l < 2 ^ W) (hg : ∀ l < L, g l < 2 ^ W) :
    pack W L f = pack W L g ↔ ∀ l < L, f l = g l := by
  constructor
  · intro e l hl
    rw [← pack_div_mod W L f hf l hl, ← pack_div_mod W L g hg l hl, e]
  · exact pack_congr W L f g

/-- The masked packed number equals the guard word iff every lane has its top bit set. -/
theorem land_guard_eq_iff (W L : ℕ) (f : ℕ → ℕ) (hW : 0 < W) (h : ∀ l < L, f l < 2 ^ W) :
    pack W L f &&& pack W L (fun _ => 2 ^ (W - 1)) = pack W L (fun _ => 2 ^ (W - 1)) ↔
      ∀ l < L, 2 ^ (W - 1) ≤ f l := by
  have hlt : 2 ^ (W - 1) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hne : 2 ^ (W - 1) ≠ 0 := by positivity
  rw [land_guard W L f hW h, pack_inj W L _ _ (fun l _ => by split_ifs <;> omega) (fun _ _ => hlt)]
  refine forall_congr' fun l => imp_congr_right fun _ => ?_
  split_ifs with hc
  · simp [hc]
  · simp only [hc, iff_false]
    exact fun e => hne e.symm

/-- The zero test of every lane: add `2^(W-1) - 1` to lanes below `2^(W-1)` and mask with the guard word;
    a lane is left `0` exactly when it was `0`. -/
theorem zero_mask (W L : ℕ) (t : ℕ → ℕ) (hW : 2 ≤ W) (ht : ∀ l < L, t l < 2 ^ (W - 1)) :
    (pack W L t + (pack W L (fun _ => 2 ^ (W - 1)) - pack W L (fun _ => 1))) &&&
        pack W L (fun _ => 2 ^ (W - 1)) =
      pack W L (fun l => if t l = 0 then 0 else 2 ^ (W - 1)) := by
  have h1 : 1 ≤ 2 ^ (W - 1) := Nat.one_le_two_pow
  have hsub : pack W L (fun _ => 2 ^ (W - 1)) - pack W L (fun _ => 1) =
      pack W L (fun _ => 2 ^ (W - 1) - 1) :=
    pack_sub W L (fun _ => 1) (fun _ => 2 ^ (W - 1)) fun _ _ => h1
  have hp : 2 ^ W = 2 ^ (W - 1) + 2 ^ (W - 1) := by
    rw [← two_mul, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ W)]
  rw [hsub, pack_add, land_guard W L _ (by omega) fun l hl => by
    have := ht l hl
    show t l + (2 ^ (W - 1) - 1) < 2 ^ W
    omega]
  refine pack_congr W L _ _ fun l hl => ?_
  have := ht l hl
  split_ifs <;> omega

/-- Multiplying by `2^(W s)` shifts the lanes up by `s`. -/
theorem pack_mul_pow (W L s : ℕ) (f : ℕ → ℕ) :
    pack W L f * 2 ^ (W * s) = pack W (L + s) (fun l => if s ≤ l then f (l - s) else 0) := by
  unfold pack
  rw [add_comm L s, Finset.sum_range_add, Finset.sum_mul]
  beta_reduce
  have h0 : ∑ x ∈ Finset.range s, (if s ≤ x then f (x - s) else 0) * 2 ^ (W * x) = 0 :=
    Finset.sum_eq_zero fun l hl => by
      have : ¬ s ≤ l := by simp at hl; omega
      simp [this]
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [le_add_iff_nonneg_right, zero_le, ite_true, Nat.add_sub_cancel_left]
  rw [mul_assoc, ← pow_add, mul_add, add_comm (W * l)]

/-- `(2^(W L) - 1) / (2^W - 1)` is the word with `1` in every lane. -/
theorem ones_div (W L : ℕ) (hW : 0 < W) : (2 ^ (W * L) - 1) / (2 ^ W - 1) = pack W L (fun _ => 1) := by
  have h2 : 2 ≤ 2 ^ W := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
  have hg : pack W L (fun _ => 1) = ∑ l ∈ Finset.range L, (2 ^ W) ^ l := by
    unfold pack
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [one_mul, pow_mul]
  rw [hg, Nat.geomSum_eq h2, pow_mul]

/-! ## The kernel constants of Ops.lean -/

theorem lmask_eq (W : ℕ) : lmask W = 2 ^ W - 1 := by
  show 1 <<< W - 1 = _
  rw [Nat.shiftLeft_eq, one_mul]

theorem ones_eq (W L : ℕ) (hW : 0 < W) : ones W L = pack W L (fun _ => 1) := by
  rw [← ones_div W L hW]
  show (1 <<< (W * L) - 1) / (1 <<< W - 1) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul, one_mul]

theorem guard_eq (W L : ℕ) (hW : 0 < W) : guard W L = pack W L (fun _ => 2 ^ (W - 1)) := by
  show ones W L <<< (W - 1) = _
  rw [Nat.shiftLeft_eq, ones_eq W L hW, mul_comm, pack_const_mul]
  simp

theorem bcast_eq (W L c : ℕ) (hW : 0 < W) : bcast W L c = pack W L (fun _ => c) := by
  show c * ones W L = _
  rw [ones_eq W L hW, pack_const_mul]
  simp

end Robbins.Lanes
