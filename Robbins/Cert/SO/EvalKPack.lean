import Robbins.Cert.SO.EvalKSound

/-!
# The packed tables of the second-order kernel evaluator

Literals of 16 packed states (`decLit`, `litOf`), the binary tree of the lookups (`bld`, `bget`,
`depth`, `lkSt`), and `chunkCheck` against the decoded states (`chunkCheck_lall2`).
-/

namespace Robbins.Cert.SO.K

open Robbins.Cert Robbins.Cert.K

/-! ## Literals -/

/-- A literal of `W`-bit states under a leading `1` bit. -/
def litOf (W : ℕ) : List ℕ → ℕ
  | [] => 1
  | v :: vs => v + 2 ^ W * litOf W vs

theorem decLit_litOf (W : ℕ) (hW : 0 < W) (vs rest : List ℕ) (hlen : vs.length ≤ 16)
    (hv : ∀ v ∈ vs, v < 2 ^ W) : decLit W (2 ^ W - 1) (litOf W vs) rest = vs ++ rest := by
  have key : ∀ (n : ℕ) (vs : List ℕ), vs.length ≤ n → (∀ v ∈ vs, v < 2 ^ W) →
      @Nat.rec (fun _ => ℕ → List ℕ) (fun _ => rest)
        (fun _ ih x => bsel (Nat.ble x 1) rest (Nat.land x (2 ^ W - 1) :: ih (Nat.shiftRight x W))) n
        (litOf W vs) = vs ++ rest := by
    intro n
    induction n with
    | zero =>
      intro vs hl _
      have : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      rfl
    | succ n ih =>
      intro vs hl hv
      show bsel (Nat.ble (litOf W vs) 1) rest
        (Nat.land (litOf W vs) (2 ^ W - 1) :: _) = _
      rw [bsel_eq]
      cases vs with
      | nil => simp [litOf]
      | cons v vs =>
        have hvv : v < 2 ^ W := hv v (by simp)
        have hpos : ∀ l : List ℕ, 1 ≤ litOf W l := by
          intro l
          induction l with
          | nil => simp [litOf]
          | cons w ws ihw =>
            simp only [litOf]
            have := Nat.one_le_two_pow (n := W)
            nlinarith
        have hgt : ¬ (litOf W (v :: vs) ≤ 1) := by
          simp only [litOf]
          have : 2 ≤ 2 ^ W := by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
          nlinarith [hpos vs]
        have hgt' : ¬ (Nat.ble (litOf W (v :: vs)) 1 = true) := by simpa [Nat.ble_eq] using hgt
        simp only [hgt']
        have e1 : Nat.land (litOf W (v :: vs)) (2 ^ W - 1) = v := by
          rw [Nat.land_eq, Nat.and_two_pow_sub_one_eq_mod]
          simp only [litOf]
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hvv]
        have e2 : Nat.shiftRight (litOf W (v :: vs)) W = litOf W vs := by
          rw [show Nat.shiftRight (litOf W (v :: vs)) W = litOf W (v :: vs) / 2 ^ W from
            Nat.shiftRight_eq_div_pow _ _]
          simp only [litOf]
          rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hvv, zero_add]
        rw [e1, e2, ih vs (by simp at hl; omega) (fun w hw => hv w (by simp [hw]))]
        rfl
  exact key 16 vs hlen hv



/-! ## The lookup tree and the check of a table -/

theorem depth_spec (len : ℕ) (h : 1 ≤ len) : len ≤ 2 ^ depth len := by
  have hlog := Nat.lt_log2_self (n := 2 * len - 1)
  have hineq : 2 * len - 1 < 2 ^ (depth len + 1) := by
    simpa [depth] using hlog
  have hpow : 2 ^ (depth len + 1) = 2 * 2 ^ depth len := by
    simp [pow_succ, mul_comm]
  rw [hpow] at hineq
  omega

theorem bget_bld_aux1 : ∀ (n : ℕ) (l : List BT), l.length ≤ n → ∀ j,
    (pairUp l).getD j (BT.lf 0) =
      if 2 * j < l.length then BT.nd (l.getD (2 * j) (BT.lf 0)) (l.getD (2 * j + 1) (BT.lf 0))
      else BT.lf 0 := by
  intro n
  induction n with
  | zero =>
    intro l hl j
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ n ih =>
    intro l hl j
    match l with
    | [] => rfl
    | [a] =>
      show [BT.nd a (BT.lf 0)].getD j (BT.lf 0) = _
      cases j with
      | zero => simp
      | succ j => simp
    | a :: b :: l =>
      show (BT.nd a b :: pairUp l).getD j (BT.lf 0) = _
      cases j with
      | zero => simp
      | succ j =>
        simp only [List.getD_cons_succ, List.length_cons]
        rw [ih l (by simp at hl; omega) j]
        have e1 : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
        rw [e1]
        simp only [List.getD_cons_succ]
        split_ifs <;> first | rfl | omega

theorem bget_bld_aux2 (a b : BT) (k li : ℕ) :
    bget (BT.nd a b) (k + 1) li = if li / 2 ^ k % 2 = 1 then bget b k li else bget a k li := by
  show bsel (Nat.beq (Nat.land (Nat.shiftRight li k) 1) 1) (bget b k li) (bget a k li) = _
  rw [bsel_eq]
  have e : Nat.land (Nat.shiftRight li k) 1 = li / 2 ^ k % 2 := by
    rw [Nat.land_eq, Nat.and_one_is_mod]
    exact congrArg (· % 2) (Nat.shiftRight_eq_div_pow li k)
  rw [e]
  by_cases h : li / 2 ^ k % 2 = 1
  · simp [h]
  · simp [h]

theorem bget_bld_aux3 (L : List ℕ) : ∀ (k j li : ℕ),
    bget ((@Nat.rec (fun _ => List BT) (lmap BT.lf L) (fun _ ih => pairUp ih) k).getD j (BT.lf 0)) k li =
      L.getD (j * 2 ^ k + li % 2 ^ k) 0 := by
  intro k
  induction k with
  | zero =>
    intro j li
    show bget ((lmap BT.lf L).getD j (BT.lf 0)) 0 li = _
    rw [lmap_eq]
    simp only [pow_zero, mul_one, Nat.mod_one, add_zero]
    rw [show BT.lf 0 = BT.lf (0 : ℕ) from rfl, List.getD_map]
    rfl
  | succ k ih =>
    intro j li
    set T := @Nat.rec (fun _ => List BT) (lmap BT.lf L) (fun _ ih => pairUp ih) k with hT
    show bget ((pairUp T).getD j (BT.lf 0)) (k + 1) li = _
    rw [bget_bld_aux1 T.length T le_rfl j]
    have hidx : j * 2 ^ (k + 1) + li % 2 ^ (k + 1) = (2 * j + li / 2 ^ k % 2) * 2 ^ k + li % 2 ^ k := by
      rw [pow_succ, Nat.mod_mul]
      ring
    rw [hidx]
    have hb : li / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by norm_num)
    split_ifs with h
    · rw [bget_bld_aux2]
      by_cases hb1 : li / 2 ^ k % 2 = 1
      · simp only [hb1, ↓reduceIte]
        rw [ih (2 * j + 1) li]
      · have hb0 : li / 2 ^ k % 2 = 0 := by omega
        simp only [hb1, ↓reduceIte]
        rw [ih (2 * j) li, hb0, add_zero]
    · have hge : T.length ≤ 2 * j + li / 2 ^ k % 2 := by omega
      have := ih (2 * j + li / 2 ^ k % 2) li
      rw [List.getD_eq_default _ _ hge] at this
      rw [← this]
      rfl

theorem bget_bld (d : ℕ) (L : List ℕ) (hL : L.length ≤ 2 ^ d) (li : ℕ) (hli : li < 2 ^ d) :
    bget (bld d L) d li = L.getD li 0 := by
  have _ := hL
  have hb : bld d L = (@Nat.rec (fun _ => List BT) (lmap BT.lf L) (fun _ ih => pairUp ih) d).getD 0 (BT.lf 0) := by
    show @List.rec BT (fun _ => BT) (BT.lf 0) (fun a _ _ => a) _ = _
    cases (@Nat.rec (fun _ => List BT) (lmap BT.lf L) (fun _ ih => pairUp ih) d) <;> rfl
  rw [hb, bget_bld_aux3 L d 0 li, Nat.mod_eq_of_lt hli]
  simp

theorem lkSt_eq (d W : ℕ) (L : List ℕ) (hL : L.length ≤ 2 ^ d) (idx : ℕ) (hidx : idx / 16 < 2 ^ d) :
    lkSt (bld d L) d W (2 ^ W - 1) idx = L.getD (idx / 16) 0 / 2 ^ (W * (idx % 16)) % 2 ^ W := by
  unfold lkSt
  have hland : Nat.land idx 15 = idx % 16 := by
    have h : (15 : ℕ) = 2 ^ 4 - 1 := by norm_num
    rw [h, Nat.land_eq, Nat.and_two_pow_sub_one_eq_mod]
  have hshift : Nat.shiftRight idx 4 = idx / 16 := by
    simpa using Nat.shiftRight_eq_div_pow idx 4
  rw [hland, hshift]
  rw [bget_bld d L hL (idx / 16) hidx]
  have hmul : Nat.mul W (idx % 16) = W * (idx % 16) := rfl
  rw [hmul, Nat.land_eq, Nat.and_two_pow_sub_one_eq_mod]
  simp [Nat.shiftRight_eq_div_pow]


theorem chunkCheck_lall2_aux1 (W MW : ℕ) : ∀ (n : ℕ) (x : ℕ) (rest1 rest2 : List ℕ),
    (Nat.rec (fun _ => rest1 ++ rest2)
      (fun _ ih x => bsel (Nat.ble x 1) (rest1 ++ rest2) (Nat.land x MW :: ih (Nat.shiftRight x W))) n x) =
    (Nat.rec (fun _ => rest1)
      (fun _ ih x => bsel (Nat.ble x 1) rest1 (Nat.land x MW :: ih (Nat.shiftRight x W))) n x) ++ rest2 := by
  intro n
  induction n with
  | zero => intro x rest1 rest2; rfl
  | succ n ih =>
      intro x rest1 rest2
      -- Use Nat.rec_add_one via congrArg to apply to x
      -- We need to use the expanded lambda form to match ih
      have h_left := congrArg (fun f => f x) (Nat.rec_add_one
        (h0 := fun _ => rest1 ++ rest2)
        (h := fun (_ : ℕ) (ih : ℕ → List ℕ) (x : ℕ) =>
          bsel (Nat.ble x 1) (rest1 ++ rest2) (Nat.land x MW :: ih (Nat.shiftRight x W)))
        (n := n))
      have h_right := congrArg (fun f => f x) (Nat.rec_add_one
        (h0 := fun _ => rest1)
        (h := fun (_ : ℕ) (ih : ℕ → List ℕ) (x : ℕ) =>
          bsel (Nat.ble x 1) rest1 (Nat.land x MW :: ih (Nat.shiftRight x W)))
        (n := n))
      rw [h_left, h_right]
      beta_reduce
      have h_inner := ih (Nat.shiftRight x W) rest1 rest2
      rw [h_inner]
      cases Nat.ble x 1 with
      | true => simp
      | false => simp

theorem chunkCheck_lall2_aux2 (W MW x : ℕ) (rest1 rest2 : List ℕ) :
    decLit W MW x (rest1 ++ rest2) = decLit W MW x rest1 ++ rest2 := by
  unfold decLit
  exact chunkCheck_lall2_aux1 W MW 16 x rest1 rest2

theorem chunkCheck_lall2_aux3 {α : Type} (f : α → ℕ → Bool) (a1 a2 : List α) (b1 b2 : List ℕ)
    (h1 : lall2 f a1 b1 = true) (h2 : lall2 f a2 b2 = true) :
    lall2 f (a1 ++ a2) (b1 ++ b2) = true := by
  induction a1 generalizing b1 with
  | nil =>
      have hb1 : b1 = [] := by
        cases b1 with
        | nil => rfl
        | cons b l =>
            unfold lall2 at h1
            simp at h1
      subst hb1
      simp
      exact h2
  | cons a a1 ih =>
      cases b1 with
      | nil =>
          unfold lall2 at h1
          simp at h1
      | cons b b1 =>
          unfold lall2 at h1
          simp at h1
          have h_fab : f a b = true := by
            cases hfab : f a b with
            | true => rfl
            | false =>
                rw [hfab] at h1
                simp at h1
          have h_a1b1 : lall2 f a1 b1 = true := by
            rw [h_fab] at h1
            simp at h1
            exact h1
          have h_ih := ih b1 h_a1b1
          calc
            lall2 f (a :: a1 ++ a2) (b :: b1 ++ b2) = lall2 f (a :: (a1 ++ a2)) (b :: (b1 ++ b2)) := by simp
            _ = bsel (f a b) (lall2 f (a1 ++ a2) (b1 ++ b2)) false := rfl
            _ = bsel true (lall2 f (a1 ++ a2) (b1 ++ b2)) false := by rw [h_fab]
            _ = lall2 f (a1 ++ a2) (b1 ++ b2) := by simp
            _ = true := h_ih

theorem chunkCheck_lall2 {α : Type} (f : α → ℕ → Bool) (W MW : ℕ) (lits : List ℕ) (sts : List α)
    (h : chunkCheck f W MW lits sts = true) :
    lall2 f sts (lfoldr (decLit W MW) [] lits) = true := by
  induction lits generalizing sts with
  | nil =>
      unfold chunkCheck at h
      simp at h
      cases sts with
      | nil => rfl
      | cons a l =>
          dsimp [lall] at h
          simp at h
  | cons x lits ih =>
      unfold chunkCheck at h
      simp at h
      rw [bsel_eq] at h
      split at h
      next h_cond =>
        -- h_cond : lall2 f (ltake 16 sts) (decLit W MW x []) = true
        -- h : chunkCheck f W MW lits (ldrop 16 sts) = true
        have h_ih := ih (ldrop 16 sts) h
        have h_lfoldr : lfoldr (decLit W MW) [] (x :: lits) = decLit W MW x (lfoldr (decLit W MW) [] lits) := by
          unfold lfoldr; rfl
        rw [h_lfoldr]
        have h_sts : sts = ltake 16 sts ++ ldrop 16 sts := by
          rw [ltake_eq, ldrop_eq]
          exact (List.take_append_drop 16 sts).symm
        rw [h_sts]
        have h_decLit : decLit W MW x (lfoldr (decLit W MW) [] lits) =
            decLit W MW x [] ++ lfoldr (decLit W MW) [] lits := by
          calc
            decLit W MW x (lfoldr (decLit W MW) [] lits) = decLit W MW x ([] ++ lfoldr (decLit W MW) [] lits) := by simp
            _ = decLit W MW x [] ++ lfoldr (decLit W MW) [] lits := by rw [chunkCheck_lall2_aux2]
        rw [h_decLit]
        exact chunkCheck_lall2_aux3 f (ltake 16 sts) (ldrop 16 sts) (decLit W MW x []) (lfoldr (decLit W MW) [] lits) h_cond h_ih
      next =>
        -- h : false = true
        contradiction

end Robbins.Cert.SO.K
