import Robbins.Cert.SO.EvalK
import Robbins.Cert.EvalM2Eq

/-!
# The lanes step: lemmas of the scalar kernel chain, copied

The lemmas of the scalar second-order kernel chain (Robbins/Cert/SO/EvalKChain.lean, EvalKPack.lean,
EvalKVar.lean, EvalKSound.lean) that the lanes step uses, copied with their
proofs: those files import the specification Robbins/Cert/SO/Spec.lean, whose names (`SC`, ...)
shadow the kernel names inside the namespace `Robbins.Cert.SO.L` of Robbins/Cert/SO/LanesSound.lean.
-/

namespace Robbins.Cert.SO.L

open Robbins.Cert Robbins.Cert.K Robbins.Cert.SO.K

theorem lget_eq (l : List ℕ) (i : ℕ) : lget l i = l.getD i 0 := by
  simp [lget, ldrop_eq, hd_eq]

theorem slopes_eq_aux1 (f : ℕ → ℕ) (m : ℕ) :
    (List.range (m + 1)).map f = f 0 :: (List.range m).map (fun i => f (i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.map_singleton]
      -- Goal: List.map f (List.range (m+1)) ++ [f (m+1)] = f 0 :: List.map (fun i => f (i+1)) (List.range (m+1))
      rw [ih]
      -- Goal: (f 0 :: List.map (fun i => f (i+1)) (List.range m)) ++ [f (m+1)] = f 0 :: List.map (fun i => f (i+1)) (List.range (m+1))
      rw [List.cons_append]
      -- Goal: f 0 :: (List.map (fun i => f (i+1)) (List.range m) ++ [f (m+1)]) = f 0 :: List.map (fun i => f (i+1)) (List.range (m+1))
      rw [List.range_succ, List.map_append, List.map_singleton]

theorem slopes_eq (m st : ℕ) :
    slopes m st = (List.range m).map fun l => st / 2 ^ (48 * (l + 1)) % 2 ^ 48 := by
  induction m generalizing st with
  | zero =>
      simp [slopes]
  | succ m ih =>
      simp only [slopes, slopes.slopes2]
      have h_first : (Nat.shiftRight st 48).land M48 = st / 2 ^ 48 % 2 ^ 48 := by
        change (st >>> 48).land M48 = st / 2 ^ 48 % 2 ^ 48
        rw [Nat.shiftRight_eq_div_pow, M48]
        exact Nat.and_two_pow_sub_one_eq_mod (x := st / 2 ^ 48) (n := 48)
      rw [h_first]
      have h_rec : Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
        (fun _ ih' x' => (Nat.shiftRight x' 48).land M48 :: ih' (Nat.shiftRight x' 48)) m (Nat.shiftRight st 48) =
        slopes m (Nat.shiftRight st 48) := by
        simp [slopes, slopes.slopes2]
      rw [h_rec]
      rw [ih (Nat.shiftRight st 48)]
      have h_map_eq : (fun (l : ℕ) => (st / 2 ^ 48) / 2 ^ (48 * (l + 1)) % 2 ^ 48) =
          (fun (l : ℕ) => st / 2 ^ (48 * (l + 1 + 1)) % 2 ^ 48) := by
        ext l
        calc
          (st / 2 ^ 48) / 2 ^ (48 * (l + 1)) % 2 ^ 48
              = st / ((2 ^ 48) * (2 ^ (48 * (l + 1)))) % 2 ^ 48 := by
            rw [Nat.div_div_eq_div_mul]
          _ = st / (2 ^ (48 + 48 * (l + 1))) % 2 ^ 48 := by rw [← pow_add, add_comm]
          _ = st / (2 ^ (48 * (l + 1 + 1))) % 2 ^ 48 := by
            rw [show (48 : ℕ) + 48 * (l + 1) = 48 * (l + 1 + 1) by omega]
      have h_target : (st / 2 ^ 48 % 2 ^ 48) :: List.map (fun l => (st / 2 ^ 48) / 2 ^ (48 * (l + 1)) % 2 ^ 48) (List.range m) =
          List.map (fun l => st / 2 ^ (48 * (l + 1)) % 2 ^ 48) (List.range (m + 1)) := by
        rw [h_map_eq]
        let f : ℕ → ℕ := fun l => st / 2 ^ (48 * (l + 1)) % 2 ^ 48
        simpa [f] using (slopes_eq_aux1 f m).symm
      simpa [Nat.shiftRight_eq_div_pow] using h_target

theorem chunkCheck_cons {α : Type} (f : α → ℕ → Bool) (W MW x : ℕ) (xs : List ℕ) (sts : List α) :
    chunkCheck f W MW (x :: xs) sts =
      (lall2 f (ltake 16 sts) (decLit W MW x []) && chunkCheck f W MW xs (ldrop 16 sts)) := by
  change bsel (lall2 f (ltake 16 sts) (decLit W MW x [])) (chunkCheck f W MW xs (ldrop 16 sts)) false = _
  rw [bsel_eq]
  split_ifs with h <;> simp [h]

theorem chunkCheck_nil {α : Type} (f : α → ℕ → Bool) (W MW : ℕ) (sts : List α) :
    chunkCheck f W MW [] sts = sts.isEmpty := by
  cases sts <;> rfl

theorem lall2_iff {α : Type} (f : α → ℕ → Bool) (l1 : List α) (l2 : List ℕ) :
    lall2 f l1 l2 = true ↔ l1.length = l2.length ∧
      ∀ i (h1 : i < l1.length) (h2 : i < l2.length), f l1[i] l2[i] = true := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => simp [lall2]
    | cons b l2 => simp [lall2]
  | cons a l1 ih =>
    cases l2 with
    | nil => simp [lall2]
    | cons b l2 =>
      change bsel (f a b) (lall2 f l1 l2) false = true ↔ _
      rw [bsel_eq]
      constructor
      · intro h
        split_ifs at h with hab
        obtain ⟨hl, hi⟩ := (ih l2).1 h
        refine ⟨by simp [hl], fun i h1 h2 => ?_⟩
        cases i with
        | zero => exact hab
        | succ i => exact hi i (by simpa using h1) (by simpa using h2)
      · rintro ⟨hl, hi⟩
        have hab : f a b = true := hi 0 (by simp) (by simp)
        simp only [hab, ↓reduceIte]
        exact (ih l2).2 ⟨by simpa using hl, fun i h1 h2 => by
          exact hi (i + 1) (by simpa using h1) (by simpa using h2)⟩

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

theorem decLit_append (W MW x : ℕ) (rest : List ℕ) :
    decLit W MW x rest = decLit W MW x [] ++ rest := by
  simpa using chunkCheck_lall2_aux2 W MW x [] rest

theorem decLit_length_le_aux1 (W MW : ℕ) : ∀ (n x : ℕ),
    (@Nat.rec (fun _ => ℕ → List ℕ) (fun _ => [])
      (fun _ ih x => bsel (Nat.ble x 1) [] (Nat.land x MW :: ih (Nat.shiftRight x W))) n x).length ≤ n := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    show (bsel (Nat.ble x 1) [] (Nat.land x MW :: _)).length ≤ n + 1
    rw [bsel_eq]
    split_ifs
    · simp
    · simpa using ih (Nat.shiftRight x W)

theorem decLit_length_le (W MW x : ℕ) : (decLit W MW x []).length ≤ 16 := by
  exact decLit_length_le_aux1 W MW 16 x

theorem decLit_getD_aux1 (W : ℕ) : ∀ (n x i : ℕ),
    i < (@Nat.rec (fun _ => ℕ → List ℕ) (fun _ => [])
      (fun _ ih x => bsel (Nat.ble x 1) [] (Nat.land x (2 ^ W - 1) :: ih (Nat.shiftRight x W))) n x).length →
    (@Nat.rec (fun _ => ℕ → List ℕ) (fun _ => [])
      (fun _ ih x => bsel (Nat.ble x 1) [] (Nat.land x (2 ^ W - 1) :: ih (Nat.shiftRight x W))) n x).getD i 0 =
      x / 2 ^ (W * i) % 2 ^ W := by
  intro n
  induction n with
  | zero => intro x i hi; simp at hi
  | succ n ih =>
    intro x i hi
    change i < (bsel (Nat.ble x 1) [] (Nat.land x (2 ^ W - 1) :: _)).length at hi
    show (bsel (Nat.ble x 1) [] (Nat.land x (2 ^ W - 1) :: _)).getD i 0 = _
    rw [bsel_eq] at hi ⊢
    split_ifs at hi ⊢
    · simp at hi
    · cases i with
      | zero =>
        simp [Nat.land_eq, Nat.and_two_pow_sub_one_eq_mod]
      | succ i =>
        simp only [List.length_cons] at hi
        simp only [List.getD_cons_succ]
        rw [ih _ i (by omega), show Nat.shiftRight x W = x / 2 ^ W from Nat.shiftRight_eq_div_pow x W,
          Nat.div_div_eq_div_mul, ← pow_add]
        congr 3
        ring

theorem decLit_getD (W x i : ℕ) (hW : 0 < W) (hi : i < (decLit W (2 ^ W - 1) x []).length) :
    (decLit W (2 ^ W - 1) x []).getD i 0 = x / 2 ^ (W * i) % 2 ^ W := by
  have _ := hW
  exact decLit_getD_aux1 W 16 x i hi

theorem tupR_succ_rec {α : Type} (k : ℕ) (xs pre : List α) :
    @List.rec α (fun _ => List α → List (List α)) (fun _ => [])
        (fun x _ r pre => tupR.tupR1 x (tupR k (lapp pre [x])) (r (lapp pre [x]))) xs pre =
      (@List.rec α (fun _ => List α → List (List (List α))) (fun _ => [])
        (fun x _ r pre => lmap (fun t => x :: t) (tupR k (lapp pre [x])) :: r (lapp pre [x])) xs pre).flatten := by
  induction xs generalizing pre with
  | nil => rfl
  | cons x xs ih =>
    show tupR.tupR1 x _ _ = (_ :: _).flatten
    rw [List.flatten_cons, ← ih]
    simp only [tupR.tupR1, lapp_eq]

theorem tupR_succ {α : Type} (k : ℕ) (xs : List α) : tupR (k + 1) xs = (tupG k xs).flatten :=
  tupR_succ_rec k xs []

theorem tupG_rec_append {α : Type} (k : ℕ) (xs ys pre : List α) :
    @List.rec α (fun _ => List α → List (List (List α))) (fun _ => [])
        (fun x _ r pre => lmap (fun t => x :: t) (tupR k (lapp pre [x])) :: r (lapp pre [x])) (xs ++ ys) pre =
      @List.rec α (fun _ => List α → List (List (List α))) (fun _ => [])
        (fun x _ r pre => lmap (fun t => x :: t) (tupR k (lapp pre [x])) :: r (lapp pre [x])) xs pre ++
      @List.rec α (fun _ => List α → List (List (List α))) (fun _ => [])
        (fun x _ r pre => lmap (fun t => x :: t) (tupR k (lapp pre [x])) :: r (lapp pre [x])) ys (pre ++ xs) := by
  induction xs generalizing pre with
  | nil => simp
  | cons x xs ih =>
    show _ :: _ = (_ :: _) ++ _
    rw [List.cons_append]
    congr 1
    refine (ih _).trans ?_
    rw [lapp_eq]
    simp

theorem tupG_snoc {α : Type} (k : ℕ) (xs : List α) (y : α) :
    tupG k (xs ++ [y]) = tupG k xs ++ [(tupR k (xs ++ [y])).map (y :: ·)] := by
  unfold tupG
  rw [tupG_rec_append]
  congr 1
  show [lmap _ (tupR k (lapp ([] ++ xs) [y]))] = _
  rw [lmap_eq, lapp_eq, List.nil_append]

theorem tupG_append {α : Type} (k : ℕ) (xs ys : List α) :
    ∃ R, tupG k (xs ++ ys) = tupG k xs ++ R := by
  unfold tupG
  rw [tupG_rec_append]
  exact ⟨_, rfl⟩

theorem tupG_length {α : Type} (k : ℕ) (xs : List α) : (tupG k xs).length = xs.length := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs y ih => rw [tupG_snoc]; simp [ih]

theorem tupR_snoc {α : Type} (k : ℕ) (xs : List α) (y : α) :
    tupR (k + 1) (xs ++ [y]) = tupR (k + 1) xs ++ (tupR k (xs ++ [y])).map (y :: ·) := by
  rw [tupR_succ, tupR_succ, tupG_snoc]
  simp

theorem tupR_zero {α : Type} (xs : List α) : tupR 0 xs = [[]] := rfl

theorem tupR_nil {α : Type} (k : ℕ) : tupR (k + 1) ([] : List α) = [] := rfl

theorem tupR_append {α : Type} (k : ℕ) (xs ys : List α) :
    ∃ R, tupR (k + 1) (xs ++ ys) = tupR (k + 1) xs ++ R := by
  obtain ⟨R, hR⟩ := tupG_append k xs ys
  exact ⟨R.flatten, by rw [tupR_succ, tupR_succ, hR, List.flatten_append]⟩

theorem tupR_length {α : Type} (m : ℕ) (xs : List α) :
    (tupR m xs).length = (xs.length + m - 1).choose m := by
  cases m with
  | zero => simp [tupR_zero]
  | succ k =>
    induction k generalizing xs with
    | zero =>
      induction xs using List.reverseRecOn with
      | nil => rfl
      | append_singleton xs y ih =>
        rw [tupR_snoc, List.length_append, ih, List.length_map, tupR_zero]
        simp
    | succ k ihk =>
      induction xs using List.reverseRecOn with
      | nil => simp [tupR_nil]
      | append_singleton xs y ih =>
        rw [tupR_snoc, List.length_append, ih, List.length_map, ihk]
        simp only [List.length_append, List.length_singleton]
        have e1 : xs.length + 1 + (k + 1) - 1 = (xs.length + k) + 1 := by omega
        have e2 : xs.length + (k + 1 + 1) - 1 = xs.length + k + 1 := by omega
        have e3 : xs.length + 1 + (k + 1 + 1) - 1 = (xs.length + k + 1) + 1 := by omega
        rw [e1, e2, e3, Nat.choose_succ_succ (xs.length + k + 1) (k + 1)]
        ring

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

theorem lmapIdx_snoc {α β : Type} (f : ℕ → α → β) (k : ℕ) (xs : List α) (y : α) :
    lmapIdx f k (xs ++ [y]) = lmapIdx f k xs ++ [f (k + xs.length) y] := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
    show f k x :: lmapIdx f (k + 1) (xs ++ [y]) = (f k x :: lmapIdx f (k + 1) xs) ++ _
    rw [ih, List.cons_append, List.length_cons, show k + 1 + xs.length = k + (xs.length + 1) by ring]

theorem lmapIdx_congr {α β : Type} (f f' : ℕ → α → β) (k : ℕ) (xs : List α)
    (h : ∀ j, j < k + xs.length → ∀ a, f j a = f' j a) : lmapIdx f k xs = lmapIdx f' k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
    show f k x :: lmapIdx f (k + 1) xs = f' k x :: lmapIdx f' (k + 1) xs
    rw [h k (by simp) x, ih (k + 1) (fun j hj a => h j (by simp at hj ⊢; omega) a)]

theorem states_tupG (f : List SR → Pre) (k : ℕ) (recs : List SR) (a : SR) :
    states recs (lmap (lmap (fun tp => f (lrevOnto tp []))) (tupG k recs)) =
      (tupR (k + 2) recs).map (fun tp => (f tp.tail.reverse, tp.headD a)) := by
  induction recs using List.reverseRecOn with
  | nil => rfl
  | append_singleton ys y ih =>
    unfold states at ih ⊢
    have hPG : lmap (lmap (fun tp => f (lrevOnto tp []))) (tupG k (ys ++ [y])) =
        lmap (lmap (fun tp => f (lrevOnto tp []))) (tupG k ys) ++
          [(tupR k (ys ++ [y])).map (fun tp => f (y :: tp).reverse)] := by
      rw [tupG_snoc, lmap_eq, lmap_eq, List.map_append, List.map_singleton, lmap_eq, List.map_map]
      congr 2
      refine List.map_congr_left (fun tp _ => ?_)
      simp [lrevOnto_eq]
    have hlen : (lmap (lmap (fun tp => f (lrevOnto tp []))) (tupG k ys)).length = ys.length := by
      rw [lmap_eq, List.length_map, tupG_length]
    rw [hPG, lmapIdx_snoc, lflat_eq, List.flatten_append, ← lflat_eq]
    rw [lmapIdx_congr _ (fun j r => lmap (fun p => (p, r))
      (lflat (ltake (Nat.succ j) (lmap (lmap (fun tp => f (lrevOnto tp []))) (tupG k ys))))) 0 ys
      (fun j hj r => by
        rw [ltake_eq, ltake_eq, List.take_append_of_le_length (by rw [hlen]; omega)])]
    rw [ih, tupR_snoc, List.map_append]
    congr 1
    have hfun : lmap (fun tp => f (lrevOnto tp [])) = List.map (fun tp => f (lrevOnto tp [])) :=
      funext (lmap_eq _)
    rw [← hPG]
    simp only [hfun, lmap_eq, lflat_eq, ltake_eq, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [List.take_of_length_le (by simp [tupG_length])]
    rw [← List.map_flatten, ← tupR_succ, List.map_map, List.map_map]
    refine List.map_congr_left (fun tp _ => ?_)
    simp [lrevOnto_eq]

theorem lkF_eq (f : ℕ → SV) (idx : ℕ) : lkF f idx = f idx := by
  cases idx <;> rfl

theorem lall_iff {α : Type} (p : α → Bool) (l : List α) : lall p l = true ↔ ∀ v ∈ l, p v = true := by
  induction l with
  | nil => simp [lall]
  | cons a l ih =>
    show bsel (p a) (lall p l) false = true ↔ _
    rw [bsel_eq]
    by_cases ha : p a = true
    · simp [ha, ih]
    · simp [ha]

end Robbins.Cert.SO.L
