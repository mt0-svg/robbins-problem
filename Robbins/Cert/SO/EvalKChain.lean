import Robbins.Cert.EvalM2Eq
import Robbins.Cert.SO.EvalKPack
import Robbins.Cert.SO.EvalKDefs

/-!
# Decoding the claimed tables, the check of time `n`, the chain

The claimed tables `T_1, ..., T_n` of a run (lists of literals of 16 packed states, the format of
Robbins/Cert/SO/EvalK.lean) form a `ChainSO` when every step `t < n` passes `checkStep` and the
table of time `n` passes `checkLast`. A step is checked by several kernel checks `checkRange` on
ranges of literals that cover the table (`checkRange_join`, `checkStep_of_checkRange`).

Here: the decoding of the literals (`chunkCheck_aligned`), the sorted tuples and their rank
(`tupR_getD_rank`, `rank_lt`), and `checkLast_sound` (the table of time `n`, section 4). The steps
(`checkStep_sound`, `chainSO_spec`) are in Robbins/Cert/SO/EvalKStep.lean, and
`le_v_of_chainSO` (Robbins/Cert/SO/EvalKMain.lean) gives the bound
`uh_1 (cnt_1, ..., cnt_1) / D ≤ v n` with `D = 2 ^ 36`.
-/

namespace Robbins.Cert.SO.K

open Robbins.Cert Robbins.Cert.K

/-! ## Ranges of literals -/

theorem lall2_triv {α : Type} (f : α → ℕ → Bool) (l1 : List α) (l2 : List ℕ)
    (h : lall2 f l1 l2 = true) : lall2 (fun _ _ => true) l1 l2 = true := by
  induction l1 generalizing l2 with
  | nil => exact h
  | cons a l1 ih =>
    cases l2 with
    | nil => exact h
    | cons b l2 =>
      change bsel (f a b) (lall2 f l1 l2) false = true at h
      change bsel true (lall2 (fun _ _ => true) l1 l2) false = true
      rw [bsel_eq] at h ⊢
      split_ifs at h
      exact ih l2 h

theorem rangeLoop_cons {α : Type} (f : α → ℕ → Bool) (W MW lo hi x : ℕ) (xs : List ℕ)
    (sts : List α) (j : ℕ) :
    rangeLoop f W MW lo hi (x :: xs) sts j =
      ((if lo ≤ j ∧ j < hi then lall2 f (ltake 16 sts) (decLit W MW x [])
        else lall2 (fun _ _ => true) (ltake 16 sts) (decLit W MW x [])) &&
        rangeLoop f W MW lo hi xs (ldrop 16 sts) (j + 1)) := by
  change bsel (bsel (Nat.ble lo j) (Nat.blt j hi) false)
      (bsel (lall2 f (ltake 16 sts) (decLit W MW x [])) (rangeLoop f W MW lo hi xs (ldrop 16 sts) (j + 1))
        false)
      (bsel (lall2 (fun _ _ => true) (ltake 16 sts) (decLit W MW x []))
        (rangeLoop f W MW lo hi xs (ldrop 16 sts) (j + 1)) false) = _
  simp only [bsel_eq]
  by_cases h1 : lo ≤ j <;> by_cases h2 : j < hi <;> simp [h1, h2, Nat.ble_eq, Nat.blt_eq]

theorem rangeLoop_nil {α : Type} (f : α → ℕ → Bool) (W MW lo hi : ℕ) (sts : List α) (j : ℕ) :
    rangeLoop f W MW lo hi [] sts j = sts.isEmpty := by
  cases sts <;> rfl

theorem chunkCheck_cons {α : Type} (f : α → ℕ → Bool) (W MW x : ℕ) (xs : List ℕ) (sts : List α) :
    chunkCheck f W MW (x :: xs) sts =
      (lall2 f (ltake 16 sts) (decLit W MW x []) && chunkCheck f W MW xs (ldrop 16 sts)) := by
  change bsel (lall2 f (ltake 16 sts) (decLit W MW x [])) (chunkCheck f W MW xs (ldrop 16 sts)) false = _
  rw [bsel_eq]
  split_ifs with h <;> simp [h]

theorem chunkCheck_nil {α : Type} (f : α → ℕ → Bool) (W MW : ℕ) (sts : List α) :
    chunkCheck f W MW [] sts = sts.isEmpty := by
  cases sts <;> rfl

/-- Two ranges `[a, b)` and `[b, c)` give `[a, c)` (whatever the order of `a`, `b`, `c`). -/
theorem rangeLoop_join {α : Type} (f : α → ℕ → Bool) (W MW a b c : ℕ) (lits : List ℕ)
    (sts : List α) (j : ℕ) (h1 : rangeLoop f W MW a b lits sts j = true)
    (h2 : rangeLoop f W MW b c lits sts j = true) : rangeLoop f W MW a c lits sts j = true := by
  induction lits generalizing sts j with
  | nil => rwa [rangeLoop_nil] at h1 ⊢
  | cons x xs ih =>
    rw [rangeLoop_cons, Bool.and_eq_true] at h1 h2 ⊢
    refine ⟨?_, ih _ _ h1.2 h2.2⟩
    have t1 := h1.1; have t2 := h2.1
    split_ifs at t1 t2 ⊢ with q1 q2 q3 q3 q2 q3 q3 <;>
      first | exact t1 | exact t2 | exact lall2_triv _ _ _ t1 | exact lall2_triv _ _ _ t2 | omega

/-- A range covering the literals is the full check. -/
theorem chunkCheck_of_rangeLoop {α : Type} (f : α → ℕ → Bool) (W MW lo hi : ℕ) (lits : List ℕ)
    (sts : List α) (j : ℕ) (h : rangeLoop f W MW lo hi lits sts j = true) (hlo : lo ≤ j)
    (hhi : j + lits.length ≤ hi) : chunkCheck f W MW lits sts = true := by
  induction lits generalizing sts j with
  | nil => rwa [rangeLoop_nil, ← chunkCheck_nil f W MW] at h
  | cons x xs ih =>
    rw [rangeLoop_cons, Bool.and_eq_true] at h
    rw [chunkCheck_cons, Bool.and_eq_true]
    simp only [List.length_cons] at hhi
    have hc : lo ≤ j ∧ j < hi := ⟨hlo, by omega⟩
    simp only [hc, and_self, ↓reduceIte] at h
    exact ⟨h.1, ih _ _ h.2 (by omega) (by omega)⟩

theorem checkRange_join (g : Grid) (t : ℕ) (Nn Nt : List ℕ) (a b c : ℕ)
    (h1 : checkRange g t Nn Nt a b = true) (h2 : checkRange g t Nn Nt b c = true) :
    checkRange g t Nn Nt a c = true :=
  rangeLoop_join _ _ _ a b c _ _ _ h1 h2

theorem checkStep_of_checkRange (g : Grid) (t : ℕ) (Nn Nt : List ℕ)
    (h : checkRange g t Nn Nt 0 Nt.length = true) : checkStep g t Nn Nt = true :=
  chunkCheck_of_rangeLoop _ _ _ 0 Nt.length _ _ 0 h le_rfl (by simp)

/-! ## Lists of pairs and literals -/

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

/-- The state `i` of a literal is its field `i`. -/
theorem decLit_getD (W x i : ℕ) (hW : 0 < W) (hi : i < (decLit W (2 ^ W - 1) x []).length) :
    (decLit W (2 ^ W - 1) x []).getD i 0 = x / 2 ^ (W * i) % 2 ^ W := by
  have _ := hW
  exact decLit_getD_aux1 W 16 x i hi

/-- A passed `chunkCheck`: `f` on every pair of a state and its decoded literal state, and the
decoded state of index `idx` is the field `idx % 16` of the literal `idx / 16`. -/
theorem chunkCheck_aligned {α : Type} (f : α → ℕ → Bool) (W : ℕ) (hW : 0 < W) (lits : List ℕ)
    (sts : List α) (h : chunkCheck f W (2 ^ W - 1) lits sts = true) :
    lall2 f sts (lfoldr (decLit W (2 ^ W - 1)) [] lits) = true ∧
      ∀ idx, idx < sts.length → (lfoldr (decLit W (2 ^ W - 1)) [] lits).getD idx 0 =
        lits.getD (idx / 16) 0 / 2 ^ (W * (idx % 16)) % 2 ^ W := by
  refine ⟨chunkCheck_lall2 f W _ lits sts h, ?_⟩
  induction lits generalizing sts with
  | nil =>
    intro idx hidx
    rw [chunkCheck_nil] at h
    cases sts with
    | nil => simp at hidx
    | cons a l => simp at h
  | cons x xs ih =>
    intro idx hidx
    rw [chunkCheck_cons, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hlen := ((lall2_iff f _ _).1 h1).1
    rw [ltake_eq, List.length_take] at hlen
    have hfold : lfoldr (decLit W (2 ^ W - 1)) [] (x :: xs) =
        decLit W (2 ^ W - 1) x [] ++ lfoldr (decLit W (2 ^ W - 1)) [] xs := by
      show decLit W (2 ^ W - 1) x (lfoldr (decLit W (2 ^ W - 1)) [] xs) = _
      exact decLit_append _ _ _ _
    rw [hfold]
    by_cases hi16 : idx < 16
    · have hlt : idx < (decLit W (2 ^ W - 1) x []).length := by
        rw [← hlen]; omega
      rw [List.getD_append _ _ _ _ hlt, decLit_getD W x idx hW hlt]
      have e1 : idx / 16 = 0 := Nat.div_eq_of_lt hi16
      have e2 : idx % 16 = idx := Nat.mod_eq_of_lt hi16
      rw [e1, e2]
      rfl
    · have h16 : (decLit W (2 ^ W - 1) x []).length = 16 := by
        have := decLit_length_le W (2 ^ W - 1) x
        omega
      rw [List.getD_append_right _ _ _ _ (by omega), h16]
      have hdrop : idx - 16 < (ldrop 16 sts).length := by
        rw [ldrop_eq, List.length_drop]; omega
      rw [ih (ldrop 16 sts) h2 (idx - 16) hdrop]
      have e1 : idx / 16 = (idx - 16) / 16 + 1 := by omega
      have e2 : idx % 16 = (idx - 16) % 16 := by omega
      rw [e1, e2]
      rfl

/-! ## Sorted tuples and their rank -/

/-- `tupR (k + 1)` with an accumulated prefix, as the concatenation of the groups of `tupG`. -/
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

theorem rank_lt {m : ℕ} (k : Fin m → ℕ) (hk : Monotone k) (c : ℕ) (hc : ∀ l, k l ≤ c) :
    rank k < (c + m).choose m := by
  induction m generalizing c with
  | zero => simp [rank]
  | succ m ih =>
    have hr : rank k = rank (fun l : Fin m => k l.castSucc) + (k (Fin.last m) + m).choose (m + 1) := by
      simp only [rank]
      rw [Fin.sum_univ_castSucc]
      simp
    rw [hr]
    have hj := hc (Fin.last m)
    have h1 := ih (fun l : Fin m => k l.castSucc) (fun a b hab => hk (Fin.castSucc_le_castSucc_iff.2 hab))
      (k (Fin.last m)) (fun l => hk (Fin.le_last _))
    have h2 : (k (Fin.last m) + m).choose m + (k (Fin.last m) + m).choose (m + 1) =
        (k (Fin.last m) + (m + 1)).choose (m + 1) := by
      rw [show k (Fin.last m) + (m + 1) = (k (Fin.last m) + m) + 1 by ring, Nat.choose_succ_succ]
    have h3 : (k (Fin.last m) + (m + 1)).choose (m + 1) ≤ (c + (m + 1)).choose (m + 1) :=
      Nat.choose_le_choose _ (by omega)
    omega

/-- `tupR m xs` lists the sorted `m`-tuples over `xs` in rank order, each reversed. -/
theorem tupR_getD_rank {α : Type} (m : ℕ) (xs : List α) (a : α) (k : Fin m → ℕ)
    (hk : Monotone k) (hlt : ∀ l, k l < xs.length) :
    (tupR m xs).getD (rank k) [] = ((List.ofFn k).map fun i => xs.getD i a).reverse := by
  induction m generalizing xs with
  | zero => simp [rank, tupR_zero]
  | succ m ih =>
    set j := k (Fin.last m) with hjdef
    have hj : j < xs.length := hlt _
    have hr : rank k = rank (fun l : Fin m => k l.castSucc) + (j + m).choose (m + 1) := by
      simp only [rank]
      rw [Fin.sum_univ_castSucc]
      simp [hjdef]
    have hinit_mono : Monotone (fun l : Fin m => k l.castSucc) :=
      fun a b hab => hk (Fin.castSucc_le_castSucc_iff.2 hab)
    have hinit_le : ∀ l : Fin m, k l.castSucc ≤ j := fun l => hk (Fin.le_last _)
    have hlt1 := rank_lt (fun l : Fin m => k l.castSucc) hinit_mono j hinit_le
    have htake : xs.take (j + 1) = xs.take j ++ [xs[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]
      rfl
    obtain ⟨R, hR⟩ := tupR_append m (xs.take (j + 1)) (xs.drop (j + 1))
    rw [List.take_append_drop] at hR
    have hlenj : (xs.take j).length = j := by rw [List.length_take]; omega
    have hlenA : (tupR (m + 1) (xs.take j)).length = (j + m).choose (m + 1) := by
      rw [tupR_length, hlenj]; congr 1
    have hlenB : (tupR m (xs.take (j + 1))).length = (j + m).choose m := by
      rw [tupR_length, List.length_take]; congr 1; omega
    have hih := ih (xs.take (j + 1)) (fun l => k l.castSucc) hinit_mono
      (fun l => by rw [List.length_take]; have := hinit_le l; omega)
    rw [hR, htake, tupR_snoc, ← htake, hr]
    have hlt2 : rank (fun l : Fin m => k l.castSucc) <
        ((tupR m (xs.take (j + 1))).map (xs[j] :: ·)).length := by
      rw [List.length_map, hlenB]; exact hlt1
    rw [List.getD_append _ _ _ _ (by rw [List.length_append, hlenA, List.length_map, hlenB]; omega),
      List.getD_append_right _ _ _ _ (by rw [hlenA]; omega), hlenA, Nat.add_sub_cancel,
      List.getD_eq_getElem _ _ hlt2, List.getElem_map, ← List.getD_eq_getElem _ [], hih]
    rw [List.ofFn_succ', List.concat_eq_append, List.map_append, List.reverse_append]
    simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append]
    congr 1
    · rw [List.getD_eq_getElem _ _ hj]
    · congr 1
      apply List.map_congr_left
      intro i hi
      rw [List.mem_ofFn] at hi
      obtain ⟨l, rfl⟩ := hi
      have := hinit_le l
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]

/-! ## Time n -/

theorem lastPts_length (g : Grid) : (lastPts g).length = g.cnt g.n + 1 := by
  simp [lastPts, lastPts.lastPts1]
  rw [lapp_eq, List.length_append, lmap_eq, List.length_map, List.length_range]
  simp
  rfl

theorem lastPts_getD (g : Grid) (k : ℕ) (hk : k ≤ g.cnt g.n) :
    (lastPts g).getD k (0, false) = (pt DS g (g.glob g.n k), decide (k = g.cnt g.n)) := by
  set w := g.win (g.start.getD (g.n - 1) 0) with hw_def
  have hw_scnt : w.s + w.cnt ≤ g.J := by
    dsimp [w, Grid.win]
    let st := g.start.getD (g.n - 1) 0
    have hmin3 : min (st + g.K) g.J ≤ g.J := Nat.min_le_right _ _
    have hle : min st g.J ≤ min (st + g.K) g.J := by
      apply (Nat.le_min (a := min st g.J) (b := st + g.K) (c := g.J)).mpr
      constructor
      · exact le_trans (Nat.min_le_left _ _) (by omega)
      · exact Nat.min_le_right _ _
    have hsub : min st g.J + (min (st + g.K) g.J - min st g.J) ≤ min (st + g.K) g.J := by
      rw [Nat.add_sub_cancel' hle]
    exact le_trans hsub hmin3
  by_cases hkcnt : k < g.cnt g.n
  · -- Case k < g.cnt g.n
    have hglob : g.glob g.n k = w.s + k := by
      have hkcnt_w : k < w.cnt := by
        dsimp [Grid.cnt, Grid.wt, w] at hkcnt
        exact hkcnt
      dsimp [Grid.glob]
      have hcnt_eq : g.cnt g.n = w.cnt := by
        dsimp [Grid.cnt, Grid.wt, w]
      have hs_eq : (g.wt g.n).s = w.s := by
        dsimp [Grid.wt, w]
      rw [hcnt_eq, hs_eq]
      rw [ite_eq_left hkcnt_w]
    have hpt : pt DS g (w.s + k) = g.gpt.getD (w.s + k) 0 := by
      dsimp [pt]
      have hlt : w.s + k < g.J := by
        have : w.s + k < w.s + w.cnt := Nat.add_lt_add_left hkcnt _
        exact lt_of_lt_of_le this hw_scnt
      simp [hlt]
    rw [hglob, hpt]
    have hdecide : decide (k = g.cnt g.n) = false := by
      apply decide_eq_false_iff_not.mpr
      intro h_eq
      rw [h_eq] at hkcnt
      exact lt_irrefl _ hkcnt
    rw [hdecide]
    unfold lastPts winAt
    simp only [lastPts.lastPts1, lapp_eq, lmap_eq, lget_eq]
    dsimp [w]
    have hcnt_eq : g.cnt g.n = w.cnt := by
      dsimp [Grid.cnt, Grid.wt, w]
    have hk_lt_wcnt : k < w.cnt := by
      rw [hcnt_eq] at hkcnt
      exact hkcnt
    have hmap_len : (List.map (fun k => (g.gpt.getD (w.s + k) 0, false)) (List.range w.cnt)).length = w.cnt := by
      simp
    have hk_lt_map_len : k < (List.map (fun k => (g.gpt.getD (w.s + k) 0, false)) (List.range w.cnt)).length := by
      rw [hmap_len]
      exact hk_lt_wcnt
    rw [List.getD_append _ _ _ _ hk_lt_map_len]
    have hmap_len' : k < (List.map (fun k => (g.gpt.getD (w.s + k) 0, false)) (List.range w.cnt)).length := hk_lt_map_len
    rw [List.getD_eq_getElem _ _ hmap_len']
    rw [List.getElem_map (h := hmap_len')]
    have h_range_len : k < (List.range w.cnt).length := by
      simpa [List.length_range] using hk_lt_wcnt
    have hk_range : (List.range w.cnt)[k] = k := by
      simp [List.getElem_range h_range_len]
    rw [hk_range]
  · -- Case k = g.cnt g.n
    have hkeq : k = g.cnt g.n := by omega
    have hglob : g.glob g.n k = g.J := by
      rw [hkeq]
      have hcnt_eq : g.cnt g.n = w.cnt := by
        dsimp [Grid.cnt, Grid.wt, w]
      have hs_eq : (g.wt g.n).s = w.s := by
        dsimp [Grid.wt, w]
      dsimp [Grid.glob]
      rw [hcnt_eq, hs_eq]
      rw [ite_eq_right (lt_irrefl _)]
    have hpt : pt DS g g.J = DS := by
      dsimp [pt]
      simp
    rw [hglob, hkeq, hpt]
    have hcnt_eq : g.cnt g.n = w.cnt := by
      dsimp [Grid.cnt, Grid.wt, w]
    rw [hcnt_eq]
    unfold lastPts winAt
    simp only [lastPts.lastPts1, lapp_eq, lmap_eq]
    have hw_def' : g.win (g.start.getD (g.n - 1) 0) = w := by
      dsimp [w]
    rw [hw_def']
    have hmap_len : (List.map (fun k => (lget g.gpt (Nat.add w.s k), false)) (List.range w.cnt)).length = w.cnt := by
      simp
    have hle : (List.map (fun k => (lget g.gpt (Nat.add w.s k), false)) (List.range w.cnt)).length ≤ w.cnt := by
      rw [hmap_len]
    rw [List.getD_append_right _ _ _ _ hle]
    rw [hmap_len]
    rw [Nat.sub_self]
    simp

/-! ## Soundness of the checks -/

theorem land_M48 (x : ℕ) : Nat.land x M48 = x % 2 ^ 48 := by
  rw [show M48 = 2 ^ 48 - 1 by norm_num [M48], Nat.land_eq, Nat.and_two_pow_sub_one_eq_mod]

theorem Wd_eq_mul {d : ℕ} (g : Grid) (hd : g.m = d + 1) : Nat.mul 48 (Nat.succ g.m) = Wd d := by
  show 48 * (g.m + 1) = 48 * (d + 2)
  rw [hd]

theorem shiftLeft_one_sub_one (W : ℕ) : Nat.sub (Nat.shiftLeft 1 W) 1 = 2 ^ W - 1 := by
  show Nat.shiftLeft 1 W - 1 = _
  rw [show Nat.shiftLeft 1 W = 1 * 2 ^ W from Nat.shiftLeft_eq 1 W, one_mul]

/-- Section 4: the table of time `n`. -/
theorem checkLast_sound (g : Grid) (hg : ok DS g = true) (d : ℕ) (hd : g.m = d + 1) (T : List ℕ)
    (h : checkLast g T = true) :
    TableOK g d g.n T ∧ ∀ k, g.IsState g.n k →
      uhOf d T k + ∑ l, pt DS g (g.glob g.n (k l)) ≤ (d + 2) * DS ∧
        ∀ l, sgOf d T k l ≤ if k l < g.cnt g.n then DS else 0 := by
  have _ := hg
  unfold checkLast at h
  rw [shiftLeft_one_sub_one, Wd_eq_mul g hd, hd] at h
  obtain ⟨hall, halign⟩ := chunkCheck_aligned _ (Wd d) (by simp [Wd]) T _ h
  change lall2 _ _ (decAll d T) = true at hall
  obtain ⟨hlen, hpair⟩ := (lall2_iff _ _ _).1 hall
  have htlen : (tupR (d + 1) (lastPts g)).length = (g.cnt g.n + d + 1).choose (d + 1) := by
    rw [tupR_length, lastPts_length]
    congr 1
    omega
  refine ⟨⟨by rw [← hlen, htlen], fun idx hidx => halign idx (by rw [hlen]; exact hidx)⟩,
    fun k hk => ?_⟩
  have hrk : rank k < (tupR (d + 1) (lastPts g)).length := by
    rw [htlen]
    simpa [add_assoc] using rank_lt k hk.1 (g.cnt g.n) hk.2
  have hck := hpair (rank k) hrk (by rw [← hlen]; exact hrk)
  set P : Fin (d + 1) → ℕ × Bool := fun l => (pt DS g (g.glob g.n (k l)), decide (k l = g.cnt g.n))
    with hP
  have htp : (tupR (d + 1) (lastPts g))[rank k] = (List.ofFn P).reverse := by
    rw [← List.getD_eq_getElem _ [], tupR_getD_rank (d + 1) (lastPts g) (0, false) k hk.1
      (fun l => by rw [lastPts_length]; have := hk.2 l; omega), List.map_ofFn]
    congr 2
    funext l
    exact lastPts_getD g (k l) (hk.2 l)
  have hdec : (decAll d T)[rank k]'(by rw [← hlen]; exact hrk) = stOf d T k := by
    rw [stOf, List.getD_eq_getElem]
  rw [htp, hdec] at hck
  change bsel (Nat.ble (Nat.add (Nat.land (stOf d T k) M48)
      (lfoldr (fun p a => Nat.add p.1 a) 0 (List.ofFn P).reverse)) (Nat.mul (Nat.succ (d + 1)) DS))
    (lastSg (lrevOnto (List.ofFn P).reverse []) (slopes (d + 1) (stOf d T k))) false = true at hck
  rw [bsel_eq] at hck
  split_ifs at hck with hle
  rw [Nat.ble_eq] at hle
  constructor
  · have hsum : lfoldr (fun p a => Nat.add p.1 a) 0 (List.ofFn P).reverse =
        ∑ l, pt DS g (g.glob g.n (k l)) := by
      rw [lfoldr_eq]
      have hgen : ∀ l : List (ℕ × Bool), l.foldr (fun p a => Nat.add p.1 a) 0 = (l.map Prod.fst).sum := by
        intro l
        induction l with
        | nil => rfl
        | cons p l ih => rw [List.foldr_cons, ih, List.map_cons, List.sum_cons]; rfl
      rw [hgen, List.map_reverse, List.sum_reverse, List.map_ofFn, List.sum_ofFn]
      rfl
    rw [land_M48, hsum] at hle
    have e : Nat.mul (Nat.succ (d + 1)) DS = (d + 2) * DS := rfl
    rw [e] at hle
    exact hle
  · intro l
    unfold lastSg at hck
    rw [lrevOnto_eq, List.append_nil, List.reverse_reverse] at hck
    obtain ⟨hl, hall2⟩ := (lall2_iff _ _ _).1 hck
    have h1 : (l : ℕ) < (List.ofFn P).length := by simp; omega
    have h2 : (l : ℕ) < (slopes (d + 1) (stOf d T k)).length := by rw [slopes_eq]; simp; omega
    have hs := hall2 l h1 h2
    rw [Nat.ble_eq, bsel_eq] at hs
    have hsl : (slopes (d + 1) (stOf d T k))[(l : ℕ)] = sgOf d T k l := by
      simp only [slopes_eq, List.getElem_map, List.getElem_range, sgOf]
    rw [hsl, List.getElem_ofFn] at hs
    have hkl := hk.2 l
    by_cases hlt : k l < g.cnt g.n
    · rw [ite_eq_left hlt]
      have hne : ¬ k l = g.cnt g.n := by omega
      simpa [hP, hne] using hs
    · have heq : k l = g.cnt g.n := by omega
      rw [ite_eq_right hlt]
      simpa [hP, heq] using hs

/-! ## The chain -/

/-- The tables of the times `t, t + 1, ..., n`, every step checked. -/
def ChainSO (g : Grid) : ℕ → List (List ℕ) → Prop
  | _, [] => False
  | t, [x] => t = g.n ∧ checkLast g x = true
  | t, x :: y :: rest => checkStep g t y x = true ∧ ChainSO g (t + 1) (y :: rest)

theorem chainSO_last {g : Grid} {x : List ℕ} (h : checkLast g x = true) : ChainSO g g.n [x] :=
  ⟨rfl, h⟩

theorem chainSO_cons {g : Grid} {t : ℕ} {x y : List ℕ} {rest : List (List ℕ)}
    (h1 : checkStep g t y x = true) (h2 : ChainSO g (t + 1) (y :: rest)) :
    ChainSO g t (x :: y :: rest) :=
  ⟨h1, h2⟩

end Robbins.Cert.SO.K
