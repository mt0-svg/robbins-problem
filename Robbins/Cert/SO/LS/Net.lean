import Robbins.Cert.SO.LS.Vec

/-!
# The lanes step: compaction networks

A stage `cst` of `cnet` moves the lanes under a full-lane mask down by `2 ^ k` lanes and adds them
to the lanes there. Every mask that `expand` produces is a full-lane mask, so after the network each
destination lane is the sum of the source lanes whose path ends there (`npath`, which depends on the
masks only). The two tests of `mkRt` (the ones and `l ↦ l + 1`) then identify the unique source of
every destination lane, and `route` moves any source lanes below `2 ^ 100` accordingly.
-/

namespace Robbins.Cert.SO.L

open Robbins.Cert Robbins.Cert.K Robbins.Cert.SO.K Robbins.Lanes

/-- The full-lane mask of `N` lanes with the lanes of `c` set. -/
noncomputable def fmk (p : ℕ × (ℕ → Bool)) : ℕ := pack LW p.1 fun l => if p.2 l then 2 ^ 144 - 1 else 0

/-- The lane of the source lane `s` after the stages `cs` from the stage `k` on (`none`: dropped
below lane `0`). -/
def npath : List (ℕ × (ℕ → Bool)) → ℕ → ℕ → Option ℕ
  | [], _, s => some s
  | p :: cs, k, s =>
    if s < p.1 ∧ p.2 s = true then
      (if 2 ^ k ≤ s then npath cs (k + 1) (s - 2 ^ k) else none)
    else npath cs (k + 1) s

/-- The path only goes down. -/
theorem npath_le (cs : List (ℕ × (ℕ → Bool))) (k s j : ℕ) (h : npath cs k s = some j) : j ≤ s := by
  induction cs generalizing k s with
  | nil =>
      simp [npath] at h
      subst h
      exact Nat.le_refl s
  | cons p cs ih =>
      simp [npath] at h
      by_cases hcond : s < p.1 ∧ p.2 s = true
      · simp [hcond] at h
        by_cases hk : 2 ^ k ≤ s
        · simp [hk] at h
          have hle := ih (k + 1) (s - 2 ^ k) h
          exact Nat.le_trans hle (Nat.sub_le s (2 ^ k))
        · simp [hk] at h
      · simp [hcond] at h
        exact ih (k + 1) s h

/-- `iota1 n` is the pack of `l ↦ l + 1`. -/
theorem iota1_eq (n : ℕ) : iota1 n = pack LW n fun l => l + 1 := by
  set x := 2 ^ LW with hx_def
  have hx_pos : 0 < x := by
    rw [hx_def]
    apply pow_pos (by norm_num) LW
  have hx_one : 1 < x := by
    rw [hx_def]
    calc
      1 < 2 := by norm_num
      _ = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ LW := Nat.pow_le_pow_right (by norm_num) (by decide : 1 ≤ LW)
  have hx1 : 1 ≤ x := by omega
  have hFM_eq : FM = x - 1 := by
    rw [hx_def]
    norm_num [FM, LW]
  have hpos : 0 < x - 1 := by
    omega
  -- key identity in ℤ
  have hkey_ℤ : (pack LW n (fun l => l + 1) : ℤ) * ((x : ℤ) - 1) + (pack LW n (fun _ => 1) : ℤ) = (n : ℤ) * (x : ℤ) ^ n := by
    induction n with
    | zero =>
        simp [pack]
    | succ n ih =>
        rw [pack_succ LW n (fun l => l + 1), pack_succ LW n (fun _ => 1)]
        push_cast
        simp
        have hx_pow : (2 ^ (LW * n) : ℤ) = ((x : ℤ) ^ n) := by
          simp [hx_def, Nat.cast_pow, pow_mul]
        rw [hx_pow]
        set P := (pack LW n (fun l => l + 1) : ℤ) with hP
        set O := (pack LW n (fun _ => 1) : ℤ) with hO
        set X := (x : ℤ) with hX
        have hcalc : (n : ℤ) * X ^ n + ((n : ℤ) + 1) * X ^ n * (X - 1) + X ^ n = ((n : ℤ) + 1) * X ^ n * X := by
          ring
        calc
          (P + ((n : ℤ) + 1) * X ^ n) * (X - 1) + (O + X ^ n)
              = (P * (X - 1) + O) + ((n : ℤ) + 1) * X ^ n * (X - 1) + X ^ n := by ring
          _ = ((n : ℤ) * X ^ n) + ((n : ℤ) + 1) * X ^ n * (X - 1) + X ^ n := by rw [ih]
          _ = ((n : ℤ) + 1) * X ^ n * X := by rw [hcalc]
          _ = ((n : ℤ) + 1) * X ^ (n + 1) := by ring
  -- Convert to ℕ
  have hkey : pack LW n (fun l => l + 1) * (x - 1) + pack LW n (fun _ => 1) = n * x ^ n := by
    apply (Nat.cast_inj (R := ℤ)).mp
    simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hx1, Nat.cast_ofNat] using hkey_ℤ
  -- Now use the key identity to prove the main result
  have hsub : n * x ^ n - pack LW n (fun _ => 1) = pack LW n (fun l => l + 1) * (x - 1) := by
    calc
      n * x ^ n - pack LW n (fun _ => 1) = (pack LW n (fun l => l + 1) * (x - 1) + pack LW n (fun _ => 1)) - pack LW n (fun _ => 1) := by rw [hkey]
      _ = pack LW n (fun l => l + 1) * (x - 1) := by rw [Nat.add_sub_cancel_right]
  -- Now compute iota1
  rw [iota1, hFM_eq]
  -- iota1 n = Nat.div (Nat.sub (Nat.mul n (Nat.shiftLeft 1 (Nat.mul LW n))) (ones LW n)) (x - 1)
  -- Rewrite using hshift, hpow, ones_eq, hsub
  have hshift : (1 <<< (LW * n)) = 2 ^ (LW * n) := by
    simp [Nat.shiftLeft_eq, one_mul]
  have hpow : (2 : ℕ) ^ (LW * n) = x ^ n := by
    rw [hx_def, ← pow_mul, mul_comm LW n]
  calc
    ((n.mul (Nat.shiftLeft 1 (LW.mul n))).sub (ones LW n)).div (x - 1)
        = ((n.mul (2 ^ (LW * n))).sub (ones LW n)).div (x - 1) := by simp [hshift]
    _ = ((n.mul (x ^ n)).sub (ones LW n)).div (x - 1) := by simp [hpow]
    _ = ((n.mul (x ^ n)).sub (pack LW n (fun _ => 1))).div (x - 1) := by simp [ones_eq LW n LW_pos]
    _ = ((pack LW n (fun l => l + 1) * (x - 1))).div (x - 1) := by simp [hsub]
    _ = pack LW n (fun l => l + 1) := by
      exact Nat.div_eq_of_eq_mul_left hpos (rfl : pack LW n (fun l => l + 1) * (x - 1) = pack LW n (fun l => l + 1) * (x - 1))

/-- A word against a guard: the pack of its guard bits. -/
theorem land_guard_any (Y N : ℕ) :
    Nat.land Y (guard LW N) = pack LW N fun l => if Y.testBit (144 * l + 143) then 2 ^ 143 else 0 := by
  have hW : 0 < LW := LW_pos
  rw [guard_eq LW N hW]
  simpa [LW] using show
    Nat.land Y (pack 144 N (fun _ => 2 ^ 143)) = pack 144 N (fun l => if Y.testBit (144 * l + 143) then 2 ^ 143 else 0) from by
      apply Nat.eq_of_testBit_eq
      intro i
      have hland : Y.land (pack 144 N (fun _ => 2 ^ 143)) = Y &&& (pack 144 N (fun _ => 2 ^ 143)) := rfl
      rw [hland, Nat.testBit_land]
      have hbound1 : ∀ l < N, (fun _ : ℕ => 2 ^ 143) l < 2 ^ 144 := by
        intro l hl; norm_num
      have hbound2 : ∀ l < N, (fun l => if Y.testBit (144 * l + 143) then 2 ^ 143 else 0) l < 2 ^ 144 := by
        intro l hl; dsimp; split <;> norm_num
      rw [testBit_pack 144 N (fun _ => 2 ^ 143) (by norm_num) hbound1 i,
        testBit_pack 144 N (fun l => if Y.testBit (144 * l + 143) then 2 ^ 143 else 0) (by norm_num) hbound2 i]
      simp only [Nat.testBit_two_pow]
      by_cases hi : i / 144 < N
      · simp [hi]
        split_ifs with hbit
        · -- hbit: Y.testBit (144 * (i / 144) + 143) = true
          by_cases hmod : i % 144 = 143
          · have heq : 144 * (i / 144) + 143 = i := by
              have := Nat.div_add_mod i 144
              rw [hmod] at this; exact this
            have hybit : Y.testBit i = true := by
              rw [← heq]; exact hbit
            rw [hmod, hybit]
            decide
          · have hdec : decide (143 = i % 144) = false := by
              have h : 143 ≠ i % 144 := mt Eq.symm hmod
              simp [h]
            rw [hdec]
            simp
            have h_pow : (2 ^ 143 : ℕ) = 11150372599265311570767859136324180752990208 := by norm_num
            rw [← h_pow]
            rw [Nat.testBit_two_pow]
            have h : 143 ≠ i % 144 := mt Eq.symm hmod
            simp [h]
        · -- hbit: ¬ Y.testBit (144 * (i / 144) + 143) = true
          have hbit' : Y.testBit (144 * (i / 144) + 143) = false := by simpa using hbit
          by_cases hmod : i % 144 = 143
          · have heq : 144 * (i / 144) + 143 = i := by
              have := Nat.div_add_mod i 144
              rw [hmod] at this; exact this
            have hybit : Y.testBit i = false := by
              rw [← heq]; exact hbit'
            rw [hmod, hybit]
            decide
          · have hdec : decide (143 = i % 144) = false := by
              simpa [eq_comm] using hmod
            rw [hdec]
            simp
      · simp [hi]

/-- Zero lanes at the top do not change a pack. -/
theorem pack_extend (W L L' : ℕ) (f : ℕ → ℕ) (hL : L ≤ L') (hz : ∀ l, L ≤ l → l < L' → f l = 0) :
    pack W L f = pack W L' f := by
  unfold pack
  apply Finset.sum_subset (Finset.range_subset_range.2 hL)
  intro l hl hn
  rw [Finset.mem_range] at hl hn
  rw [hz l (by omega) hl, zero_mul]

/-- A full-lane mask against a pack: the lanes of the mask are kept, the others cleared. -/
theorem land_fmk (n : ℕ) (p : ℕ × (ℕ → Bool)) (w : ℕ → ℕ) (hw : ∀ l < n, w l < 2 ^ 144) :
    Nat.land (pack LW n w) (fmk p) = pack LW n fun l => if l < p.1 ∧ p.2 l = true then w l else 0 := by
  unfold fmk
  set L := max n p.1 with hL
  have e1 : pack LW n w = pack LW L (fun l => if l < n then w l else 0) := by
    rw [pack_congr LW n w (fun l => if l < n then w l else 0) (fun l hl => by simp [hl])]
    exact pack_extend _ _ _ _ (le_max_left _ _) (fun l hl _ => by simp; omega)
  have e2 : (pack LW p.1 fun l => if p.2 l = true then 2 ^ 144 - 1 else 0) =
      pack LW L (fun l => if l < p.1 ∧ p.2 l = true then 2 ^ 144 - 1 else 0) := by
    rw [pack_congr LW p.1 _ (fun l => if l < p.1 ∧ p.2 l = true then 2 ^ 144 - 1 else 0)
      (fun l hl => by simp [hl])]
    exact pack_extend _ _ _ _ (le_max_right _ _) (fun l hl _ => by simp; omega)
  have e3 : (pack LW n fun l => if l < p.1 ∧ p.2 l = true then w l else 0) =
      pack LW L (fun l => if l < n ∧ l < p.1 ∧ p.2 l = true then w l else 0) := by
    rw [pack_congr LW n _ (fun l => if l < n ∧ l < p.1 ∧ p.2 l = true then w l else 0)
      (fun l hl => by simp [hl])]
    exact pack_extend _ _ _ _ (le_max_left _ _) (fun l hl _ => by simp; omega)
  rw [e1, e2, e3]
  show (_ : ℕ) &&& (_ : ℕ) = _
  rw [land_pack LW L _ _ LW_pos (fun l hl => by
      show (if l < n then w l else 0) < 2 ^ 144
      split_ifs with h
      · exact hw l h
      · norm_num)
    (fun l hl => by
      show (if l < p.1 ∧ p.2 l = true then 2 ^ 144 - 1 else 0) < 2 ^ 144
      split_ifs <;> norm_num)]
  apply pack_congr
  intro l _
  by_cases h1 : l < n
  · by_cases h2 : l < p.1 ∧ p.2 l = true
    · simp only [h1, h2, and_self, ite_true]
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hw l h1)]
    · simp only [h1, h2, ite_true, ite_false, and_false, Nat.and_zero]
  · simp [h1]

/-- One stage: the lanes of `c` move down by `2 ^ k` lanes. -/
theorem cst_eq (n k : ℕ) (p : ℕ × (ℕ → Bool)) (w : ℕ → ℕ) (hw : ∀ l < n, w l < 2 ^ 144) :
    cst (LW * 2 ^ k) (fmk p) (pack LW n w) =
      pack LW n fun j => (if j < p.1 ∧ p.2 j = true then 0 else w j) +
        (if j + 2 ^ k < n ∧ j + 2 ^ k < p.1 ∧ p.2 (j + 2 ^ k) = true then w (j + 2 ^ k) else 0) := by
  set m : ℕ → ℕ := fun l => if l < p.1 ∧ p.2 l = true then w l else 0 with hm
  have hVm : Nat.land (pack LW n w) (fmk p) = pack LW n m := land_fmk n p w hw
  have hml : ∀ l < n, m l < 2 ^ LW := fun l hl => by
    simp only [hm]
    split_ifs
    · exact hw l hl
    · exact Nat.two_pow_pos _
  show Nat.add (Nat.sub (pack LW n w) (Nat.land (pack LW n w) (fmk p)))
    (Nat.shiftRight (Nat.land (pack LW n w) (fmk p)) (LW * 2 ^ k)) = _
  rw [hVm]
  have hsub : Nat.sub (pack LW n w) (pack LW n m) =
      pack LW n (fun l => if l < p.1 ∧ p.2 l = true then 0 else w l) := by
    show pack LW n w - pack LW n m = _
    rw [pack_sub LW n m w (fun l _ => by simp only [hm]; split_ifs <;> omega)]
    apply pack_congr
    intro l _
    simp only [hm]
    split_ifs <;> omega
  have hshr : Nat.shiftRight (pack LW n m) (LW * 2 ^ k) =
      pack LW n (fun j => if j + 2 ^ k < n then m (j + 2 ^ k) else 0) := by
    have h1 := drp_pack LW n (2 ^ k) m hml
    have h2 : drp LW (2 ^ k) (pack LW n m) = Nat.shiftRight (pack LW n m) (LW * 2 ^ k) := rfl
    rw [← h2, h1, pack_congr LW (n - 2 ^ k) _ (fun j => if j + 2 ^ k < n then m (j + 2 ^ k) else 0)
      (fun j hj => by rw [ite_eq_left (by omega)])]
    exact pack_extend _ _ _ _ (Nat.sub_le _ _) (fun j hj _ => by rw [ite_eq_right (by omega)])
  rw [hsub, hshr]
  show pack LW n _ + pack LW n _ = _
  rw [pack_add]
  apply pack_congr
  intro j _
  simp only [hm]
  congr 1
  by_cases h : j + 2 ^ k < n <;> simp [h]

/-- The network from the stage `k` (shift `s = LW 2 ^ k`). -/
noncomputable def cnetFrom (Ms : List ℕ) (s V : ℕ) : ℕ :=
  @List.rec ℕ (fun _ => ℕ → ℕ → ℕ) (fun _ V => V)
    (fun M _ ih s V => frc2 (cst s M V) 1 (fun V' _ => ih (Nat.add s s) V')) Ms s V

theorem cnet_eq_from (Ms : List ℕ) (V : ℕ) : cnet Ms V = cnetFrom Ms LW V := rfl

/-- A sum over the lanes `j` with `j + t < n` of the lane `j + t` is a sum over the lanes `t ≤ s < n`. -/
theorem sum_shift_eq (n t : ℕ) (h : ℕ → ℕ) (F : ℕ → ℕ) (hF : ∀ s, s < t → F s = 0)
    (hh : ∀ i, i + t < n → h i = F (t + i)) (hh0 : ∀ i, n ≤ i + t → h i = 0) :
    ∑ i ∈ Finset.range n, h i = ∑ s ∈ Finset.range n, F s := by
  have e1 : ∑ i ∈ Finset.range n, h i = ∑ i ∈ Finset.range (n - t), h i := by
    refine (Finset.sum_subset (Finset.range_subset_range.2 (Nat.sub_le n t)) ?_).symm
    intro i hi hi'
    rw [Finset.mem_range] at hi hi'
    exact hh0 i (by omega)
  have e2 : ∑ s ∈ Finset.range n, F s = ∑ s ∈ Finset.Ico t n, F s := by
    refine (Finset.sum_subset (fun s hs => ?_) ?_).symm
    · rw [Finset.mem_Ico] at hs
      exact Finset.mem_range.2 hs.2
    · intro s hs hs'
      rw [Finset.mem_range] at hs
      rw [Finset.mem_Ico] at hs'
      exact hF s (by omega)
  rw [e1, e2, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  exact hh i (by omega)

/-- One stage on the path sums: the sums after the stage `k` over the stages `cs` from `k + 1`
are the sums over the stages `p :: cs` from `k`. -/
theorem npath_step_sum (cs : List (ℕ × (ℕ → Bool))) (p : ℕ × (ℕ → Bool)) (k n j : ℕ) (w : ℕ → ℕ) :
    ∑ s ∈ Finset.range n, (if npath cs (k + 1) s = some j then
        (if s < p.1 ∧ p.2 s = true then 0 else w s) +
          (if s + 2 ^ k < n ∧ s + 2 ^ k < p.1 ∧ p.2 (s + 2 ^ k) = true then w (s + 2 ^ k) else 0)
      else 0) =
      ∑ s ∈ Finset.range n, if npath (p :: cs) k s = some j then w s else 0 := by
  have hR : ∀ s, (if npath (p :: cs) k s = some j then w s else 0) =
      (if ¬ (s < p.1 ∧ p.2 s = true) ∧ npath cs (k + 1) s = some j then w s else 0) +
        (if 2 ^ k ≤ s ∧ (s < p.1 ∧ p.2 s = true) ∧ npath cs (k + 1) (s - 2 ^ k) = some j
          then w s else 0) := by
    intro s
    simp only [npath]
    by_cases hc : s < p.1 ∧ p.2 s = true
    · by_cases ht : 2 ^ k ≤ s
      · simp [hc, ht]
      · simp [hc, ht]
    · simp [hc]
  have hL : ∀ s, (if npath cs (k + 1) s = some j then
        (if s < p.1 ∧ p.2 s = true then 0 else w s) +
          (if s + 2 ^ k < n ∧ s + 2 ^ k < p.1 ∧ p.2 (s + 2 ^ k) = true then w (s + 2 ^ k) else 0)
      else 0) =
      (if ¬ (s < p.1 ∧ p.2 s = true) ∧ npath cs (k + 1) s = some j then w s else 0) +
        (if npath cs (k + 1) s = some j then
          (if s + 2 ^ k < n ∧ s + 2 ^ k < p.1 ∧ p.2 (s + 2 ^ k) = true then w (s + 2 ^ k) else 0)
          else 0) := by
    intro s
    by_cases h1 : npath cs (k + 1) s = some j <;> by_cases h2 : s < p.1 ∧ p.2 s = true <;> simp [h1, h2]
  rw [Finset.sum_congr rfl (fun s _ => hL s), Finset.sum_congr rfl (fun s _ => hR s),
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  apply sum_shift_eq n (2 ^ k)
  · intro s hs
    rw [ite_eq_right_iff]
    intro h
    omega
  · intro i hi
    rw [add_comm (2 ^ k) i, Nat.add_sub_cancel]
    by_cases h1 : npath cs (k + 1) i = some j <;>
      by_cases h2 : i + 2 ^ k < p.1 ∧ p.2 (i + 2 ^ k) = true <;> simp [h1, h2, hi]
  · intro i hi
    by_cases h1 : npath cs (k + 1) i = some j
    · simp only [h1, ite_true]
      rw [ite_eq_right_iff]
      intro h
      omega
    · simp [h1]

/-- One stage does not increase the total of the lanes. -/
theorem stage_sum_le (p : ℕ × (ℕ → Bool)) (k n : ℕ) (w : ℕ → ℕ) :
    ∑ j ∈ Finset.range n, ((if j < p.1 ∧ p.2 j = true then 0 else w j) +
        (if j + 2 ^ k < n ∧ j + 2 ^ k < p.1 ∧ p.2 (j + 2 ^ k) = true then w (j + 2 ^ k) else 0)) ≤
      ∑ s ∈ Finset.range n, w s := by
  rw [Finset.sum_add_distrib]
  have e : ∑ j ∈ Finset.range n,
      (if j + 2 ^ k < n ∧ j + 2 ^ k < p.1 ∧ p.2 (j + 2 ^ k) = true then w (j + 2 ^ k) else 0) =
      ∑ s ∈ Finset.range n, if 2 ^ k ≤ s ∧ s < p.1 ∧ p.2 s = true then w s else 0 :=
    sum_shift_eq n (2 ^ k) _ _ (fun s hs => by rw [ite_eq_right_iff]; intro h; omega)
      (fun i hi => by
        rw [add_comm (2 ^ k) i]
        by_cases h : i + 2 ^ k < p.1 ∧ p.2 (i + 2 ^ k) = true <;> simp [h, hi])
      (fun i hi => by rw [ite_eq_right_iff]; intro h; omega)
  rw [e, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  by_cases hc : s < p.1 ∧ p.2 s = true
  · by_cases ht : 2 ^ k ≤ s <;> simp [hc, ht]
  · have hc' : ¬ (2 ^ k ≤ s ∧ s < p.1 ∧ p.2 s = true) := fun h => hc h.2
    rw [ite_eq_right hc, ite_eq_right hc', add_zero]

/-- The network on full-lane masks: each lane is the sum of the source lanes whose path ends there. -/
theorem cnetFrom_eq (cs : List (ℕ × (ℕ → Bool))) (k n : ℕ) (w : ℕ → ℕ)
    (hw : ∑ s ∈ Finset.range n, w s < 2 ^ 144) :
    cnetFrom (cs.map fmk) (LW * 2 ^ k) (pack LW n w) =
      pack LW n fun j => ∑ s ∈ Finset.range n, if npath cs k s = some j then w s else 0 := by
  induction cs generalizing k w with
  | nil =>
    show pack LW n w = _
    apply pack_congr
    intro j hj
    simp [npath, Finset.sum_ite_eq', hj]
  | cons p cs ih =>
    have hwl : ∀ l < n, w l < 2 ^ 144 := fun l hl =>
      lt_of_le_of_lt (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hl)) hw
    show frc2 (cst (LW * 2 ^ k) (fmk p) (pack LW n w)) 1
      (fun V' _ => cnetFrom (cs.map fmk) (Nat.add (LW * 2 ^ k) (LW * 2 ^ k)) V') = _
    rw [frc2_eq, cst_eq n k p w hwl]
    have hs : Nat.add (LW * 2 ^ k) (LW * 2 ^ k) = LW * 2 ^ (k + 1) := by
      show LW * 2 ^ k + LW * 2 ^ k = _
      rw [pow_succ]
      ring
    rw [hs, ih (k + 1) _ (lt_of_le_of_lt (stage_sum_le p k n w) hw)]
    apply pack_congr
    intro j _
    exact npath_step_sum cs p k n j w

/-- A full-lane mask moved up by `2 ^ k` lanes. -/
theorem fmk_shift (p : ℕ × (ℕ → Bool)) (k : ℕ) :
    Nat.shiftLeft (fmk p) (Nat.shiftLeft LW k) =
      fmk (p.1 + 2 ^ k, fun l => decide (2 ^ k ≤ l) && p.2 (l - 2 ^ k)) := by
  unfold fmk
  show pack LW p.1 _ <<< (LW <<< k) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, pack_mul_pow]
  apply pack_congr
  intro l _
  by_cases h : 2 ^ k ≤ l <;> simp [h]

/-- The full lanes of the guard bits of a word. -/
theorem full_land_guard (Y N : ℕ) :
    full LW (Nat.land Y (guard LW N)) = fmk (N, fun l => Y.testBit (144 * l + 143)) := by
  rw [land_guard_any, full_eq N (fun l => Y.testBit (144 * l + 143) = true)]
  rfl

/-- The masks of the inverse network with an accumulator of full-lane masks. -/
theorem expand_fmk_aux (N K : ℕ) : ∀ X (acc : List ℕ), (∃ cs : List (ℕ × (ℕ → Bool)), acc = cs.map fmk) →
    ∃ cs : List (ℕ × (ℕ → Bool)), (@Nat.rec (fun _ => ℕ → List ℕ → ℕ × List ℕ) (fun X acc => (X, acc))
      (fun k ih X acc => exp1 (guard LW N) k X (fun X' M => ih X' (M :: acc))) K X acc).2 =
        cs.map fmk := by
  induction K with
  | zero => intro X acc h; exact h
  | succ K ih =>
    rintro X acc ⟨cs, hcs⟩
    show ∃ cs, (exp1 (guard LW N) K X _).2 = _
    unfold exp1 exp1.exp2 exp1.exp3
    rw [frc2_eq]
    apply ih
    rw [full_land_guard, fmk_shift, hcs]
    exact ⟨_ :: cs, rfl⟩

/-- The masks of `expand` are full-lane masks. -/
theorem expand_fmk (N K X : ℕ) : ∃ cs : List (ℕ × (ℕ → Bool)),
    (expand (guard LW N) K X).2 = cs.map fmk := by
  exact expand_fmk_aux N K X [] ⟨[], rfl⟩

/-- A sum of `NS` terms each at most `B`, with `NS B < 2 ^ 144`. -/
theorem sum_lt_of_le (NS B : ℕ) (w : ℕ → ℕ) (hw : ∀ s < NS, w s ≤ B) (h : NS * B < 2 ^ 144) :
    ∑ s ∈ Finset.range NS, w s < 2 ^ 144 := by
  refine lt_of_le_of_lt ?_ h
  have := Finset.sum_le_card_nsmul (Finset.range NS) w B (fun s hs => hw s (Finset.mem_range.1 hs))
  simpa using this

/-- A sum of selected terms is at most the whole sum. -/
theorem sum_ite_le (NS : ℕ) (P : ℕ → Prop) [DecidablePred P] (w : ℕ → ℕ) :
    ∑ s ∈ Finset.range NS, (if P s then w s else 0) ≤ ∑ s ∈ Finset.range NS, w s :=
  Finset.sum_le_sum fun s _ => by split_ifs <;> omega

/-- `pre` of a pack whose lanes from `n` on are `0`. -/
theorem pre_pack_zero (n m : ℕ) (g : ℕ → ℕ) (hg : ∀ l < n, g l < 2 ^ 144) (hz : ∀ l, n ≤ l → g l = 0) :
    pre LW m (pack LW n g) = pack LW m g := by
  by_cases h : m ≤ n
  · exact pre_pack LW n m g hg h
  · rw [pack_extend LW n m g (by omega) (fun l hl _ => hz l hl)]
    refine pre_pack LW m m g (fun l _ => ?_) le_rfl
    by_cases h' : l < n
    · exact hg l h'
    · rw [hz l (by omega)]; exact Nat.two_pow_pos _

/-- The two sums of a test give a unique source. -/
theorem uniq_of_sums (NS i : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (h1 : ∑ s ∈ Finset.range NS, (if P s then 1 else 0) = 1)
    (h2 : ∑ s ∈ Finset.range NS, (if P s then s + 1 else 0) = i + 1) :
    i < NS ∧ ∀ f : ℕ → ℕ, ∑ s ∈ Finset.range NS, (if P s then f s else 0) = f i := by
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_eq_one] at h1
  obtain ⟨s0, hs0⟩ := h1
  have hsum : ∀ g : ℕ → ℕ, ∑ s ∈ Finset.range NS, (if P s then g s else 0) = g s0 := by
    intro g
    rw [← Finset.sum_filter, hs0, Finset.sum_singleton]
  rw [hsum] at h2
  have hmem : s0 ∈ (Finset.range NS).filter P := by rw [hs0]; exact Finset.mem_singleton_self _
  have hi : s0 = i := by omega
  subst hi
  exact ⟨Finset.mem_range.1 (Finset.mem_filter.1 hmem).1, hsum⟩

/-- The network on the selected full lanes of `NS` source lanes, cut to `ND` lanes. -/
theorem cnet_sel (NS ND : ℕ) (cs : List (ℕ × (ℕ → Bool))) (c : ℕ → Bool) (w : ℕ → ℕ)
    (hw : ∑ s ∈ Finset.range NS, w s < 2 ^ 144) :
    pre LW ND (cnet (cs.map fmk) (Nat.land (pack LW NS w) (fmk (NS, c)))) =
      pack LW ND fun j => ∑ s ∈ Finset.range NS, if c s = true ∧ npath cs 0 s = some j then w s else 0 := by
  have hwl : ∀ l < NS, w l < 2 ^ 144 := fun l hl =>
    lt_of_le_of_lt (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hl)) hw
  have hvs : ∑ s ∈ Finset.range NS, (if c s = true then w s else 0) < 2 ^ 144 :=
    lt_of_le_of_lt (sum_ite_le NS _ w) hw
  have hc := cnetFrom_eq cs 0 NS _ hvs
  rw [pow_zero, mul_one] at hc
  rw [land_fmk NS (NS, c) w hwl,
    pack_congr LW NS _ (fun s => if c s = true then w s else 0) (fun l hl => by simp [hl]),
    cnet_eq_from, hc]
  rw [pre_pack_zero NS ND _ (fun j _ => lt_of_le_of_lt (le_trans (sum_ite_le NS _ _) (sum_ite_le NS _ w)) hw)
    (fun j hj => Finset.sum_eq_zero fun s hs => by
      rw [ite_eq_right_iff]
      intro h
      have := npath_le cs 0 s j h
      have := Finset.mem_range.1 hs
      omega)]
  apply pack_congr
  intro j _
  apply Finset.sum_congr rfl
  intro s _
  by_cases h1 : c s = true <;> by_cases h2 : npath cs 0 s = some j <;> simp [h1, h2]

/-- The two tests of a compaction on full-lane masks. -/
theorem route_gen (NS ND : ℕ) (Iv : ℕ → ℕ) (cs : List (ℕ × (ℕ → Bool))) (c : ℕ → Bool)
    (hNS : NS < 2 ^ 40) (hIv : ∀ j < ND, Iv j < 2 ^ 40)
    (h1 : pre LW ND (cnet (cs.map fmk) (Nat.land (ones LW NS) (fmk (NS, c)))) = ones LW ND)
    (h2 : pre LW ND (cnet (cs.map fmk) (Nat.land (iota1 NS) (fmk (NS, c)))) =
      Nat.add (pack LW ND Iv) (ones LW ND)) :
    (∀ j < ND, Iv j < NS) ∧ ∀ f : ℕ → ℕ, (∀ s < NS, f s < 2 ^ 100) →
      pre LW ND (cnet (cs.map fmk) (Nat.land (pack LW NS f) (fmk (NS, c)))) =
        pack LW ND fun j => f (Iv j) := by
  have hb1 : ∑ s ∈ Finset.range NS, (fun _ => 1) s < 2 ^ 144 :=
    sum_lt_of_le NS 1 _ (fun _ _ => le_rfl) (by omega)
  have hb2 : ∑ s ∈ Finset.range NS, (fun l => l + 1) s < 2 ^ 144 := by
    refine sum_lt_of_le NS NS _ (fun s hs => by show s + 1 ≤ NS; omega) ?_
    calc NS * NS < 2 ^ 40 * 2 ^ 40 := Nat.mul_lt_mul'' hNS hNS
      _ ≤ 2 ^ 144 := by norm_num
  rw [ones_eq LW NS LW_pos, cnet_sel NS ND cs c _ hb1, ones_eq LW ND LW_pos] at h1
  rw [iota1_eq, cnet_sel NS ND cs c _ hb2] at h2
  have h2' : (pack LW ND fun j => ∑ s ∈ Finset.range NS,
      if c s = true ∧ npath cs 0 s = some j then s + 1 else 0) = pack LW ND fun j => Iv j + 1 := by
    rw [h2, ones_eq LW ND LW_pos]
    exact pack_add LW ND Iv _
  have e1 := (pack_inj LW ND _ _ (fun j _ => lt_of_le_of_lt (sum_ite_le _ _ _) hb1)
    (fun _ _ => by norm_num [LW])).1 h1
  have e2 := (pack_inj LW ND _ _ (fun j _ => lt_of_le_of_lt (sum_ite_le _ _ _) hb2)
    (fun j hj => by have := hIv j hj; show Iv j + 1 < 2 ^ 144; omega)).1 h2'
  have hu : ∀ j < ND, Iv j < NS ∧ ∀ f : ℕ → ℕ, ∑ s ∈ Finset.range NS,
      (if c s = true ∧ npath cs 0 s = some j then f s else 0) = f (Iv j) :=
    fun j hj => uniq_of_sums NS (Iv j) _ (e1 j hj) (e2 j hj)
  refine ⟨fun j hj => (hu j hj).1, fun f hf => ?_⟩
  have hbf : ∑ s ∈ Finset.range NS, f s < 2 ^ 144 := by
    refine sum_lt_of_le NS (2 ^ 100) _ (fun s hs => (hf s hs).le) ?_
    calc NS * 2 ^ 100 < 2 ^ 40 * 2 ^ 100 := Nat.mul_lt_mul_of_pos_right hNS (Nat.two_pow_pos _)
      _ ≤ 2 ^ 144 := by norm_num
  rw [cnet_sel NS ND cs c f hbf]
  exact pack_congr _ _ _ _ fun j hj => (hu j hj).2 f

/-- A compaction that passes its two tests moves the source lane `Iv j` to the destination lane
`j`, for sources below `2 ^ 100`. -/
theorem route_spec_gen (NS ND : ℕ) (Iv : ℕ → ℕ) (hNS : NS < 2 ^ 40) (hIv : ∀ j < ND, Iv j < 2 ^ 40)
    (hok : (mkRt NS ND (pack LW ND Iv)).ok = true) :
    (∀ j < ND, Iv j < NS) ∧ ∀ f : ℕ → ℕ, (∀ s < NS, f s < 2 ^ 100) →
      route (mkRt NS ND (pack LW ND Iv)) (pack LW NS f) = pack LW ND fun j => f (Iv j) := by
  obtain ⟨cs, hcs⟩ := expand_fmk NS (Nat.succ (Nat.log2 NS))
    (Nat.add (Nat.sub (pack LW ND Iv) (Nat.sub (iota1 ND) (ones LW ND))) (guard LW ND))
  have hmk : mkRt NS ND (pack LW ND Iv) = mkRt.mkRt2 NS ND (pack LW ND Iv) (cs.map fmk)
      (fmk (NS, fun l => (expand (guard LW NS) (Nat.succ (Nat.log2 NS))
        (Nat.add (Nat.sub (pack LW ND Iv) (Nat.sub (iota1 ND) (ones LW ND))) (guard LW ND))).1.testBit
          (144 * l + 143))) := by
    rw [← hcs, ← full_land_guard]
    rfl
  rw [hmk] at hok ⊢
  generalize (fun l => _) = c at hok ⊢
  simp only [mkRt.mkRt2, bsel_eq] at hok
  split_ifs at hok with hA
  have hB := Nat.eq_of_beq_eq_true hok
  have hA' := Nat.eq_of_beq_eq_true hA
  exact route_gen NS ND Iv cs c hNS hIv hA' hB

end Robbins.Cert.SO.L
