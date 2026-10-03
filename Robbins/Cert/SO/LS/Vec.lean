import Robbins.Cert.SO.Lanes
import Robbins.Lanes.OpsSound
import Robbins.Cert.EvalM2Eq

/-!
# The vector operations of the lanes step on packs

The operations of Robbins/Cert/SO/Lanes.lean on `n` lanes of `LW = 144` bits (`mkVC n`), applied to
packs, are the packs of the lanewise operations. A guard mask is
`pack LW n (fun l => if c l then 2 ^ 143 else 0)`.
-/

namespace Robbins.Cert.SO.L

open Robbins.Cert Robbins.Cert.K Robbins.Cert.SO.K Robbins.Lanes

theorem LW_eq : LW = 144 := rfl

theorem LW_pos : 0 < LW := by decide

theorem mkVC_n (n : ℕ) : (mkVC n).n = n := rfl

theorem mkVC_G (n : ℕ) : (mkVC n).G = pack LW n (fun _ => 2 ^ 143) := guard_eq LW n LW_pos

theorem mkVC_O (n : ℕ) : (mkVC n).O = pack LW n (fun _ => 1) := ones_eq LW n LW_pos

theorem bc_eq (n c : ℕ) : bc (mkVC n) c = pack LW n (fun _ => c) := by
  show c * ones LW n = _
  rw [ones_eq LW n LW_pos, pack_const_mul]
  simp

theorem ge_eq (n : ℕ) (a b : ℕ → ℕ) (ha : ∀ l < n, a l < 2 ^ 143) (hb : ∀ l < n, b l < 2 ^ 143) :
    ge (mkVC n) (pack LW n a) (pack LW n b) =
      pack LW n (fun l => if b l ≤ a l then 2 ^ 143 else 0) :=
  geMask_pack LW n a b LW_pos ha hb

theorem full_eq (n : ℕ) (c : ℕ → Prop) [DecidablePred c] :
    full LW (pack LW n (fun l => if c l then 2 ^ 143 else 0)) =
      pack LW n (fun l => if c l then 2 ^ 144 - 1 else 0) :=
  full_pack LW n c LW_pos

theorem sl_eq (n : ℕ) (c : ℕ → Prop) [DecidablePred c] (a b : ℕ → ℕ)
    (ha : ∀ l < n, a l < 2 ^ 144) (hb : ∀ l < n, b l < 2 ^ 144) :
    sl (pack LW n (fun l => if c l then 2 ^ 143 else 0)) (pack LW n a) (pack LW n b) =
      pack LW n (fun l => if c l then a l else b l) := by
  unfold sl
  rw [full_eq]
  exact sel_pack LW n c a b LW_pos ha hb

theorem msk_eq (n : ℕ) (c : ℕ → Prop) [DecidablePred c] (a : ℕ → ℕ) (ha : ∀ l < n, a l < 2 ^ 144) :
    msk (pack LW n (fun l => if c l then 2 ^ 143 else 0)) (pack LW n a) =
      pack LW n (fun l => if c l then a l else 0) := by
  unfold msk
  rw [full_eq]
  show pack LW n a &&& _ = _
  rw [land_pack LW n _ _ LW_pos ha (fun l _ => by
    show (if c l then 2 ^ 144 - 1 else 0) < 2 ^ LW
    split_ifs <;> norm_num [LW])]
  refine pack_congr _ _ _ _ fun l hl => ?_
  split_ifs
  · rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (ha l hl)]
  · simp

theorem notM_eq (n : ℕ) (c : ℕ → Prop) [DecidablePred c] :
    notM (mkVC n) (pack LW n (fun l => if c l then 2 ^ 143 else 0)) =
      pack LW n (fun l => if ¬ c l then 2 ^ 143 else 0) := by
  show (mkVC n).G - _ = _
  rw [mkVC_G, pack_sub _ _ _ _ (fun l _ => by split_ifs <;> simp)]
  exact pack_congr _ _ _ _ fun l _ => by split_ifs <;> simp_all

theorem land_gm (n : ℕ) (c d : ℕ → Prop) [DecidablePred c] [DecidablePred d] :
    Nat.land (pack LW n (fun l => if c l then 2 ^ 143 else 0))
        (pack LW n (fun l => if d l then 2 ^ 143 else 0)) =
      pack LW n (fun l => if c l ∧ d l then 2 ^ 143 else 0) := by
  have hb : ∀ (p : Prop) [Decidable p], ∀ l < n, (fun l => if p then (2 : ℕ) ^ 143 else 0) l < 2 ^ LW :=
    fun p _ l _ => by show (if p then (2 : ℕ) ^ 143 else 0) < 2 ^ 144; split_ifs <;> norm_num
  show (_ : ℕ) &&& (_ : ℕ) = _
  rw [land_pack LW n _ _ LW_pos (fun l hl => hb (c l) l hl) (fun l hl => hb (d l) l hl)]
  refine pack_congr _ _ _ _ fun l _ => ?_
  by_cases h1 : c l <;> by_cases h2 : d l <;> simp [h1, h2]

theorem lor_gm (n : ℕ) (c d : ℕ → Prop) [DecidablePred c] [DecidablePred d] :
    Nat.lor (pack LW n (fun l => if c l then 2 ^ 143 else 0))
        (pack LW n (fun l => if d l then 2 ^ 143 else 0)) =
      pack LW n (fun l => if c l ∨ d l then 2 ^ 143 else 0) := by
  have hb : ∀ (p : Prop) [Decidable p], ∀ l < n, (fun l => if p then (2 : ℕ) ^ 143 else 0) l < 2 ^ LW :=
    fun p _ l _ => by show (if p then (2 : ℕ) ^ 143 else 0) < 2 ^ 144; split_ifs <;> norm_num
  show (_ : ℕ) ||| (_ : ℕ) = _
  rw [lor_pack LW n _ _ LW_pos (fun l hl => hb (c l) l hl) (fun l hl => hb (d l) l hl)]
  refine pack_congr _ _ _ _ fun l _ => ?_
  by_cases h1 : c l <;> by_cases h2 : d l <;> simp [h1, h2]

theorem lmin_eq (n : ℕ) (a b : ℕ → ℕ) (ha : ∀ l < n, a l < 2 ^ 143) (hb : ∀ l < n, b l < 2 ^ 143) :
    lmin LW (mkVC n).G (pack LW n a) (pack LW n b) = pack LW n (fun l => min (a l) (b l)) :=
  lmin_pack LW n a b LW_pos ha hb

theorem tsub_eq (n : ℕ) (a b : ℕ → ℕ) (ha : ∀ l < n, a l < 2 ^ 143) (hb : ∀ l < n, b l < 2 ^ 143) :
    tsub (mkVC n) (pack LW n a) (pack LW n b) = pack LW n (fun l => a l - b l) := by
  unfold tsub
  rw [lmin_eq n a b ha hb]
  show (_ : ℕ) - (_ : ℕ) = _
  rw [pack_sub _ _ _ _ (fun l _ => min_le_left _ _)]
  exact pack_congr _ _ _ _ fun l _ => by omega

theorem mulv_eq (n Q : ℕ) (a b : ℕ → ℕ) (hQ : Q ≤ 144) (ha : ∀ l < n, ∀ j < Q, a l * 2 ^ j < 2 ^ 144)
    (hb : ∀ l < n, b l < 2 ^ 144) :
    mulv (mkVC n) Q (pack LW n a) (pack LW n b) = pack LW n (fun l => a l * (b l % 2 ^ Q)) :=
  mulBS_pack_mod LW n Q a b LW_pos hQ ha hb

/-- `mulv` with a multiplier below `2 ^ Q`. -/
theorem mulv_eq' (n Q : ℕ) (a b : ℕ → ℕ) (hQ : Q ≤ 144) (ha : ∀ l < n, ∀ j < Q, a l * 2 ^ j < 2 ^ 144)
    (hb : ∀ l < n, b l < 2 ^ Q) :
    mulv (mkVC n) Q (pack LW n a) (pack LW n b) = pack LW n (fun l => a l * b l) :=
  mulBS_pack LW n Q a b LW_pos hQ ha hb

theorem shr36_eq (n : ℕ) (a : ℕ → ℕ) (ha : ∀ l < n, a l < 2 ^ 144) :
    shr36 (pack LW n a) (mkVC n) = pack LW n (fun l => a l / 2 ^ 36) := by
  unfold shr36
  rw [bc_eq]
  exact shrL_pack LW n 36 a (by decide) ha

theorem nz_eq (n : ℕ) (a : ℕ → ℕ) (ha : ∀ l < n, a l < 2 ^ 143) :
    nz (mkVC n) (pack LW n a) = pack LW n (fun l => if a l ≠ 0 then 2 ^ 143 else 0) := by
  unfold nz
  rw [bc_eq, ge_eq n _ a (fun _ _ => by norm_num) ha, mkVC_G]
  show (_ : ℕ) - (_ : ℕ) = _
  rw [pack_sub _ _ _ _ (fun l _ => by split_ifs <;> simp)]
  exact pack_congr _ _ _ _ fun l _ => by split_ifs <;> simp_all

theorem ind_eq (n : ℕ) (c : ℕ → Prop) [DecidablePred c] :
    ind LW (pack LW n (fun l => if c l then 2 ^ 143 else 0)) = pack LW n (fun l => if c l then 1 else 0) :=
  ind_pack LW n c LW_pos

theorem allGe_eq (n : ℕ) (a b : ℕ → ℕ) (ha : ∀ l < n, a l < 2 ^ 143) (hb : ∀ l < n, b l < 2 ^ 143) :
    allGe (mkVC n).G (pack LW n a) (pack LW n b) = true ↔ ∀ l < n, b l ≤ a l :=
  allGe_iff LW n a b LW_pos ha hb

theorem divQR_eq (n : ℕ) (a b : ℕ → ℕ) (ha : ∀ l < n, a l < 2 ^ 143)
    (hb : ∀ l < n, ∀ j < 37, b l * 2 ^ j < 2 ^ 143) :
    divQR LW 37 (mkVC n).G (pack LW n a) (pack LW n b) =
      (pack LW n (fun l => if b l = 0 then 2 ^ 37 - 1 else min (a l / b l) (2 ^ 37 - 1)),
        pack LW n (fun l => a l - b l * (if b l = 0 then 2 ^ 37 - 1 else min (a l / b l) (2 ^ 37 - 1)))) :=
  divQR_pack LW n 37 a b LW_pos (by decide) ha hb

theorem pre_eq (n k : ℕ) (f : ℕ → ℕ) (hf : ∀ l < n, f l < 2 ^ 144) (hk : k ≤ n) :
    pre LW k (pack LW n f) = pack LW k f :=
  pre_pack LW n k f hf hk

theorem preL_eq {ι : Type} (n k : ℕ) (F : ι → ℕ → ℕ) (xs : List ι) (hF : ∀ i ∈ xs, ∀ l < n, F i l < 2 ^ 144)
    (hk : k ≤ n) :
    preL k (xs.map fun i => pack LW n (F i)) = xs.map fun i => pack LW k (F i) := by
  unfold preL
  rw [lmap_eq, List.map_map]
  exact List.map_congr_left fun i hi => pre_eq n k (F i) (hF i hi) hk

theorem eqM_eq (n i : ℕ) (P : ℕ → ℕ) (hi : i < 2 ^ 143) (hP : ∀ l < n, P l < 2 ^ 143) :
    eqM (mkVC n) i (pack LW n P) = pack LW n (fun l => if P l = i then 2 ^ 143 else 0) := by
  unfold eqM
  rw [bc_eq, ge_eq n _ _ (fun _ _ => hi) hP, ge_eq n _ _ hP (fun _ _ => hi), land_gm]
  exact pack_congr _ _ _ _ fun l _ => by
    by_cases h : P l = i
    · simp [h]
    · have : ¬ (P l ≤ i ∧ i ≤ P l) := fun h' => h (le_antisymm h'.1 h'.2)
      simp [h, this]

end Robbins.Cert.SO.L
