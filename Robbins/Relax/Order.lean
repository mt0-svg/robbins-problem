import Robbins.Relax.Defs

/-!
# Memories: order facts and the counting identity

Section 2.1 and Lemma 3.2 of the paper. `ins y x` is again a memory, `ins` and `drop` are nondecreasing,
and the counting identity `#{k | y k < z} + 1{x < z} = #{k | ins y x k < z} + 1{drop y x < z}`
(`card_lt_add_ite`), by induction on `m` through `ins_snoc` and `drop_snoc`.
-/

namespace Robbins

open MeasureTheory

theorem isMemory_one (m : ℕ) : IsMemory (fun _ : Fin m => (1 : ℝ)) := by
  refine ⟨monotone_const, ?_⟩
  intro k
  rw [Set.mem_Icc]
  constructor
  · norm_num
  · norm_num

theorem IsMemory.init {m : ℕ} {y : Fin (m + 1) → ℝ} (hy : IsMemory y) : IsMemory (Fin.init y) := by
  refine ⟨fun i j hij => hy.1 (Fin.castSucc_le_castSucc_iff.mpr hij), fun i => hy.2 _⟩

theorem IsMemory.le_last {m : ℕ} {y : Fin (m + 1) → ℝ} (hy : IsMemory y) (k : Fin m) :
    Fin.init y k ≤ y (Fin.last m) := by
  exact hy.1 (Fin.le_last _)

theorem drop_mem_Icc {m : ℕ} {y : Fin m → ℝ} (hy : IsMemory y) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : drop y x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold drop
  split_ifs with h
  · exact hx
  · rcases hy with ⟨_, hy_mem⟩
    rcases hy_mem ⟨m - 1, by omega⟩ with ⟨hy0, hy1⟩
    rcases hx with ⟨hx0, hx1⟩
    refine ⟨le_max_iff.mpr (Or.inl hy0), max_le hy1 hx1⟩

theorem ins_mem_Icc {m : ℕ} {y : Fin m → ℝ} (hy : IsMemory y) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (k : Fin m) : ins y x k ∈ Set.Icc (0 : ℝ) 1 := by
  have hy_mem := hy.2
  have hyk := hy_mem k
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have hyk0 : 0 ≤ y k := hyk.1
  have hyk1 : y k ≤ 1 := hyk.2
  unfold ins
  have hleft0 : 0 ≤ (if h : (k : ℕ) = 0 then 0 else y ⟨k - 1, by omega⟩) := by
    split
    · exact le_refl 0
    · rename_i h
      have hkpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero h
      have hkm1_lt_m : (k : ℕ) - 1 < m := by
        have hk_lt_m : (k : ℕ) < m := k.isLt
        omega
      have hmem := hy_mem ⟨(k : ℕ) - 1, hkm1_lt_m⟩
      exact hmem.1
  have hleft1 : (if h : (k : ℕ) = 0 then 0 else y ⟨k - 1, by omega⟩) ≤ 1 := by
    split
    · exact zero_le_one
    · rename_i h
      have hkpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero h
      have hkm1_lt_m : (k : ℕ) - 1 < m := by
        have hk_lt_m : (k : ℕ) < m := k.isLt
        omega
      have hmem := hy_mem ⟨(k : ℕ) - 1, hkm1_lt_m⟩
      exact hmem.2
  have hright0 : 0 ≤ min (y k) x := by
    exact (le_min_iff.mpr ⟨hyk0, hx0⟩)
  have hright1 : min (y k) x ≤ 1 := by
    exact le_trans (min_le_left _ _) hyk1
  have h0 : 0 ≤ max (if h : (k : ℕ) = 0 then 0 else y ⟨k - 1, by omega⟩) (min (y k) x) :=
    le_trans hleft0 (le_max_left _ _)
  have h1 : max (if h : (k : ℕ) = 0 then 0 else y ⟨k - 1, by omega⟩) (min (y k) x) ≤ 1 :=
    max_le hleft1 hright1
  exact ⟨h0, h1⟩

theorem ins_monotone {m : ℕ} {y : Fin m → ℝ} (hy : IsMemory y) (x : ℝ) : Monotone (ins y x) := by
  rcases hy with ⟨hy_mono, hy_bound⟩
  intro a b h
  unfold ins
  apply max_le_max
  · dsimp
    by_cases ha : (a : ℕ) = 0
    · simp [ha]
      by_cases hb : (b : ℕ) = 0
      · simp [hb]
      · simp [hb]
        have hmem := hy_bound ⟨(b : ℕ) - 1, by
          have hb_lt_m : (b : ℕ) < m := b.2
          omega⟩
        exact hmem.1
    · simp [ha]
      by_cases hb : (b : ℕ) = 0
      · have ha_pos : 0 < (a : ℕ) := Nat.pos_of_ne_zero ha
        have h_ab : (a : ℕ) ≤ (b : ℕ) := h
        rw [hb] at h_ab
        omega
      · simp [hb]
        apply hy_mono
        have h_ab : (a : ℕ) ≤ (b : ℕ) := h
        exact Nat.sub_le_sub_right h_ab 1
  · apply min_le_min
    · apply hy_mono h
    · rfl

theorem ins_mem {m : ℕ} {y : Fin m → ℝ} (hy : IsMemory y) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : IsMemory (ins y x) := by
  exact ⟨ins_monotone hy x, ins_mem_Icc hy hx⟩

theorem ins_mono {m : ℕ} {y y' : Fin m → ℝ} {x x' : ℝ} (hy : y ≤ y') (hx : x ≤ x') :
    ins y x ≤ ins y' x' := by
  intro k
  unfold ins
  apply max_le_max
  · by_cases hk : (k : ℕ) = 0
    · simp [hk]
    · simp [hk]
      exact hy ⟨k - 1, by omega⟩
  · exact min_le_min (hy k) hx

theorem drop_mono {m : ℕ} {y y' : Fin m → ℝ} {x x' : ℝ} (hy : y ≤ y') (hx : x ≤ x') :
    drop y x ≤ drop y' x' := by
  unfold drop
  split_ifs with h
  · exact hx
  · exact max_le_max (hy ⟨m - 1, by omega⟩) hx

theorem ins_snoc {m : ℕ} (y : Fin m → ℝ) (a x : ℝ) (hy : ∀ k, y k ≤ a) (h0 : 0 ≤ min x a) :
    ins (Fin.snoc (α := fun _ => ℝ) y a) x =
      Fin.snoc (α := fun _ => ℝ) (ins y x) (min (drop y x) a) := by
  funext k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · simp only [Fin.snoc_last, ins, Fin.val_last]
    by_cases hm : m = 0
    · subst hm
      simp only [drop, dif_pos]
      rw [max_eq_right (by simpa [min_comm] using h0), min_comm]
    · rw [dif_neg hm]
      have hb : y ⟨m - 1, by omega⟩ ≤ a := hy _
      have e : (Fin.snoc (α := fun _ => ℝ) y a ⟨m - 1, by omega⟩ : ℝ) = y ⟨m - 1, by omega⟩ := by
        simp [Fin.snoc, show m - 1 < m by omega]
      rw [e]
      simp only [drop, dif_neg hm]
      rcases le_total x a with hxa | hxa
      · rw [min_eq_right hxa, min_eq_left (max_le hb hxa)]
      · rw [min_eq_left hxa, max_eq_right hb, min_eq_right (le_max_of_le_right hxa)]
  · simp only [Fin.snoc_castSucc, ins, Fin.coe_castSucc]
    split_ifs with hk
    · rfl
    · congr 1
      simp [Fin.snoc, show (k : ℕ) - 1 < m by omega]

theorem drop_snoc {m : ℕ} (y : Fin m → ℝ) (a x : ℝ) (hy : ∀ k, y k ≤ a) :
    drop (Fin.snoc (α := fun _ => ℝ) y a) x = max (drop y x) a := by
  have e : (Fin.snoc (α := fun _ => ℝ) y a ⟨m + 1 - 1, by omega⟩ : ℝ) = a := by
    simp [Fin.snoc]
  simp only [drop, dif_neg (Nat.succ_ne_zero m), e]
  by_cases hm : m = 0
  · rw [dif_pos hm, max_comm]
  · rw [dif_neg hm, max_assoc, max_comm x a, ← max_assoc, max_eq_right (hy _)]

theorem ite_lt_add_ite_lt (d a z : ℝ) :
    (if d < z then 1 else 0 : ℕ) + (if a < z then 1 else 0) =
      (if min d a < z then 1 else 0) + (if max d a < z then 1 else 0) := by
  rcases le_total d a with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, add_comm]

theorem card_filter_castSucc {k : ℕ} (f : Fin (k + 1) → ℝ) (z : ℝ) :
    (Finset.univ.filter fun i => f i < z).card =
      (Finset.univ.filter fun i : Fin k => f (Fin.castSucc i) < z).card +
        (if f (Fin.last k) < z then 1 else 0) := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]

/-- B1, the counting identity. -/
theorem card_lt_add_ite {m : ℕ} {y : Fin m → ℝ} (hy : IsMemory y) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (z : ℝ) :
    (Finset.univ.filter fun k => y k < z).card + (if x < z then 1 else 0) =
      (Finset.univ.filter fun k => ins y x k < z).card + (if drop y x < z then 1 else 0) := by
  induction m with
  | zero =>
    simp [drop]
  | succ m ih =>
    have hya : y = Fin.snoc (α := fun _ => ℝ) (Fin.init y) (y (Fin.last m)) :=
      (Fin.snoc_init_self y).symm
    have hle : ∀ k, Fin.init y k ≤ y (Fin.last m) := hy.le_last
    have h0 : 0 ≤ min x (y (Fin.last m)) := le_min hx.1 (hy.2 _).1
    have hins := ins_snoc (Fin.init y) (y (Fin.last m)) x hle h0
    have hdrop := drop_snoc (Fin.init y) (y (Fin.last m)) x hle
    rw [← hya] at hins hdrop
    rw [hins, hdrop, card_filter_castSucc y z, card_filter_castSucc _ z]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    have := ih hy.init
    have hid := ite_lt_add_ite_lt (drop (Fin.init y) x) (y (Fin.last m)) z
    change (Finset.univ.filter fun i : Fin m => Fin.init y i < z).card + _ + _ = _
    omega

end Robbins
