import Robbins.Mono.Basic
import Robbins.Basic.Time

/-!
# Monotonicity of `v`: the simulating rule against `σ` (step 5 of C1)

On a sequence `y` with values below 1 and `w > 0`, the simulating rule `simRule σ J w` stops at the
time of `σ` on `virt J w y` when that time is before `J`, one step earlier when it is after `J`, and
its rank is at most the rank of `σ` (`rank_simRule_le`).
-/

namespace Robbins

open MeasureTheory

theorem val_succAbove {N : ℕ} (J : Fin (N + 1)) (j : Fin N) :
    (J.succAbove j : ℕ) = if (j : ℕ) < J then (j : ℕ) else j + 1 := by
  by_cases h : Fin.castSucc j < J
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, if_pos (by simpa [Fin.lt_def] using h)]
    rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (not_lt.mp h), if_neg (by simpa [Fin.lt_def] using h)]
    rfl

theorem simCond_congr {n : ℕ} (σ : Rule (n + 2)) (J : Fin (n + 2)) (w : ℝ) (i : Fin (n + 1))
    {y y' : Fin (n + 1) → ℝ} (hyy : ∀ j : Fin (n + 1), (j : ℕ) ≤ i → y j = y' j) :
    simCond σ J w i y ↔ simCond σ J w i y' := by
  have key : ∀ k : Fin (n + 2), (∀ j : Fin (n + 1), (J.succAbove j : ℕ) ≤ k → (j : ℕ) ≤ i) →
      history (virt J w y) k = history (virt J w y') k := fun k hk =>
    history_virt_congr J w k fun j hj => hyy j (hk j hj)
  unfold simCond
  split_ifs with h
  · have e := key i.castSucc fun j hj => by
      rw [val_succAbove] at hj
      simp only [Fin.coe_castSucc] at hj
      split_ifs at hj <;> omega
    rw [e]
  · have e1 := key J fun j hj => by
      rw [val_succAbove] at hj
      split_ifs at hj <;> omega
    have e2 := key i.succ fun j hj => by
      rw [val_succAbove] at hj
      simp only [Fin.val_succ] at hj
      split_ifs at hj <;> omega
    rw [e1, e2]

theorem mem_simRule_stopSet {n : ℕ} (σ : Rule (n + 2)) (J : Fin (n + 2)) (w : ℝ)
    (y : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    history y i ∈ (simRule σ J w).stopSet i ↔ simCond σ J w i y := by
  show simCond σ J w i (pad i (history y i)) ↔ simCond σ J w i y
  exact simCond_congr σ J w i fun j hj => pad_history y i j hj

theorem time_simRule_of_lt {n : ℕ} (σ : Rule (n + 2)) (J : Fin (n + 2)) (w : ℝ)
    (y : Fin (n + 1) → ℝ) (ht : (σ.time (virt J w y) : ℕ) < J) :
    ((simRule σ J w).time y : ℕ) = σ.time (virt J w y) := by
  have hJ := J.isLt
  have hspec := (σ.time_eq_iff (virt J w y) (σ.time (virt J w y))).mp rfl
  let s : Fin (n + 1) := ⟨σ.time (virt J w y), by omega⟩
  have hcs : s.castSucc = σ.time (virt J w y) := Fin.ext rfl
  suffices h : (simRule σ J w).time y = s by rw [h]
  rw [Rule.time_eq_iff]
  refine ⟨Or.inl ?_, fun r hr => ?_⟩
  · rw [mem_simRule_stopSet]
    unfold simCond
    rw [if_pos (show (s : ℕ) < J from ht), hcs]
    rcases hspec.1 with h | h
    · exact h
    · exfalso
      have := congrArg Fin.val h
      simp only [Fin.val_last] at this
      omega
  · rw [mem_simRule_stopSet]
    unfold simCond
    have hr' : (r : ℕ) < s := hr
    have hs : (s : ℕ) = σ.time (virt J w y) := rfl
    rw [if_pos (show (r : ℕ) < J by omega)]
    exact hspec.2 r.castSucc (by rw [Fin.lt_def, Fin.coe_castSucc]; omega)

theorem time_simRule_of_gt {n : ℕ} (σ : Rule (n + 2)) (J : Fin (n + 2)) (w : ℝ)
    (y : Fin (n + 1) → ℝ) (ht : (J : ℕ) < σ.time (virt J w y)) :
    ((simRule σ J w).time y : ℕ) + 1 = σ.time (virt J w y) := by
  have hT := (σ.time (virt J w y)).isLt
  have hspec := (σ.time_eq_iff (virt J w y) (σ.time (virt J w y))).mp rfl
  let s : Fin (n + 1) := ⟨σ.time (virt J w y) - 1, by omega⟩
  have hss : s.succ = σ.time (virt J w y) := Fin.ext (by simp [s]; omega)
  have hJs : ¬ (s : ℕ) < J := by simp only [s]; omega
  have hJT : ¬ history (virt J w y) J ∈ σ.stopSet J := hspec.2 J (Fin.lt_def.mpr ht)
  suffices h : (simRule σ J w).time y = s by rw [h]; simp only [s]; omega
  rw [Rule.time_eq_iff]
  refine ⟨?_, fun r hr => ?_⟩
  · rcases hspec.1 with h | h
    · left
      rw [mem_simRule_stopSet]
      unfold simCond
      rw [if_neg hJs, hss]
      exact Or.inr h
    · right
      have := congrArg Fin.val h
      simp only [Fin.val_last] at this
      exact Fin.ext (by simp only [s, Fin.val_last]; omega)
  · rw [mem_simRule_stopSet]
    unfold simCond
    have hr' : (r : ℕ) < s := hr
    split_ifs with hrJ
    · exact hspec.2 r.castSucc (by rw [Fin.lt_def]; simp only [Fin.coe_castSucc, s] at hr' ⊢; omega)
    · rintro (h | h)
      · exact hJT h
      · exact hspec.2 r.succ (by rw [Fin.lt_def]; simp only [Fin.val_succ, s] at hr' ⊢; omega) h

theorem rank_simRule_le {n : ℕ} (σ : Rule (n + 2)) (J : Fin (n + 2)) {w : ℝ} (hw : 0 < w)
    (y : Fin (n + 1) → ℝ) (hy : ∀ j, y j < 1) :
    (simRule σ J w).rank y ≤ σ.rank (virt J w y) := by
  have hcount : ∀ s : Fin (n + 1),
      (Finset.univ.filter fun k => virt J w y k < w * y s).card =
        (Finset.univ.filter fun j => y j < y s).card := by
    intro s
    rw [card_virt_lt, if_neg (not_lt.mpr (by nlinarith [hy s])), add_zero]
    congr 1
    exact Finset.filter_congr fun j _ => mul_lt_mul_iff_right₀ hw
  unfold Rule.rank
  rcases lt_trichotomy (σ.time (virt J w y) : ℕ) J with h | h | h
  · have ht := time_simRule_of_lt σ J w y h
    have hx := virt_apply_lt J w y _ h
    have hs : (⟨σ.time (virt J w y), by omega⟩ : Fin (n + 1)) = (simRule σ J w).time y :=
      Fin.ext ht.symm
    rw [hx, hs, hcount]
  · have hJ : σ.time (virt J w y) = J := Fin.ext h
    rw [hJ, virt_apply_same, card_virt_lt, if_neg (lt_irrefl w), add_zero]
    have hall : (Finset.univ.filter fun j => w * y j < w) = Finset.univ :=
      Finset.filter_true_of_mem fun j _ => by nlinarith [hy j]
    rw [hall, Finset.card_univ, Fintype.card_fin]
    have := (simRule σ J w).rank_le y
    unfold Rule.rank at this
    omega
  · have ht := time_simRule_of_gt σ J w y h
    have hx := virt_apply_gt J w y _ h
    have hs : (⟨σ.time (virt J w y) - 1, by omega⟩ : Fin (n + 1)) = (simRule σ J w).time y :=
      Fin.ext (by simp only; omega)
    rw [hx, hs, hcount]

end Robbins
