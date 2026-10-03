import Mathlib
import Robbins.Cert.EvalM2

/-!
# The kernel combinators as list functions

Each recursor-form combinator of Robbins/Cert/EvalK.lean and Robbins/Cert/EvalM2.lean equals the
list function it implements, so that the correctness proofs of the evaluator reason with the list
library.
-/

namespace Robbins.Cert.K

theorem bsel_eq {α : Type} (b : Bool) (x y : α) : bsel b x y = if b then x else y := by
  cases b <;> rfl

@[simp] theorem bsel_true {α : Type} (x y : α) : bsel true x y = x := rfl

@[simp] theorem bsel_false {α : Type} (x y : α) : bsel false x y = y := rfl

theorem lfoldr_eq {α β : Type} (f : α → β → β) (b : β) (l : List α) :
    lfoldr f b l = l.foldr f b := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (f a) ih

theorem lmap_eq {α β : Type} (f : α → β) (l : List α) : lmap f l = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (f a :: ·) ih

theorem hd_eq (l : List Nat) : hd l = l.headD 0 := by
  cases l <;> rfl

theorem tl_eq {α : Type} (l : List α) : tl l = l.tail := by
  cases l <;> rfl

theorem ldrop_eq {α : Type} (k : Nat) (l : List α) : ldrop k l = l.drop k := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    show ldrop k (tl l) = l.drop (k + 1)
    rw [ih, tl_eq]
    cases l <;> simp

theorem ltake_eq {α : Type} (k : Nat) (l : List α) : ltake k l = l.take k := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    cases l with
    | nil => rfl
    | cons a l => exact congrArg (a :: ·) (ih l)

theorem lapp_eq {α : Type} (l1 l2 : List α) : lapp l1 l2 = l1 ++ l2 := by
  induction l1 with
  | nil => rfl
  | cons a l ih => exact congrArg (a :: ·) ih

theorem lrevOnto_eq {α : Type} (l acc : List α) : lrevOnto l acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a l ih =>
    show lrevOnto l (a :: acc) = (a :: l).reverse ++ acc
    rw [ih]; simp

theorem llast_eq {α : Type} (dflt : α) (l : List α) : llast dflt l = l.getLastD dflt := by
  suffices h : ∀ d, llast d l = l.getLastD d from h dflt
  induction l with
  | nil => intro d; rfl
  | cons a l ih =>
    intro d
    show llast a l = (a :: l).getLastD d
    rw [ih]
    cases l <;> simp [List.getLastD]

theorem lzipWith_eq {α β γ : Type} (f : α → β → γ) (l1 : List α) (l2 : List β) :
    lzipWith f l1 l2 = List.zipWith f l1 l2 := by
  induction l1 generalizing l2 with
  | nil => rfl
  | cons a l ih =>
    cases l2 with
    | nil => rfl
    | cons b l2 => exact congrArg (f a b :: ·) (ih l2)

theorem lflat_eq {α : Type} (l : List (List α)) : lflat l = l.flatten := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show lapp a (lflat l) = (a :: l).flatten
    rw [lapp_eq, ih]; simp

theorem lmapIdx_eq {α β : Type} (f : Nat → α → β) (k : Nat) (l : List α) :
    lmapIdx f k l = mapIdxFrom f k l := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih => exact congrArg (f k a :: ·) (ih (k + 1))

theorem lbeq_eq (l1 l2 : List Nat) : lbeq l1 l2 = true ↔ l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp [lbeq]
  | cons a l ih =>
    cases l2 with
    | nil => simp [lbeq]
    | cons b l2 =>
      show bsel (Nat.beq a b) (lbeq l l2) false = true ↔ a :: l = b :: l2
      rw [bsel_eq]
      by_cases hab : a = b
      · subst hab; simp [ih]
      · have : Nat.beq a b = false := by
          cases h : Nat.beq a b
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true h) hab
        simp [this, hab]

end Robbins.Cert.K

namespace Robbins.Cert.M2

open Robbins.Cert.K

theorem nmin_eq (a b : Nat) : nmin a b = min a b := by
  unfold nmin
  rw [bsel_eq]
  by_cases h : a ≤ b
  · simp [Nat.ble_eq, h]
  · simp [Nat.ble_eq, h]; omega

theorem lbeq2_eq (l1 l2 : List (List Nat)) : lbeq2 l1 l2 = true ↔ l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp [lbeq2]
  | cons a l ih =>
    cases l2 with
    | nil => simp [lbeq2]
    | cons b l2 =>
      show bsel (lbeq a b) (lbeq2 l l2) false = true ↔ a :: l = b :: l2
      rw [bsel_eq]
      by_cases hab : a = b
      · subst hab
        have : lbeq a a = true := (lbeq_eq a a).2 rfl
        simp [this, ih]
      · have : lbeq a b = false := by
          cases h : lbeq a b
          · rfl
          · exact absurd ((lbeq_eq a b).1 h) hab
        simp [this, hab]

end Robbins.Cert.M2
