import Robbins.Lanes.OpsSound
import Robbins.Cert.SO.EvalK

/-!
# Packed lanes: the states of the claimed tables against `decLit`

The decoding `decLit` of the scalar second-order check (Robbins/Cert/SO/EvalK.lean), folded over
the literals of a claimed table, lists the states `allStates` of Robbins/Lanes/OpsSound.lean.
-/

namespace Robbins.Lanes

open Robbins.Cert.K Robbins.Cert.SO.K

/-- The recursion of `decLit` with `k` steps lists the states `litStates Ws k x`. -/
theorem decLit_rec (Ws : ℕ) (rest : List ℕ) (k : ℕ) : ∀ x,
    (@Nat.rec (fun _ => ℕ → List ℕ) (fun _ => rest)
      (fun _ ih x => bsel (Nat.ble x 1) rest (Nat.land x (2 ^ Ws - 1) :: ih (Nat.shiftRight x Ws)))
      k) x = litStates Ws k x ++ rest := by
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    show bsel (Nat.ble x 1) rest (Nat.land x (2 ^ Ws - 1) :: _) = _
    rw [ih]
    by_cases hx : x ≤ 1
    · have : Nat.ble x 1 = true := by rw [Nat.ble_eq]; exact hx
      rw [this]
      simp [litStates, hx, bsel]
    · have : Nat.ble x 1 = false := Bool.eq_false_iff.2 fun h => hx (by rw [Nat.ble_eq] at h; exact h)
      rw [this]
      show Nat.land x (2 ^ Ws - 1) :: (litStates Ws k (Nat.shiftRight x Ws) ++ rest) = _
      simp only [litStates, hx, ↓reduceIte, List.cons_append]
      rw [show Nat.land x (2 ^ Ws - 1) = x &&& (2 ^ Ws - 1) from rfl,
        Nat.and_two_pow_sub_one_eq_mod,
        show Nat.shiftRight x Ws = x >>> Ws from rfl, Nat.shiftRight_eq_div_pow]

theorem decLit_eq (Ws x : ℕ) (rest : List ℕ) :
    decLit Ws (2 ^ Ws - 1) x rest = litStates Ws 16 x ++ rest :=
  decLit_rec Ws rest 16 x

/-- The states of the literals, as the scalar check decodes them. -/
theorem lfoldr_decLit (Ws : ℕ) (lits : List ℕ) :
    lfoldr (decLit Ws (2 ^ Ws - 1)) [] lits = allStates Ws lits := by
  induction lits with
  | nil => rfl
  | cons x t ih =>
    show decLit Ws (2 ^ Ws - 1) x (lfoldr (decLit Ws (2 ^ Ws - 1)) [] t) = _
    rw [ih, decLit_eq, allStates, allStates, List.flatMap_cons]

end Robbins.Lanes
