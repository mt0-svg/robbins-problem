import Mathlib
import Robbins.Cert.Spec
import Robbins.Cert.SO.EvalK

/-!
# The decoded tables of a second-order run

A claimed table is a list of literals of 16 packed states (Robbins/Cert/SO/EvalK.lean). Its states
in rank order are `decAll d T`; the state of a sorted tuple `k` is the one of rank `rank k` (the rank
of section 2 of the format), and `uhOf`, `sgOf` read its fields. `TableOK g d t T`: the table has one
state per sorted tuple of local indices of `G_t`, and the decoded state of index `idx` is the field
`idx % 16` of the literal `idx / 16` (what the lookups of the evaluator read).
-/

namespace Robbins.Cert.SO.K

open Robbins.Cert Robbins.Cert.K

/-- The rank of a sorted tuple (section 2 of the format): `sum over l of C (k_l + l, l + 1)`. -/
def rank {m : ℕ} (k : Fin m → ℕ) : ℕ := ∑ l : Fin m, (k l + (l : ℕ)).choose ((l : ℕ) + 1)

/-- `W = 48 (d + 2)`, the bits of a state with `d + 1` slopes. -/
def Wd (d : ℕ) : ℕ := 48 * (d + 2)

/-- The states of a table, in rank order. -/
noncomputable def decAll (d : ℕ) (T : List ℕ) : List ℕ := lfoldr (decLit (Wd d) (2 ^ Wd d - 1)) [] T

/-- The packed state of `k`. -/
noncomputable def stOf (d : ℕ) (T : List ℕ) (k : Fin (d + 1) → ℕ) : ℕ := (decAll d T).getD (rank k) 0

/-- `uh (k)` of a table. -/
noncomputable def uhOf (d : ℕ) (T : List ℕ) (k : Fin (d + 1) → ℕ) : ℕ := stOf d T k % 2 ^ 48

/-- `sg (k)_l` of a table. -/
noncomputable def sgOf (d : ℕ) (T : List ℕ) (k : Fin (d + 1) → ℕ) (l : Fin (d + 1)) : ℕ :=
  stOf d T k / 2 ^ (48 * ((l : ℕ) + 1)) % 2 ^ 48

/-- A table of time `t`: one state per sorted tuple of local indices of `G_t`, and the decoded
state of index `idx` is the field `idx % 16` of the literal `idx / 16` (what the lookups of the
evaluator read). -/
def TableOK (g : Grid) (d t : ℕ) (T : List ℕ) : Prop :=
  (decAll d T).length = (g.cnt t + d + 1).choose (d + 1) ∧
    ∀ idx, idx < (decAll d T).length →
      (decAll d T).getD idx 0 = T.getD (idx / 16) 0 / 2 ^ (Wd d * (idx % 16)) % 2 ^ Wd d

end Robbins.Cert.SO.K
