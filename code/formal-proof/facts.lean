import Lean
import Robbins.Solution

/-! For the badges of ci.yml: the hypotheses of the theorems of config.json (their binders whose type is a
proposition, the bound `n ≥ 300` of `∀ n ≥ 300, ...` included) and the axioms they use. Run with
`lake env lean code/formal-proof/facts.lean`. -/

open Lean Meta in
#eval show MetaM Unit from do
  let mut hyps := 0
  let mut axs : Array Name := #[]
  for n in [``Robbins.v300, ``Robbins.main_so, ``Robbins.main_so_limit, ``Robbins.two_lt_v, ``Robbins.relaxed300,
      ``Robbins.RelaxedSubSolution.val_one_le_v, ``Robbins.v_mono, ``Robbins.robbinsValue_eq_v,
      ``Robbins.lower_bound_of_base, ``Robbins.limit_lower_bound_of_base, ``Robbins.v_le_five,
      ``Robbins.exists_tendsto_v, ``Robbins.main_limit, ``Robbins.two_lt_limit] do
    let c ← getConstInfo n
    hyps := hyps + (← forallTelescope c.type fun xs _ =>
      xs.foldlM (fun k x => do return if ← isProp (← inferType x) then k + 1 else k) 0)
    for a in ← collectAxioms n do
      unless axs.contains a do axs := axs.push a
  IO.println s!"hypotheses {hyps}"
  IO.println s!"axioms {axs.size}"
  IO.println s!"sorryAx {axs.contains ``sorryAx}"
