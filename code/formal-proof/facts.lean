import Lean
import Robbins.Solution

/-! For the badges of ci.yml: the hypotheses of the theorems of config.json and the axioms they use. A hypothesis
is a binder whose type is a proposition that mentions none of the earlier binders: `n ≥ 300` in
`∀ n ≥ 300, ...` or `Tendsto v atTop (𝓝 V)` in `∀ V, Tendsto v atTop (𝓝 V) → ...` restricts a quantified
variable and is not counted. Run with `lake env lean code/formal-proof/facts.lean`. -/

open Lean Meta in
#eval show MetaM Unit from do
  let mut hyps := 0
  let mut axs : Array Name := #[]
  for n in [``Robbins.v300, ``Robbins.main_so, ``Robbins.main_so_limit, ``Robbins.two_lt_v, ``Robbins.relaxed300,
      ``Robbins.RelaxedSubSolution.val_one_le_v, ``Robbins.v_mono, ``Robbins.robbinsValue_eq_v,
      ``Robbins.lower_bound_of_base, ``Robbins.limit_lower_bound_of_base] do
    let c ← getConstInfo n
    hyps := hyps + (← forallTelescope c.type fun xs _ => do
      let mut k := 0
      for i in [0:xs.size] do
        let ty ← inferType xs[i]!
        if ← isProp ty then
          unless (xs.extract 0 i).any (fun y => ty.containsFVar y.fvarId!) do k := k + 1
      return k)
    for a in ← collectAxioms n do
      unless axs.contains a do axs := axs.push a
  IO.println s!"hypotheses {hyps}"
  IO.println s!"axioms {axs.size}"
  IO.println s!"sorryAx {axs.contains ``sorryAx}"
