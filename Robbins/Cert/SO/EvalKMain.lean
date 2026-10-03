import Robbins.Cert.SO.EvalKStep
import Robbins.Cert.SO.Sound

/-!
# The bound of a chain of checked second-order tables

`le_v_of_chainSO`: Theorem B (`le_v_of_tables`, Robbins/Cert/SO/Sound.lean) for the decoded tables of
a `ChainSO` (Robbins/Cert/SO/EvalKChain.lean).
-/

namespace Robbins.Cert.SO.K

open Robbins.Cert Robbins.Cert.K

/-- Theorem B for a chain of checked tables: `uh_1 (cnt_1, ..., cnt_1) / D ≤ v n`. -/
theorem le_v_of_chainSO (g : Grid) (hg : ok DS g = true) (d : ℕ) (hd1 : 1 ≤ d) (hd : g.m = d + 1)
    (L : List (List ℕ)) (hL : ChainSO g 1 L) :
    (uhOf d (L.getD 0 []) (fun _ => g.cnt 1) : ℝ) / DS ≤ Robbins.v g.n := by
  obtain ⟨-, -, hlast, hstep⟩ := chainSO_spec g hg d hd1 hd L 1 hL le_rfl
  have h := le_v_of_tables DS (by norm_num [DS]) g hg d (fun t => uhOf d (L.getD (t - 1) []))
    (fun t => sgOf d (L.getD (t - 1) [])) hlast (fun t ht1 ht k hk x hx => by
      have e : t + 1 - 1 = t - 1 + 1 := by omega
      simpa [e] using hstep t ht1 ht k hk x hx)
  simpa using h

end Robbins.Cert.SO.K
