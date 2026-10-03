import Robbins.Cert.SO.EvalKMain

/-!
# The relaxed sub-solution of a chain of checked second-order tables

`relaxed_of_chainSO`: the tables of a `ChainSO` (Robbins/Cert/SO/EvalKChain.lean) give a relaxed
sub-solution (`relaxed_of_tables`, Robbins/Cert/SO/Sound.lean) whose value at time `1` and the memory
`(1, ..., 1)` is `uh_1 (cnt_1, ..., cnt_1) / D`, the bound of `le_v_of_chainSO`.
-/

namespace Robbins.Cert.SO.K

open Robbins.Cert

/-- A chain of checked tables gives a relaxed sub-solution of value
`uh_1 (cnt_1, ..., cnt_1) / D` at time `1` and the memory `(1, ..., 1)`. -/
theorem relaxed_of_chainSO (g : Grid) (hg : ok DS g = true) (d : ℕ) (hd1 : 1 ≤ d)
    (hd : g.m = d + 1) (L : List (List ℕ)) (hL : ChainSO g 1 L) :
    ∃ u : RelaxedSubSolution g.n (d + 1),
      u.u 1 (fun _ => 1) = (uhOf d (L.getD 0 []) (fun _ => g.cnt 1) : ℝ) / DS := by
  obtain ⟨-, -, hlast, hstep⟩ := chainSO_spec g hg d hd1 hd L 1 hL le_rfl
  obtain ⟨u, hu⟩ := relaxed_of_tables DS (by norm_num [DS]) g hg d
    (fun t => uhOf d (L.getD (t - 1) [])) (fun t => sgOf d (L.getD (t - 1) [])) hlast
    (fun t ht1 ht k hk x hx => by
      have e : t + 1 - 1 = t - 1 + 1 := by omega
      simpa [e] using hstep t ht1 ht k hk x hx)
  refine ⟨u, ?_⟩
  rw [hu]
  unfold uSO
  simp only [g.so_ceilR_one DS hg 1]
  have hpt : (pt DS g (g.glob 1 (g.cnt 1)) : ℝ) / DS - 1 = 0 := by
    rw [g.glob_of_ge le_rfl, g.so_pt_of_ge DS le_rfl, div_self (by norm_num [DS]), sub_self]
  simp [hpt]

end Robbins.Cert.SO.K
