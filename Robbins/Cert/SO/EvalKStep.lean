import Robbins.Cert.SO.EvalKVar
import Robbins.Cert.SO.EvalKTop

/-!
# The soundness of a checked step and of a chain

`checkStep_sound`: a passed step `checkStep g t Nn Nt` on a table `Nn` of the shape of `G_{t+1}`
gives a table `Nt` of the shape of `G_t` whose decoded states are below `bound` for every state of
`G_t` and every valid choice (the hypothesis `hstep` of `le_v_of_tables`, Robbins/Cert/SO/Sound.lean).
`chainSO_spec`: the same, time by time, for the tables of a `ChainSO`, with the table of time `n`
bounded by section 4 (`checkLast_sound`).
-/

namespace Robbins.Cert.SO.K

open Robbins.Cert Robbins.Cert.K

/-- Sections 5 and 6: a step. -/
theorem checkStep_sound (g : Grid) (hg : ok DS g = true) (d : ℕ) (hd1 : 1 ≤ d) (hd : g.m = d + 1)
    (t : ℕ) (ht1 : 1 ≤ t) (ht : t < g.n) (Nn Nt : List ℕ) (hNn : TableOK g d (t + 1) Nn)
    (h : checkStep g t Nn Nt = true) :
    TableOK g d t Nt ∧ ∀ k, g.IsState t k → ∀ x, ValidChoice g t x →
      (uhOf d Nt k : ℤ) ≤ (bound DS g d (uhOf d Nn) (sgOf d Nn) t (recList DS g t k x)).1 ∧
        ∀ l, (sgOf d Nt k l : ℤ) ≤ (bound DS g d (uhOf d Nn) (sgOf d Nn) t (recList DS g t k x)).2 l := by
  obtain ⟨hNt, hall⟩ := checkStep_states g hg hd1 hd ht1 ht h
  refine ⟨hNt, fun k hk x hx => ?_⟩
  obtain ⟨h1, h2⟩ := checkVar_sound g hg hd1 hd ht1 ht (fun H hH => lkOf_rank g hd hNn hH)
    (recList_ok (D := DS) hg ht1 ht hk hx) (hall k hk x hx)
  refine ⟨h1, fun l => ?_⟩
  have h2l := h2 l
  rwa [slopes_getD g hd] at h2l

/-- What a chain gives, time by time: the table of time `s` is `L[s - t]`. -/
theorem chainSO_spec (g : Grid) (hg : ok DS g = true) (d : ℕ) (hd1 : 1 ≤ d) (hd : g.m = d + 1) :
    ∀ (L : List (List ℕ)) (t : ℕ), ChainSO g t L → 1 ≤ t →
      L.length + t = g.n + 1 ∧ TableOK g d t (L.getD 0 []) ∧
      (∀ k, g.IsState g.n k →
        uhOf d (L.getD (g.n - t) []) k + ∑ l, pt DS g (g.glob g.n (k l)) ≤ (d + 2) * DS ∧
          ∀ l, sgOf d (L.getD (g.n - t) []) k l ≤ if k l < g.cnt g.n then DS else 0) ∧
      ∀ s, t ≤ s → s < g.n → ∀ k, g.IsState s k → ∀ x, ValidChoice g s x →
        (uhOf d (L.getD (s - t) []) k : ℤ) ≤ (bound DS g d (uhOf d (L.getD (s + 1 - t) []))
          (sgOf d (L.getD (s + 1 - t) [])) s (recList DS g s k x)).1 ∧
        ∀ l, (sgOf d (L.getD (s - t) []) k l : ℤ) ≤ (bound DS g d (uhOf d (L.getD (s + 1 - t) []))
          (sgOf d (L.getD (s + 1 - t) [])) s (recList DS g s k x)).2 l := by
  intro L t hChain ht1
  induction L generalizing t with
  | nil =>
      exfalso
      exact hChain
  | cons x rest ih =>
      cases rest with
      | nil =>
          rcases hChain with ⟨htn, hLast⟩
          subst htn
          have hLastSound := checkLast_sound g hg d hd x hLast
          rcases hLastSound with ⟨hTableOK, hRest⟩
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp; rw [add_comm]
          · simpa using hTableOK
          · simpa using hRest
          · intro s hs1 hs2
            omega
      | cons y rest' =>
          rcases hChain with ⟨hStep, hRest⟩
          have hIH := ih (t + 1) hRest (by omega)
          rcases hIH with ⟨hlenIH, hTableOKsucc, hTimeN, hBoundSucc⟩
          have ht_lt_gn : t < g.n := by
            have hpos : 0 < (y :: rest').length := by
              simp
            omega
          have hStepSound := checkStep_sound g hg d hd1 hd t ht1 ht_lt_gn
            ((y :: rest').getD 0 []) x hTableOKsucc hStep
          rcases hStepSound with ⟨hTableOKt, hBoundt⟩
          refine ⟨?_, ?_, ?_, ?_⟩
          · have : (x :: y :: rest').length = (y :: rest').length + 1 := by simp
            omega
          · simpa using hTableOKt
          · have hsub : g.n - t = (g.n - (t + 1)) + 1 := by omega
            have hgetD : (x :: y :: rest').getD (g.n - t) [] = (y :: rest').getD (g.n - (t + 1)) [] := by
              rw [hsub, List.getD_cons_succ]
            rw [hgetD]
            exact hTimeN
          · intro s hs1 hs2 k hk x' hx'
            have hs_cases : s = t ∨ t < s := by omega
            rcases hs_cases with (hs_eq | hs_gt)
            · subst hs_eq
              simp
              exact hBoundt k hk x' hx'
            · have hgetD1 : (x :: y :: rest').getD (s - t) [] = (y :: rest').getD (s - (t + 1)) [] := by
                have : s - t = (s - (t + 1)) + 1 := by omega
                rw [this, List.getD_cons_succ]
              have hgetD2 : (x :: y :: rest').getD (s + 1 - t) [] = (y :: rest').getD (s - t) [] := by
                have : s + 1 - t = (s - t) + 1 := by omega
                rw [this, List.getD_cons_succ]
              rw [hgetD1, hgetD2]
              simpa [show s + 1 - (t + 1) = s - t by omega] using
                hBoundSucc s (Nat.succ_le_of_lt hs_gt) hs2 k hk x' hx'

end Robbins.Cert.SO.K
