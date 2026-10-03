import Robbins.Basic.Time

/-!
# Bounds on the rank and the expected rank

`1 ≤ r.rank x ≤ n + 1`, the rank is measurable and integrable, so `1 ≤ r.expectedRank ≤ n + 1`:
the infimum `v (n + 1)` is over a nonempty set bounded below, hence the true infimum
(`v_succ_le`, `le_v_succ`).
-/

namespace Robbins

open MeasureTheory

theorem Rule.one_le_rank {n : ℕ} (r : Rule (n + 1)) (x : Fin (n + 1) → ℝ) : 1 ≤ r.rank x := by
  unfold Rule.rank
  exact Nat.le_add_right 1 _

theorem Rule.rank_le {n : ℕ} (r : Rule (n + 1)) (x : Fin (n + 1) → ℝ) : r.rank x ≤ n + 1 := by
  unfold Rule.rank
  have hfilter : (Finset.univ.filter fun j => x j < x (r.time x)) ⊆ Finset.univ.erase (r.time x) := by
    intro j hj
    simp at hj ⊢
    intro h_eq
    have : x (r.time x) < x (r.time x) := by
      rw [h_eq] at hj
      exact hj
    exact lt_irrefl _ this
  have hcard : (Finset.univ.erase (r.time x)).card = n := by
    simp
  have hle : (Finset.univ.filter fun j => x j < x (r.time x)).card ≤ n := by
    calc
      (Finset.univ.filter fun j => x j < x (r.time x)).card ≤ (Finset.univ.erase (r.time x)).card :=
        Finset.card_le_card hfilter
      _ = n := hcard
  omega

theorem Rule.measurable_rank {n : ℕ} (r : Rule (n + 1)) :
    Measurable fun x => (r.rank x : ℝ) := by
  let g : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ := fun t x =>
    1 + ∑ j : Fin (n + 1), if x j < x t then (1 : ℝ) else 0
  have hg_meas : ∀ t, Measurable (g t) := by
    intro t
    dsimp [g]
    refine Measurable.add measurable_const ?_
    refine Finset.measurable_sum Finset.univ fun j _ => ?_
    refine Measurable.ite (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply t))
      measurable_const measurable_const
  have h_f_prod : Measurable (fun (p : (Fin (n + 1) → ℝ) × Fin (n + 1)) => g p.2 p.1) := by
    apply measurable_from_prod_countable_left
    exact hg_meas
  have h_time_meas : Measurable r.time := Rule.measurable_time r
  have h_eq : (fun x => (r.rank x : ℝ)) = (fun x => g (r.time x) x) := by
    ext x
    dsimp [g, Rule.rank]
    simp only [Nat.cast_add, Nat.cast_one]
    congr 1
    have h := Finset.card_filter (fun j => x j < x (r.time x)) (Finset.univ : Finset (Fin (n + 1)))
    simpa using congrArg (fun k : ℕ => (k : ℝ)) h
  rw [h_eq]
  have h_pair : Measurable (fun x => (x, r.time x)) :=
    Measurable.prodMk measurable_id h_time_meas
  exact h_f_prod.comp h_pair

theorem Rule.integrable_rank {n : ℕ} (r : Rule (n + 1)) :
    Integrable (fun x => (r.rank x : ℝ)) (law (n + 1)) := by
  refine MeasureTheory.Integrable.of_bound (r.measurable_rank).aestronglyMeasurable (n + 1 : ℝ) ?_
  refine ae_of_all _ ?_
  intro x
  have hrank := r.rank_le x
  have hrank_nonneg : 0 ≤ (r.rank x : ℝ) := Nat.cast_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hrank_nonneg]
  exact mod_cast hrank

theorem Rule.one_le_expectedRank {n : ℕ} (r : Rule (n + 1)) : 1 ≤ r.expectedRank := by
  unfold Rule.expectedRank
  calc
    (1 : ℝ) = ∫ x, (1 : ℝ) ∂law (n + 1) := by
      rw [integral_const, probReal_univ, smul_eq_mul, mul_one]
    _ ≤ ∫ x, (r.rank x : ℝ) ∂law (n + 1) :=
      integral_mono (integrable_const (1 : ℝ)) r.integrable_rank (fun x => by
        have h := r.one_le_rank x
        simpa using h)

theorem Rule.expectedRank_le {n : ℕ} (r : Rule (n + 1)) : r.expectedRank ≤ n + 1 := by
  unfold Rule.expectedRank
  calc
    ∫ x, (r.rank x : ℝ) ∂law (n + 1) ≤ ∫ x, ((n : ℝ) + 1) ∂law (n + 1) :=
      integral_mono r.integrable_rank (integrable_const ((n : ℝ) + 1)) (fun x => by
        have h := r.rank_le x
        simpa using Nat.cast_le.mpr h)
    _ = ((law (n + 1)).real Set.univ) • ((n : ℝ) + 1) := by rw [integral_const]
    _ = (1 : ℝ) • ((n : ℝ) + 1) := by rw [probReal_univ]
    _ = (n : ℝ) + 1 := by simp
    _ = (n + 1 : ℝ) := by simp
    _ = n + 1 := by norm_cast

theorem bddBelow_expectedRank (n : ℕ) :
    BddBelow (Set.range fun r : Rule (n + 1) => r.expectedRank) := by
  exact ⟨1, by rintro _ ⟨r, rfl⟩; exact r.one_le_expectedRank⟩

theorem v_succ_le {n : ℕ} (r : Rule (n + 1)) : v (n + 1) ≤ r.expectedRank := by
  exact ciInf_le (bddBelow_expectedRank n) r

theorem le_v_succ {n : ℕ} {c : ℝ} (h : ∀ r : Rule (n + 1), c ≤ r.expectedRank) :
    c ≤ v (n + 1) := by
  exact le_ciInf h

theorem one_le_v_succ (n : ℕ) : 1 ≤ v (n + 1) := by
  exact le_v_succ fun r => r.one_le_expectedRank

end Robbins
