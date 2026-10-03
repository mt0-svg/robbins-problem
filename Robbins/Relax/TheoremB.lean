import Robbins.Relax.Traj
import Robbins.Basic.Verification

/-!
# Theorem B

Theorem 2.2 of the paper: a relaxed sub-solution for `n ≥ 1` values bounds `v n` from below at the
memory `(1, ..., 1)`. The proof is the verification lemma (`le_v_of_verification`) with the
functions `relaxL n m u k` of its proof: `L_0 = u_1 (1, ..., 1)` and, for a history `(h, x)` of length
`k + 1` (paper time `t = k + 1`, memory `y = traj m k h`),
`L_t (h, x) = relaxStep n u t y x + phi m (n - t) k h x`, where `relaxStep` is
`min (S_t (y, x), pi_t (y, x) + u_{t+1} (ins y x))` for `t < n` and `S_n (y, x)` at `t = n`.
-/

namespace Robbins

open MeasureTheory

/-- The stop or continue part of `L_t` at memory `y` and value `x`:
`min (S_t (y, x)) (pi_t (y, x) + u_{t+1} (ins y x))` for `t < n`, and `S_n (y, x)` at `t = n`. -/
noncomputable def relaxStep (n : ℕ) {m : ℕ} (u : ℕ → (Fin m → ℝ) → ℝ) (t : ℕ) (y : Fin m → ℝ)
    (x : ℝ) : ℝ :=
  if t < n then min (relaxStop n t y x) (dropPenalty n t y x + u (t + 1) (ins y x))
  else relaxStop n t y x

/-- The functions `L_k` of the proof of Theorem B, on histories of length `k`. -/
noncomputable def relaxL (n m : ℕ) (u : ℕ → (Fin m → ℝ) → ℝ) : (k : ℕ) → (Fin k → ℝ) → ℝ
  | 0, _ => u 1 (fun _ => 1)
  | k + 1, h => relaxStep n u (k + 1) (traj m k (Fin.init h)) (h (Fin.last k)) +
      phi m (n - (k + 1)) k (Fin.init h) (h (Fin.last k))

theorem measurable_relaxStop (n t m : ℕ) :
    Measurable fun p : (Fin m → ℝ) × ℝ => relaxStop n t p.1 p.2 := by
  unfold relaxStop
  -- Goal: Measurable fun p => 1 + (↑(Finset.univ.filter fun k => p.1 k < p.2).card : ℝ) + (↑n - ↑t) * p.2
  -- Use Finset.card_filter to rewrite the cardinality as a sum
  have hcard_eq : (fun (p : (Fin m → ℝ) × ℝ) => ((Finset.univ.filter fun k => p.1 k < p.2).card : ℝ)) =
      (fun p => ∑ k : Fin m, (if p.1 k < p.2 then (1 : ℝ) else 0)) := by
    ext p
    rw [Finset.card_filter]
    simp
  -- Measurability of the sum
  have hmeas_sum : Measurable fun (p : (Fin m → ℝ) × ℝ) =>
      ∑ k : Fin m, (if p.1 k < p.2 then (1 : ℝ) else 0) := by
    refine Finset.measurable_sum _ (fun k _ => ?_)
    have hlt : MeasurableSet {p : (Fin m → ℝ) × ℝ | p.1 k < p.2} :=
      measurableSet_lt ((measurable_pi_apply k).comp measurable_fst) measurable_snd
    refine Measurable.ite hlt measurable_const measurable_const
  -- Combine: rewrite the goal using hcard_eq, avoiding simp loops
  have hgoal_eq : (fun p : (Fin m → ℝ) × ℝ => 1 + ((Finset.univ.filter fun k => p.1 k < p.2).card : ℝ) + ((n : ℝ) - (t : ℝ)) * p.2) =
      (fun p => 1 + (∑ k : Fin m, (if p.1 k < p.2 then (1 : ℝ) else 0)) + ((n : ℝ) - (t : ℝ)) * p.2) := by
    ext p
    have h := congr_fun hcard_eq p
    rw [h]
  rw [hgoal_eq]
  exact ((measurable_const.add hmeas_sum).add (measurable_const.mul measurable_snd))

theorem measurable_dropPenalty (n t m : ℕ) :
    Measurable fun p : (Fin m → ℝ) × ℝ => dropPenalty n t p.1 p.2 := by
  unfold dropPenalty
  exact ((measurable_const.sub (measurable_drop m)).pow_const (n - t))

theorem abs_relaxStop_le (n t : ℕ) {m : ℕ} (ht : t ≤ n) (y : Fin m → ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : |relaxStop n t y x| ≤ m + n + 1 := by
  rcases hx with ⟨hx0, hx1⟩
  have hnonneg : 0 ≤ relaxStop n t y x := by
    unfold relaxStop
    have hcard : 0 ≤ ((Finset.univ.filter fun k => y k < x).card : ℝ) := by
      simp
    have hsub : 0 ≤ (n : ℝ) - (t : ℝ) := by
      have : (t : ℝ) ≤ (n : ℝ) := by exact_mod_cast ht
      linarith
    have hprod : 0 ≤ ((n : ℝ) - (t : ℝ)) * x := by
      nlinarith
    nlinarith
  rw [abs_of_nonneg hnonneg]
  unfold relaxStop
  have hcard : ((Finset.univ.filter fun k => y k < x).card : ℝ) ≤ (m : ℝ) := by
    have hcard_nat : (Finset.univ.filter fun k => y k < x).card ≤ m := by
      calc
        (Finset.univ.filter fun k => y k < x).card ≤ (Finset.univ : Finset (Fin m)).card :=
          Finset.card_filter_le _ _
        _ = m := by simp
    exact_mod_cast hcard_nat
  have hsub : 0 ≤ (n : ℝ) - (t : ℝ) := by
    have : (t : ℝ) ≤ (n : ℝ) := by exact_mod_cast ht
    linarith
  have hprod : ((n : ℝ) - (t : ℝ)) * x ≤ (n : ℝ) := by
    nlinarith
  nlinarith

theorem dropPenalty_mem_Icc (n t : ℕ) {m : ℕ} {y : Fin m → ℝ} (hy : IsMemory y) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : dropPenalty n t y x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold dropPenalty
  have hdrop : drop y x ∈ Set.Icc (0 : ℝ) 1 := drop_mem_Icc hy hx
  have hlo : (0 : ℝ) ≤ 1 - drop y x := sub_nonneg.mpr hdrop.2
  have hhi : 1 - drop y x ≤ 1 := sub_le_self 1 hdrop.1
  have hnonneg : (0 : ℝ) ≤ (1 - drop y x) ^ (n - t) := pow_nonneg hlo (n - t)
  have hle1 : (1 - drop y x) ^ (n - t) ≤ 1 := pow_le_one₀ hlo hhi
  exact ⟨hnonneg, hle1⟩

/-- The stop payoff of `Robbins.Basic.Payoff` in the terms of the relaxation (B2 at `z = x_t`). -/
theorem stopPayoff_eq_relaxStop (n t m : ℕ) (h : Fin (t + 1) → ℝ)
    (hh : ∀ i, h i ∈ Set.Icc (0 : ℝ) 1) :
    stopPayoff n h = relaxStop (n + 1) (t + 1) (traj m t (Fin.init h)) (h (Fin.last t)) +
      ((Finset.univ.filter fun s => drops m t (Fin.init h) s < h (Fin.last t)).card : ℝ) := by
  have h1 := card_filter_castSucc h (h (Fin.last t))
  rw [if_neg (lt_irrefl _), add_zero] at h1
  have h2 := Robbins.card_traj m t (Fin.init h) (fun i => hh _) (hh (Fin.last t)).2
  change _ = (Finset.univ.filter fun i : Fin t => Fin.init h i < h (Fin.last t)).card at h1
  unfold stopPayoff relaxStop
  rw [h1, h2]
  push_cast
  ring

theorem relaxStep_le_relaxStop (n : ℕ) {m : ℕ} (u : ℕ → (Fin m → ℝ) → ℝ) (t : ℕ)
    (y : Fin m → ℝ) (x : ℝ) : relaxStep n u t y x ≤ relaxStop n t y x := by
  unfold relaxStep
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem relaxStep_le_cont (n : ℕ) {m : ℕ} (u : ℕ → (Fin m → ℝ) → ℝ) {t : ℕ} (ht : t < n)
    (y : Fin m → ℝ) (x : ℝ) :
    relaxStep n u t y x ≤ dropPenalty n t y x + u (t + 1) (ins y x) := by
  unfold relaxStep
  rw [if_pos ht]
  exact min_le_right _ _

theorem measurable_relaxStep (n : ℕ) {m : ℕ} (u : ℕ → (Fin m → ℝ) → ℝ) (t : ℕ)
    (hu : t < n → Measurable (u (t + 1))) :
    Measurable fun p : (Fin m → ℝ) × ℝ => relaxStep n u t p.1 p.2 := by
  unfold relaxStep
  by_cases ht : t < n
  · simp only [if_pos ht]
    exact (measurable_relaxStop n t m).min
      ((measurable_dropPenalty n t m).add ((hu ht).comp (measurable_ins m)))
  · simp only [if_neg ht]
    exact measurable_relaxStop n t m

theorem abs_relaxStep_le (n : ℕ) {m : ℕ} (u : ℕ → (Fin m → ℝ) → ℝ) {t : ℕ} (htn : t ≤ n)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : t < n → ∀ z, IsMemory z → |u (t + 1) z| ≤ C)
    {y : Fin m → ℝ} (hy : IsMemory y) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |relaxStep n u t y x| ≤ m + n + 2 + C := by
  have hS := abs_relaxStop_le n t htn y hx
  unfold relaxStep
  split_ifs with ht
  · have hP := dropPenalty_mem_Icc n t hy hx
    have hU := hC ht (ins y x) (ins_mem hy hx)
    have hB : |dropPenalty n t y x + u (t + 1) (ins y x)| ≤ 1 + C := by
      have := abs_add_le (dropPenalty n t y x) (u (t + 1) (ins y x))
      rw [abs_of_nonneg hP.1] at this
      linarith [hP.2]
    have := abs_min_le_max_abs_abs (a := relaxStop n t y x)
      (b := dropPenalty n t y x + u (t + 1) (ins y x))
    calc _ ≤ max |relaxStop n t y x| |dropPenalty n t y x + u (t + 1) (ins y x)| := this
      _ ≤ _ := max_le (by linarith) (by linarith)
  · linarith

theorem RelaxedSubSolution.le_integral_relaxStep {n m : ℕ} (u : RelaxedSubSolution n m) {t : ℕ}
    (ht1 : 1 ≤ t) (htn : t ≤ n) {y : Fin m → ℝ} (hy : IsMemory y) :
    u.u t y ≤ ∫ x in Set.Icc (0 : ℝ) 1, relaxStep n u.u t y x := by
  by_cases ht : t < n
  · simp only [relaxStep, if_pos ht]
    exact u.step t ht1 ht y hy
  · obtain rfl : t = n := by omega
    simp only [relaxStep, lt_irrefl, if_false]
    exact u.last y hy

theorem RelaxedSubSolution.integrable_relaxStep {n m : ℕ} (u : RelaxedSubSolution n m) {t : ℕ}
    (ht1 : 1 ≤ t) (htn : t ≤ n) {y : Fin m → ℝ} (hy : IsMemory y) :
    Integrable (fun x => relaxStep n u.u t y x) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have h1 := measurable_relaxStep n u.u t fun ht => u.measurable (t + 1) (by omega) ht
  have h2 : Measurable fun x : ℝ => ((y, x) : (Fin m → ℝ) × ℝ) :=
    measurable_const.prodMk measurable_id
  have hmeas : Measurable fun x : ℝ => relaxStep n u.u t y x := by
    have := h1.comp h2
    exact this
  by_cases ht : t < n
  · obtain ⟨C, hC⟩ := u.bounded (t + 1) (by omega) ht
    refine integrable_Icc_of_bound hmeas _ fun x hx =>
      abs_relaxStep_le n u.u htn (le_max_right C 0) (fun _ z hz => (hC z hz).trans
        (le_max_left C 0)) hy hx
  · refine integrable_Icc_of_bound hmeas _ fun x hx =>
      abs_relaxStep_le n u.u htn le_rfl (fun h => absurd h ht) hy hx

theorem integrable_phi (m e k : ℕ) (h : Fin k → ℝ) (hh : ∀ i, h i ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun x => phi m e k h x) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have h2 : Measurable fun x : ℝ => ((h, x) : (Fin k → ℝ) × ℝ) :=
    measurable_const.prodMk measurable_id
  have hmeas : Measurable fun x : ℝ => phi m e k h x := by
    have := (measurable_phi m e k).comp h2
    exact this
  refine integrable_Icc_of_bound hmeas k fun x _ => ?_
  rw [abs_of_nonneg (phi_nonneg m e k h hh x)]
  exact phi_le m e k h hh x

theorem init_mem {k : ℕ} {h : Fin (k + 1) → ℝ} (hh : ∀ i, h i ∈ Set.Icc (0 : ℝ) 1) :
    ∀ i, Fin.init h i ∈ Set.Icc (0 : ℝ) 1 := fun _ => hh _

theorem RelaxedSubSolution.measurable_relaxL {n m : ℕ} (u : RelaxedSubSolution n m) (k : ℕ)
    (hk : k ≤ n) : Measurable (relaxL n m u.u k) := by
  cases k with
  | zero => exact measurable_const
  | succ k =>
    have hpair : Measurable fun h : Fin (k + 1) → ℝ => (traj m k (Fin.init h), h (Fin.last k)) :=
      ((measurable_traj m k).comp (measurable_init k)).prodMk (measurable_pi_apply _)
    have hpair' : Measurable fun h : Fin (k + 1) → ℝ => (Fin.init h, h (Fin.last k)) :=
      (measurable_init k).prodMk (measurable_pi_apply _)
    exact ((measurable_relaxStep n u.u (k + 1) fun ht => u.measurable (k + 2) (by omega) ht).comp
      hpair).add ((measurable_phi m (n - (k + 1)) k).comp hpair')

theorem RelaxedSubSolution.bound_relaxL {n m : ℕ} (u : RelaxedSubSolution n m) (k : ℕ)
    (hk : k ≤ n) : ∃ C, ∀ h : Fin k → ℝ, (∀ i, h i ∈ Set.Icc (0 : ℝ) 1) →
      |relaxL n m u.u k h| ≤ C := by
  cases k with
  | zero => exact ⟨|u.u 1 fun _ => 1|, fun _ _ => le_rfl⟩
  | succ k =>
    obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧
        (k + 1 < n → ∀ z, IsMemory z → |u.u (k + 1 + 1) z| ≤ C) := by
      by_cases ht : k + 1 < n
      · obtain ⟨C, hC⟩ := u.bounded (k + 2) (by omega) ht
        exact ⟨max C 0, le_max_right _ _, fun _ z hz => (hC z hz).trans (le_max_left _ _)⟩
      · exact ⟨0, le_rfl, fun h => absurd h ht⟩
    refine ⟨m + n + 2 + C + k, fun h hh => ?_⟩
    have hg := init_mem hh
    have h1 := abs_relaxStep_le n u.u hk hC0 hC (traj_mem m k _ hg) (hh (Fin.last k))
    have h2 := phi_nonneg m (n - (k + 1)) k _ hg (h (Fin.last k))
    have h3 := phi_le m (n - (k + 1)) k _ hg (h (Fin.last k))
    simp only [relaxL]
    have := abs_add_le (relaxStep n u.u (k + 1) (traj m k (Fin.init h)) (h (Fin.last k)))
      (phi m (n - (k + 1)) k (Fin.init h) (h (Fin.last k)))
    rw [abs_of_nonneg h2] at this
    linarith

theorem relaxL_le_stopPayoff (n m : ℕ) (u : ℕ → (Fin m → ℝ) → ℝ) (t : ℕ)
    (h : Fin (t + 1) → ℝ) (hh : ∀ i, h i ∈ Set.Icc (0 : ℝ) 1) :
    relaxL (n + 1) m u (t + 1) h ≤ stopPayoff n h := by
  simp only [relaxL]
  rw [stopPayoff_eq_relaxStop n t m h hh]
  have h1 := relaxStep_le_relaxStop (n + 1) u (t + 1) (traj m t (Fin.init h)) (h (Fin.last t))
  have h2 := phi_le_card m (n + 1 - (t + 1)) t (Fin.init h) (init_mem hh) (h (Fin.last t))
  linarith

theorem RelaxedSubSolution.relaxL_le_integral {n m : ℕ} (u : RelaxedSubSolution n m) (k : ℕ)
    (hk : k < n) (h : Fin k → ℝ) (hh : ∀ i, h i ∈ Set.Icc (0 : ℝ) 1) :
    relaxL n m u.u k h ≤
      ∫ a in Set.Icc (0 : ℝ) 1, relaxL n m u.u (k + 1) (Fin.snoc (α := fun _ => ℝ) h a) := by
  have hsnoc : ∀ a, relaxL n m u.u (k + 1) (Fin.snoc (α := fun _ => ℝ) h a) =
      relaxStep n u.u (k + 1) (traj m k h) a + phi m (n - (k + 1)) k h a := by
    intro a
    simp only [relaxL, Fin.init_snoc, Fin.snoc_last]
  simp_rw [hsnoc]
  rw [integral_add (u.integrable_relaxStep (by omega) (by omega) (traj_mem m k h hh))
    (integrable_phi m _ k h hh), integral_phi m _ k h hh]
  have hI := u.le_integral_relaxStep (t := k + 1) (by omega) (by omega) (traj_mem m k h hh)
  cases k with
  | zero =>
    simp only [relaxL, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact hI
  | succ j =>
    have hg := init_mem hh
    have hc := relaxStep_le_cont n u.u (t := j + 1) (by omega) (traj m j (Fin.init h))
      (h (Fin.last j))
    have hd := phi_add_drop m (n - (j + 1)) j h
    have he : n - (j + 1 + 1) + 1 = n - (j + 1) := by omega
    rw [he]
    simp only [relaxL]
    rw [traj_succ] at hI ⊢
    unfold dropPenalty at hc
    linarith

/-- Theorem B: `u 1 (1, ..., 1) ≤ v n`. -/
theorem RelaxedSubSolution.val_one_le_v {n m : ℕ} (u : RelaxedSubSolution n m) (hn : 1 ≤ n) :
    u.u 1 (fun _ => 1) ≤ v n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  exact le_v_of_verification (relaxL (n' + 1) m u.u) (fun k hk => u.measurable_relaxL k hk)
    (fun k hk => u.bound_relaxL k hk)
    (fun t h _ hh => relaxL_le_stopPayoff n' m u.u t h hh)
    (fun k h hk hh => u.relaxL_le_integral k (by omega) h hh)

end Robbins
