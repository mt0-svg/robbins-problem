import Robbins.Relax.Order
import Robbins.Basic.Integrals

/-!
# The trajectory of the memory, the dropped values and the drop weights

Lemma 3.3 of the paper and the function `Phi_t` of the proof of Theorem 2.2, 0-indexed: for a history
`h : Fin k → ℝ` (the values `x_1, ..., x_k` are `h 0, ..., h (k - 1)`),

* `traj m k h` is the memory `y^(k)` after the `k` values, from the padding `(1, ..., 1)`;
* `drops m k h s` is the value dropped at time `s + 1`, `delta_{s+1} = drop (y^(s)) (x_{s+1})`;
* `alive m k h s` is `1` if every value after time `s + 1` up to time `k` exceeds the drop
  `delta_{s+1}`, else `0`;
* `phi m e k h x = ∑ s, alive * 1{drops < x} * (1 - drops) ^ e`: with `x` the value at time `t = k + 1`
  and `e = n - t`, this is `Phi_t` at the history `(h, x)`.

Lemma 3.3 is `card_traj`: `#{i | h i < z} = #{j | traj h j < z} + #{s | drops h s < z}` for `z ≤ 1`.
-/

namespace Robbins

open MeasureTheory

/-- The memory after the values `h 0, ..., h (k - 1)`, from the padding `(1, ..., 1)`. -/
noncomputable def traj (m : ℕ) : (k : ℕ) → (Fin k → ℝ) → Fin m → ℝ
  | 0, _ => fun _ => 1
  | k + 1, h => ins (traj m k (Fin.init h)) (h (Fin.last k))

/-- `drops m k h s`: the value dropped from the memory when the value `h s` arrives. -/
noncomputable def drops (m : ℕ) : (k : ℕ) → (Fin k → ℝ) → Fin k → ℝ
  | 0, _ => fun s => s.elim0
  | k + 1, h => Fin.snoc (α := fun _ => ℝ) (drops m k (Fin.init h))
      (drop (traj m k (Fin.init h)) (h (Fin.last k)))

/-- `alive m k h s`: `1` if every value `h r`, `s < r < k`, is above the drop `drops m k h s`,
else `0`. -/
noncomputable def alive (m : ℕ) : (k : ℕ) → (Fin k → ℝ) → Fin k → ℝ
  | 0, _ => fun s => s.elim0
  | k + 1, h => Fin.snoc (α := fun _ => ℝ)
      (fun s => alive m k (Fin.init h) s *
        (if drops m k (Fin.init h) s < h (Fin.last k) then 1 else 0)) 1

/-- The drop weight `Phi` of B4 at the history `(h, x)` with exponent `e`. -/
noncomputable def phi (m e k : ℕ) (h : Fin k → ℝ) (x : ℝ) : ℝ :=
  ∑ s, alive m k h s * (if drops m k h s < x then 1 else 0) * (1 - drops m k h s) ^ e

theorem traj_zero (m : ℕ) (h : Fin 0 → ℝ) : traj m 0 h = fun _ => 1 := rfl

theorem traj_succ (m k : ℕ) (h : Fin (k + 1) → ℝ) :
    traj m (k + 1) h = ins (traj m k (Fin.init h)) (h (Fin.last k)) := rfl

theorem drops_succ (m k : ℕ) (h : Fin (k + 1) → ℝ) :
    drops m (k + 1) h = Fin.snoc (α := fun _ => ℝ) (drops m k (Fin.init h))
      (drop (traj m k (Fin.init h)) (h (Fin.last k))) := rfl

theorem alive_succ (m k : ℕ) (h : Fin (k + 1) → ℝ) :
    alive m (k + 1) h = Fin.snoc (α := fun _ => ℝ)
      (fun s => alive m k (Fin.init h) s *
        (if drops m k (Fin.init h) s < h (Fin.last k) then 1 else 0)) 1 := rfl

theorem traj_mem (m k : ℕ) (h : Fin k → ℝ) (hh : ∀ i, h i ∈ Set.Icc (0 : ℝ) 1) :
    IsMemory (traj m k h) := by
  induction k with
  | zero => exact isMemory_one m
  | succ k ih => exact ins_mem (ih (Fin.init h) fun i => hh _) (hh (Fin.last k))

theorem drops_mem (m k : ℕ) (h : Fin k → ℝ) (hh : ∀ i, h i ∈ Set.Icc (0 : ℝ) 1) (s : Fin k) :
    drops m k h s ∈ Set.Icc (0 : ℝ) 1 := by
  induction k with
  | zero => exact s.elim0
  | succ k ih =>
    rw [drops_succ]
    refine Fin.lastCases ?_ (fun s => ?_) s
    · rw [Fin.snoc_last]
      exact drop_mem_Icc (Robbins.traj_mem m k _ fun i => hh _) (hh (Fin.last k))
    · rw [Fin.snoc_castSucc]
      exact ih (Fin.init h) (fun i => hh _) s

theorem alive_mem (m k : ℕ) (h : Fin k → ℝ) (s : Fin k) : alive m k h s ∈ Set.Icc (0 : ℝ) 1 := by
  induction k with
  | zero => exact s.elim0
  | succ k ih =>
    rw [alive_succ]
    refine Fin.lastCases ?_ (fun s => ?_) s
    · rw [Fin.snoc_last]
      exact ⟨zero_le_one, le_rfl⟩
    · rw [Fin.snoc_castSucc]
      have := ih (Fin.init h) s
      split_ifs
      · simpa using this
      · simp

/-- B2, the trajectory identity. -/
theorem card_traj (m k : ℕ) (h : Fin k → ℝ) (hh : ∀ i, h i ∈ Set.Icc (0 : ℝ) 1) {z : ℝ}
    (hz : z ≤ 1) :
    (Finset.univ.filter fun i => h i < z).card =
      (Finset.univ.filter fun j => traj m k h j < z).card +
        (Finset.univ.filter fun s => drops m k h s < z).card := by
  induction k with
  | zero =>
    have : (Finset.univ.filter fun j => traj m 0 h j < z) = ∅ := by
      ext j
      simp [traj_zero, not_lt.mpr hz]
    rw [this]
    simp
  | succ k ih =>
    have hg : ∀ i, Fin.init h i ∈ Set.Icc (0 : ℝ) 1 := fun i => hh _
    have h1 := card_filter_castSucc h z
    have h2 := ih (Fin.init h) hg
    have h3 := card_lt_add_ite (Robbins.traj_mem m k _ hg) (hh (Fin.last k)) z
    have h4 : (Finset.univ.filter fun s => drops m (k + 1) h s < z).card =
        (Finset.univ.filter fun s => drops m k (Fin.init h) s < z).card +
          (if drop (traj m k (Fin.init h)) (h (Fin.last k)) < z then 1 else 0) := by
      have := card_filter_castSucc (drops m (k + 1) h) z
      simpa only [drops_succ, Fin.snoc_castSucc, Fin.snoc_last] using this
    rw [traj_succ, h4]
    change _ = (Finset.univ.filter fun i : Fin k => Fin.init h i < z).card + _ at h1
    omega

theorem phi_le_card (m e k : ℕ) (h : Fin k → ℝ) (hh : ∀ i, h i ∈ Set.Icc (0 : ℝ) 1) (x : ℝ) :
    phi m e k h x ≤ (Finset.univ.filter fun s => drops m k h s < x).card := by
  unfold phi
  have hcard : ((Finset.univ.filter fun s => drops m k h s < x).card : ℝ) =
      ∑ s : Fin k, (if drops m k h s < x then (1 : ℝ) else 0) := by
    simpa [Nat.cast_sum] using congrArg (fun (n : ℕ) => (n : ℝ))
      (Finset.card_filter (fun s => drops m k h s < x) Finset.univ)
  rw [hcard]
  refine Finset.sum_le_sum ?_
  intro s _
  by_cases hd : drops m k h s < x
  · simp [hd]
    have ha := alive_mem m k h s
    have hd' := drops_mem m k h hh s
    rcases ha with ⟨ha_l, ha_u⟩
    rcases hd' with ⟨hd_l, hd_u⟩
    have h_nonneg : 0 ≤ 1 - drops m k h s := by linarith
    have h_le_one : 1 - drops m k h s ≤ 1 := by linarith
    have h_pow : (1 - drops m k h s) ^ e ≤ 1 :=
      pow_le_one₀ h_nonneg h_le_one
    nlinarith
  · simp [hd]

theorem phi_nonneg (m e k : ℕ) (h : Fin k → ℝ) (hh : ∀ i, h i ∈ Set.Icc (0 : ℝ) 1) (x : ℝ) :
    0 ≤ phi m e k h x := by
  unfold phi
  refine Finset.sum_nonneg ?_
  intro s _
  have halive : 0 ≤ alive m k h s := (alive_mem m k h s).1
  have hdrops_mem : drops m k h s ∈ Set.Icc (0 : ℝ) 1 := drops_mem m k h hh s
  have hdrops_le_one : drops m k h s ≤ 1 := hdrops_mem.2
  have hdrops_ge_zero : 0 ≤ drops m k h s := hdrops_mem.1
  have h_nonneg_pow : 0 ≤ (1 - drops m k h s) ^ e := by
    have h_nonneg_base : 0 ≤ 1 - drops m k h s := by linarith
    exact pow_nonneg h_nonneg_base e
  have h_if_nonneg : 0 ≤ (if drops m k h s < x then (1 : ℝ) else 0) := by
    split <;> norm_num
  have h_prod1 : 0 ≤ alive m k h s * (if drops m k h s < x then (1 : ℝ) else 0) :=
    mul_nonneg halive h_if_nonneg
  exact mul_nonneg h_prod1 h_nonneg_pow

theorem phi_le (m e k : ℕ) (h : Fin k → ℝ) (hh : ∀ i, h i ∈ Set.Icc (0 : ℝ) 1) (x : ℝ) :
    phi m e k h x ≤ k := by
  unfold phi
  refine le_trans (Finset.sum_le_sum (g := fun (_ : Fin k) => (1 : ℝ)) fun s _ => ?_) ?_
  · -- each term ≤ 1
    have ha := alive_mem m k h s
    have hd := drops_mem m k h hh s
    rcases ha with ⟨ha0, ha1⟩
    rcases hd with ⟨hd0, hd1⟩
    have h_nonneg_one_minus_d : 0 ≤ 1 - drops m k h s := by linarith
    have h_one_minus_d_le_one : 1 - drops m k h s ≤ 1 := by linarith
    have h_pow : (1 - drops m k h s) ^ e ≤ 1 :=
      pow_le_one₀ h_nonneg_one_minus_d h_one_minus_d_le_one
    have h_nonneg_a : 0 ≤ alive m k h s := ha0
    have h_nonneg_pow : 0 ≤ (1 - drops m k h s) ^ e :=
      pow_nonneg h_nonneg_one_minus_d _
    calc
      alive m k h s * (if drops m k h s < x then 1 else 0) * (1 - drops m k h s) ^ e
          ≤ alive m k h s * 1 * (1 - drops m k h s) ^ e := by
        gcongr
        split <;> norm_num
      _ ≤ alive m k h s * 1 * 1 := by
        gcongr
      _ = alive m k h s := by ring
      _ ≤ 1 := ha1
  · -- sum of 1's = k
    simp

theorem integral_phi (m e k : ℕ) (h : Fin k → ℝ) (hh : ∀ i, h i ∈ Set.Icc (0 : ℝ) 1) :
    ∫ x in Set.Icc (0 : ℝ) 1, phi m e k h x =
      ∑ s, alive m k h s * (1 - drops m k h s) ^ (e + 1) := by
  unfold phi
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun s hs => ?_
    have hd := drops_mem m k h hh s
    calc
      ∫ a in Set.Icc (0 : ℝ) 1, (alive m k h s * (if drops m k h s < a then (1 : ℝ) else 0)) * (1 - drops m k h s) ^ e
          = (∫ a in Set.Icc (0 : ℝ) 1, (alive m k h s * (if drops m k h s < a then (1 : ℝ) else 0))) * (1 - drops m k h s) ^ e := by
        rw [MeasureTheory.integral_mul_const]
      _ = (alive m k h s * ∫ a in Set.Icc (0 : ℝ) 1, (if drops m k h s < a then (1 : ℝ) else 0)) * (1 - drops m k h s) ^ e := by
        rw [MeasureTheory.integral_const_mul]
      _ = (alive m k h s * (1 - drops m k h s)) * (1 - drops m k h s) ^ e := by
        rw [integral_Icc_ite_gt hd]
      _ = alive m k h s * ((1 - drops m k h s) * (1 - drops m k h s) ^ e) := by ring
      _ = alive m k h s * (1 - drops m k h s) ^ (e + 1) := by rw [pow_succ']
  · intro i hi
    have h_int : Integrable (fun (x : ℝ) => (alive m k h i * (if drops m k h i < x then (1 : ℝ) else 0)) * (1 - drops m k h i) ^ e)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      apply MeasureTheory.Integrable.of_mem_Icc (0 : ℝ) (1 : ℝ)
      · refine (Measurable.aemeasurable ?_).restrict
        refine ((measurable_const.mul ?_).mul measurable_const)
        refine Measurable.indicator measurable_const (measurableSet_Ioi (a := drops m k h i))
      · filter_upwards [self_mem_ae_restrict (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1))] with x hx
        have hx0 : (0 : ℝ) ≤ x := hx.1
        have hx1 : x ≤ 1 := hx.2
        have h_alive_mem := alive_mem m k h i
        have h_alive_nonneg : 0 ≤ alive m k h i := h_alive_mem.1
        have h_alive_le_one : alive m k h i ≤ 1 := h_alive_mem.2
        have h_drops_mem := drops_mem m k h hh i
        have h_drops_nonneg : 0 ≤ drops m k h i := h_drops_mem.1
        have h_drops_le_one : drops m k h i ≤ 1 := h_drops_mem.2
        have h_one_minus_drops_nonneg : 0 ≤ 1 - drops m k h i := by linarith
        have h_one_minus_drops_le_one : 1 - drops m k h i ≤ 1 := by linarith
        have h_pow_nonneg : 0 ≤ (1 - drops m k h i) ^ e := pow_nonneg h_one_minus_drops_nonneg e
        have h_pow_le_one : (1 - drops m k h i) ^ e ≤ 1 := by
          exact pow_le_one₀ h_one_minus_drops_nonneg h_one_minus_drops_le_one
        have h_indicator_nonneg : 0 ≤ (if drops m k h i < x then (1 : ℝ) else 0) := by
          split <;> norm_num
        have h_indicator_le_one : (if drops m k h i < x then (1 : ℝ) else 0) ≤ 1 := by
          split <;> norm_num
        have h_val_nonneg : 0 ≤ (alive m k h i * (if drops m k h i < x then (1 : ℝ) else 0)) * (1 - drops m k h i) ^ e := by
          apply mul_nonneg
          · apply mul_nonneg h_alive_nonneg h_indicator_nonneg
          · exact h_pow_nonneg
        have h_val_le_one : (alive m k h i * (if drops m k h i < x then (1 : ℝ) else 0)) * (1 - drops m k h i) ^ e ≤ 1 := by
          have h_prod_le_one : alive m k h i * (if drops m k h i < x then (1 : ℝ) else 0) ≤ 1 := by
            nlinarith
          nlinarith
        exact ⟨h_val_nonneg, h_val_le_one⟩
    exact h_int

theorem phi_add_drop (m e k : ℕ) (h : Fin (k + 1) → ℝ) :
    phi m e k (Fin.init h) (h (Fin.last k)) +
        (1 - drop (traj m k (Fin.init h)) (h (Fin.last k))) ^ e =
      ∑ s, alive m (k + 1) h s * (1 - drops m (k + 1) h s) ^ e := by
  rw [Fin.sum_univ_castSucc, alive_succ, drops_succ]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, one_mul]
  unfold phi
  congr 1

theorem phi_zero (m e : ℕ) (h : Fin 0 → ℝ) (x : ℝ) : phi m e 0 h x = 0 := by
  simp [phi]

theorem measurable_ins (m : ℕ) : Measurable fun p : (Fin m → ℝ) × ℝ => ins p.1 p.2 := by
  rw [measurable_pi_iff]
  intro k
  dsimp [ins]
  split_ifs with h
  · refine Measurable.max ?_ ?_
    · exact measurable_const
    · refine Measurable.min ?_ ?_
      · exact (measurable_pi_apply k).comp measurable_fst
      · exact measurable_snd
  · refine Measurable.max ?_ ?_
    · exact (measurable_pi_apply (⟨k.1 - 1, by
        have hk : (k : ℕ) ≠ 0 := h
        omega⟩ : Fin m)).comp measurable_fst
    · refine Measurable.min ?_ ?_
      · exact (measurable_pi_apply k).comp measurable_fst
      · exact measurable_snd

theorem measurable_drop (m : ℕ) : Measurable fun p : (Fin m → ℝ) × ℝ => drop p.1 p.2 := by
  unfold drop
  split
  · exact measurable_snd
  · refine Measurable.max ?_ measurable_snd
    exact (measurable_pi_apply _).comp measurable_fst

theorem measurable_init (k : ℕ) : Measurable fun h : Fin (k + 1) → ℝ => Fin.init h := by
  rw [measurable_pi_iff]
  intro i
  simpa [Fin.init_def] using measurable_pi_apply (Fin.castSucc i)

theorem measurable_traj (m k : ℕ) : Measurable (traj m k) := by
  induction' k with k ih
  · -- k = 0: traj m 0 is the constant function returning fun _ => 1
    have h0 : traj m 0 = fun _ => fun _ => (1 : ℝ) := by
      ext h i; rw [traj_zero]
    rw [h0]
    exact measurable_const
  · -- k = k+1: traj m (k+1) h = ins (traj m k (Fin.init h)) (h (Fin.last k))
    have h_succ : traj m (k + 1) = fun h => ins (traj m k (Fin.init h)) (h (Fin.last k)) := by
      ext h i; rw [traj_succ m k h]
    rw [h_succ]
    have h_prod : Measurable (fun h : Fin (k + 1) → ℝ => (traj m k (Fin.init h), h (Fin.last k))) :=
      (ih.comp (measurable_init k)).prodMk (measurable_pi_apply (Fin.last k))
    exact Measurable.comp (measurable_ins m) h_prod

theorem measurable_drops (m k : ℕ) : Measurable (drops m k) := by
  induction' k with k ih
  · -- k = 0
    apply measurable_of_subsingleton_codomain
  · -- k = k + 1
    rw [measurable_pi_iff]
    intro i
    refine Fin.lastCases ?_ ?_ i
    · -- i = Fin.last k
      have h_eq : (fun h : Fin (k + 1) → ℝ => drops m (k + 1) h (Fin.last k)) =
          (fun h => drop (traj m k (Fin.init h)) (h (Fin.last k))) := by
        ext h
        simp [drops_succ, Fin.snoc_last]
      rw [h_eq]
      exact (measurable_drop m).comp
        (((measurable_traj m k).comp (measurable_init k)).prodMk (measurable_pi_apply (Fin.last k)))
    · -- i = Fin.castSucc j
      intro j
      have h_eq : (fun h : Fin (k + 1) → ℝ => drops m (k + 1) h (Fin.castSucc j)) =
          (fun h => (drops m k (Fin.init h)) j) := by
        ext h
        simp [drops_succ, Fin.snoc_castSucc]
      rw [h_eq]
      exact (measurable_pi_apply j).comp (ih.comp (measurable_init k))

theorem measurable_alive (m k : ℕ) : Measurable (alive m k) := by
  induction' k with k ih
  · -- k = 0: alive m 0 is constant (does not depend on h)
    have : alive m 0 = fun _ => fun s => s.elim0 := by
      ext h s; rfl
    rw [this]
    exact measurable_const
  · -- k = k+1
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ ?_ i
    · -- i = Fin.last k: the value is 1
      have : (fun (h : Fin (k+1) → ℝ) => (alive m (k+1) h) (Fin.last k)) = fun _ => (1 : ℝ) := by
        ext h; simp [alive_succ, Fin.snoc_last]
      rw [this]
      exact measurable_const
    · -- i = Fin.castSucc i' for some i' : Fin k
      intro i'
      have h_eq : (fun (h : Fin (k+1) → ℝ) => (alive m (k+1) h) (Fin.castSucc i')) =
        (fun h => (alive m k (Fin.init h)) i' *
          (if (drops m k (Fin.init h)) i' < h (Fin.last k) then (1 : ℝ) else (0 : ℝ))) := by
        ext h; simp [alive_succ, Fin.snoc_castSucc]
      rw [h_eq]
      -- f1 h := (alive m k (Fin.init h)) i'
      have hf1 : Measurable (fun (h : Fin (k+1) → ℝ) => (alive m k (Fin.init h)) i') :=
        (measurable_pi_apply i').comp (ih.comp (measurable_init k))
      -- f2 h := (drops m k (Fin.init h)) i'
      have hf2 : Measurable (fun (h : Fin (k+1) → ℝ) => (drops m k (Fin.init h)) i') :=
        (measurable_pi_apply i').comp ((measurable_drops m k).comp (measurable_init k))
      -- f3 h := h (Fin.last k)
      have hf3 : Measurable (fun (h : Fin (k+1) → ℝ) => h (Fin.last k)) :=
        measurable_pi_apply (Fin.last k)
      -- The condition f2 h < f3 h is measurable
      have h_cond : MeasurableSet {h : Fin (k+1) → ℝ | (drops m k (Fin.init h)) i' < h (Fin.last k)} :=
        measurableSet_lt hf2 hf3
      -- Combine: f1 * (if condition then 1 else 0)
      refine Measurable.mul hf1 (Measurable.ite h_cond measurable_const measurable_const)

theorem measurable_phi (m e k : ℕ) :
    Measurable fun p : (Fin k → ℝ) × ℝ => phi m e k p.1 p.2 := by
  unfold phi
  refine Finset.measurable_sum _ (fun s _ => ?_)
  refine Measurable.mul ?_ ?_
  · refine Measurable.mul ?_ ?_
    · refine (measurable_pi_apply s).comp ((Robbins.measurable_alive m k).comp measurable_fst)
    · refine Measurable.ite (measurableSet_lt
        ((measurable_pi_apply s).comp ((Robbins.measurable_drops m k).comp measurable_fst))
        measurable_snd) measurable_const measurable_const
  · refine Measurable.pow_const ?_ e
    refine Measurable.sub measurable_const
      ((measurable_pi_apply s).comp ((Robbins.measurable_drops m k).comp measurable_fst))

theorem integrable_Icc_of_bound {f : ℝ → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ C) :
    Integrable f (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  refine ae_restrict_of_forall_mem measurableSet_Icc ?_
  intro x hx
  simpa [Real.norm_eq_abs] using hC x hx

end Robbins
