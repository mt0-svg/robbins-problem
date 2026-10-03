-- The statements that Comparator checks (config.json): the definitions of Robbins/Statement.lean,
-- Robbins/Relax/Defs.lean and Robbins/StatementCheck/Indep.lean, in this order and less their imports, then the
-- theorems with `sorry`. The file builds with the warnings `declaration uses sorry`, which are expected.
import Mathlib

/-!
# Robbins' problem: the frozen definitions

Values `x 0, x 1, ..., x n` (that is `n + 1` values, `x t` being the value `X_{t+1}` of the
textbook) are drawn independently and uniformly on `[0, 1]` and shown one at a time. After seeing
`x t` the decision maker either stops and selects `x t`, or rejects it for good and goes on; at the
last time `n` it must select `x n`. The rule may use every value seen so far (full information).
The loss is the rank of the selected value among all `n + 1` values: one plus the number of values
strictly below it. `v (n + 1)` is the least expected rank over all stopping rules; `v 0 = 0` is a
convention (there is no value to select).

Model.
* The law of the values (`law`) is the product of `n` copies of Lebesgue measure restricted to
  `[0, 1]`: the uniform distribution on the unit cube. It is a probability measure
  (`isProbabilityMeasure_law`).
* A stopping rule (`Rule`) gives, for each time `t`, a measurable set `stopSet t` of histories
  `x 0, ..., x t` (`history x t : Fin (t + 1) → ℝ`) on which it stops. The selected time
  (`Rule.time`) is the first time `t` whose history lies in `stopSet t`, and the last time if there
  is none; so the set given for the last time plays no role. Every stopping time adapted to the
  values has this form (take for `stopSet t` a Borel set whose preimage is the event of stopping at
  `t`), so the rules here are exactly the deterministic stopping rules. Randomized rules do not
  lower the infimum and are not part of this statement.
* Ties have probability `0`; the rank counts the values strictly below the selected one.
* `v (n + 1) = ⨅ r, r.expectedRank` is an infimum in `ℝ`. The set of rules is nonempty (the
  instance below) and the expected ranks are at least `1`, so this is the true infimum and not a
  junk value; `Robbins/Basic` proves the bounds.

The targets are stated in `Robbins/Target.lean`.
-/

namespace Robbins

open MeasureTheory

/-- The uniform distribution on `[0, 1]`, Lebesgue measure restricted to `[0, 1]`, is a probability
measure. -/
instance isProbabilityMeasure_unitInterval :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

/-- The law of `n` values: independent, each uniform on `[0, 1]`. -/
noncomputable def law (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)

instance isProbabilityMeasure_law (n : ℕ) : IsProbabilityMeasure (law n) := by
  unfold law
  infer_instance

/-- The values seen up to time `t` included: `x 0, ..., x t`. -/
def history {n : ℕ} (x : Fin n → ℝ) (t : Fin n) : Fin (t + 1) → ℝ :=
  fun s => x (Fin.castLE t.isLt s)

/-- A stopping rule for `n` values: for each time `t`, a measurable set of histories
`x 0, ..., x t` on which the rule stops at `t`. -/
structure Rule (n : ℕ) where
  /-- The histories up to time `t` on which the rule stops at time `t`. -/
  stopSet : (t : Fin n) → Set (Fin (t + 1) → ℝ)
  /-- Each stop set is measurable. -/
  measurableSet_stopSet : ∀ t, MeasurableSet (stopSet t)

/-- There are rules (for instance the rule that never stops before the last time). -/
instance (n : ℕ) : Nonempty (Rule n) :=
  ⟨⟨fun _ => ∅, fun _ => MeasurableSet.empty⟩⟩

open Classical in
/-- The time selected by the rule `r` on the values `x`: the first time `t` whose history is in the
stop set of `t`, and the last time `n` if there is none. -/
noncomputable def Rule.time {n : ℕ} (r : Rule (n + 1)) (x : Fin (n + 1) → ℝ) : Fin (n + 1) :=
  (Finset.univ.filter fun t => history x t ∈ r.stopSet t ∨ t = Fin.last n).min'
    ⟨Fin.last n, by simp⟩

/-- The rank of the value selected by `r` among the `n + 1` values `x`: one plus the number of
values strictly below it. -/
noncomputable def Rule.rank {n : ℕ} (r : Rule (n + 1)) (x : Fin (n + 1) → ℝ) : ℕ :=
  1 + (Finset.univ.filter fun j => x j < x (r.time x)).card

/-- The expected rank of the value selected by `r`, the `n + 1` values being independent and
uniform on `[0, 1]`. -/
noncomputable def Rule.expectedRank {n : ℕ} (r : Rule (n + 1)) : ℝ :=
  ∫ x, (r.rank x : ℝ) ∂law (n + 1)

/-- `v n`: the least expected rank of the selected value over all stopping rules for `n` values
(Robbins' problem with full information). `v 0 = 0` by convention. -/
noncomputable def v : ℕ → ℝ
  | 0 => 0
  | n + 1 => ⨅ r : Rule (n + 1), r.expectedRank

end Robbins


/-!
# The drop penalty relaxation: the interface of the certificate

Section 2.1 of the paper (Definition 2.1), with its indexing: `n` values, times `t = 1, ..., n`. A
memory is a sorted `m`-tuple `y 0 ≤ ... ≤ y (m - 1)` of values in `[0, 1]` (`IsMemory`); the
coordinate `y k` here is `y_{k+1}` of the paper.

* `ins y x`: the `m` smallest of `y 0, ..., y (m - 1), x`, sorted: coordinate `k` is
  `max (y (k - 1)) (min (y k) x)`, with `y (-1) = 0`;
* `drop y x`: the largest of them, `max (y (m - 1)) x`, and `x` when `m = 0`;
* `relaxStop n t y x = 1 + #{k | y k < x} + (n - t) x`: the relaxed stop cost `S_t(y, x)`;
* `dropPenalty n t y x = (1 - drop y x) ^ (n - t)`: the drop penalty `pi_t(y, x)`.

A `RelaxedSubSolution n m` is a family `u t` of functions on memories, measurable and bounded on
memories for `1 ≤ t ≤ n`, with (R_n) and (R_t) at every memory. Theorem B
(`RelaxedSubSolution.val_one_le_v`, Robbins/Relax/TheoremB.lean): `u 1` at the memory
`(1, ..., 1)` is a lower bound of `v n`.
-/

namespace Robbins

open MeasureTheory

/-- A memory: a sorted tuple of values in `[0, 1]`. -/
def IsMemory {m : ℕ} (y : Fin m → ℝ) : Prop :=
  Monotone y ∧ ∀ k, y k ∈ Set.Icc (0 : ℝ) 1

/-- The `m` smallest of `y 0, ..., y (m - 1), x`, sorted (for a sorted `y`): coordinate `k` is
`max (y (k - 1)) (min (y k) x)`, with `y (-1) = 0`. -/
noncomputable def ins {m : ℕ} (y : Fin m → ℝ) (x : ℝ) : Fin m → ℝ :=
  fun k => max (if h : (k : ℕ) = 0 then 0 else y ⟨k - 1, by omega⟩) (min (y k) x)

/-- The largest of `y 0, ..., y (m - 1), x` (for a sorted `y`): `max (y (m - 1)) x`, and `x` when
`m = 0`. -/
noncomputable def drop {m : ℕ} (y : Fin m → ℝ) (x : ℝ) : ℝ :=
  if h : m = 0 then x else max (y ⟨m - 1, by omega⟩) x

/-- The relaxed stop cost at time `t` of `n`, memory `y`, current value `x`:
`1 + #{k | y k < x} + (n - t) x`. -/
noncomputable def relaxStop (n t : ℕ) {m : ℕ} (y : Fin m → ℝ) (x : ℝ) : ℝ :=
  1 + ((Finset.univ.filter fun k => y k < x).card : ℝ) + ((n : ℝ) - t) * x

/-- The drop penalty at time `t` of `n`, memory `y`, current value `x`: `(1 - drop y x) ^ (n - t)`. -/
noncomputable def dropPenalty (n t : ℕ) {m : ℕ} (y : Fin m → ℝ) (x : ℝ) : ℝ :=
  (1 - drop y x) ^ (n - t)

/-- A relaxed sub-solution for `n` values and memory size `m` (Definition 2.1 of the paper). -/
structure RelaxedSubSolution (n m : ℕ) where
  /-- The value `u t y` at time `t` and memory `y`. -/
  u : ℕ → (Fin m → ℝ) → ℝ
  /-- Each `u t` is measurable, `1 ≤ t ≤ n`. -/
  measurable : ∀ t, 1 ≤ t → t ≤ n → Measurable (u t)
  /-- Each `u t` is bounded on memories, `1 ≤ t ≤ n`. -/
  bounded : ∀ t, 1 ≤ t → t ≤ n → ∃ C, ∀ y, IsMemory y → |u t y| ≤ C
  /-- (R_n). -/
  last : ∀ y, IsMemory y → u n y ≤ ∫ x in Set.Icc (0 : ℝ) 1, relaxStop n n y x
  /-- (R_t), `1 ≤ t < n`. -/
  step : ∀ t, 1 ≤ t → t < n → ∀ y, IsMemory y →
    u t y ≤ ∫ x in Set.Icc (0 : ℝ) 1,
      min (relaxStop n t y x) (dropPenalty n t y x + u (t + 1) (ins y x))

end Robbins

set_option autoImplicit true
set_option relaxedAutoImplicit true

/-! A second formalization of the problem, written separately from the statement of the problem alone (stopping times for the filtration of the values), verbatim but for this comment, the namespace `Indep` and the `end` that closes its `noncomputable section`. Written with auto-bound implicits. -/

namespace Indep

open MeasureTheory
open Set
open ENNReal

noncomputable section

/-!
# Robbins' Problem: Formalization of the Full-Information Expected Rank Problem

We formalize the problem where X_1, ..., X_n are i.i.d. uniform on [0,1].
A stopping rule τ stops at some time 1 ≤ τ ≤ n based on the observed values.
The loss is the rank of the selected value (rank 1 = smallest).
v(n) is the minimal expected rank over all stopping rules.
-/

-- 1. The probability space

/-- Lebesgue measure restricted to [0,1], a probability measure on ℝ. -/
abbrev unitMeasure : Measure ℝ :=
  MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unitMeasure := by
  refine ⟨?h⟩
  dsimp [unitMeasure]
  rw [Measure.restrict_apply MeasurableSet.univ]
  rw [Set.univ_inter]
  rw [Real.volume_Icc]
  simp

/-- The sample space Ω_n = [0,1]^n with product measure. -/
@[reducible]
def Ω (n : ℕ) : Type := Fin n → ℝ

instance (n : ℕ) : MeasurableSpace (Ω n) := inferInstanceAs (MeasurableSpace (Fin n → ℝ))

/-- The probability measure on Ω_n (product of n copies of unitMeasure). -/
def P (n : ℕ) : Measure (Ω n) :=
  Measure.pi (fun (_ : Fin n) => unitMeasure)

instance (n : ℕ) : IsProbabilityMeasure (P n) := by
  unfold P
  infer_instance

/-- The i-th random variable X_i : Ω_n → ℝ, the i-th coordinate. -/
def X (n : ℕ) (i : Fin n) : Ω n → ℝ := fun ω => ω i

lemma X_measurable (n : ℕ) (i : Fin n) : Measurable (X n i) := by
  -- X n i is definitionally fun ω => ω i
  exact measurable_pi_apply i

-- 2. The filtration

/-- The σ-algebra generated by the first k coordinates (k ≤ n). -/
@[instance_reducible]
def filtration (n k : ℕ) (hk : k ≤ n) : MeasurableSpace (Ω n) :=
  MeasurableSpace.comap (fun ω i => ω (Fin.castLE hk i)) inferInstance

-- 3. Stopping rules

/-- A stopping rule is a measurable function τ : Ω_n → Fin n
    (representing the selected time, where 0 = first observation, n-1 = last observation)
    such that for all t : Fin n, the event {τ ≤ t} is in the σ-algebra generated by X_0,...,X_t. -/
structure StoppingRule (n : ℕ) where
  τ : Ω n → Fin n
  measurable_τ : Measurable τ
  stopping_time : ∀ (t : Fin n),
    @MeasurableSet (Ω n) (filtration n (t.val + 1) (by
      have h := t.is_lt
      omega)) {ω | (τ ω).val ≤ t.val}

-- 4. The rank

/-- The rank of a value x among a finite set of values (1 = smallest). -/
def rankValue (x : ℝ) (values : Finset ℝ) : ℕ :=
  1 + (values.filter (fun y => y < x)).card

/-- The rank of the selected value X_τ(ω) among all X_i(ω). -/
def selectedRank (n : ℕ) (τ : StoppingRule n) (ω : Ω n) : ℕ :=
  let i := τ.τ ω
  rankValue (X n i ω) (Finset.image (fun (j : Fin n) => X n j ω) Finset.univ)

-- 5. Expected rank

/-- The expected rank for a stopping rule. -/
def expectedRank (n : ℕ) (τ : StoppingRule n) : ℝ :=
  ∫ ω, (selectedRank n τ ω : ℝ) ∂(P n)

-- 6. Optimal value

/-- A constant stopping rule: always stop at time 1 (i.e., select the first observation).
    Requires n ≥ 1. -/
def alwaysStop1 (n : ℕ) [NeZero n] : StoppingRule n where
  τ := fun _ => 0
  measurable_τ := by
    exact measurable_const
  stopping_time := by
    intro t
    have : {ω : Ω n | ((0 : Fin n).val : ℕ) ≤ (t : ℕ)} = Set.univ := by
      ext ω; simp
    rw [this]
    exact MeasurableSet.univ

/-- The set of expected ranks is nonempty (there is at least one stopping rule).
    Requires n ≥ 1. -/
theorem expectedRank_nonempty (n : ℕ) [NeZero n] :
    {r : ℝ | ∃ (τ : StoppingRule n), expectedRank n τ = r}.Nonempty := by
  refine ⟨expectedRank n (alwaysStop1 n), ?_⟩
  exact ⟨alwaysStop1 n, rfl⟩

/-- The rank is always at least 1. -/
theorem selectedRank_ge_one (n : ℕ) (τ : StoppingRule n) (ω : Ω n) :
    1 ≤ (selectedRank n τ ω : ℝ) := by
  dsimp [selectedRank, rankValue]
  have : (1 : ℕ) ≤ 1 + (Finset.filter (fun y => y < X n (τ.τ ω) ω)
    (Finset.image (fun (j : Fin n) => X n j ω) Finset.univ)).card := by
    omega
  exact_mod_cast this

/-- The optimal value v(n) = inf over all stopping rules of the expected rank. -/
def robbinsValue (n : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ (τ : StoppingRule n), expectedRank n τ = r}

end

end Indep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Robbins

open Filter Topology

/-- The bound on `v 300` (Section 6.1). -/
theorem v300 : ((137704521264 : ℝ) / 2 ^ 36) ≤ v 300 := sorry

/-- Theorem 1.2, for every `n ≥ 300`. -/
theorem main_so : ∀ n ≥ 300, ((137704521264 : ℝ) / 2 ^ 36) ≤ v n := sorry

/-- Theorem 1.2, for every limit of `v n`. -/
theorem main_so_limit : ∀ V : ℝ, Tendsto v atTop (𝓝 V) → (137704521264 : ℝ) / 2 ^ 36 ≤ V := sorry

/-- `v n > 2` for every `n ≥ 300` (Theorem 1.2). -/
theorem two_lt_v : ∀ n ≥ 300, (2 : ℝ) < v n := sorry

/-- Proposition 2.4. -/
theorem relaxed300 :
    ∃ u : RelaxedSubSolution 300 5, u.u 1 (fun _ => 1) = (137704521264 : ℝ) / 2 ^ 36 := sorry

/-- Theorem 2.2. -/
theorem RelaxedSubSolution.val_one_le_v {n m : ℕ} (u : RelaxedSubSolution n m) (hn : 1 ≤ n) :
    u.u 1 (fun _ => 1) ≤ v n := sorry

/-- Theorem 2.3. -/
theorem v_mono : Monotone v := sorry

/-- Proposition A.1: `v` is the value of the second formalization, over stopping rules. -/
theorem robbinsValue_eq_v (n : ℕ) : Indep.robbinsValue (n + 1) = v (n + 1) := sorry

/-- From `v N` to every `n ≥ N` (Section 6.1), by Theorem 2.3. -/
theorem lower_bound_of_base {c : ℝ} {N : ℕ} (h : c ≤ v N) : ∀ n ≥ N, c ≤ v n := sorry

/-- From `v N` to every limit of `v n` (Section 6.1). -/
theorem limit_lower_bound_of_base {c : ℝ} {N : ℕ} (h : c ≤ v N) (V : ℝ) (hV : Tendsto v atTop (𝓝 V)) :
    c ≤ V := sorry

end Robbins
