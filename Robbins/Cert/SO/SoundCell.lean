import Robbins.Cert.SO.SoundRec
import Robbins.Cert.SO.SoundArith
import Robbins.Cert.SoundState

/-!
# The pointwise bounds of one record list (second-order soundness, 8.2, 8.3)

Sections 8.2 and 8.3 of the specification (Robbins/Cert/SO/Spec.lean). Fix `t < n`, a record list `c` with the facts of 8.1
(`RecOK`), a memory `y` that fits it, the tables `uh`, `sg` and a value `x`. Write
`delta_l = val_l / D - y_l` (`≥ 0`, at most `w_l / D` for a credited record).

On a cell `i ≤ im` (`p_{i-1} < x D ≤ p_i`):

* `relaxStop_cell`: the stop cost is `alpha_i + r x + #{l : pos_l = i, y_l < x}` (8.2 (a));
* `drop_ge_cell`: the penalty is at least `Em / D` plus the credit of the last record (8.2 (b));
* `ceilR_ins_cell`: `ceil_{t+1} (ins y x) = H_i` (8.2 (c), (d));
* `slot_term`, `cont_succ_ge_cell`: `u_{t+1} (ins y x)` is at least the continuation part of
  `beta`, slot by slot (8.2 (e)): the slots of the records below the cell `i` and above it carry
  `ev_l` and `delta_l`, the first slot of the block of the cell `i` carries `x`, every other slot of
  the block carries `ev_l` only;
* `cont_ge_cell`: the continuation is at least `(beta - sigma X) / D ^ 2 + s (x)` (8.2 (f)).

Above `p_im`, the last record not forgotten (the tail), `relaxStop_tail` and `cont_tail` give the
stop cost and the continuation exactly (8.3).
-/

namespace Robbins.Cert.SO

open Robbins.Cert

variable {D : ℕ} {g : Grid}

/-! ## Cells -/

theorem inCell_max {t i : ℕ} {a b : ℝ} (ha : InCell D g t i a) (hb : InCell D g t i b) :
    InCell D g t i (max a b) := by
  refine ⟨?_, ?_⟩
  · rcases ha.1 with h | h
    · exact Or.inl h
    · right
      calc (cp D g t (i - 1) : ℝ) < a * D := h
        _ ≤ max a b * D := by gcongr; exact le_max_left _ _
  · rw [max_mul_of_nonneg _ _ (Nat.cast_nonneg D)]
    exact max_le ha.2 hb.2

theorem inCell_min {t i : ℕ} {a b : ℝ} (ha : InCell D g t i a) (hb : InCell D g t i b) :
    InCell D g t i (min a b) := by
  refine ⟨?_, ?_⟩
  · rcases ha.1 with h | h
    · exact Or.inl h
    · rcases hb.1 with h' | h'
      · exact Or.inl h'
      · right
        rw [min_mul_of_nonneg _ _ (Nat.cast_nonneg D)]
        exact lt_min h h'
  · calc min a b * D ≤ a * D := by gcongr; exact min_le_left _ _
      _ ≤ _ := ha.2

/-! ## A memory that fits a record list -/

section Fit

variable {t d : ℕ} {c : Fin (d + 1) → Rec} {y : Fin (d + 1) → ℝ}

theorem fit_mul_le (hc : RecOK D g t c) (hfit : Fits D g t c y) (l : Fin (d + 1)) :
    y l * D ≤ (c l).val := by
  rw [hc.val_eq l]; exact (hfit l).2

theorem fit_delta_nonneg (hD : 0 < D) (hc : RecOK D g t c) (hfit : Fits D g t c y)
    (l : Fin (d + 1)) : 0 ≤ ((c l).val : ℝ) / D - y l := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [sub_nonneg, le_div_iff₀ hD']
  exact fit_mul_le hc hfit l

theorem fit_cp_pred_le (hy : IsMemory y) (hfit : Fits D g t c y) (l : Fin (d + 1)) :
    (cp D g t ((c l).pos - 1) : ℝ) ≤ y l * D := by
  rcases (hfit l).1 with h | h
  · rw [h]
    simp only [Nat.sub_self, cp, ite_true, Nat.cast_zero]
    exact mul_nonneg (hy.2 l).1 (Nat.cast_nonneg D)
  · exact h.le

theorem fit_delta_le (hD : 0 < D) (hy : IsMemory y) (hc : RecOK D g t c)
    (hfit : Fits D g t c y) (l : Fin (d + 1)) (hw : 0 < (c l).w) :
    ((c l).val : ℝ) / D - y l ≤ ((c l).w : ℝ) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hweq : ((c l).w : ℝ) + cp D g t ((c l).pos - 1) = (c l).val := by
    rw [hc.val_eq l]; exact_mod_cast hc.w_eq l hw
  have := fit_cp_pred_le hy hfit l
  rw [div_sub' (ne_of_gt hD'), div_le_div_iff_of_pos_right hD']
  linarith

/-- 8.1 (e): `ceil_{t+1} (y_l) = map_l`. -/
theorem fit_ceilR (hg : ok D g = true) (ht1 : 1 ≤ t) (htn : t < g.n) (hy : IsMemory y)
    (hc : RecOK D g t c) (hfit : Fits D g t c y) (l : Fin (d + 1)) :
    ceilR D g (t + 1) (y l) = (c l).map := by
  rw [hc.map_eq l]
  exact ceilR_succ_of_inCell hg ht1 htn (hc.pos_pos l) (hc.pos_le l) (hy.2 l).1 (hfit l)

/-- A coordinate of a cell below the cell `i` is below every point of the cell `i`. -/
theorem fit_lt_of_pos_lt (hg : ok D g = true) (hfit : Fits D g t c y)
    {l : Fin (d + 1)} {i : ℕ} (hiL : i ≤ g.L t) (h : (c l).pos < i) {x : ℝ}
    (hxa : (cp D g t (i - 1) : ℝ) < x * D) : y l < x := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast g.so_D_pos D hg
  have h1 : y l * D ≤ cp D g t (c l).pos := (hfit l).2
  have h2 : cp D g t (c l).pos ≤ cp D g t (i - 1) := g.so_cp_mono D hg (by omega) (by omega)
  have h3 : (cp D g t (c l).pos : ℝ) ≤ cp D g t (i - 1) := by exact_mod_cast h2
  exact lt_of_mul_lt_mul_right (by linarith) hD'.le

/-- A coordinate of a cell above the cell `i` is above every point of the cell `i`. -/
theorem fit_gt_of_lt_pos (hg : ok D g = true) (hc : RecOK D g t c) (hfit : Fits D g t c y)
    {l : Fin (d + 1)} {i : ℕ} (hi1 : 1 ≤ i) (h : i < (c l).pos) {x : ℝ} (hxb : x * D ≤ cp D g t i) :
    x < y l := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast g.so_D_pos D hg
  have h1 : (cp D g t ((c l).pos - 1) : ℝ) < y l * D := by
    rcases (hfit l).1 with h' | h'
    · omega
    · exact h'
  have h2 : cp D g t i ≤ cp D g t ((c l).pos - 1) := g.so_cp_mono D hg (by omega)
    (by have := hc.pos_le l; omega)
  have h3 : (cp D g t i : ℝ) ≤ cp D g t ((c l).pos - 1) := by exact_mod_cast h2
  exact lt_of_mul_lt_mul_right (by linarith) hD'.le

theorem pos_le_im (hc : RecOK D g t c) (l : Fin (d + 1)) : (c l).pos ≤ im d c :=
  hc.pos_mono (Fin.le_last l)

/-- A forgotten record forces the last one to be forgotten. -/
theorem forg_last_of_forg (hc : RecOK D g t c) {l : Fin (d + 1)} (h : (c l).forg = true) :
    (c (Fin.last d)).forg = true := by
  have h1 := (hc.forg_iff l).mp h
  have h2 := pos_le_im hc l
  have h3 := hc.pos_le (Fin.last d)
  exact (hc.forg_iff _).mpr (le_antisymm h3 (h1 ▸ h2))

end Fit

/-! ## The slots of `H_i` -/

section Slot

variable {d : ℕ} {c : Fin (d + 1) → Rec}

/-- `below_i` counts an initial segment: `l < below_i ↔ pos_l < i`. -/
theorem lt_below_iff (hmono : Monotone fun l => (c l).pos) (i : ℕ) (l : Fin d) :
    (l : ℕ) < below d c i ↔ (c l.castSucc).pos < i := by
  unfold below
  constructor
  · intro h
    by_contra hge
    push Not at hge
    have hsub : (Finset.univ.filter fun l' : Fin d => (c l'.castSucc).pos + 1 ≤ i) ⊆
        Finset.Iio l := by
      intro l' hl'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl'
      simp only [Finset.mem_Iio]
      by_contra hle
      push Not at hle
      have := hmono (Fin.castSucc_le_castSucc_iff.mpr hle)
      simp only at this
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega
  · intro h
    have hsub : Finset.Iic l ⊆
        (Finset.univ.filter fun l' : Fin d => (c l'.castSucc).pos + 1 ≤ i) := by
      intro l' hl'
      simp only [Finset.mem_Iic] at hl'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := hmono (Fin.castSucc_le_castSucc_iff.mpr hl')
      simp only at this
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega

/-- `slot` is the insertion of the slot `below_i`. -/
theorem slot_eq_succAbove (hmono : Monotone fun l => (c l).pos) (i : ℕ) (l : Fin d) :
    slot d c i l = (belowF d c i).succAbove l := by
  unfold slot
  by_cases h : i ≤ (c l.castSucc).pos
  · rw [ite_eq_left h, Fin.succAbove_of_le_castSucc]
    rw [Fin.le_def]
    simp only [belowF, Fin.val_castSucc]
    have := (lt_below_iff hmono i l).not.mpr (by omega)
    omega
  · rw [ite_eq_right h, Fin.succAbove_of_castSucc_lt]
    rw [Fin.lt_def]
    simp only [belowF, Fin.val_castSucc]
    exact (lt_below_iff hmono i l).mpr (by omega)

theorem Hc_below (g : Grid) (t i : ℕ) : Hc g d t c i (belowF d c i) = g.nxt t i := by
  unfold Hc
  simp [belowF]

theorem Hc_succAbove (g : Grid) (t i : ℕ) (l : Fin d) :
    Hc g d t c i ((belowF d c i).succAbove l) = (c l.castSucc).map := by
  unfold Hc
  by_cases h : (l : ℕ) < below d c i
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa [belowF] using h)]
    simp [h]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp [belowF]; omega)]
    have h1 : ¬ ((l.succ : ℕ) < below d c i) := by simp; omega
    have h2 : ¬ ((l.succ : ℕ) = below d c i) := by simp; omega
    rw [ite_eq_right h1, ite_eq_right h2]
    congr 2

theorem coefC_castSucc (D : ℕ) (g : Grid) (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) (t i : ℕ)
    (l : Fin d) :
    coefC D g d Sg t c i l.castSucc =
      if (c l.castSucc).forg = true ∨ (c l.castSucc).pos = i then 0
      else (Sg (Hc g d t c i) (slot d c i l) : ℤ) := by
  unfold coefC slot
  have hl : ¬ ((l.castSucc : Fin (d + 1)) : ℕ) = d := by
    simp only [Fin.val_castSucc]; exact Nat.ne_of_lt l.isLt
  rw [dite_eq_right hl]
  have hfin : (⟨(l.castSucc : ℕ), by simp⟩ : Fin d) = l := by ext; simp
  simp only [hfin]
  by_cases hf : (c l.castSucc).forg = true
  · simp [hf]
  · simp only [hf, false_or, Bool.false_eq_true, ite_false]
    by_cases h1 : i < (c l.castSucc).pos
    · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_left (by omega)]
    · rw [ite_eq_right h1]
      by_cases h2 : (c l.castSucc).pos = i
      · rw [ite_eq_left h2, ite_eq_left h2]
      · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_right (by omega)]

theorem coefC_last (D : ℕ) (g : Grid) (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) (t i : ℕ) :
    coefC D g d Sg t c i (Fin.last d) =
      if (c (Fin.last d)).forg = true ∨ i = im d c then 0
      else (((g.n - t) * Epen D (pt D g (c (Fin.last d)).gi) (g.n - t - 1) : ℕ) : ℤ) := by
  unfold coefC
  rw [dite_eq_left (by simp)]

end Slot

/-! ## `ins` -/

theorem ins_eq_self {m : ℕ} {y : Fin m → ℝ} (hy : IsMemory y) {x : ℝ} {q : Fin m}
    (h : y q ≤ x) : ins y x q = y q := by
  unfold ins
  rw [min_eq_left h]
  apply max_eq_right
  split_ifs with h0
  · exact (hy.2 q).1
  · exact hy.1 (Fin.mk_le_mk.mpr (by omega))

theorem ins_succ {d : ℕ} (y : Fin (d + 1) → ℝ) (x : ℝ) (l : Fin d) :
    ins y x l.succ = max (y l.castSucc) (min (y l.succ) x) := by
  unfold ins
  have h : ¬ ((l.succ : ℕ) = 0) := by simp
  rw [dite_eq_right h]
  congr 2

theorem ins_succ_eq {d : ℕ} {y : Fin (d + 1) → ℝ} {x : ℝ} {l : Fin d} (h : x ≤ y l.castSucc) :
    ins y x l.succ = y l.castSucc := by
  rw [ins_succ]
  exact max_eq_left ((min_le_right _ _).trans h)

/-! ## The bounds on a cell `i ≤ im` -/

section CellBounds

variable {t d : ℕ} {c : Fin (d + 1) → Rec} {y : Fin (d + 1) → ℝ}

/-- The records at or above the slot `below_i` are at or above the cell `i`. -/
theorem le_pos_of_below_le (hc : RecOK D g t c) {i : ℕ} (him : i ≤ im d c) {q : Fin (d + 1)}
    (hq : below d c i ≤ q) : i ≤ (c q).pos := by
  rcases Fin.eq_castSucc_or_eq_last q with ⟨l, rfl⟩ | rfl
  · have := (lt_below_iff hc.pos_mono i l).not.mp (by simp at hq; omega)
    omega
  · exact him

/-- On the cell `i`, `min (y_q, x)` lies in the cell `i` when the record `q` is at or above it. -/
theorem inCell_min_of_le_pos (hg : ok D g = true) (hc : RecOK D g t c) (hfit : Fits D g t c y)
    {i : ℕ} (hi1 : 1 ≤ i) {q : Fin (d + 1)} (hq : i ≤ (c q).pos) {x : ℝ}
    (hxa : (cp D g t (i - 1) : ℝ) < x * D) (hxb : x * D ≤ cp D g t i) :
    InCell D g t i (min (y q) x) := by
  refine ⟨?_, ?_⟩
  · by_cases hi : i = 1
    · exact Or.inl hi
    · right
      rw [min_mul_of_nonneg _ _ (Nat.cast_nonneg D)]
      refine lt_min ?_ hxa
      rcases (hfit q).1 with h | h
      · omega
      · have h2 : cp D g t (i - 1) ≤ cp D g t ((c q).pos - 1) :=
          g.so_cp_mono D hg (by omega) (by have := hc.pos_le q; omega)
        have h3 : (cp D g t (i - 1) : ℝ) ≤ cp D g t ((c q).pos - 1) := by exact_mod_cast h2
        linarith
  · calc min (y q) x * D ≤ x * D := by gcongr; exact min_le_right _ _
      _ ≤ _ := hxb

/-- 8.2 (c), (d): on the cell `i ≤ im`, `ceil_{t+1} (ins y x) = H_i`; and the values of `ins y x`
slot by slot. -/
theorem ins_cell (hg : ok D g = true) (hy : IsMemory y) (hc : RecOK D g t c)
    (hfit : Fits D g t c y) {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ im d c) {x : ℝ}
    (hxa : (cp D g t (i - 1) : ℝ) < x * D) (hxb : x * D ≤ cp D g t i) :
    (ins y x (belowF d c i) ≤ x ∧ InCell D g t i (ins y x (belowF d c i))) ∧
      ∀ l : Fin d, ((c l.castSucc).pos ≠ i →
        ins y x ((belowF d c i).succAbove l) = y l.castSucc) ∧
        ((c l.castSucc).pos = i → InCell D g t i (ins y x ((belowF d c i).succAbove l))) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast g.so_D_pos D hg
  have hiL : i ≤ g.L t := him.trans (hc.pos_le _)
  have hx0 : 0 ≤ x := by
    have : (0 : ℝ) ≤ cp D g t (i - 1) := Nat.cast_nonneg _
    exact le_of_lt (pos_of_mul_pos_left (by linarith) hD'.le)
  set b := belowF d c i with hb
  constructor
  · -- the slot `below_i`: `ins y x b = min (y_b, x)`
    have hbq : i ≤ (c b).pos := le_pos_of_below_le hc him (by simp [b, belowF])
    have hmin := inCell_min_of_le_pos hg hc hfit hi1 hbq hxa hxb
    have hprev : (if h : (b : ℕ) = 0 then (0 : ℝ) else y ⟨b - 1, by omega⟩) ≤ min (y b) x := by
      split_ifs with h0
      · exact le_min (hy.2 b).1 hx0
      · have hb1 : (b : ℕ) - 1 < d := by have := below_le d c i; simp [b, belowF] at h0 ⊢; omega
        set l0 : Fin d := ⟨b - 1, hb1⟩
        have hl0 : (c l0.castSucc).pos < i :=
          (lt_below_iff hc.pos_mono i l0).mp (by simp [l0, b, belowF] at h0 ⊢; omega)
        have hlt := fit_lt_of_pos_lt hg hfit hiL hl0 hxa
        have hcs : (⟨b - 1, by omega⟩ : Fin (d + 1)) = l0.castSucc := by ext; simp [l0]
        rw [hcs]
        exact le_min (hy.1 (by rw [Fin.le_def]; simp [l0])) hlt.le
    have heq : ins y x b = min (y b) x := by unfold ins; exact max_eq_right hprev
    rw [heq]
    exact ⟨min_le_right _ _, hmin⟩
  · intro l
    have hmono := hc.pos_mono
    constructor
    · intro hne
      by_cases hlt : (c l.castSucc).pos < i
      · rw [Fin.succAbove_of_castSucc_lt _ _ (by
          rw [Fin.lt_def]; simpa [b, belowF] using (lt_below_iff hmono i l).mpr hlt)]
        exact ins_eq_self hy (fit_lt_of_pos_lt hg hfit hiL hlt hxa).le
      · have hgt : i < (c l.castSucc).pos := by omega
        rw [Fin.succAbove_of_le_castSucc _ _ (by
          rw [Fin.le_def]; simp only [b, belowF, Fin.val_castSucc]
          have := (lt_below_iff hmono i l).not.mpr (by omega); omega)]
        exact ins_succ_eq (fit_gt_of_lt_pos hg hc hfit hi1 hgt hxb).le
    · intro heq
      rw [Fin.succAbove_of_le_castSucc _ _ (by
        rw [Fin.le_def]; simp only [b, belowF, Fin.val_castSucc]
        have := (lt_below_iff hmono i l).not.mpr (by omega); omega)]
      rw [ins_succ]
      have h1 : InCell D g t i (y l.castSucc) := heq ▸ hfit l.castSucc
      have hq : i ≤ (c l.succ).pos := by
        have := hmono (show l.castSucc ≤ l.succ from Fin.castSucc_le_succ l)
        simp only at this; omega
      exact inCell_max h1 (inCell_min_of_le_pos hg hc hfit hi1 hq hxa hxb)


/-- A point of the cell `i` lies in `[0, 1]`. -/
theorem mem_Icc_of_cell (hg : ok D g = true) {i : ℕ} {x : ℝ}
    (hxa : (cp D g t (i - 1) : ℝ) < x * D) (hxb : x * D ≤ cp D g t i) : x ∈ Set.Icc (0 : ℝ) 1 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast g.so_D_pos D hg
  have h0 : (0 : ℝ) ≤ cp D g t (i - 1) := Nat.cast_nonneg _
  have h1 : (cp D g t i : ℝ) ≤ D := by exact_mod_cast g.so_cp_le_D D hg t i
  refine ⟨le_of_lt (pos_of_mul_pos_left (by linarith) hD'.le), ?_⟩
  by_contra h
  push Not at h
  nlinarith

/-- 8.2 (c): the ceilings of the slots of `ins y x` other than `below_i`. -/
theorem ceilR_ins_succAbove (hg : ok D g = true) (ht1 : 1 ≤ t) (htn : t < g.n) (hy : IsMemory y)
    (hc : RecOK D g t c) (hfit : Fits D g t c y) {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ im d c)
    {x : ℝ} (hxa : (cp D g t (i - 1) : ℝ) < x * D) (hxb : x * D ≤ cp D g t i) (l : Fin d) :
    ceilR D g (t + 1) (ins y x ((belowF d c i).succAbove l)) = (c l.castSucc).map := by
  have hiL : i ≤ g.L t := him.trans (hc.pos_le _)
  have hx01 := mem_Icc_of_cell hg hxa hxb
  have hz01 := ins_mem_Icc hy hx01 ((belowF d c i).succAbove l)
  obtain ⟨hne, heq⟩ := (ins_cell hg hy hc hfit hi1 him hxa hxb).2 l
  by_cases hpi : (c l.castSucc).pos = i
  · rw [hc.map_eq, hpi]
    exact ceilR_succ_of_inCell hg ht1 htn hi1 hiL hz01.1 (heq hpi)
  · rw [hne hpi]
    exact fit_ceilR hg ht1 htn hy hc hfit _

/-- 8.2 (c), (d): `ceil_{t+1} (ins y x) = H_i` on the cell `i ≤ im`. -/
theorem ceilR_ins_cell (hg : ok D g = true) (ht1 : 1 ≤ t) (htn : t < g.n) (hy : IsMemory y)
    (hc : RecOK D g t c) (hfit : Fits D g t c y) {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ im d c)
    {x : ℝ} (hxa : (cp D g t (i - 1) : ℝ) < x * D) (hxb : x * D ≤ cp D g t i) :
    (fun q => ceilR D g (t + 1) (ins y x q)) = Hc g d t c i := by
  have hiL : i ≤ g.L t := him.trans (hc.pos_le _)
  have hx01 := mem_Icc_of_cell hg hxa hxb
  funext q
  rcases Fin.eq_self_or_eq_succAbove (belowF d c i) q with rfl | ⟨l, rfl⟩
  · rw [Hc_below]
    have h := (ins_cell hg hy hc hfit hi1 him hxa hxb).1
    exact ceilR_succ_of_inCell hg ht1 htn hi1 hiL (ins_mem_Icc hy hx01 _).1 h.2
  · rw [Hc_succAbove, ceilR_ins_succAbove hg ht1 htn hy hc hfit hi1 him hxa hxb]

/-- 8.2 (e), one slot: the slot of the record `l ≤ m - 2` (below the cell `i`, in its block, or
above it) carries at least `s ev_l / D ^ 2`, plus `s delta_l / D` when the record is credited and
not in the cell `i` (the own-cell slot accounting). -/
theorem slot_term (hg : ok D g = true) (ht1 : 1 ≤ t) (htn : t < g.n) (hy : IsMemory y)
    (hc : RecOK D g t c) (hfit : Fits D g t c y) {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ im d c)
    {x : ℝ} (hxa : (cp D g t (i - 1) : ℝ) < x * D) (hxb : x * D ≤ cp D g t i) (l : Fin d)
    (s : ℕ) :
    (s : ℝ) * (ev D g d t c l.castSucc : ℝ) / (D : ℝ) ^ 2 +
        (if 0 < (c l.castSucc).w then
          (((if (c l.castSucc).forg = true ∨ (c l.castSucc).pos = i then (0 : ℤ) else (s : ℤ)) :
            ℤ) : ℝ) * (((c l.castSucc).val : ℝ) / D - y l.castSucc) / D
        else 0) ≤
      (s : ℝ) / D * ((pt D g (g.glob (t + 1) (c l.castSucc).map) : ℝ) / D -
        ins y x ((belowF d c i).succAbove l)) := by
  have hD : 0 < D := g.so_D_pos D hg
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hx01 := mem_Icc_of_cell hg hxa hxb
  set z := ins y x ((belowF d c i).succAbove l) with hz
  have hz01 := ins_mem_Icc hy hx01 ((belowF d c i).succAbove l)
  rw [← hz] at hz01
  set P : ℝ := (pt D g (g.glob (t + 1) (c l.castSucc).map) : ℝ) with hP
  have hzP : z * D ≤ P := by
    have := g.so_le_pt_ceilR D hD (t + 1) hz01.2
    rwa [ceilR_ins_succAbove hg ht1 htn hy hc hfit hi1 him hxa hxb l] at this
  have hzP' : z ≤ P / D := by rw [le_div_iff₀ hD']; exact hzP
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hδ := fit_delta_nonneg hD hc hfit l.castSucc
  obtain ⟨hne, heq⟩ := (ins_cell hg hy hc hfit hi1 him hxa hxb).2 l
  unfold ev
  by_cases hf : (c l.castSucc).forg = true
  · simp only [hf, ite_true, true_or, Int.cast_zero, mul_zero, zero_div, zero_mul, ite_self,
      add_zero]
    exact mul_nonneg (div_nonneg hs0 hD'.le) (by linarith)
  · simp only [hf, Bool.false_eq_true, ite_false, false_or]
    push_cast
    have hsplit : (s : ℝ) / D * (P / D - z) =
        (s : ℝ) * (P - (c l.castSucc).val) / (D : ℝ) ^ 2 +
          (s : ℝ) / D * (((c l.castSucc).val : ℝ) / D - z) := by
      field_simp; ring
    rw [hsplit]
    by_cases hpi : (c l.castSucc).pos = i
    · simp only [hpi, ite_true, zero_mul, zero_div, ite_self, add_zero]
      have hzv : z ≤ ((c l.castSucc).val : ℝ) / D := by
        rw [le_div_iff₀ hD', hc.val_eq, hpi]; exact (heq hpi).2
      have : 0 ≤ (s : ℝ) / D * (((c l.castSucc).val : ℝ) / D - z) :=
        mul_nonneg (div_nonneg hs0 hD'.le) (by linarith)
      linarith
    · simp only [hpi, ite_false]
      rw [hz, hne hpi]
      have hmain : (s : ℝ) / D * (((c l.castSucc).val : ℝ) / D - y l.castSucc) =
          (s : ℝ) * (((c l.castSucc).val : ℝ) / D - y l.castSucc) / D := by ring
      split_ifs
      · linarith
      · have : 0 ≤ (s : ℝ) / D * (((c l.castSucc).val : ℝ) / D - y l.castSucc) :=
          mul_nonneg (div_nonneg hs0 hD'.le) hδ
        linarith

/-- 8.2 (e): `u_{t+1} (ins y x)` on the cell `i ≤ im`. -/
theorem cont_succ_ge_cell (hg : ok D g = true) (ht1 : 1 ≤ t) (htn : t < g.n) (hy : IsMemory y)
    (hc : RecOK D g t c) (hfit : Fits D g t c y) {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ im d c)
    {x : ℝ} (hxa : (cp D g t (i - 1) : ℝ) < x * D) (hxb : x * D ≤ cp D g t i)
    (uh : ℕ → (Fin (d + 1) → ℕ) → ℕ) (sg : ℕ → (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) :
    ((D : ℝ) * (uh (t + 1) (Hc g d t c i) : ℝ) +
          (sg (t + 1) (Hc g d t c i) (belowF d c i) : ℝ) *
            (pt D g (g.glob (t + 1) (g.nxt t i)) : ℝ) -
          (sg (t + 1) (Hc g d t c i) (belowF d c i) : ℝ) * (x * D) +
          ∑ l : Fin d, (sg (t + 1) (Hc g d t c i) (slot d c i l) : ℝ) *
            (ev D g d t c l.castSucc : ℝ)) / (D : ℝ) ^ 2 +
        ∑ l : Fin d, (if 0 < (c l.castSucc).w then
          (coefC D g d (sg (t + 1)) t c i l.castSucc : ℝ) *
            (((c l.castSucc).val : ℝ) / D - y l.castSucc) / D else 0) ≤
      uSO D g d uh sg (t + 1) (ins y x) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast g.so_D_pos D hg
  have hmono := hc.pos_mono
  set H := Hc g d t c i with hH
  set b := belowF d c i with hb
  have hceilq : ∀ q, ceilR D g (t + 1) (ins y x q) = H q := fun q =>
    congrFun (ceilR_ins_cell hg ht1 htn hy hc hfit hi1 him hxa hxb) q
  unfold uSO
  simp only [hceilq]
  rw [Fin.sum_univ_succAbove _ b]
  -- the slot `below_i`
  have hbz : ins y x b ≤ x := (ins_cell hg hy hc hfit hi1 him hxa hxb).1.1
  have hHb : H b = g.nxt t i := Hc_below g t i
  have hterm_b : (sg (t + 1) H b : ℝ) * ((pt D g (g.glob (t + 1) (g.nxt t i)) : ℝ) - x * D) /
      (D : ℝ) ^ 2 ≤ (sg (t + 1) H b : ℝ) / D *
        ((pt D g (g.glob (t + 1) (H b)) : ℝ) / D - ins y x b) := by
    rw [hHb]
    have h1 : (sg (t + 1) H b : ℝ) * ((pt D g (g.glob (t + 1) (g.nxt t i)) : ℝ) - x * D) /
        (D : ℝ) ^ 2 = (sg (t + 1) H b : ℝ) / D *
          ((pt D g (g.glob (t + 1) (g.nxt t i)) : ℝ) / D - x) := by field_simp
    rw [h1]
    exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg (Nat.cast_nonneg _) hD'.le)
  -- the other slots
  have hterm : ∀ l : Fin d,
      (sg (t + 1) H (slot d c i l) : ℝ) * (ev D g d t c l.castSucc : ℝ) / (D : ℝ) ^ 2 +
          (if 0 < (c l.castSucc).w then
            (coefC D g d (sg (t + 1)) t c i l.castSucc : ℝ) *
              (((c l.castSucc).val : ℝ) / D - y l.castSucc) / D else 0) ≤
        (sg (t + 1) H (b.succAbove l) : ℝ) / D *
          ((pt D g (g.glob (t + 1) (H (b.succAbove l))) : ℝ) / D - ins y x (b.succAbove l)) := by
    intro l
    have h := slot_term hg ht1 htn hy hc hfit hi1 him hxa hxb l (sg (t + 1) H (b.succAbove l))
    rw [hH, Hc_succAbove g t i l, ← hH]
    rw [coefC_castSucc, slot_eq_succAbove hmono, ← hb, ← hH]
    exact h
  have hsum := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hterm l
  rw [Finset.sum_add_distrib] at hsum
  have hsplit : ((D : ℝ) * (uh (t + 1) H : ℝ) + (sg (t + 1) H b : ℝ) *
        (pt D g (g.glob (t + 1) (g.nxt t i)) : ℝ) - (sg (t + 1) H b : ℝ) * (x * D) +
        ∑ l : Fin d, (sg (t + 1) H (slot d c i l) : ℝ) * (ev D g d t c l.castSucc : ℝ)) /
          (D : ℝ) ^ 2 =
      (uh (t + 1) H : ℝ) / D + (sg (t + 1) H b : ℝ) *
        ((pt D g (g.glob (t + 1) (g.nxt t i)) : ℝ) - x * D) / (D : ℝ) ^ 2 +
        ∑ l : Fin d, (sg (t + 1) H (slot d c i l) : ℝ) * (ev D g d t c l.castSucc : ℝ) /
          (D : ℝ) ^ 2 := by
    rw [← Finset.sum_div]; field_simp; ring
  rw [hsplit]
  linarith

/-- 8.2 (b): the drop penalty on the cell `i ≤ im`. -/
theorem drop_ge_cell (hg : ok D g = true) (hy : IsMemory y) (hc : RecOK D g t c)
    (hfit : Fits D g t c y) (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) {i : ℕ} (hi1 : 1 ≤ i)
    (him : i ≤ im d c) {x : ℝ} (hxa : (cp D g t (i - 1) : ℝ) < x * D)
    (hxb : x * D ≤ cp D g t i) :
    (Epen D (pt D g (c (Fin.last d)).gi) (g.n - t) : ℝ) / D +
        (if 0 < (c (Fin.last d)).w then
          (coefC D g d Sg t c i (Fin.last d) : ℝ) *
            (((c (Fin.last d)).val : ℝ) / D - y (Fin.last d)) / D else 0) ≤
      dropPenalty g.n t y x := by
  have hD : 0 < D := g.so_D_pos D hg
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hx01 := mem_Icc_of_cell hg hxa hxb
  have hdrop : drop y x = max (y (Fin.last d)) x := by
    unfold drop
    rw [dite_eq_right (by omega)]
    rfl
  have hval := hc.val_eq (Fin.last d)
  have hpos := hc.pos_le (Fin.last d)
  unfold dropPenalty
  rw [hdrop, coefC_last, hc.gi_eq]
  set z := (c (Fin.last d)).val with hzdef
  have hzD : z ≤ D := by rw [hval]; exact g.so_cp_le_D D hg t _
  set p : ℝ := (z : ℝ) / D with hp
  have hp0 : 0 ≤ p := div_nonneg (Nat.cast_nonneg _) hD'.le
  have hp1 : p ≤ 1 := by rw [hp, div_le_one hD']; exact_mod_cast hzD
  have hyl : y (Fin.last d) ≤ p := by rw [hp, le_div_iff₀ hD']; exact fit_mul_le hc hfit _
  have hxp : x ≤ p := by
    rw [hp, le_div_iff₀ hD', hval]
    have := g.so_cp_mono D hg him hpos
    calc x * D ≤ cp D g t i := hxb
      _ ≤ _ := by exact_mod_cast this
  have hE : ∀ r, (Epen D z r : ℝ) / D ≤ (1 - p) ^ r := fun r => by
    rw [div_le_iff₀ hD']
    have := Epen_le hD hzD r
    rw [hp]; linarith [this]
  have hbasic : (Epen D z (g.n - t) : ℝ) / D ≤ (1 - max (y (Fin.last d)) x) ^ (g.n - t) := by
    have hmaxp : max (y (Fin.last d)) x ≤ p := max_le hyl hxp
    calc (Epen D z (g.n - t) : ℝ) / D ≤ (1 - p) ^ (g.n - t) := hE _
      _ ≤ (1 - max (y (Fin.last d)) x) ^ (g.n - t) :=
        pow_le_pow_left₀ (by linarith) (by linarith) _
  split_ifs with hw hC
  · simp only [Int.cast_zero, zero_mul, zero_div, add_zero]
    exact hbasic
  · have him' : i < im d c := lt_of_le_of_ne him (fun h => hC (Or.inr h))
    have hxy : x < y (Fin.last d) := fit_gt_of_lt_pos hg hc hfit hi1 him' hxb
    rw [max_eq_left hxy.le]
    have htan := tangent_le_one_sub_pow (hy.2 (Fin.last d)).1 (hy.2 (Fin.last d)).2 hp0 hp1
      (g.n - t)
    have h1 := hE (g.n - t)
    have h2 := hE (g.n - t - 1)
    have hδ : 0 ≤ p - y (Fin.last d) := by linarith
    have h3 : ((g.n - t : ℕ) : ℝ) * (Epen D z (g.n - t - 1) : ℝ) * (p - y (Fin.last d)) / D ≤
        ((g.n - t : ℕ) : ℝ) * (1 - p) ^ (g.n - t - 1) * (p - y (Fin.last d)) := by
      have : ((g.n - t : ℕ) : ℝ) * (Epen D z (g.n - t - 1) : ℝ) * (p - y (Fin.last d)) / D =
          ((g.n - t : ℕ) : ℝ) * ((Epen D z (g.n - t - 1) : ℝ) / D) * (p - y (Fin.last d)) := by
        ring
      rw [this]
      apply mul_le_mul_of_nonneg_right _ hδ
      exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    push_cast
    linarith
  · rw [add_zero]
    exact hbasic

/-- 8.2 (a): the stop cost on the cell `i ≤ im`. -/
theorem relaxStop_cell (hg : ok D g = true) (htn : t ≤ g.n) (hc : RecOK D g t c)
    (hfit : Fits D g t c y) {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ im d c) {x : ℝ}
    (hxa : (cp D g t (i - 1) : ℝ) < x * D) (hxb : x * D ≤ cp D g t i) :
    relaxStop g.n t y x = ((1 + below d c i : ℕ) : ℝ) + ((g.n - t : ℕ) : ℝ) * x +
      ((Finset.univ.filter fun l => (c l).pos = i ∧ y l < x).card : ℝ) := by
  have hiL : i ≤ g.L t := him.trans (hc.pos_le _)
  unfold relaxStop
  have hsplit : (Finset.univ.filter fun l => y l < x) =
      (Finset.univ.filter fun l => (c l).pos < i) ∪
        (Finset.univ.filter fun l => (c l).pos = i ∧ y l < x) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h
      rcases lt_trichotomy (c l).pos i with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h⟩
      · exact absurd h (not_lt.mpr (fit_gt_of_lt_pos hg hc hfit hi1 h1 hxb).le)
    · rintro (h | h)
      · exact fit_lt_of_pos_lt hg hfit hiL h hxa
      · exact h.2
  have hdisj : Disjoint (Finset.univ.filter fun l => (c l).pos < i)
      (Finset.univ.filter fun l => (c l).pos = i ∧ y l < x) := by
    rw [Finset.disjoint_filter]
    intro l _ h1 h2
    omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  have hbelow : (Finset.univ.filter fun l : Fin (d + 1) => (c l).pos < i).card = below d c i := by
    unfold below
    rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
    have hlast : ¬ (c (Fin.last d)).pos < i := by unfold im at him; omega
    simp only [hlast, ite_false, add_zero, Nat.lt_iff_add_one_le]
  rw [hbelow]
  push_cast
  rw [Nat.cast_sub htn]
  ring

/-- 8.2 (f): the continuation on the cell `i ≤ im`. -/
theorem cont_ge_cell (hg : ok D g = true) (ht1 : 1 ≤ t) (htn : t < g.n) (hy : IsMemory y)
    (hc : RecOK D g t c) (hfit : Fits D g t c y) {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ im d c)
    {x : ℝ} (hxa : (cp D g t (i - 1) : ℝ) < x * D) (hxb : x * D ≤ cp D g t i)
    (uh : ℕ → (Fin (d + 1) → ℕ) → ℕ) (sg : ℕ → (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) :
    ((betaC D g d (uh (t + 1)) (sg (t + 1)) t c i : ℝ) -
          (sigmaC g d (sg (t + 1)) t c i : ℝ) * (x * D)) / (D : ℝ) ^ 2 +
        ∑ l, (if 0 < (c l).w then
          (coefC D g d (sg (t + 1)) t c i l : ℝ) * (((c l).val : ℝ) / D - y l) / D else 0) ≤
      dropPenalty g.n t y x + uSO D g d uh sg (t + 1) (ins y x) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast g.so_D_pos D hg
  have h1 := drop_ge_cell hg hy hc hfit (sg (t + 1)) hi1 him hxa hxb
  have h2 := cont_succ_ge_cell hg ht1 htn hy hc hfit hi1 him hxa hxb uh sg
  rw [Fin.sum_univ_castSucc]
  unfold betaC sigmaC
  simp only []
  push_cast
  have key : ((D : ℝ) * ((Epen D (pt D g (c (Fin.last d)).gi) (g.n - t) : ℝ) +
        (uh (t + 1) (Hc g d t c i) : ℝ)) +
        (sg (t + 1) (Hc g d t c i) (belowF d c i) : ℝ) *
          (pt D g (g.glob (t + 1) (g.nxt t i)) : ℝ) +
        ∑ l : Fin d, (sg (t + 1) (Hc g d t c i) (slot d c i l) : ℝ) *
          (ev D g d t c l.castSucc : ℝ) -
        (sg (t + 1) (Hc g d t c i) (belowF d c i) : ℝ) * (x * D)) / (D : ℝ) ^ 2 =
      (Epen D (pt D g (c (Fin.last d)).gi) (g.n - t) : ℝ) / D +
        ((D : ℝ) * (uh (t + 1) (Hc g d t c i) : ℝ) +
          (sg (t + 1) (Hc g d t c i) (belowF d c i) : ℝ) *
            (pt D g (g.glob (t + 1) (g.nxt t i)) : ℝ) -
          (sg (t + 1) (Hc g d t c i) (belowF d c i) : ℝ) * (x * D) +
          ∑ l : Fin d, (sg (t + 1) (Hc g d t c i) (slot d c i l) : ℝ) *
            (ev D g d t c l.castSucc : ℝ)) / (D : ℝ) ^ 2 := by
    field_simp; ring
  rw [key]
  linarith

/-! ## The tail (8.3) -/

/-- 8.3: above `p_im` every coordinate is below `x`. -/
theorem relaxStop_tail (hg : ok D g = true) (htn : t ≤ g.n) (hc : RecOK D g t c)
    (hfit : Fits D g t c y) {x : ℝ} (hx : (cp D g t (im d c) : ℝ) < x * D) :
    relaxStop g.n t y x = ((d + 2 : ℕ) : ℝ) + ((g.n - t : ℕ) : ℝ) * x := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast g.so_D_pos D hg
  have hall : ∀ l, y l < x := fun l => by
    have h1 : y l * D ≤ cp D g t (c l).pos := (hfit l).2
    have h2 := g.so_cp_mono D hg (pos_le_im hc l) (hc.pos_le (Fin.last d))
    have h3 : (cp D g t (c l).pos : ℝ) ≤ cp D g t (im d c) := by exact_mod_cast h2
    exact lt_of_mul_lt_mul_right (by linarith) hD'.le
  unfold relaxStop
  rw [Finset.filter_true_of_mem (fun l _ => hall l), Finset.card_univ, Fintype.card_fin]
  push_cast
  rw [Nat.cast_sub htn]
  ring

/-- 8.3: above `p_im`, the last record not forgotten, the continuation is
`(1 - x) ^ r + U / D ^ 2 + sum over l of slc_l delta_l / D`. -/
theorem cont_tail (hg : ok D g = true) (ht1 : 1 ≤ t) (htn : t < g.n) (hy : IsMemory y)
    (hc : RecOK D g t c) (hfit : Fits D g t c y) (htf : (c (Fin.last d)).forg = false)
    (uh : ℕ → (Fin (d + 1) → ℕ) → ℕ) (sg : ℕ → (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) {x : ℝ}
    (hx : (cp D g t (im d c) : ℝ) < x * D) :
    dropPenalty g.n t y x + uSO D g d uh sg (t + 1) (ins y x) =
      (1 - x) ^ (g.n - t) + (UT D g d (uh (t + 1)) (sg (t + 1)) t c : ℝ) / (D : ℝ) ^ 2 +
        ∑ l, (sg (t + 1) (fun l => (c l).map) l : ℝ) * (((c l).val : ℝ) / D - y l) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast g.so_D_pos D hg
  have hylast : y (Fin.last d) ≤ x := by
    have h1 : y (Fin.last d) * D ≤ (c (Fin.last d)).val := fit_mul_le hc hfit _
    rw [hc.val_eq] at h1
    exact le_of_lt (lt_of_mul_lt_mul_right (by unfold im at hx; linarith) hD'.le)
  have hforg : ∀ l, (c l).forg = false := fun l => by
    by_contra h
    simp only [Bool.not_eq_false] at h
    rw [forg_last_of_forg hc h] at htf
    exact Bool.noConfusion htf
  unfold dropPenalty
  rw [drop_of_ge y hylast, ins_of_ge hy hylast]
  have hK : ∀ l, ceilR D g (t + 1) (y l) = (c l).map := fun l => fit_ceilR hg ht1 htn hy hc hfit l
  unfold uSO
  simp only [hK]
  unfold UT ev
  simp only [hforg, Bool.false_eq_true, ite_false]
  push_cast
  have e1 : ((D : ℝ) * (uh (t + 1) fun l => (c l).map) +
      ∑ l, (sg (t + 1) (fun l => (c l).map) l : ℝ) *
        ((pt D g (g.glob (t + 1) (c l).map) : ℝ) - (c l).val)) / (D : ℝ) ^ 2 =
      ((uh (t + 1) fun l => (c l).map) : ℝ) / D +
        ∑ l, (sg (t + 1) (fun l => (c l).map) l : ℝ) *
          ((pt D g (g.glob (t + 1) (c l).map) : ℝ) - (c l).val) / (D : ℝ) ^ 2 := by
    rw [add_div, Finset.sum_div]; congr 1; field_simp
  rw [e1, add_assoc, add_assoc, ← Finset.sum_add_distrib]
  congr 2
  apply Finset.sum_congr rfl
  intro l _
  field_simp
  ring

end CellBounds

end Robbins.Cert.SO
