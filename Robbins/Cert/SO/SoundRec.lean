import Robbins.Cert.SO.SoundGrid
import Robbins.Relax.Defs

/-!
# Records and record lists of the second-order soundness (8.1, 8.7)

Sections 8.1 and 8.7 of the specification (Robbins/Cert/SO/Spec.lean).

* `uSO D g d uh sg t y`: the function `u_t` of the tables `uh`, `sg`;
* `InCell D g t i v`: the value `v` lies in the cell `i` of `P_t`, `(p_{i-1}, p_i]`, closed at `0`
  for `i = 1`;
* `RecOK D g t c`: the facts of 8.1 on a record list `c` that the bounds of 8.2 to 8.6 use (the cell
  of each record, its value `p_pos`, `map = nxt_pos`, `forg` exactly at the cell `L`, a positive
  width is the width of the cell);
* `Fits D g t c y`: every coordinate of `y` lies in the cell of its record;
* `choiceOf D g t v`: the least new point or `J` at or above `v`, the choice of section 6 that a
  memory selects (8.7).

The record lists of section 6 satisfy `RecOK` (`recList_ok`); a memory `y` fits the record list of
the state `ceil_t (y)` and the choice `choiceOf` at its coordinates (`fits_choice`).
-/

namespace Robbins.Cert

/-- A nondecreasing list read at two indices. -/
theorem nondec_getD {p : ℕ} {l : List ℕ} (h : nondec p l = true) {i j : ℕ} (hij : i ≤ j)
    (hj : j < l.length) : l.getD i 0 ≤ l.getD j 0 := by
  have hall : ∀ (l : List ℕ) (a : ℕ), nondec a l = true → ∀ b ∈ l, a ≤ b := by
    intro l
    induction l with
    | nil => intro a _ b hb; simp at hb
    | cons x xs ih =>
      intro a h b hb
      simp only [nondec, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact h.1
      · exact le_trans h.1 (ih x h.2 b hb)
  induction l generalizing p i j with
  | nil => exact absurd hj (Nat.not_lt_zero _)
  | cons x xs ih =>
    simp only [nondec, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.length_cons] at hj
    rcases i with _ | i
    · rcases j with _ | j
      · exact le_rfl
      · simp only [List.getD_cons_zero, List.getD_cons_succ]
        rw [List.getD_eq_getElem (l := xs) (d := 0) (n := j) (by omega)]
        exact hall xs x h.2 _ (List.getElem_mem (by omega))
    · rcases j with _ | j
      · omega
      · simp only [List.getD_cons_succ]
        exact ih h.2 (by omega) (by omega)

namespace Grid

variable (g : Grid)

/-! ## The cells of `P_t` as indices (no denominator) -/

theorem cellPts_idxOf {t j : ℕ} (hj : j ∈ g.cellPts t) :
    (g.cellPts t).idxOf j < g.L t ∧ (g.cellPts t).getD ((g.cellPts t).idxOf j) 0 = j := by
  have hL : g.L t = (g.cellPts t).length := rfl
  have h_lt_len : (g.cellPts t).idxOf j < (g.cellPts t).length :=
    List.idxOf_lt_length_of_mem hj
  have h_lt : (g.cellPts t).idxOf j < g.L t := by
    rw [hL]
    exact h_lt_len
  have h_get : (g.cellPts t).getD ((g.cellPts t).idxOf j) 0 = j := by
    rw [List.getD_eq_getElem _ _ h_lt_len, List.getElem_idxOf h_lt_len]
  exact And.intro h_lt h_get

theorem cellPts_getD_mem {t i : ℕ} (hi : i < g.L t) : (g.cellPts t).getD i 0 ∈ g.cellPts t := by
  unfold Grid.L at hi
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem cellPts_getD_lt {t i i' : ℕ} (h : i < i') (hi' : i' < g.L t) :
    (g.cellPts t).getD i 0 < (g.cellPts t).getD i' 0 := by
  unfold Grid.L Grid.cellPts at *
  exact filterRange_getD_lt_getD (g.J + 1) (fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j) h hi'

theorem idxOf_getD {t i : ℕ} (hi : i < g.L t) :
    (g.cellPts t).idxOf ((g.cellPts t).getD i 0) = i := by
  have hL : g.L t = (g.cellPts t).length := rfl
  have hi' : i < (g.cellPts t).length := by rwa [← hL]
  have hNodup : (g.cellPts t).Nodup := by
    unfold cellPts
    have hSorted : (List.range (g.J + 1)).SortedLT := List.sortedLT_range _
    have hNodupRange : (List.range (g.J + 1)).Nodup := hSorted.nodup
    exact hNodupRange.filter _
  have hGetD : (g.cellPts t).getD i 0 = (g.cellPts t)[i] := by
    rw [List.getD_eq_getElem _ _ hi']
  rw [hGetD]
  let fi : Fin (g.cellPts t).length := ⟨i, hi'⟩
  have hGetIdxOf := List.get_idxOf hNodup fi
  rw [List.get_eq_getElem] at hGetIdxOf
  simpa using hGetIdxOf

theorem idxOf_lt_idxOf {t j j' : ℕ} (hj : j ∈ g.cellPts t) (hj' : j' ∈ g.cellPts t) (h : j < j') :
    (g.cellPts t).idxOf j < (g.cellPts t).idxOf j' := by
  by_contra! hle
  set i := (g.cellPts t).idxOf j with hi
  set i' := (g.cellPts t).idxOf j' with hi'
  have hi_lt_L : i < g.L t := (g.cellPts_idxOf hj).1
  have hi'_lt_L : i' < g.L t := (g.cellPts_idxOf hj').1
  have h_get_i : (g.cellPts t).getD i 0 = j := (g.cellPts_idxOf hj).2
  have h_get_i' : (g.cellPts t).getD i' 0 = j' := (g.cellPts_idxOf hj').2
  rcases Nat.eq_or_lt_of_le hle with (heq | hlt)
  · rw [heq] at h_get_i'
    rw [h_get_i] at h_get_i'
    omega
  · have h_lt_val : (g.cellPts t).getD i' 0 < (g.cellPts t).getD i 0 :=
      g.cellPts_getD_lt hlt hi_lt_L
    rw [h_get_i', h_get_i] at h_lt_val
    omega

theorem idxOf_le_idxOf {t j j' : ℕ} (hj : j ∈ g.cellPts t) (hj' : j' ∈ g.cellPts t) (h : j ≤ j') :
    (g.cellPts t).idxOf j ≤ (g.cellPts t).idxOf j' := by
  rcases h.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (g.idxOf_lt_idxOf hj hj' hlt).le

/-- The point `1` (global index `J`) is the last cell. -/
theorem pos_cnt (t : ℕ) : g.pos t (g.cnt t) = g.L t := by
  have hglob : g.glob t (g.cnt t) = g.J := g.glob_of_ge (le_refl (g.cnt t))
  have hlast : (g.cellPts t).getD (g.L t - 1) 0 = g.J := g.cellPts_last t
  have hone_le : 1 ≤ g.L t := g.one_le_L t
  have h_lt : g.L t - 1 < g.L t := by omega
  have hidx : (g.cellPts t).idxOf ((g.cellPts t).getD (g.L t - 1) 0) = g.L t - 1 :=
    g.idxOf_getD h_lt
  calc
    g.pos t (g.cnt t) = (g.cellPts t).idxOf (g.glob t (g.cnt t)) + 1 := rfl
    _ = (g.cellPts t).idxOf g.J + 1 := by rw [hglob]
    _ = (g.cellPts t).idxOf ((g.cellPts t).getD (g.L t - 1) 0) + 1 := by rw [hlast]
    _ = (g.L t - 1) + 1 := by rw [hidx]
    _ = g.L t := by omega

theorem pos_lt_L {t k : ℕ} (hk : k < g.cnt t) : g.pos t k < g.L t := by
  have hpos_le_L := (g.pos_spec (le_of_lt hk)).2.1
  by_contra! H
  have h_eq : g.pos t k = g.L t := by omega
  have hpos_spec := g.pos_spec (le_of_lt hk)
  have h_glob_eq_J : g.glob t k = g.J := by
    calc
      g.glob t k = (g.cellPts t).getD (g.pos t k - 1) 0 := by
        rw [hpos_spec.2.2.symm]
      _ = (g.cellPts t).getD (g.L t - 1) 0 := by rw [h_eq]
      _ = g.J := g.cellPts_last t
  have h_glob_lt_J := g.glob_lt_J hk
  omega

/-- The first point of `G_t` is the first endpoint of `P_t` (`s_t ≤ s_{t+1}`). -/
theorem pos_zero {t : ℕ} (hs : (g.wt t).s ≤ (g.wt (t + 1)).s) (hc : 1 ≤ g.cnt t) :
    g.pos t 0 = 1 := by
  have hcnt0 : 0 < g.cnt t := by omega
  have hglob0 : g.glob t 0 = (g.wt t).s := by
    unfold glob
    simp [hcnt0]
  have hglob_mem : g.glob t 0 ∈ g.cellPts t :=
    Robbins.Cert.Grid.glob_mem_cellPts g (by omega)
  have hLpos : 0 < g.L t := by
    have hlen : 0 < (g.cellPts t).length :=
      List.length_pos_of_mem hglob_mem
    unfold L
    omega
  by_contra! hpos
  unfold pos at hpos
  have hidx_ne_zero : (g.cellPts t).idxOf (g.glob t 0) ≠ 0 := by omega
  have hcell_idx := Robbins.Cert.Grid.cellPts_idxOf g hglob_mem
  have hidx_lt_L : (g.cellPts t).idxOf (g.glob t 0) < g.L t := hcell_idx.1
  have hgetD_eq : (g.cellPts t).getD ((g.cellPts t).idxOf (g.glob t 0)) 0 = g.glob t 0 := hcell_idx.2
  have hidx_pos : 0 < (g.cellPts t).idxOf (g.glob t 0) :=
    Nat.pos_of_ne_zero hidx_ne_zero
  have hlt : (g.cellPts t).getD 0 0 < (g.cellPts t).getD ((g.cellPts t).idxOf (g.glob t 0)) 0 :=
    Robbins.Cert.Grid.cellPts_getD_lt g hidx_pos hidx_lt_L
  have hmem_getD0 : (g.cellPts t).getD 0 0 ∈ g.cellPts t :=
    Robbins.Cert.Grid.cellPts_getD_mem g (by omega)
  have hmem_ge : ∀ j, j ∈ g.cellPts t → (g.wt t).s ≤ j := by
    intro j hj
    rcases (Robbins.Cert.Grid.mem_cellPts g).mp hj with ⟨hj_le_J, hj_cond⟩
    rcases hj_cond with (rfl | hinWin_t | hinWin_t1)
    · have h := s_add_cnt_le g t
      omega
    · have hinWin_t' := by simpa [inWin, Bool.and_eq_true] using hinWin_t
      omega
    · have hinWin_t1' := by simpa [inWin, Bool.and_eq_true] using hinWin_t1
      omega
  have hge_s : (g.wt t).s ≤ (g.cellPts t).getD 0 0 := hmem_ge _ hmem_getD0
  have hgetD_eq_st : (g.cellPts t).getD ((g.cellPts t).idxOf (g.glob t 0)) 0 = (g.wt t).s := by
    rw [hgetD_eq, hglob0]
  rw [hgetD_eq_st] at hlt
  omega

/-- Consecutive points of `G_t` are consecutive endpoints of `P_t` (8.1 (b)). -/
theorem pos_pred {t k : ℕ} (hk1 : 1 ≤ k) (hk : k < g.cnt t) : g.pos t (k - 1) = g.pos t k - 1 := by
  have hk' : k - 1 < g.cnt t := by omega
  have hg1 : g.glob t (k - 1) = (g.wt t).s + (k - 1) := by
    unfold Grid.glob
    rw [ite_eq_left hk']
  have hg2 : g.glob t k = (g.wt t).s + k := by
    unfold Grid.glob
    rw [ite_eq_left hk]
  have hm1 := g.glob_mem_cellPts (t := t) (k := k - 1) hk'.le
  have hm2 := g.glob_mem_cellPts (t := t) (k := k) hk.le
  have hlt := g.idxOf_lt_idxOf hm1 hm2 (by rw [hg1, hg2]; omega)
  obtain ⟨hi1L, he1⟩ := g.cellPts_idxOf hm1
  obtain ⟨hi2L, he2⟩ := g.cellPts_idxOf hm2
  unfold Grid.pos
  by_contra hne
  have h2 : (g.cellPts t).idxOf (g.glob t (k - 1)) < (g.cellPts t).idxOf (g.glob t k) - 1 := by
    omega
  have e1 := g.cellPts_getD_lt h2 (by omega : (g.cellPts t).idxOf (g.glob t k) - 1 < g.L t)
  have e2 := g.cellPts_getD_lt (by omega : (g.cellPts t).idxOf (g.glob t k) - 1 <
    (g.cellPts t).idxOf (g.glob t k)) hi2L
  rw [he1] at e1
  rw [he2] at e2
  omega

theorem nxt_pos {t k : ℕ} (hk : k ≤ g.cnt t) : g.nxt t (g.pos t k) = g.mapL t k := by
  unfold Grid.nxt Grid.mapL
  have h := g.pos_spec hk
  rcases h with ⟨_, _, h3⟩
  rw [h3]

/-- The first cell maps to the first point of `G_{t+1}`. -/
theorem nxt_one {t : ℕ} (hc : 1 ≤ g.cnt (t + 1)) : g.nxt t 1 = 0 := by
  -- expand definitions
  dsimp [Grid.nxt, Grid.ceilG, ceilLocal]
  -- hcnt_pos : 0 < (g.wt (t + 1)).cnt
  have hcnt_pos : 0 < (g.wt (t + 1)).cnt :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one hc
  have hcnt_ne_zero : (g.wt (t + 1)).cnt ≠ 0 := by omega
  have hpos0 : 0 ≤ g.cnt (t + 1) := by omega
  -- s1 = (g.wt (t + 1)).s is in cellPts t
  have hs1_mem : g.glob (t + 1) 0 ∈ g.cellPts t :=
    glob_succ_mem_cellPts g hpos0
  have hs1_eq : g.glob (t + 1) 0 = (g.wt (t + 1)).s := by
    unfold Grid.glob Grid.cnt
    simp [hcnt_pos]
  have hs1_mem' : (g.wt (t + 1)).s ∈ g.cellPts t := by
    rw [← hs1_eq]
    exact hs1_mem
  have hidx := cellPts_idxOf g hs1_mem'
  have hidx_lt : (g.cellPts t).idxOf ((g.wt (t + 1)).s) < g.L t := hidx.1
  have hidx_get : (g.cellPts t).getD ((g.cellPts t).idxOf ((g.wt (t + 1)).s)) 0 = (g.wt (t + 1)).s := hidx.2
  have hsum := s_add_cnt_le g (t + 1)
  have hs1_lt_J : (g.wt (t + 1)).s < g.J := by
    dsimp [Grid.cnt] at hsum
    omega
  -- prove (g.cellPts t).getD 0 0 ≤ (g.wt (t + 1)).s
  have h_get0_le_s1 : (g.cellPts t).getD 0 0 ≤ (g.wt (t + 1)).s := by
    by_cases hidx_zero : (g.cellPts t).idxOf ((g.wt (t + 1)).s) = 0
    · -- idxOf = 0, so getD 0 0 = s1
      have h_eq : (g.cellPts t).getD 0 0 = (g.wt (t + 1)).s := by
        calc
          (g.cellPts t).getD 0 0 = (g.cellPts t).getD ((g.cellPts t).idxOf ((g.wt (t + 1)).s)) 0 := by rw [← hidx_zero]
          _ = (g.wt (t + 1)).s := hidx_get
      exact h_eq.le
    · -- idxOf > 0, so getD 0 0 < getD (idxOf s1) 0 = s1
      have hpos_idx : 0 < (g.cellPts t).idxOf ((g.wt (t + 1)).s) := by omega
      have h_get_lt : (g.cellPts t).getD 0 0 < (g.cellPts t).getD ((g.cellPts t).idxOf ((g.wt (t + 1)).s)) 0 :=
        cellPts_getD_lt g hpos_idx hidx_lt
      rw [hidx_get] at h_get_lt
      exact Nat.le_of_lt h_get_lt
  -- getD 0 0 ≠ g.J because getD 0 0 ≤ s1 < J
  have hJ_ne : (g.cellPts t).getD 0 0 ≠ g.J := by
    intro h_eq
    rw [h_eq] at h_get0_le_s1
    omega
  -- Now the first || condition is false, so the if condition (|| = true) is false
  have h_or_false : ((g.cellPts t).getD 0 0 == g.J || (g.wt (t + 1)).cnt == 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    rcases ((Bool.or_eq_true (a := (g.cellPts t).getD 0 0 == g.J) (b := (g.wt (t + 1)).cnt == 0)).mp h) with (hJ | hcnt)
    · exact hJ_ne (by simpa using hJ)
    · exact hcnt_ne_zero (by simpa using hcnt)
  have h_cond_false : ¬ (((g.cellPts t).getD 0 0 == g.J || (g.wt (t + 1)).cnt == 0) = true) := by
    intro h
    rw [h_or_false] at h
    exact Bool.false_ne_true h
  rw [if_neg h_cond_false]
  -- goal: (if (g.cellPts t).getD 0 0 < (g.wt (t + 1)).s then 0 else ...) = 0
  by_cases hlt : (g.cellPts t).getD 0 0 < (g.wt (t + 1)).s
  · rw [if_pos hlt]
  · -- not (getD 0 0 < s1), so s1 ≤ getD 0 0
    -- combined with getD 0 0 ≤ s1, we get equality
    have heq : (g.cellPts t).getD 0 0 = (g.wt (t + 1)).s := by omega
    rw [if_neg hlt]
    -- goal: (if (g.cellPts t).getD 0 0 < (g.wt (t + 1)).s + (g.wt (t + 1)).cnt then (g.cellPts t).getD 0 0 - (g.wt (t + 1)).s else (g.wt (t + 1)).cnt) = 0
    by_cases hlt2 : (g.cellPts t).getD 0 0 < (g.wt (t + 1)).s + (g.wt (t + 1)).cnt
    · -- getD 0 0 < s1 + cnt, so we go to the subtraction branch: getD 0 0 - s1 = 0
      rw [if_pos hlt2, heq, Nat.sub_self]
    · -- ¬ getD 0 0 < s1 + cnt, so s1 + cnt ≤ getD 0 0 = s1, so cnt = 0, contradiction
      rw [if_neg hlt2]
      have : (g.wt (t + 1)).cnt = 0 := by omega
      exfalso; exact hcnt_ne_zero this

/-! ## New points -/

theorem mem_newPts {t j : ℕ} :
    j ∈ SO.newPts g t ↔ j < g.J ∧ g.inWin (t + 1) j = true ∧ (g.wt t).s + (g.wt t).cnt ≤ j := by
  unfold SO.newPts
  simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]

theorem newPts_mem_cellPts {t j : ℕ} (hj : j ∈ SO.newPts g t) : j ∈ g.cellPts t := by
  rcases ((mem_newPts g).mp hj) with ⟨hjJ, hinWin, hineq⟩
  apply (mem_cellPts g).mpr
  exact ⟨Nat.le_of_lt hjJ, Or.inr (Or.inr hinWin)⟩

theorem newPts_idx_lt {t j : ℕ} (hj : j ∈ SO.newPts g t) : (g.cellPts t).idxOf j + 1 < g.L t := by
  have hj_cell : j ∈ g.cellPts t := newPts_mem_cellPts g hj
  have h_idx_lt_L : (g.cellPts t).idxOf j < g.L t := (cellPts_idxOf g hj_cell).1
  have h_getD : (g.cellPts t).getD ((g.cellPts t).idxOf j) 0 = j := (cellPts_idxOf g hj_cell).2
  have h_j_lt_J : j < g.J := ((mem_newPts g).mp hj).1
  have h_last : (g.cellPts t).getD (g.L t - 1) 0 = g.J := cellPts_last g t
  by_contra! h_ge
  have h_eq : (g.cellPts t).idxOf j = g.L t - 1 := by omega
  have h_j_eq_J : j = g.J := by
    calc
      j = (g.cellPts t).getD ((g.cellPts t).idxOf j) 0 := by rw [h_getD]
      _ = (g.cellPts t).getD (g.L t - 1) 0 := by rw [h_eq]
      _ = g.J := h_last
  omega

theorem nxt_newPt {t j : ℕ} (hj : j ∈ SO.newPts g t) :
    g.nxt t ((g.cellPts t).idxOf j + 1) = j - (g.wt (t + 1)).s := by
  have hmem := List.mem_filter.mp hj
  have hJ : j < g.J := List.mem_range.mp hmem.1
  have h_and_true : (g.inWin (t + 1) j && decide ((g.wt t).s + (g.wt t).cnt ≤ j)) = true := hmem.2
  rw [Bool.and_eq_true] at h_and_true
  rcases h_and_true with ⟨h_inWin, h_le⟩
  have h_inWin_val : g.inWin (t + 1) j = true := h_inWin
  simp [Grid.inWin] at h_inWin_val
  rcases h_inWin_val with ⟨h_s_le_j, h_j_lt_s_cnt⟩
  have hj_cell : j ∈ g.cellPts t := by
    dsimp [Grid.cellPts]
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_range.mpr; omega
    · simp [h_inWin]
  have h_getElem? : (g.cellPts t)[List.idxOf j (g.cellPts t)]? = some j := List.getElem?_idxOf hj_cell
  have h_getD : (g.cellPts t).getD ((g.cellPts t).idxOf j) 0 = j := by
    rw [List.getD, h_getElem?]
    simp
  calc
    g.nxt t ((g.cellPts t).idxOf j + 1)
        = g.ceilG (t + 1) ((g.cellPts t).getD (((g.cellPts t).idxOf j + 1) - 1) 0) := rfl
    _ = g.ceilG (t + 1) ((g.cellPts t).getD ((g.cellPts t).idxOf j) 0) := by
      rw [show ((g.cellPts t).idxOf j + 1) - 1 = (g.cellPts t).idxOf j by omega]
    _ = g.ceilG (t + 1) j := by rw [h_getD]
    _ = ceilLocal g.J (g.wt (t + 1)) j := rfl
    _ = j - (g.wt (t + 1)).s := by
      rw [ceilLocal]
      have hcnt_ne_zero : (g.wt (t + 1)).cnt ≠ 0 := by omega
      have h_not_eq_J : j ≠ g.J := by omega
      have h_not_lt_s : ¬ j < (g.wt (t + 1)).s := by omega
      simp [h_not_eq_J, hcnt_ne_zero, h_not_lt_s, h_j_lt_s_cnt]

theorem glob_lt_newPt {t k j : ℕ} (hk : k < g.cnt t) (hj : j ∈ SO.newPts g t) : g.glob t k < j := by
  rcases (mem_newPts g).mp hj with ⟨hjJ, hwin, hle⟩
  have hglob : g.glob t k = (g.wt t).s + k := by
    unfold glob
    simp [hk]
  rw [hglob]
  have hsum : (g.wt t).s + k < (g.wt t).s + (g.wt t).cnt :=
    Nat.add_lt_add_left hk (g.wt t).s
  exact Nat.lt_of_lt_of_le hsum hle

/-! ## Data conditions -/

variable (D : ℕ)

theorem so_ok_cnt (hg : SO.ok D g = true) {t : ℕ} (ht1 : 1 ≤ t) (htn : t ≤ g.n) : 1 ≤ g.cnt t := by
  have hall : ∀ x, x < g.n → 1 ≤ g.cnt (x + 1) := by
    unfold SO.ok at hg
    simp [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hg
    exact hg.2
  have hlt : t - 1 < g.n := by omega
  have h := hall (t - 1) hlt
  have : (t - 1) + 1 = t := by omega
  rw [this] at h
  exact h

theorem so_s_le_s (hg : SO.ok D g = true) {t : ℕ} (ht1 : 1 ≤ t) (htn : t < g.n) :
    (g.wt t).s ≤ (g.wt (t + 1)).s := by
  unfold SO.ok at hg
  have h_nondec : nondec 0 g.start = true := by
    have h := hg
    rw [Bool.and_eq_true] at h
    rcases h with ⟨h_rest, h_D⟩
    rw [Bool.and_eq_true] at h_rest
    rcases h_rest with ⟨h_rest2, h_C⟩
    exact h_C
  have h_len_eq : g.start.length = g.n := by
    have h := hg
    rw [Bool.and_eq_true] at h
    rcases h with ⟨h_rest, h_D⟩
    rw [Bool.and_eq_true] at h_rest
    rcases h_rest with ⟨h_rest2, h_C⟩
    rw [Bool.and_eq_true] at h_rest2
    rcases h_rest2 with ⟨h_rest3, h_B⟩
    simpa using h_B
  have h_le : t - 1 ≤ t := by omega
  have h_lt : t < g.start.length := by
    rw [h_len_eq]
    exact htn
  have h_getD : g.start.getD (t - 1) 0 ≤ g.start.getD t 0 :=
    nondec_getD h_nondec h_le h_lt
  unfold Grid.wt Grid.win
  simp only
  exact min_le_min_right _ h_getD

/-- Property (W) (8.1 (a), Lemma 4.1 of the paper): for `1 ≤ t < n`, every
point of `G_{t+1}` (a global index `j` in the window of time `t + 1`) whose value is at most
`top_t`, the largest point of `G_t` below `1`, is a point of `G_t`. -/
theorem so_propW (hg : SO.ok D g = true) {t : ℕ} (ht1 : 1 ≤ t) (htn : t < g.n) {j : ℕ}
    (hj : g.inWin (t + 1) j = true)
    (hle : SO.pt D g j ≤ SO.pt D g (g.glob t (g.cnt t - 1))) : g.inWin t j = true := by
  have hcnt : 1 ≤ g.cnt t := g.so_ok_cnt D hg ht1 htn.le
  have hs := g.so_s_le_s D hg ht1 htn
  have hJ := g.s_add_cnt_le (t + 1)
  unfold Grid.inWin at hj ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hj ⊢
  have hglob : g.glob t (g.cnt t - 1) = (g.wt t).s + (g.cnt t - 1) := by
    unfold Grid.glob; rw [ite_eq_left (by omega)]
  refine ⟨by omega, ?_⟩
  by_contra hlt
  have : g.glob t (g.cnt t - 1) < j := by rw [hglob]; unfold Grid.cnt at *; omega
  have := g.so_pt_lt_pt D hg this (by unfold Grid.cnt Grid.J at *; omega)
  omega

end Grid

namespace SO

/-- The function `u_t` of the tables `uh`, `sg`:
`u_t (y) = uh_t (k) / D + sum over l of (sg_t (k)_l / D) (G_l - y_l)`, `k = ceil_t (y)`,
`G_l = pt (glob t (k_l)) / D`. -/
noncomputable def uSO (D : ℕ) (g : Grid) (d : ℕ) (uh : ℕ → (Fin (d + 1) → ℕ) → ℕ)
    (sg : ℕ → (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) (t : ℕ) (y : Fin (d + 1) → ℝ) : ℝ :=
  let k : Fin (d + 1) → ℕ := fun l => ceilR D g t (y l)
  (uh t k : ℝ) / D + ∑ l, (sg t k l : ℝ) / D * ((pt D g (g.glob t (k l)) : ℝ) / D - y l)

/-- The value `v` lies in the cell `i` of `P_t`: `(p_{i-1}, p_i]`, `[0, p_1]` for `i = 1`. -/
def InCell (D : ℕ) (g : Grid) (t i : ℕ) (v : ℝ) : Prop :=
  (i = 1 ∨ (cp D g t (i - 1) : ℝ) < v * D) ∧ v * D ≤ cp D g t i

/-- The facts of 8.1 on a record list `c` of time `t`. -/
structure RecOK (D : ℕ) (g : Grid) (t : ℕ) {m : ℕ} (c : Fin m → Rec) : Prop where
  /-- The cells are `1, ..., L`. -/
  pos_pos : ∀ l, 1 ≤ (c l).pos
  /-- The cells are `1, ..., L`. -/
  pos_le : ∀ l, (c l).pos ≤ g.L t
  /-- The cells are nondecreasing along the list. -/
  pos_mono : Monotone fun l => (c l).pos
  /-- The value is the right endpoint of the cell. -/
  val_eq : ∀ l, (c l).val = cp D g t (c l).pos
  /-- The value is the point of the global index. -/
  gi_eq : ∀ l, pt D g (c l).gi = (c l).val
  /-- `map = nxt_pos`. -/
  map_eq : ∀ l, (c l).map = g.nxt t (c l).pos
  /-- The forgotten records are those of the cell `L` (the point `1`). -/
  forg_iff : ∀ l, (c l).forg = true ↔ (c l).pos = g.L t
  /-- A positive width is the width of the cell. -/
  w_eq : ∀ l, 0 < (c l).w → (c l).w + cp D g t ((c l).pos - 1) = cp D g t (c l).pos

/-- `y` fits the record list `c`: every `y l` lies in the cell of `c l`. -/
def Fits (D : ℕ) (g : Grid) (t : ℕ) {m : ℕ} (c : Fin m → Rec) (y : Fin m → ℝ) : Prop :=
  ∀ l, InCell D g t (c l).pos (y l)

/-- The choice of section 6 that a value selects: the least new point or `J` with `v D ≤ pt j`
(`J` if there is none). -/
noncomputable def choiceOf (D : ℕ) (g : Grid) (t : ℕ) (v : ℝ) : ℕ := by
  classical
  exact if h : ∃ j, (j ∈ newPts g t ∨ j = g.J) ∧ v * D ≤ pt D g j then Nat.find h else g.J

variable {D : ℕ} {g : Grid}

/-- On the cell `i`, `ceil_{t+1}` is `nxt_i` (8.1 (d)). -/
theorem ceilR_succ_of_inCell (hg : ok D g = true) {t i : ℕ} (ht1 : 1 ≤ t) (htn : t < g.n)
    (hi1 : 1 ≤ i) (hiL : i ≤ g.L t) {v : ℝ} (hv0 : 0 ≤ v) (hv : InCell D g t i v) :
    ceilR D g (t + 1) v = g.nxt t i := by
  have hDpos : 0 < D := Grid.so_D_pos g D hg
  have hDpos' : 0 < (D : ℝ) := by exact_mod_cast hDpos
  by_cases hvpos : 0 < v
  · -- case 0 < v
    have hxDpos : 0 < v * (D : ℝ) := by
      nlinarith
    rcases hv with ⟨hv_left, hv_right⟩
    have h_lt : (SO.cp D g t (i - 1) : ℝ) < v * (D : ℝ) := by
      rcases hv_left with (hi_eq | h_lt')
      · -- i = 1
        subst hi_eq
        have hcp0 : SO.cp D g t 0 = 0 := Grid.so_cp_zero g D t
        simpa [hcp0] using hxDpos
      · -- (cp D g t (i - 1) : ℝ) < v * D
        exact h_lt'
    exact Grid.so_ceilR_of_cell g D hg hi1 hiL h_lt hv_right
  · -- case ¬ 0 < v, combined with hv0: 0 ≤ v, so v = 0
    have hv_eq_zero : v = 0 := by nlinarith
    subst hv_eq_zero
    have hceil0 : SO.ceilR D g (t + 1) 0 = 0 := Grid.so_ceilR_of_nonpos g D hDpos (t + 1) (by norm_num)
    rcases hv with ⟨hv_left, hv_right⟩
    -- hv_left: i = 1 ∨ (SO.cp D g t (i - 1) : ℝ) < 0, but cp ≥ 0, so i = 1
    have hi_eq_one : i = 1 := by
      rcases hv_left with (h | h)
      · exact h
      · have hcp_nonneg : 0 ≤ (SO.cp D g t (i - 1) : ℝ) := Nat.cast_nonneg _
        nlinarith
    subst hi_eq_one
    have hcnt : 1 ≤ g.cnt (t + 1) := Grid.so_ok_cnt g D hg (by omega) (Nat.succ_le_of_lt htn)
    rw [hceil0, Grid.nxt_one g hcnt]

/-- The facts of `RecOK` for the record of a local point. -/
theorem locRec_facts (hg : ok D g = true) {t : ℕ} (ht1 : 1 ≤ t) (htn : t < g.n) {k : ℕ}
    (hk : k ≤ g.cnt t) :
    1 ≤ (locRec D g t k).pos ∧ (locRec D g t k).pos ≤ g.L t ∧
      (locRec D g t k).val = cp D g t (locRec D g t k).pos ∧
      pt D g (locRec D g t k).gi = (locRec D g t k).val ∧
      (locRec D g t k).map = g.nxt t (locRec D g t k).pos ∧
      ((locRec D g t k).forg = true ↔ (locRec D g t k).pos = g.L t) ∧
      (0 < (locRec D g t k).w → (locRec D g t k).w + cp D g t ((locRec D g t k).pos - 1) =
        cp D g t (locRec D g t k).pos) := by
  obtain ⟨h1, h2, -⟩ := g.pos_spec hk
  refine ⟨h1, h2, (g.so_cp_pos D hk).symm, rfl, (g.nxt_pos hk).symm, ?_, ?_⟩
  · show decide (k = g.cnt t) = true ↔ g.pos t k = g.L t
    rw [decide_eq_true_eq]
    constructor
    · rintro rfl; exact g.pos_cnt t
    · intro h
      by_contra hne
      exact absurd h (g.pos_lt_L (lt_of_le_of_ne hk hne)).ne
  · show 0 < width D g t k → width D g t k + cp D g t (g.pos t k - 1) = cp D g t (g.pos t k)
    intro hw
    have hkc : k < g.cnt t := by
      by_contra h; simp [width, h] at hw
    rw [g.so_cp_pos D hk]
    unfold width
    rw [ite_eq_left hkc]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have hc1 : 1 ≤ g.cnt t := by omega
      rw [g.pos_zero (g.so_s_le_s D hg ht1 htn) hc1, ite_eq_left rfl]
      simp [cp]
    · rw [ite_eq_right (by omega), ← g.pos_pred hk0 hkc, g.so_cp_pos D (by omega)]
      have := g.so_pt_glob_lt D hg (show k - 1 < k by omega) hk
      omega

/-- The facts of `RecOK` for the record of a new point. -/
theorem newRec_facts {t j : ℕ} (hj : j ∈ newPts g t) :
    1 ≤ (newRec D g t j).pos ∧ (newRec D g t j).pos < g.L t ∧
      (newRec D g t j).val = cp D g t (newRec D g t j).pos ∧
      pt D g (newRec D g t j).gi = (newRec D g t j).val ∧
      (newRec D g t j).map = g.nxt t (newRec D g t j).pos ∧ (newRec D g t j).forg = false ∧
      (newRec D g t j).w = 0 := by
  have hlt := g.newPts_idx_lt hj
  obtain ⟨-, hget⟩ := g.cellPts_idxOf (g.newPts_mem_cellPts hj)
  refine ⟨by simp [newRec], hlt, ?_, rfl, (g.nxt_newPt hj).symm, rfl, rfl⟩
  show pt D g j = cp D g t ((g.cellPts t).idxOf j + 1)
  rw [g.so_cp_of_pos D (by omega), Nat.add_sub_cancel, hget]

theorem recList_of_lt {t m : ℕ} {k x : Fin m → ℕ} {l : Fin m} (hl : k l < g.cnt t) :
    recList D g t k x l = locRec D g t (k l) := by
  unfold recList
  rw [ite_eq_right (fun h => hl.ne h.1)]

/-- The facts of `RecOK` at one record of a record list. -/
theorem recList_facts (hg : ok D g = true) {t : ℕ} (ht1 : 1 ≤ t) (htn : t < g.n) {m : ℕ}
    {k x : Fin m → ℕ} (hk : g.IsState t k) (l : Fin m) :
    1 ≤ (recList D g t k x l).pos ∧ (recList D g t k x l).pos ≤ g.L t ∧
      (recList D g t k x l).val = cp D g t (recList D g t k x l).pos ∧
      pt D g (recList D g t k x l).gi = (recList D g t k x l).val ∧
      (recList D g t k x l).map = g.nxt t (recList D g t k x l).pos ∧
      ((recList D g t k x l).forg = true ↔ (recList D g t k x l).pos = g.L t) ∧
      (0 < (recList D g t k x l).w →
        (recList D g t k x l).w + cp D g t ((recList D g t k x l).pos - 1) =
          cp D g t (recList D g t k x l).pos) := by
  by_cases h : k l = g.cnt t ∧ x l ∈ newPts g t
  · have e : recList D g t k x l = newRec D g t (x l) := by unfold recList; rw [ite_eq_left h]
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := newRec_facts (D := D) h.2
    rw [e]
    refine ⟨f1, f2.le, f3, f4, f5, ?_, ?_⟩
    · rw [f6]; simp only [Bool.false_eq_true, false_iff]; exact f2.ne
    · rw [f7]; intro h0; omega
  · have e : recList D g t k x l = locRec D g t (k l) := by unfold recList; rw [ite_eq_right h]
    rw [e]
    exact locRec_facts hg ht1 htn (hk.2 l)

/-- 8.1: the record lists of section 6 satisfy `RecOK`. -/
theorem recList_ok (hg : ok D g = true) {t : ℕ} (ht1 : 1 ≤ t) (htn : t < g.n) {m : ℕ}
    {k x : Fin m → ℕ} (hk : g.IsState t k) (hx : ValidChoice g t x) :
    RecOK D g t (recList D g t k x) := by
  have F := recList_facts (D := D) (x := x) hg ht1 htn hk
  refine ⟨fun l => (F l).1, fun l => (F l).2.1, ?_, fun l => (F l).2.2.1, fun l => (F l).2.2.2.1,
    fun l => (F l).2.2.2.2.1, fun l => (F l).2.2.2.2.2.1, fun l => (F l).2.2.2.2.2.2⟩
  have hnew : ∀ l, k l = g.cnt t ∧ x l ∈ newPts g t →
      recList D g t k x l = newRec D g t (x l) := fun l h => by
    unfold recList; rw [ite_eq_left h]
  have hloc : ∀ l, ¬ (k l = g.cnt t ∧ x l ∈ newPts g t) →
      recList D g t k x l = locRec D g t (k l) := fun l h => by
    unfold recList; rw [ite_eq_right h]
  have hJ : ∀ l, x l ∉ newPts g t → x l = g.J := fun l h => (hx.2 l).resolve_left h
  intro l l' hll'
  show (recList D g t k x l).pos ≤ (recList D g t k x l').pos
  have hkk := hk.1 hll'
  have hxx := hx.1 hll'
  by_cases h' : k l' = g.cnt t ∧ x l' ∈ newPts g t
  · rw [hnew l' h']
    show _ ≤ (g.cellPts t).idxOf (x l') + 1
    have hmem' := g.newPts_mem_cellPts h'.2
    by_cases h : k l = g.cnt t ∧ x l ∈ newPts g t
    · rw [hnew l h]
      show (g.cellPts t).idxOf (x l) + 1 ≤ _
      exact Nat.add_le_add_right (g.idxOf_le_idxOf (g.newPts_mem_cellPts h.2) hmem' hxx) 1
    · rw [hloc l h]
      show (g.cellPts t).idxOf (g.glob t (k l)) + 1 ≤ _
      by_cases hkl : k l < g.cnt t
      · exact Nat.add_le_add_right (g.idxOf_le_idxOf (g.glob_mem_cellPts (hk.2 l)) hmem'
          (g.glob_lt_newPt hkl h'.2).le) 1
      · have hkl' : k l = g.cnt t := le_antisymm (hk.2 l) (not_lt.mp hkl)
        have hxl : x l = g.J := hJ l (fun hm => h ⟨hkl', hm⟩)
        have := (g.mem_newPts.mp h'.2).1
        omega
  · rw [hloc l' h']
    by_cases h : k l = g.cnt t ∧ x l ∈ newPts g t
    · rw [hnew l h]
      have hkl' : k l' = g.cnt t := le_antisymm (hk.2 l') (h.1 ▸ hkk)
      show (g.cellPts t).idxOf (x l) + 1 ≤ g.pos t (k l')
      rw [hkl', g.pos_cnt t]
      exact (g.newPts_idx_lt h.2).le
    · rw [hloc l h]
      exact g.so_pos_mono D hg hkk (hk.2 l')

/-- The credited records of a record list are the coordinates below the point `1`. -/
theorem recList_w_pos (hg : ok D g = true) {t : ℕ} (ht1 : 1 ≤ t) (htn : t < g.n) {m : ℕ}
    {k x : Fin m → ℕ} (hk : g.IsState t k) (l : Fin m) :
    0 < (recList D g t k x l).w ↔ k l < g.cnt t := by
  unfold recList
  split_ifs with h
  · rcases h with ⟨hkl, _⟩
    have hw : (newRec D g t (x l)).w = 0 := rfl
    simp [hkl, hw]
  · by_cases hkl_eq : k l = g.cnt t
    · have hw : (locRec D g t (g.cnt t)).w = 0 := by
        simp [locRec, width]
      simp [hkl_eq, locRec, width]
    · have hle := (hk.2 l)
      have hlt : k l < g.cnt t := Nat.lt_of_le_of_ne hle hkl_eq
      have hw_pos : 0 < width D g t (k l) := by
        rw [width]
        rw [if_pos hlt]
        by_cases hk0 : k l = 0
        · rw [hk0]
          simp
          exact Grid.so_pt_pos g D hg (g.glob t 0)
        · rw [if_neg hk0]
          have h_lt : k l - 1 < k l := by
            have hpos : 1 ≤ k l := Nat.one_le_of_lt (Nat.pos_of_ne_zero hk0)
            omega
          have h_le : k l ≤ g.cnt t := Nat.le_of_lt hlt
          have h_pt_lt : SO.pt D g (g.glob t (k l - 1)) < SO.pt D g (g.glob t (k l)) :=
            Grid.so_pt_glob_lt g D hg h_lt h_le
          exact Nat.sub_pos_of_lt h_pt_lt
      have hw_loc : (locRec D g t (k l)).w = width D g t (k l) := rfl
      rw [hw_loc]
      simp [hlt, hw_pos]

/-- `choiceOf` at the coordinates of a memory is a choice of section 6. -/
theorem choiceOf_valid {t m : ℕ} {y : Fin m → ℝ} (hy : IsMemory y) :
    ValidChoice g t (fun l => choiceOf D g t (y l)) := by
  rcases hy with ⟨hy_mono, hy_bound⟩
  have hy_le_one : ∀ k, y k ≤ 1 := fun k => (hy_bound k).2
  have hJ_pt : pt D g g.J = D := by
    unfold pt
    simp
  have hJ_witness : ∀ v, v ≤ 1 → (g.J ∈ newPts g t ∨ g.J = g.J) ∧ v * (D : ℝ) ≤ (pt D g g.J : ℝ) := by
    intro v hv
    refine ⟨Or.inr rfl, ?_⟩
    rw [hJ_pt]
    have h : v * (D : ℝ) ≤ 1 * (D : ℝ) := mul_le_mul_of_nonneg_right hv (by norm_num : 0 ≤ (D : ℝ))
    simpa using h
  constructor
  · intro l₁ l₂ hle
    have hyl₁_le_yl₂ : y l₁ ≤ y l₂ := hy_mono hle
    dsimp [choiceOf]
    by_cases h₁ : ∃ j, (j ∈ newPts g t ∨ j = g.J) ∧ y l₁ * (D : ℝ) ≤ (pt D g j : ℝ)
    · by_cases h₂ : ∃ j, (j ∈ newPts g t ∨ j = g.J) ∧ y l₂ * (D : ℝ) ≤ (pt D g j : ℝ)
      · rw [dif_pos h₁, dif_pos h₂]
        apply Nat.find_mono
        · intro n hn
          rcases hn with ⟨hn_or, hn_le⟩
          refine ⟨hn_or, ?_⟩
          have h_mul : y l₁ * (D : ℝ) ≤ y l₂ * (D : ℝ) :=
            mul_le_mul_of_nonneg_right hyl₁_le_yl₂ (by norm_num : 0 ≤ (D : ℝ))
          linarith
      · exfalso
        exact h₂ ⟨g.J, hJ_witness (y l₂) (hy_le_one l₂)⟩
    · exfalso
      exact h₁ ⟨g.J, hJ_witness (y l₁) (hy_le_one l₁)⟩
  · intro l
    dsimp [choiceOf]
    split
    · rename_i h
      have hspec := Nat.find_spec h
      rcases hspec with ⟨h_or, _⟩
      exact h_or
    · exact Or.inr rfl

/-- `choiceOf` is the least new point or `J` at or above `v`. -/
theorem choiceOf_spec {t : ℕ} {v : ℝ} (hv : v ≤ 1) :
    (choiceOf D g t v ∈ newPts g t ∨ choiceOf D g t v = g.J) ∧
      v * D ≤ pt D g (choiceOf D g t v) ∧
      ∀ j < choiceOf D g t v, j ∈ newPts g t → (pt D g j : ℝ) < v * D := by
  classical
  have hex : ∃ j, (j ∈ newPts g t ∨ j = g.J) ∧ v * D ≤ pt D g j := by
    refine ⟨g.J, Or.inr rfl, ?_⟩
    rw [g.so_pt_of_ge D le_rfl]
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) hv
  have e : choiceOf D g t v = Nat.find hex := by
    unfold choiceOf; rw [dite_eq_left hex]
  rw [e]
  refine ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, fun j hj hjn => ?_⟩
  have := Nat.find_min hex hj
  push Not at this
  exact this (Or.inl hjn)

/-- 8.7: a memory fits the record list of its state `ceil_t (y)` and of its choice. -/
theorem fits_choice (hg : ok D g = true) {t : ℕ} (ht1 : 1 ≤ t) (htn : t < g.n) {m : ℕ}
    {y : Fin m → ℝ} (hy : IsMemory y) :
    Fits D g t (recList D g t (fun l => ceilR D g t (y l)) (fun l => choiceOf D g t (y l))) y := by
  have hD : 0 < D := g.so_D_pos D hg
  have hc1 : 1 ≤ g.cnt t := g.so_ok_cnt D hg ht1 htn.le
  intro l
  have hy1 : y l ≤ 1 := (hy.2 l).2
  have hkle : ceilR D g t (y l) ≤ g.cnt t := g.so_ceilR_le_cnt D t (y l)
  rcases lt_or_eq_of_le hkle with hlt | heq
  · -- a coordinate below the point `1`: its own record
    rw [recList_of_lt hlt]
    set k := ceilR D g t (y l) with hk
    have hspec := (g.so_ceilR_eq_iff D hD t hy1 hkle).mp rfl
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos k with h0 | hk0
      · left
        show g.pos t k = 1
        rw [h0]
        exact g.pos_zero (g.so_s_le_s D hg ht1 htn) hc1
      · right
        show (cp D g t (g.pos t k - 1) : ℝ) < y l * D
        rw [← g.pos_pred hk0 hlt, g.so_cp_pos D (by omega)]
        exact hspec.2 (k - 1) (by omega)
    · show y l * D ≤ cp D g t (g.pos t k)
      rw [g.so_cp_pos D hkle]
      exact hspec.1
  · -- a forgotten coordinate: the record of the cell of `choiceOf`
    have hspec := (g.so_ceilR_eq_iff D hD t hy1 hkle).mp rfl
    rw [heq] at hspec
    have htop : (pt D g (g.glob t (g.cnt t - 1)) : ℝ) < y l * D := hspec.2 _ (by omega)
    set j := choiceOf D g t (y l) with hj
    obtain ⟨hjm, hjv, hjmin⟩ := choiceOf_spec (D := D) (g := g) (t := t) hy1
    rw [← hj] at hjm hjv hjmin
    -- `j` is an endpoint of `P_t`, and the record of the list at `l` has the cell `idxOf j + 1`
    have hjc : j ∈ g.cellPts t := by
      rcases hjm with h | h
      · exact g.newPts_mem_cellPts h
      · rw [h]; exact g.J_mem_cellPts t
    have hpos : (recList D g t (fun l => ceilR D g t (y l)) (fun l => choiceOf D g t (y l)) l).pos =
        (g.cellPts t).idxOf j + 1 := by
      unfold recList
      split_ifs with h
      · rfl
      · show g.pos t (ceilR D g t (y l)) = _
        have hjJ : j = g.J := hjm.resolve_left (fun hm => h ⟨heq, hm⟩)
        rw [heq, Grid.pos, g.glob_of_ge le_rfl, hjJ]
    obtain ⟨hidx, hget⟩ := g.cellPts_idxOf hjc
    unfold InCell
    rw [hpos]
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos ((g.cellPts t).idxOf j) with h0 | hi0
      · left; omega
      · right
        rw [Nat.add_sub_cancel, g.so_cp_of_pos D hi0]
        set e := (g.cellPts t).getD ((g.cellPts t).idxOf j - 1) 0 with he
        have hel : e < j := by
          have := g.cellPts_getD_lt (t := t) (show (g.cellPts t).idxOf j - 1 < (g.cellPts t).idxOf j by omega)
            hidx
          rwa [hget] at this
        have hec : e ∈ g.cellPts t := g.cellPts_getD_mem (by omega)
        have hjJ : j ≤ g.J := ((g.mem_cellPts).mp hjc).1
        obtain ⟨heJ, hcase⟩ := (g.mem_cellPts).mp hec
        by_cases hnew : e ∈ newPts g t
        · exact hjmin e hel hnew
        · -- `e` is at most the top point of `G_t`
          have hetop : e ≤ g.glob t (g.cnt t - 1) := by
            have hg' : g.glob t (g.cnt t - 1) = (g.wt t).s + (g.cnt t - 1) := by
              unfold Grid.glob; rw [ite_eq_left (by omega)]
            rw [hg']
            rcases hcase with h | h | h
            · omega
            · unfold Grid.inWin at h
              simp only [Bool.and_eq_true, decide_eq_true_eq] at h
              unfold Grid.cnt; omega
            · by_contra hlt
              apply hnew
              rw [g.mem_newPts]
              refine ⟨by omega, h, ?_⟩
              unfold Grid.cnt at hlt; omega
          have := g.so_pt_mono D hg hetop
          calc (pt D g e : ℝ) ≤ pt D g (g.glob t (g.cnt t - 1)) := by exact_mod_cast this
            _ < y l * D := htop
    · rw [g.so_cp_of_pos D (by omega), Nat.add_sub_cancel, hget]
      exact hjv

end SO

end Robbins.Cert
