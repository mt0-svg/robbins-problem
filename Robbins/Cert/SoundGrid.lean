import Robbins.Cert.Spec

/-!
# Grid facts for the soundness of the certificate

Sections 1 and 4.1 of the certificate format: under the data conditions
`Grid.ok`, the point values `pt` are strictly increasing up to the point `1` (global index `J`);
the local points of `G_t` (`glob t k`, `k ≤ cnt t`) are increasing; `ceilG` and `ceilR` are the
ceiling to `G_t` on global indices and on values, and agree at grid points; the cells of `P_t`
(endpoints `cp t i`, `i ≤ L t`) are increasing from `0` to `D`, contain the points of `G_t` and
`G_{t+1}` as endpoints, and no point of either grid in their interior. On a cell, `ceilR (t + 1)`
is constant (`ceilR_of_cell`) and the comparison with a grid point is decided by the right
endpoint (`le_pt_iff_of_cell`).
-/

namespace Robbins.Cert

/-! ## Lists -/

theorem strictInc_getD (p : ℕ) (l : List ℕ) (h : strictInc p l = true) {i : ℕ}
    (hi : i < l.length) : p < l.getD i 0 ∧ ∀ j, i < j → j < l.length → l.getD i 0 < l.getD j 0 := by
  induction l generalizing p i with
  | nil => simp at hi
  | cons x xs ih =>
    simp only [strictInc, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hpx, hxs⟩ := h
    have key : ∀ j, j < xs.length → x < xs.getD j 0 := fun j hj => (ih x hxs hj).1
    cases i with
    | zero =>
      refine ⟨by simpa using hpx, fun j hj hjl => ?_⟩
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      exact key j (by simpa using hjl)
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      obtain ⟨h1, h2⟩ := ih x hxs hi'
      refine ⟨by simp only [List.getD_cons_succ]; exact hpx.trans h1, fun j hj hjl => ?_⟩
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [List.getD_cons_succ]
      exact h2 j (by omega) (by simpa using hjl)

theorem filterRange_getD_lt_getD (N : ℕ) (p : ℕ → Bool) {i j : ℕ} (hij : i < j)
    (hj : j < ((List.range N).filter p).length) :
    ((List.range N).filter p).getD i 0 < ((List.range N).filter p).getD j 0 := by
  set l := (List.range N).filter p with hl
  have h_sorted_range : (List.range N).SortedLT := List.sortedLT_range N
  have h_pairwise : List.Pairwise (· < ·) (List.range N) :=
    (List.sortedLT_iff_pairwise.mp h_sorted_range)
  have h_pairwise_filter : List.Pairwise (· < ·) l :=
    List.Pairwise.filter p h_pairwise
  have h_sorted_l : l.SortedLT :=
    (List.sortedLT_iff_pairwise.mpr h_pairwise_filter)
  have hi : i < l.length := lt_trans hij hj
  have h := h_sorted_l.getElem_lt_getElem_of_lt (hi := hi) (hj := hj) hij
  rw [← List.getElem_eq_getD (h := hi) (fallback := 0), ← List.getElem_eq_getD (h := hj) (fallback := 0)]
  exact h

theorem filterRange_getD_mem (N : ℕ) (p : ℕ → Bool) {i : ℕ}
    (hi : i < ((List.range N).filter p).length) :
    ((List.range N).filter p).getD i 0 < N ∧ p (((List.range N).filter p).getD i 0) = true := by
  rw [List.getD_eq_getElem _ _ hi]
  have hm := List.getElem_mem hi
  rcases (List.mem_filter.mp hm) with ⟨hm_range, hm_p⟩
  have h_lt_N : ((List.range N).filter p)[i] < N := by
    rwa [List.mem_range] at hm_range
  exact And.intro h_lt_N hm_p

theorem filterRange_idxOf (N : ℕ) (p : ℕ → Bool) {j : ℕ} (hj : j < N) (hp : p j = true) :
    ((List.range N).filter p).idxOf j < ((List.range N).filter p).length ∧
      ((List.range N).filter p).getD (((List.range N).filter p).idxOf j) 0 = j := by
  have hmem : j ∈ List.range N := List.mem_range.mpr hj
  have hmem_filter : j ∈ (List.range N).filter p := by
    apply List.mem_filter.mpr
    exact ⟨hmem, hp⟩
  have hidx_lt : ((List.range N).filter p).idxOf j < ((List.range N).filter p).length :=
    List.idxOf_lt_length_of_mem hmem_filter
  have hget : ((List.range N).filter p).getD (((List.range N).filter p).idxOf j) 0 = j := by
    calc
      ((List.range N).filter p).getD (((List.range N).filter p).idxOf j) 0
          = ((List.range N).filter p)[((List.range N).filter p).idxOf j] := by
        rw [List.getD_eq_getElem _ _ hidx_lt]
      _ = j := List.getElem_idxOf hidx_lt
  exact And.intro hidx_lt hget

theorem filterRange_gap (N : ℕ) (p : ℕ → Bool) {i j : ℕ}
    (hi : i < ((List.range N).filter p).length) (hj : j < N) (hp : p j = true)
    (hlt : i = 0 ∨ ((List.range N).filter p).getD (i - 1) 0 < j) :
    ((List.range N).filter p).getD i 0 ≤ j := by
  set f := List.filter p (List.range N) with hf
  have h_idx := filterRange_idxOf N p hj hp
  rcases h_idx with ⟨h_idx_lt, h_idx_eq⟩
  set i' := f.idxOf j with hi'_def
  have hi'_lt_len : i' < f.length := h_idx_lt
  have h_get_i' : f.getD i' 0 = j := h_idx_eq
  by_contra! H
  -- H: j < f.getD i 0
  by_cases h_le : i ≤ i'
  · -- i ≤ i', so f.getD i 0 ≤ f.getD i' 0 = j, contradicting H
    by_cases h_eq : i = i'
    · rw [h_eq, h_get_i'] at H
      exact lt_irrefl _ H
    · have h_lt : i < i' := Nat.lt_of_le_of_ne h_le h_eq
      have h_get_lt' : f.getD i 0 < f.getD i' 0 :=
        filterRange_getD_lt_getD N p h_lt hi'_lt_len
      rw [h_get_i'] at h_get_lt'
      exact lt_irrefl _ (lt_trans H h_get_lt')
  · -- i' < i
    have h_lt' : i' < i := Nat.lt_of_not_ge h_le
    have h_get_le : f.getD i' 0 ≤ f.getD (i - 1) 0 := by
      by_cases h_eq' : i' = i - 1
      · rw [h_eq']
      · have h_lt'' : i' < i - 1 := by omega
        have h_sub_lt : i - 1 < f.length :=
          Nat.lt_of_le_of_lt (Nat.sub_le i 1) hi
        have h_lt_get : f.getD i' 0 < f.getD (i - 1) 0 :=
          filterRange_getD_lt_getD N p h_lt'' h_sub_lt
        exact le_of_lt h_lt_get
    rw [h_get_i'] at h_get_le
    rcases hlt with (h_i0 | h_lt_j)
    · -- i = 0, but i' < i, impossible
      rw [h_i0] at h_lt'
      exact Nat.not_lt_zero _ h_lt'
    · -- f.getD (i-1) 0 < j ≤ f.getD (i-1) 0, contradiction
      exact lt_irrefl _ (lt_of_lt_of_le h_lt_j h_get_le)

namespace Grid

variable (g : Grid)

/-! ## The data conditions and the point values -/

theorem ok_two_le_n (hg : g.ok = true) : 2 ≤ g.n := by
  simp only [Grid.ok, Bool.and_eq_true, decide_eq_true_eq] at hg
  rcases hg with ⟨⟨⟨⟨⟨_, hn⟩, _⟩, _⟩, _⟩, _⟩
  exact hn

theorem ok_gpt (hg : g.ok = true) {i : ℕ} (hi : i < g.J) :
    0 < g.gpt.getD i 0 ∧ g.gpt.getD i 0 < D := by
  have hi' : i < g.gpt.length := hi
  have h_all : ((((1 ≤ g.m ∧ 2 ≤ g.n) ∧ strictInc 0 g.gpt = true) ∧ ∀ x ∈ g.gpt, x < D) ∧ g.start.length = g.n) ∧ nondec 0 g.start = true := by
    unfold Grid.ok at hg
    simpa [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] using hg
  rcases h_all with ⟨⟨⟨⟨⟨hm, hn⟩, hstrict⟩, hall⟩, hlen⟩, hnondec⟩
  have hpos := strictInc_getD 0 g.gpt hstrict hi'
  rcases hpos with ⟨hleftpos, _⟩
  have hmem : g.gpt.getD i 0 ∈ g.gpt := by
    rw [List.getD_eq_getElem g.gpt 0 hi']
    exact List.getElem_mem hi'
  have hright' : g.gpt.getD i 0 < D := by
    have := hall (g.gpt.getD i 0) hmem
    simpa using this
  exact And.intro hleftpos hright'

theorem ok_gpt_lt (hg : g.ok = true) {i j : ℕ} (hij : i < j) (hj : j < g.J) :
    g.gpt.getD i 0 < g.gpt.getD j 0 := by
  have hg' : strictInc 0 g.gpt = true := by
    simp [Grid.ok, Bool.and_eq_true] at hg
    exact hg.1.1.1.2
  have hi : i < g.gpt.length := by
    have : g.J = g.gpt.length := rfl
    omega
  have h := strictInc_getD 0 g.gpt hg' hi
  exact h.right j hij (by
    have : g.J = g.gpt.length := rfl
    omega)

theorem pt_of_lt {j : ℕ} (hj : j < g.J) : g.pt j = g.gpt.getD j 0 := by
  unfold Grid.pt
  rw [ite_eq_left hj]

theorem pt_of_ge {j : ℕ} (hj : g.J ≤ j) : g.pt j = D := by
  unfold Grid.pt
  rw [ite_eq_right (not_lt.mpr hj)]

theorem pt_pos (hg : g.ok = true) (j : ℕ) : 0 < g.pt j := by
  by_cases hj : j < g.J
  · have hpos := (g.ok_gpt hg hj).1
    rw [g.pt_of_lt hj]
    exact hpos
  · have hle : g.J ≤ j := Nat.le_of_not_lt hj
    rw [g.pt_of_ge hle]
    exact D_pos

theorem pt_le_D (hg : g.ok = true) (j : ℕ) : g.pt j ≤ D := by
  by_cases hj : j < g.J
  · rw [g.pt_of_lt hj]
    exact Nat.le_of_lt ((g.ok_gpt hg hj).2)
  · rw [g.pt_of_ge (by omega)]

theorem pt_lt_D (hg : g.ok = true) {j : ℕ} (hj : j < g.J) : g.pt j < D := by
  rw [pt_of_lt g hj]
  exact (ok_gpt g hg hj).right

theorem pt_lt_pt (hg : g.ok = true) {i j : ℕ} (hij : i < j) (hj : j ≤ g.J) : g.pt i < g.pt j := by
  by_cases hj' : j < g.J
  · have hi_lt_J : i < g.J := lt_trans hij hj'
    rw [g.pt_of_lt hi_lt_J, g.pt_of_lt hj']
    exact g.ok_gpt_lt hg hij hj'
  · have hj_eq : j = g.J := by omega
    rw [hj_eq]
    rw [g.pt_of_ge (le_refl g.J)]
    have hi_lt_J : i < g.J := by
      rw [hj_eq] at hij
      exact hij
    exact g.pt_lt_D hg hi_lt_J

theorem pt_mono (hg : g.ok = true) : Monotone g.pt := by
  intro i j hij
  by_cases hj : g.J ≤ j
  · rw [g.pt_of_ge hj]
    exact g.pt_le_D hg i
  · have hj' : j < g.J := Nat.lt_of_not_ge hj
    by_cases hij' : i < j
    · have h := g.pt_lt_pt hg hij' (Nat.le_of_lt hj')
      exact Nat.le_of_lt h
    · have heq : i = j := Nat.le_antisymm hij (Nat.le_of_not_gt hij')
      rw [heq]

/-! ## The local points of `G_t` -/

theorem s_add_cnt_le (t : ℕ) : (g.wt t).s + g.cnt t ≤ g.J := by
  simp only [Grid.cnt, Grid.wt, Grid.win, Grid.J]
  omega

theorem glob_lt_J {t k : ℕ} (hk : k < g.cnt t) : g.glob t k < g.J := by
  unfold Grid.glob
  simp [hk]
  have h := g.s_add_cnt_le t
  omega

theorem glob_of_ge {t k : ℕ} (hk : g.cnt t ≤ k) : g.glob t k = g.J := by
  dsimp [Grid.glob]; split <;> omega

theorem glob_le_J (t k : ℕ) : g.glob t k ≤ g.J := by
  unfold Grid.glob
  split_ifs with h
  · have hle := g.s_add_cnt_le t
    omega
  · exact le_rfl

theorem glob_lt_glob {t k k' : ℕ} (h : k < k') (hk' : k' ≤ g.cnt t) : g.glob t k < g.glob t k' := by
  have hk : k < g.cnt t := lt_of_lt_of_le h hk'
  have hsum : (g.wt t).s + g.cnt t ≤ g.J := by
    unfold wt win cnt
    set st := g.start.getD (t - 1) 0
    have hle : min st g.J ≤ min (st + g.K) g.J := by
      by_cases hst : g.J ≤ st
      · have h1 : min st g.J = g.J := Nat.min_eq_right hst
        have h2 : min (st + g.K) g.J = g.J :=
          Nat.min_eq_right (le_trans hst (Nat.le_add_right st g.K))
        simp [h1, h2]
      · have hst_lt : st < g.J := Nat.lt_of_not_ge hst
        have h1 : min st g.J = st := Nat.min_eq_left (Nat.le_of_lt hst_lt)
        have h_le : st ≤ min (st + g.K) g.J :=
          Nat.le_min.mpr ⟨Nat.le_add_right st g.K, Nat.le_of_lt hst_lt⟩
        simp [h1, h_le]
    have h_eq : min st g.J + (min (st + g.K) g.J - min st g.J) = min (st + g.K) g.J :=
      Nat.add_sub_cancel' hle
    have h_min_le : min (st + g.K) g.J ≤ g.J := Nat.min_le_right _ _
    calc
      min st g.J + (min (st + g.K) g.J - min st g.J) = min (st + g.K) g.J := h_eq
      _ ≤ g.J := h_min_le
  have h_lt_sum : (g.wt t).s + k < (g.wt t).s + g.cnt t := Nat.add_lt_add_left hk _
  have h_lt_J : (g.wt t).s + k < g.J := lt_of_lt_of_le h_lt_sum hsum
  unfold glob
  simp [hk]
  by_cases hk'lt : k' < g.cnt t
  · simp [hk'lt]
    omega
  · have hk'eq : k' = g.cnt t := by omega
    simp [hk'eq]
    exact h_lt_J

theorem glob_mono (t : ℕ) : Monotone (g.glob t) := by
  intro a b h
  unfold Grid.glob
  split_ifs with ha hb
  · omega
  · have hle := g.s_add_cnt_le t; omega
  · omega
  · rfl

theorem inWin_glob {t k : ℕ} (hk : k < g.cnt t) : g.inWin t (g.glob t k) = true := by
  unfold Grid.inWin Grid.glob
  dsimp [Grid.cnt] at hk ⊢
  simp [hk]

theorem pt_glob_lt (hg : g.ok = true) {t k k' : ℕ} (h : k < k') (hk' : k' ≤ g.cnt t) :
    g.pt (g.glob t k) < g.pt (g.glob t k') := by
  exact pt_lt_pt g hg (glob_lt_glob g h hk') (glob_le_J g t k')

theorem pt_glob_mono (hg : g.ok = true) (t : ℕ) : Monotone fun k => g.pt (g.glob t k) := by
  intro k k' h
  exact g.pt_mono hg (g.glob_mono t h)

/-! ## `ceil_t` on global indices and on values -/

theorem ceilG_le_cnt (t j : ℕ) : g.ceilG t j ≤ g.cnt t := by
  simp only [Grid.ceilG, ceilLocal, Grid.cnt]
  split_ifs
  · exact Nat.le_refl _
  · exact Nat.zero_le _
  · omega
  · exact Nat.le_refl _

theorem ceilG_spec (hg : g.ok = true) (t : ℕ) {j : ℕ} (hj : j ≤ g.J) :
    g.pt j ≤ g.pt (g.glob t (g.ceilG t j)) ∧ ∀ k < g.ceilG t j, g.pt (g.glob t k) < g.pt j := by
  have hsc : (g.wt t).s + g.cnt t ≤ g.J := g.s_add_cnt_le t
  have hmono : Monotone g.pt := g.pt_mono hg
  have hpt_le_D : ∀ j, g.pt j ≤ D := fun j => g.pt_le_D hg j
  have hpt_of_ge : ∀ {j}, g.J ≤ j → g.pt j = D := fun h => g.pt_of_ge h
  have hglob_ge : ∀ {k}, g.cnt t ≤ k → g.glob t k = g.J := fun h => g.glob_of_ge h
  have hglob_lt_J : ∀ {k}, k < g.cnt t → g.glob t k < g.J := fun h => g.glob_lt_J h
  have hglob_eq : ∀ {k}, k < g.cnt t → g.glob t k = (g.wt t).s + k := by
    intro k hk
    unfold Grid.glob
    simp [hk]
  unfold Grid.ceilG
  unfold ceilLocal
  dsimp [Grid.cnt] at *
  by_cases hJ : j = g.J
  · -- Then ceilG = (g.wt t).cnt
    have hceil : (if j == g.J || (g.wt t).cnt == 0 then (g.wt t).cnt
      else if j < (g.wt t).s then 0
      else if j < (g.wt t).s + (g.wt t).cnt then j - (g.wt t).s
      else (g.wt t).cnt) = (g.wt t).cnt := by
      simp [hJ]
    rw [hceil]
    have hfirst : g.pt j ≤ g.pt (g.glob t ((g.wt t).cnt)) := by
      have hglob_c : g.glob t ((g.wt t).cnt) = g.J := hglob_ge (le_refl _)
      rw [hglob_c]
      rw [hpt_of_ge (le_refl g.J)]
      exact hpt_le_D j
    have hsecond : ∀ k < (g.wt t).cnt, g.pt (g.glob t k) < g.pt j := by
      intro k hk
      have hglob_k_lt_j : g.glob t k < j := by
        rw [hglob_eq hk, hJ]
        omega
      exact g.pt_lt_pt hg hglob_k_lt_j hj
    exact And.intro hfirst hsecond
  · -- j ≠ g.J
    by_cases hc0 : (g.wt t).cnt = 0
    · -- Then ceilG = (g.wt t).cnt (=0)
      have hceil : (if j == g.J || (g.wt t).cnt == 0 then (g.wt t).cnt
        else if j < (g.wt t).s then 0
        else if j < (g.wt t).s + (g.wt t).cnt then j - (g.wt t).s
        else (g.wt t).cnt) = (g.wt t).cnt := by
        simp [hJ, hc0]
      rw [hceil]
      have hc0' : (g.wt t).cnt = 0 := hc0
      have hfirst : g.pt j ≤ g.pt (g.glob t ((g.wt t).cnt)) := by
        have hcnt_le_c : (g.wt t).cnt ≤ (g.wt t).cnt := le_refl _
        have hglob_c : g.glob t ((g.wt t).cnt) = g.J := hglob_ge hcnt_le_c
        rw [hglob_c]
        rw [hpt_of_ge (le_refl g.J)]
        exact hpt_le_D j
      have hsecond : ∀ k < (g.wt t).cnt, g.pt (g.glob t k) < g.pt j := by
        rw [hc0']
        intro k hk; omega
      exact And.intro hfirst hsecond
    · -- c ≠ 0
      by_cases hjs : j < (g.wt t).s
      · -- ceilG = 0
        have hceil : (if j == g.J || (g.wt t).cnt == 0 then (g.wt t).cnt
          else if j < (g.wt t).s then 0
          else if j < (g.wt t).s + (g.wt t).cnt then j - (g.wt t).s
          else (g.wt t).cnt) = 0 := by
          simp [hJ, hc0, hjs]
        rw [hceil]
        have hfirst : g.pt j ≤ g.pt (g.glob t 0) := by
          have hpos : 0 < (g.wt t).cnt := Nat.pos_of_ne_zero hc0
          have hglob_0 : g.glob t 0 = (g.wt t).s := by
            unfold Grid.glob
            have hpos' : 0 < g.cnt t := hpos
            simp [hpos']
          rw [hglob_0]
          have hjs' : j ≤ (g.wt t).s := by omega
          exact hmono hjs'
        have hsecond : ∀ k < 0, g.pt (g.glob t k) < g.pt j := by
          intro k hk; omega
        exact And.intro hfirst hsecond
      · -- j ≥ s
        by_cases hjsc : j < (g.wt t).s + (g.wt t).cnt
        · -- ceilG = j - (g.wt t).s
          have hceil : (if j == g.J || (g.wt t).cnt == 0 then (g.wt t).cnt
            else if j < (g.wt t).s then 0
            else if j < (g.wt t).s + (g.wt t).cnt then j - (g.wt t).s
            else (g.wt t).cnt) = j - (g.wt t).s := by
            simp [hJ, hc0, hjs, hjsc]
          rw [hceil]
          have hfirst : g.pt j ≤ g.pt (g.glob t (j - (g.wt t).s)) := by
            have h_sub_lt : j - (g.wt t).s < (g.wt t).cnt := by omega
            have hglob_sub : g.glob t (j - (g.wt t).s) = (g.wt t).s + (j - (g.wt t).s) := by
              unfold Grid.glob
              have h_sub_lt' : j - (g.wt t).s < g.cnt t := h_sub_lt
              simp [h_sub_lt']
            rw [hglob_sub]
            have : (g.wt t).s + (j - (g.wt t).s) = j := by omega
            rw [this]
          have hsecond : ∀ k < j - (g.wt t).s, g.pt (g.glob t k) < g.pt j := by
            intro k hk
            have hk_lt_c : k < (g.wt t).cnt := by omega
            have hglob_k : g.glob t k = (g.wt t).s + k := hglob_eq hk_lt_c
            rw [hglob_k]
            have h_lt_j : (g.wt t).s + k < j := by omega
            exact g.pt_lt_pt hg h_lt_j hj
          exact And.intro hfirst hsecond
        · -- ceilG = (g.wt t).cnt
          have hceil : (if j == g.J || (g.wt t).cnt == 0 then (g.wt t).cnt
            else if j < (g.wt t).s then 0
            else if j < (g.wt t).s + (g.wt t).cnt then j - (g.wt t).s
            else (g.wt t).cnt) = (g.wt t).cnt := by
            simp [hJ, hc0, hjs, hjsc]
          rw [hceil]
          have hfirst : g.pt j ≤ g.pt (g.glob t ((g.wt t).cnt)) := by
            have hglob_c : g.glob t ((g.wt t).cnt) = g.J := hglob_ge (le_refl _)
            rw [hglob_c]
            rw [hpt_of_ge (le_refl g.J)]
            exact hpt_le_D j
          have hsecond : ∀ k < (g.wt t).cnt, g.pt (g.glob t k) < g.pt j := by
            intro k hk
            have hglob_k : g.glob t k = (g.wt t).s + k := hglob_eq hk
            rw [hglob_k]
            have h_lt_j : (g.wt t).s + k < j := by
              have : (g.wt t).s + k < (g.wt t).s + (g.wt t).cnt := by omega
              omega
            exact g.pt_lt_pt hg h_lt_j hj
          exact And.intro hfirst hsecond

theorem ceilR_le_cnt (t : ℕ) (y : ℝ) : g.ceilR t y ≤ g.cnt t := by
  unfold Grid.ceilR
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact le_rfl

theorem ceilR_eq_iff (t : ℕ) {y : ℝ} (hy : y ≤ 1) {k : ℕ} (hk : k ≤ g.cnt t) :
    g.ceilR t y = k ↔
      y * D ≤ g.pt (g.glob t k) ∧ ∀ k' < k, (g.pt (g.glob t k') : ℝ) < y * D := by
  classical
  have hDpos : (0 : ℝ) < D := Nat.cast_pos.mpr D_pos
  have hex : ∃ k', k' ≤ g.cnt t ∧ y * (D : ℝ) ≤ (g.pt (g.glob t k') : ℝ) := by
    refine ⟨g.cnt t, le_rfl, ?_⟩
    have hglob : g.glob t (g.cnt t) = g.J := g.glob_of_ge (le_refl _)
    have hpt : g.pt g.J = D := g.pt_of_ge (le_refl _)
    calc
      y * (D : ℝ) ≤ 1 * (D : ℝ) := by nlinarith
      _ = (D : ℝ) := by ring
      _ = (g.pt g.J : ℝ) := by simp [hpt]
      _ = (g.pt (g.glob t (g.cnt t)) : ℝ) := by rw [hglob]
  unfold Grid.ceilR
  rw [dite_eq_left hex]
  rw [Nat.find_eq_iff hex]
  constructor
  · rintro ⟨⟨hle, hge⟩, hforall⟩
    refine ⟨hge, ?_⟩
    intro k' hk'
    have hk'cnt : k' ≤ g.cnt t := Nat.le_trans (Nat.le_of_lt hk') hk
    have hnot := hforall k' hk'
    have hnot' : ¬ (y * (D : ℝ) ≤ (g.pt (g.glob t k') : ℝ)) := by
      intro h
      apply hnot
      exact ⟨hk'cnt, h⟩
    linarith
  · rintro ⟨hge, hforall⟩
    refine ⟨⟨hk, hge⟩, ?_⟩
    intro m hm
    have hmcnt : m ≤ g.cnt t := Nat.le_trans (Nat.le_of_lt hm) hk
    intro h
    rcases h with ⟨_, hge'⟩
    have hlt := hforall m hm
    linarith

theorem le_pt_ceilR (t : ℕ) {y : ℝ} (hy : y ≤ 1) : y * D ≤ g.pt (g.glob t (g.ceilR t y)) := by
  have h_exists : ∃ k, k ≤ g.cnt t ∧ y * (D : ℝ) ≤ (g.pt (g.glob t k) : ℝ) := by
    refine ⟨g.cnt t, le_rfl, ?_⟩
    have hglob : g.glob t (g.cnt t) = g.J := glob_of_ge g le_rfl
    have hpt : g.pt (g.J) = D := pt_of_ge g le_rfl
    have hDpos : (0 : ℝ) < D := by exact_mod_cast D_pos
    have hyD : y * (D : ℝ) ≤ (D : ℝ) := by
      nlinarith
    calc
      y * (D : ℝ) ≤ (D : ℝ) := hyD
      _ = (g.pt (g.J) : ℝ) := by rw [hpt]
      _ = (g.pt (g.glob t (g.cnt t)) : ℝ) := by rw [hglob]
  unfold Grid.ceilR
  rw [dite_eq_left h_exists]
  exact (Nat.find_spec h_exists).2

theorem ceilR_mono (t : ℕ) : Monotone (g.ceilR t) := by
  intro y y' h
  unfold Grid.ceilR
  split
  · rename_i h
    have hy_spec := Nat.find_spec h
    rcases hy_spec with ⟨hle, hy_pt⟩
    split
    · rename_i h'
      have hy'_spec := Nat.find_spec h'
      have hyD : y * (D : ℝ) ≤ y' * (D : ℝ) := by
        nlinarith
      have hy_pt' : y * (D : ℝ) ≤ g.pt (g.glob t (Nat.find h')) := by
        linarith
      exact Nat.find_min' h ⟨(Nat.find_spec h').1, hy_pt'⟩
    · rename_i h'
      exact hle
  · rename_i h
    split
    · rename_i h'
      have hy'_spec := Nat.find_spec h'
      rcases hy'_spec with ⟨hle', hy'_pt⟩
      have hyD : y * (D : ℝ) ≤ y' * (D : ℝ) := by
        nlinarith
      have hy_pt' : y * (D : ℝ) ≤ g.pt (g.glob t (Nat.find h')) := by
        linarith
      exfalso
      exact h ⟨Nat.find h', hle', hy_pt'⟩
    · rfl

theorem ceilR_of_nonpos (t : ℕ) {y : ℝ} (hy : y ≤ 0) : g.ceilR t y = 0 := by
  have hDpos : 0 < D := D_pos
  have hDposℝ : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hyD : y * (D : ℝ) ≤ 0 := by
    nlinarith
  have hpt_nonneg (k : ℕ) : (0 : ℝ) ≤ (g.pt (g.glob t k) : ℝ) := by
    exact_mod_cast Nat.zero_le (g.pt (g.glob t k))
  have h_exists : ∃ k, k ≤ g.cnt t ∧ y * (D : ℝ) ≤ (g.pt (g.glob t k) : ℝ) := by
    refine ⟨0, Nat.zero_le _, ?_⟩
    have h0 : (0 : ℝ) ≤ (g.pt (g.glob t 0) : ℝ) := hpt_nonneg 0
    nlinarith
  unfold Grid.ceilR
  split_ifs
  · -- Goal: Nat.find h_exists = 0
    -- Using Nat.find_eq_zero: Nat.find h = 0 ↔ p 0
    rw [Nat.find_eq_zero]
    -- Goal: 0 ≤ g.cnt t ∧ y * (D : ℝ) ≤ (g.pt (g.glob t 0) : ℝ)
    refine ⟨Nat.zero_le _, ?_⟩
    have h0pt : (0 : ℝ) ≤ (g.pt (g.glob t 0) : ℝ) := hpt_nonneg 0
    nlinarith

theorem ceilR_one (hg : g.ok = true) (t : ℕ) : g.ceilR t 1 = g.cnt t := by
  have h_one_le_one : (1 : ℝ) ≤ 1 := le_rfl
  have h_cnt_le : g.cnt t ≤ g.cnt t := le_rfl
  rw [g.ceilR_eq_iff t h_one_le_one h_cnt_le]
  have h_glob_cnt : g.glob t (g.cnt t) = g.J := by
    simp [Grid.glob]
  have h_pt_glob_cnt : (g.pt (g.glob t (g.cnt t)) : ℝ) = (D : ℝ) := by
    rw [h_glob_cnt]
    have h_pt_J : g.pt g.J = D := g.pt_of_ge (le_rfl : g.J ≤ g.J)
    simp [h_pt_J]
  constructor
  · rw [h_pt_glob_cnt]
    simp
  · intro k' hk'
    have h_glob_lt_J : g.glob t k' < g.J := g.glob_lt_J hk'
    have h_pt_lt_D : g.pt (g.glob t k') < D := g.pt_lt_D hg h_glob_lt_J
    have h_cast : (g.pt (g.glob t k') : ℝ) < (D : ℝ) := by exact_mod_cast h_pt_lt_D
    calc
      (g.pt (g.glob t k') : ℝ) < (D : ℝ) := h_cast
      _ = (1 : ℝ) * (D : ℝ) := by simp

theorem ceilR_pt (hg : g.ok = true) (t : ℕ) {j : ℕ} (hj : j ≤ g.J) :
    g.ceilR t ((g.pt j : ℝ) / D) = g.ceilG t j := by
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast D_pos
  have hy_le_one : (g.pt j : ℝ) / (D : ℝ) ≤ 1 := by
    have hpt_le_D : (g.pt j : ℝ) ≤ (D : ℝ) := by exact mod_cast g.pt_le_D hg j
    exact (div_le_one hDpos).mpr hpt_le_D
  have hk_le_cnt : g.ceilG t j ≤ g.cnt t := g.ceilG_le_cnt t j
  refine ((g.ceilR_eq_iff t hy_le_one hk_le_cnt).mpr ?_)
  constructor
  · calc
      (g.pt j : ℝ) / (D : ℝ) * (D : ℝ) = (g.pt j : ℝ) := by
        field_simp [hDpos.ne.symm]
      _ ≤ (g.pt (g.glob t (g.ceilG t j)) : ℝ) := by
        exact mod_cast (g.ceilG_spec hg t hj).1
  · intro k' hk'
    have h_lt_nat : g.pt (g.glob t k') < g.pt j := (g.ceilG_spec hg t hj).2 k' hk'
    have h_lt : (g.pt (g.glob t k') : ℝ) < (g.pt j : ℝ) := by exact mod_cast h_lt_nat
    calc
      (g.pt (g.glob t k') : ℝ) < (g.pt j : ℝ) := h_lt
      _ = ((g.pt j : ℝ) / (D : ℝ)) * (D : ℝ) := by field_simp [hDpos.ne.symm]

theorem measurable_ceilR (t : ℕ) : Measurable (g.ceilR t) := by
  have h_mono : Monotone (g.ceilR t) := g.ceilR_mono t
  exact h_mono.measurable

/-! ## The cells of `P_t` -/

theorem mem_cellPts {t j : ℕ} :
    j ∈ g.cellPts t ↔ j ≤ g.J ∧ (j = g.J ∨ g.inWin t j = true ∨ g.inWin (t + 1) j = true) := by
  unfold Grid.cellPts
  simp only [List.mem_filter, List.mem_range, Bool.or_eq_true, beq_iff_eq, Nat.lt_succ_iff]
  tauto

theorem J_mem_cellPts (t : ℕ) : g.J ∈ g.cellPts t := by
  apply ((mem_cellPts g (t := t) (j := g.J)).mpr)
  exact ⟨le_rfl, Or.inl rfl⟩

theorem glob_mem_cellPts {t k : ℕ} (hk : k ≤ g.cnt t) : g.glob t k ∈ g.cellPts t := by
  rcases Nat.lt_or_eq_of_le hk with (h | h)
  · -- h : k < g.cnt t
    have hglob_lt_J : g.glob t k < g.J := g.glob_lt_J h
    have hinWin : g.inWin t (g.glob t k) = true := g.inWin_glob h
    rw [g.mem_cellPts]
    exact ⟨Nat.le_of_lt hglob_lt_J, Or.inr (Or.inl hinWin)⟩
  · -- h : k = g.cnt t
    have hglob_eq_J : g.glob t k = g.J := g.glob_of_ge (by omega)
    rw [g.mem_cellPts, hglob_eq_J]
    exact ⟨le_refl g.J, Or.inl rfl⟩

theorem glob_succ_mem_cellPts {t k : ℕ} (hk : k ≤ g.cnt (t + 1)) :
    g.glob (t + 1) k ∈ g.cellPts t := by
  rw [g.mem_cellPts]
  constructor
  · by_cases h : k < g.cnt (t + 1)
    · exact Nat.le_of_lt (g.glob_lt_J h)
    · have hge : g.cnt (t + 1) ≤ k := by omega
      rw [g.glob_of_ge hge]
  · by_cases h : k < g.cnt (t + 1)
    · right; right; rw [g.inWin_glob h]
    · have hge : g.cnt (t + 1) ≤ k := by omega
      left; exact g.glob_of_ge hge

theorem one_le_L (t : ℕ) : 1 ≤ g.L t := by
  have hpos : 0 < g.L t := by
    have hmem : g.J ∈ g.cellPts t := g.J_mem_cellPts t
    have h := List.length_pos_of_mem hmem
    simpa [Grid.L] using h
  omega

theorem cellPts_last (t : ℕ) : (g.cellPts t).getD (g.L t - 1) 0 = g.J := by
  unfold Grid.L
  unfold Grid.cellPts
  let p : ℕ → Bool := fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j
  have hJ_lt : g.J < g.J + 1 := by omega
  have hp_J : p g.J := by
    simp [p]
  have h_idx := filterRange_idxOf (g.J + 1) p hJ_lt hp_J
  rcases h_idx with ⟨h_idx_lt, h_idx_eq⟩
  dsimp [p] at h_idx_lt h_idx_eq
  let l := (List.range (g.J + 1)).filter (fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j)
  have hlen_pos : 0 < l.length := by
    by_contra! h
    have hlen0 : l.length = 0 := by omega
    rw [hlen0] at h_idx_lt
    exact Nat.not_lt_zero _ h_idx_lt
  have h_sub_lt : l.length - 1 < l.length :=
    Nat.sub_lt hlen_pos (by omega)
  by_cases h_lt : l.idxOf g.J < l.length - 1
  · have h_lt_getD := filterRange_getD_lt_getD (g.J + 1) (fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j) h_lt h_sub_lt
    have h_mem := filterRange_getD_mem (g.J + 1) (fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j) (i := l.length - 1) h_sub_lt
    rcases h_mem with ⟨h_lt_N, _⟩
    rw [h_idx_eq] at h_lt_getD
    have h_le : l.getD (l.length - 1) 0 ≤ g.J := Nat.le_of_lt_succ h_lt_N
    have : g.J < g.J := Nat.lt_of_lt_of_le h_lt_getD h_le
    exact absurd this (Nat.lt_irrefl g.J)
  · have h_eq : l.idxOf g.J = l.length - 1 := by
      have : l.idxOf g.J < l.length := h_idx_lt
      omega
    rw [h_eq] at h_idx_eq
    exact h_idx_eq

theorem cp_zero (t : ℕ) : g.cp t 0 = 0 := by
  unfold Grid.cp; simp

theorem cp_of_pos {t i : ℕ} (hi : 1 ≤ i) : g.cp t i = g.pt ((g.cellPts t).getD (i - 1) 0) := by
  simp [Grid.cp, show i ≠ 0 from by omega]

theorem cp_L (t : ℕ) : g.cp t (g.L t) = D := by
  have hL := g.one_le_L t
  have hcell := g.cellPts_last t
  have hpt := g.pt_of_ge (le_refl g.J)
  calc
    g.cp t (g.L t) = g.pt ((g.cellPts t).getD (g.L t - 1) 0) := by
      rw [g.cp_of_pos hL]
    _ = g.pt g.J := by rw [hcell]
    _ = D := hpt

theorem cp_le_D (hg : g.ok = true) (t i : ℕ) : g.cp t i ≤ D := by
  by_cases hi : i = 0
  · rw [hi, g.cp_zero t]
    exact Nat.zero_le _
  · have hi_pos : 1 ≤ i := Nat.one_le_of_lt (Nat.pos_of_ne_zero hi)
    rw [g.cp_of_pos hi_pos]
    exact g.pt_le_D hg _

theorem cp_lt_cp (hg : g.ok = true) {t i i' : ℕ} (h : i < i') (hi' : i' ≤ g.L t) :
    g.cp t i < g.cp t i' := by
  unfold Grid.L Grid.cellPts at hi'
  have hi'_pos : 1 ≤ i' := by omega
  have hi'_lt_len : i' - 1 < ((List.range (g.J + 1)).filter fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j).length := by
    omega
  by_cases hi0 : i = 0
  · rw [hi0, g.cp_zero t, g.cp_of_pos hi'_pos]
    exact g.pt_pos hg _
  · have hi_pos : 1 ≤ i := by omega
    rw [g.cp_of_pos hi_pos, g.cp_of_pos hi'_pos]
    have h_getD_lt : ((List.range (g.J + 1)).filter fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j).getD (i - 1) 0 <
        ((List.range (g.J + 1)).filter fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j).getD (i' - 1) 0 := by
      refine filterRange_getD_lt_getD (g.J + 1) (fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j) ?_ ?_
      · omega
      · exact hi'_lt_len
    have h_getD_mem : ((List.range (g.J + 1)).filter fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j).getD (i' - 1) 0 ≤ g.J := by
      have hmem := filterRange_getD_mem (g.J + 1) (fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j) hi'_lt_len
      omega
    exact g.pt_lt_pt hg h_getD_lt h_getD_mem

theorem cp_mono (hg : g.ok = true) {t i i' : ℕ} (h : i ≤ i') (hi' : i' ≤ g.L t) :
    g.cp t i ≤ g.cp t i' := by
  rcases h.eq_or_lt with (rfl | hlt)
  · rfl
  · exact (g.cp_lt_cp hg hlt hi').le

theorem cp_lt_D (hg : g.ok = true) {t i : ℕ} (hi : i < g.L t) : g.cp t i < D := by
  have hDpos : 0 < D := by
    unfold D
    omega
  unfold Grid.cp
  split
  · omega
  · rename_i hi_ne
    have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_ne
    have h_idx_lt : i - 1 < g.L t := by omega
    -- cellPts t is SortedLT (strictly increasing)
    have h_sorted : (g.cellPts t).SortedLT := by
      unfold Grid.cellPts
      rw [List.sortedLT_iff_pairwise]
      apply List.Pairwise.filter
      rw [← List.sortedLT_iff_pairwise]
      exact List.sortedLT_range _
    have h_strictMono : StrictMono (g.cellPts t).get :=
      List.SortedLT.strictMono_get h_sorted
    -- J is in cellPts t (so the list is nonempty)
    have h_mem_J : g.J ∈ g.cellPts t := by
      unfold Grid.cellPts
      apply List.mem_filter.mpr
      constructor
      · apply List.mem_range.mpr; omega
      · simp
    have h_ne : g.cellPts t ≠ [] := by
      intro h; rw [h] at h_mem_J; exact (List.not_mem_nil (a := g.J)) h_mem_J
    -- All elements of cellPts t are ≤ g.J (since they come from range (g.J+1))
    have h_le_J : ∀ x ∈ g.cellPts t, x ≤ g.J := by
      intro x hx
      unfold Grid.cellPts at hx
      rcases List.mem_filter.1 hx with ⟨hx_range, _⟩
      have hx_lt : x < g.J + 1 := List.mem_range.1 hx_range
      omega
    -- The last element is ≤ g.J
    have h_len_eq : (g.cellPts t).length = g.L t := rfl
    have h_lt_len_last : g.L t - 1 < (g.cellPts t).length := by
      rw [h_len_eq]
      have h_pos : 0 < g.L t := by
        rw [← h_len_eq]
        exact List.length_pos_of_ne_nil h_ne
      omega
    have h_last_le_J : (g.cellPts t).get ⟨g.L t - 1, h_lt_len_last⟩ ≤ g.J :=
      h_le_J _ (List.getElem_mem h_lt_len_last)
    -- Now prove (cellPts t).getD (i-1) 0 < g.J
    have h_lt_J : (g.cellPts t).getD (i - 1) 0 < g.J := by
      have h_idx_lt_len : i - 1 < (g.cellPts t).length := by
        unfold Grid.L at h_idx_lt
        exact h_idx_lt
      -- Convert getD to get
      rw [List.getD_eq_getElem (g.cellPts t) 0 h_idx_lt_len]
      -- We know i-1 < g.L t - 1 because i < g.L t and i > 0
      have h_idx_lt_last : i - 1 < g.L t - 1 := by omega
      -- Convert to Fin
      let idx_i : Fin (g.cellPts t).length := ⟨i - 1, h_idx_lt_len⟩
      let idx_last : Fin (g.cellPts t).length := ⟨g.L t - 1, h_lt_len_last⟩
      have h_lt_fin : idx_i < idx_last :=
        Fin.mk_lt_mk.mpr h_idx_lt_last
      -- Now use strict monotonicity
      have h_val_lt : (g.cellPts t).get idx_i < (g.cellPts t).get idx_last :=
        h_strictMono h_lt_fin
      -- So (cellPts t).get idx_i < g.J
      exact lt_of_lt_of_le h_val_lt h_last_le_J
    -- Now use h_lt_J to show cp t i < D
    unfold Grid.pt
    rw [if_pos h_lt_J]
    have hgpt_all : g.gpt.all (· < D) = true := by
      unfold Grid.ok at hg
      simp at hg
      rw [List.all_eq_true]
      intro x hx
      have hx_lt_D := hg.1.1.2 x hx
      simp [hx_lt_D]
    have h_all := (List.all_eq_true (l := g.gpt) (p := fun x => x < D)).mp hgpt_all
    have h_idx_lt_gpt_len : (g.cellPts t).getD (i - 1) 0 < g.gpt.length := by
      unfold Grid.J at h_lt_J
      exact h_lt_J
    have h_getD_eq : g.gpt.getD ((g.cellPts t).getD (i - 1) 0) 0 = g.gpt[((g.cellPts t).getD (i - 1) 0)] :=
      List.getD_eq_getElem g.gpt 0 h_idx_lt_gpt_len
    rw [h_getD_eq]
    have h_mem_gpt : g.gpt[((g.cellPts t).getD (i - 1) 0)] ∈ g.gpt :=
      List.getElem_mem h_idx_lt_gpt_len
    have h_lt_D := h_all _ h_mem_gpt
    simpa using h_lt_D

theorem pos_spec {t k : ℕ} (hk : k ≤ g.cnt t) :
    1 ≤ g.pos t k ∧ g.pos t k ≤ g.L t ∧ (g.cellPts t).getD (g.pos t k - 1) 0 = g.glob t k := by
  have hglob_mem : g.glob t k ∈ g.cellPts t := glob_mem_cellPts (g := g) hk
  have hmem := ((mem_cellPts (g := g) (t := t) (j := g.glob t k)).mp hglob_mem)
  rcases hmem with ⟨hglob_le_J, hfilter⟩
  have h_lt : g.glob t k < g.J + 1 := by omega
  have hp : (fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j) (g.glob t k) = true := by
    rcases hfilter with (h | h | h)
    · simp [h]
    · simp [h]
    · simp [h]
  have h_filter_idx := filterRange_idxOf (g.J + 1) (fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j) h_lt hp
  rcases h_filter_idx with ⟨h_idx_lt_len, h_getD⟩
  have hpos_eq : g.pos t k = ((g.cellPts t).idxOf (g.glob t k)) + 1 := rfl
  have hL_eq : g.L t = (g.cellPts t).length := rfl
  have h_sub : g.pos t k - 1 = (g.cellPts t).idxOf (g.glob t k) := by
    rw [hpos_eq, Nat.add_sub_cancel]
  refine ⟨?_, ?_, ?_⟩
  · -- 1 ≤ g.pos t k
    rw [hpos_eq]
    omega
  · -- g.pos t k ≤ g.L t
    rw [hpos_eq, hL_eq]
    have : (g.cellPts t).idxOf (g.glob t k) < (g.cellPts t).length := h_idx_lt_len
    omega
  · -- (g.cellPts t).getD (g.pos t k - 1) 0 = g.glob t k
    rw [h_sub]
    exact h_getD

theorem cp_pos {t k : ℕ} (hk : k ≤ g.cnt t) : g.cp t (g.pos t k) = g.pt (g.glob t k) := by
  have h := g.pos_spec hk
  rcases h with ⟨hpos, _, hget⟩
  have hne0 : g.pos t k ≠ 0 := by omega
  unfold Grid.cp
  simp [hne0]
  -- hget: (g.cellPts t).getD (g.pos t k - 1) 0 = g.glob t k
  -- goal: g.pt ((g.cellPts t)[g.pos t k - 1]?.getD 0) = g.pt (g.glob t k)
  simpa [List.getD] using congrArg g.pt hget

theorem pos_mono (hg : g.ok = true) {t k k' : ℕ} (h : k ≤ k') (hk' : k' ≤ g.cnt t) :
    g.pos t k ≤ g.pos t k' := by
  by_contra! H
  have hk : k ≤ g.cnt t := Nat.le_trans h hk'
  have hposk := (g.pos_spec hk).2.1
  have hposk' := (g.pos_spec hk').2.1
  have cp_lt : g.cp t (g.pos t k') < g.cp t (g.pos t k) :=
    g.cp_lt_cp hg H hposk
  have cp_eq : g.cp t (g.pos t k') = g.pt (g.glob t k') := g.cp_pos hk'
  have cp_eq' : g.cp t (g.pos t k) = g.pt (g.glob t k) := g.cp_pos hk
  rw [cp_eq, cp_eq'] at cp_lt
  have hpt : g.pt (g.glob t k) ≤ g.pt (g.glob t k') := (pt_glob_mono g hg t) h
  linarith

theorem le_pt_iff_of_cell (hg : g.ok = true) {t i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ g.L t) {j : ℕ}
    (hj : j ∈ g.cellPts t) {x : ℝ} (hxa : (g.cp t (i - 1) : ℝ) < x * D)
    (hxb : x * D ≤ g.cp t i) : x * D ≤ g.pt j ↔ g.cp t i ≤ g.pt j := by
  constructor
  · -- (→) x * D ≤ g.pt j → g.cp t i ≤ g.pt j
    intro hxptj
    set l := g.cellPts t with hl_def
    have hlen : i - 1 < l.length := by
      rw [hl_def]
      have : g.L t = (g.cellPts t).length := rfl
      omega
    have hj_lt_J1 : j < g.J + 1 := by
      rcases ((Grid.mem_cellPts g).mp hj) with ⟨hjJ, _⟩
      omega
    have hp_j : (fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j) j = true := by
      have : j ∈ l := hj
      rw [hl_def] at this
      exact (List.mem_filter.mp this).2
    have hcp_eq : g.cp t i = g.pt (l.getD (i - 1) 0) := by
      rw [g.cp_of_pos hi1, hl_def]
    rw [hcp_eq]
    set j0 := l.getD (i - 1) 0 with hj0_def
    by_cases h_j0_le_j : j0 ≤ j
    · exact g.pt_mono hg h_j0_le_j
    · have h_lt : j < j0 := by omega
      have h_not_or : ¬ (i - 1 = 0 ∨ l.getD (i - 2) 0 < j) := by
        intro h_or
        have h_le' := filterRange_gap (g.J + 1) (fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j)
          hlen
          hj_lt_J1
          hp_j
          h_or
        have h_j0_le_j' : j0 ≤ j := by
          rw [hj0_def, hl_def]
          exact h_le'
        omega
      have hi_ge2 : 1 ≤ i - 1 := by
        by_contra! hzero
        have hzero' : i - 1 = 0 := by omega
        apply h_not_or
        left; exact hzero'
      have h_j_le : j ≤ l.getD (i - 2) 0 := by
        by_contra! hlt'
        apply h_not_or
        right; exact hlt'
      have h_pt_j_le : g.pt j ≤ g.pt (l.getD (i - 2) 0) := g.pt_mono hg h_j_le
      have h_cp_pred_eq : g.cp t (i - 1) = g.pt (l.getD (i - 2) 0) := by
        rw [g.cp_of_pos hi_ge2, hl_def]
        have h_sub : (i - 1) - 1 = i - 2 := by omega
        rw [h_sub]
      rw [← h_cp_pred_eq] at h_pt_j_le
      have h_pt_j_le' : (g.pt j : ℝ) ≤ (g.cp t (i - 1) : ℝ) := by exact_mod_cast h_pt_j_le
      have hxptj' : x * (D : ℝ) ≤ (g.pt j : ℝ) := hxptj
      linarith
  · -- (←) g.cp t i ≤ g.pt j → x * D ≤ g.pt j
    intro hcpij
    have hcpij' : (g.cp t i : ℝ) ≤ (g.pt j : ℝ) := by exact_mod_cast hcpij
    exact le_trans hxb hcpij'

theorem lt_iff_pos_lt (hg : g.ok = true) {t i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ g.L t) {k : ℕ}
    (hk : k ≤ g.cnt t) {x : ℝ} (hxa : (g.cp t (i - 1) : ℝ) < x * D)
    (hxb : x * D ≤ g.cp t i) : (g.pt (g.glob t k) : ℝ) < x * D ↔ g.pos t k < i := by
  have hj : g.glob t k ∈ g.cellPts t := glob_mem_cellPts g hk
  have h_cell := le_pt_iff_of_cell g hg hi1 hiL hj hxa hxb
  have h_pos_spec := pos_spec g hk
  rcases h_pos_spec with ⟨h_pos1, h_posL, _⟩
  have h_pt_eq : (g.cp t (g.pos t k) : ℝ) = (g.pt (g.glob t k) : ℝ) := by
    simpa using congrArg (fun n : ℕ => (n : ℝ)) (cp_pos g hk)
  have h_iff : (g.cp t (g.pos t k) : ℝ) < (g.cp t i : ℝ) ↔ g.pos t k < i := by
    constructor
    · intro h_lt
      by_contra! h_ge
      have h_cp_le : g.cp t i ≤ g.cp t (g.pos t k) := cp_mono g hg h_ge h_posL
      have h_le' : (g.cp t i : ℝ) ≤ (g.cp t (g.pos t k) : ℝ) := by exact_mod_cast h_cp_le
      linarith
    · intro h_lt_pos
      have h_cp_lt : g.cp t (g.pos t k) < g.cp t i := cp_lt_cp g hg h_lt_pos hiL
      exact_mod_cast h_cp_lt
  have h_not_iff := h_cell.not
  constructor
  · intro h_lt_pt
    have h_not_A : ¬ (x * D ≤ (g.pt (g.glob t k) : ℝ)) := by linarith
    have h_not_B_nat : ¬ (g.cp t i ≤ g.pt (g.glob t k)) := h_not_iff.mp h_not_A
    have h_lt_cp_nat : g.pt (g.glob t k) < g.cp t i := Nat.lt_of_not_ge h_not_B_nat
    have h_lt_cp : (g.pt (g.glob t k) : ℝ) < (g.cp t i : ℝ) := by exact_mod_cast h_lt_cp_nat
    rw [← h_pt_eq] at h_lt_cp
    exact h_iff.mp h_lt_cp
  · intro h_lt_pos
    have h_lt_cp : (g.cp t (g.pos t k) : ℝ) < (g.cp t i : ℝ) := h_iff.mpr h_lt_pos
    rw [h_pt_eq] at h_lt_cp
    have h_not_B : ¬ ((g.cp t i : ℝ) ≤ (g.pt (g.glob t k) : ℝ)) := by linarith
    have h_not_B_nat : ¬ (g.cp t i ≤ g.pt (g.glob t k)) := by
      intro h; apply h_not_B; exact_mod_cast h
    have h_not_A : ¬ (x * D ≤ (g.pt (g.glob t k) : ℝ)) := h_not_iff.mpr h_not_B_nat
    linarith

theorem ceilR_of_cell (hg : g.ok = true) {t i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ g.L t) {x : ℝ}
    (hxa : (g.cp t (i - 1) : ℝ) < x * D) (hxb : x * D ≤ g.cp t i) :
    g.ceilR (t + 1) x = g.nxt t i := by
  set j0 := (g.cellPts t).getD (i - 1) 0 with hj0
  have hcp_eq : g.cp t i = g.pt j0 := by
    rw [hj0]
    exact g.cp_of_pos hi1
  have hnxt_eq : g.nxt t i = g.ceilG (t + 1) j0 := by
    unfold Grid.nxt
    rw [hj0]
  have hDpos_nat : 0 < D := Robbins.Cert.D_pos
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast hDpos_nat
  have hcpD : g.cp t i ≤ D := g.cp_le_D hg t i
  have hcpD' : (g.cp t i : ℝ) ≤ (D : ℝ) := by exact_mod_cast hcpD
  have hx1 : x ≤ 1 := by
    nlinarith
  have hk_le : g.ceilG (t + 1) j0 ≤ g.cnt (t + 1) := g.ceilG_le_cnt (t + 1) j0
  rw [hnxt_eq]
  apply ((g.ceilR_eq_iff (t + 1) hx1 hk_le).mpr ?_)
  constructor
  · -- first goal: x * D ≤ g.pt (g.glob (t + 1) (g.ceilG (t + 1) j0))
    have hmem : j0 ∈ g.cellPts t := by
      rw [hj0]
      have hlen_eq : (g.cellPts t).length = g.L t := rfl
      have hlt : i - 1 < (g.cellPts t).length := by
        rw [hlen_eq]
        omega
      rw [List.getD_eq_getElem (g.cellPts t) 0 hlt]
      exact List.get_mem (g.cellPts t) ⟨i - 1, hlt⟩
    have hj0_le_J : j0 ≤ g.J := ((g.mem_cellPts).mp hmem).1
    have hceilG_spec := g.ceilG_spec hg (t + 1) hj0_le_J
    rcases hceilG_spec with ⟨hle_pt, hlt_pt⟩
    have hx_le_pt_j0 : x * (D : ℝ) ≤ (g.pt j0 : ℝ) := by
      have hle : g.cp t i ≤ g.pt j0 := by
        rw [hcp_eq]
      exact ((g.le_pt_iff_of_cell hg hi1 hiL hmem hxa hxb).mpr hle)
    exact le_trans hx_le_pt_j0 (by exact_mod_cast hle_pt)
  · -- second goal: ∀ k' < g.ceilG (t + 1) j0, (g.pt (g.glob (t + 1) k') : ℝ) < x * D
    intro k' hk'
    have hk'_le_cnt : k' ≤ g.cnt (t + 1) := by
      have hceilG_le_cnt : g.ceilG (t + 1) j0 ≤ g.cnt (t + 1) := g.ceilG_le_cnt (t + 1) j0
      omega
    have hmem' : g.glob (t + 1) k' ∈ g.cellPts t :=
      g.glob_succ_mem_cellPts hk'_le_cnt
    have hle_iff := g.le_pt_iff_of_cell hg hi1 hiL hmem' hxa hxb
    have hlt_nat : g.pt (g.glob (t + 1) k') < g.pt j0 := by
      have hmem : j0 ∈ g.cellPts t := by
        rw [hj0]
        have hlen_eq : (g.cellPts t).length = g.L t := rfl
        have hlt : i - 1 < (g.cellPts t).length := by
          rw [hlen_eq]
          omega
        rw [List.getD_eq_getElem (g.cellPts t) 0 hlt]
        exact List.get_mem (g.cellPts t) ⟨i - 1, hlt⟩
      have hj0_le_J : j0 ≤ g.J := ((g.mem_cellPts).mp hmem).1
      have hceilG_spec := g.ceilG_spec hg (t + 1) hj0_le_J
      rcases hceilG_spec with ⟨_, hlt_pt⟩
      exact hlt_pt k' hk'
    have hlt_real : (g.pt (g.glob (t + 1) k') : ℝ) < (g.pt j0 : ℝ) := by exact_mod_cast hlt_nat
    have hlt_real' : (g.pt (g.glob (t + 1) k') : ℝ) < (g.cp t i : ℝ) := by
      simpa [hcp_eq] using hlt_real
    have h_not_le_nat : ¬ (g.cp t i ≤ g.pt (g.glob (t + 1) k')) := by
      rw [← hcp_eq] at hlt_nat
      omega
    have h_not_xD_le : ¬ (x * (D : ℝ) ≤ (g.pt (g.glob (t + 1) k') : ℝ)) :=
      mt hle_iff.mp h_not_le_nat
    exact lt_of_not_ge h_not_xD_le

theorem exists_cell (t : ℕ) {i0 : ℕ} {x : ℝ} (hx0 : 0 < x)
    (hx : x * D ≤ g.cp t i0) :
    ∃ i, 1 ≤ i ∧ i ≤ i0 ∧ (g.cp t (i - 1) : ℝ) < x * D ∧ x * D ≤ g.cp t i := by
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast D_pos
  have hcp0 : (g.cp t 0 : ℝ) = 0 := by exact_mod_cast g.cp_zero t
  have hxDpos : 0 < x * (D : ℝ) := by
    nlinarith
  let S : ℕ → Prop := λ i => i ≤ i0 ∧ x * (D : ℝ) ≤ (g.cp t i : ℝ)
  have hS_nonempty : ∃ i, S i := by
    refine ⟨i0, le_rfl, hx⟩
  let i := Nat.find hS_nonempty
  have hi_spec : S i := Nat.find_spec hS_nonempty
  have hi_min : ∀ j, j < i → ¬ S j := λ j hj => Nat.find_min hS_nonempty hj
  have hi_pos : 1 ≤ i := by
    by_contra! hlt
    have hi0 : i = 0 := by omega
    rw [hi0] at hi_spec
    rcases hi_spec with ⟨_, hle⟩
    rw [hcp0] at hle
    linarith
  have h_lt : i - 1 < i := by
    omega
  have h_not_S : ¬ ((i - 1 ≤ i0) ∧ x * (D : ℝ) ≤ (g.cp t (i - 1) : ℝ)) :=
    hi_min (i - 1) h_lt
  have h_le_i0 : i - 1 ≤ i0 := by
    omega
  have h_lt_cp : ¬ (x * (D : ℝ) ≤ (g.cp t (i - 1) : ℝ)) := by
    intro hle
    apply h_not_S
    exact ⟨h_le_i0, hle⟩
  refine ⟨i, hi_pos, hi_spec.1, lt_of_not_ge h_lt_cp, hi_spec.2⟩

end Grid

end Robbins.Cert
