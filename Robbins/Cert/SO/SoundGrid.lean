import Robbins.Cert.SoundGrid
import Robbins.Cert.SO.Spec

/-!
# The grid facts of the second-order soundness: points over a denominator `D`

The lemmas of Robbins/Cert/SoundGrid.lean that depend on the denominator (the values `pt`, the cell
endpoints `cp`, `ceil_t` on values and the data conditions), for `SO.pt D`, `SO.cp D`, `SO.ceilR D` and
`SO.ok D` of Robbins/Cert/SO/Spec.lean, with the same proofs; prefix `so_`. The lemmas on indices
(windows, `glob`, `cellPts`, `pos`, `ceilG`) do not depend on `D` and are used as they are.
-/

namespace Robbins.Cert

namespace Grid

variable (g : Grid) (D : ℕ)

/-! ## The data conditions and the point values -/

theorem so_ok_two_le_n (hg : SO.ok D g = true) : 2 ≤ g.n := by
  simp only [SO.ok, Bool.and_eq_true, decide_eq_true_eq] at hg
  rcases hg with ⟨⟨⟨⟨⟨⟨_, hn⟩, _⟩, _⟩, _⟩, _⟩, _⟩
  exact hn

theorem so_ok_gpt (hg : SO.ok D g = true) {i : ℕ} (hi : i < g.J) :
    0 < g.gpt.getD i 0 ∧ g.gpt.getD i 0 < D := by
  have hi' : i < g.gpt.length := hi
  have h_all : (((((1 ≤ g.m ∧ 2 ≤ g.n) ∧ strictInc 0 g.gpt = true) ∧ ∀ x ∈ g.gpt, x < D) ∧
      g.start.length = g.n) ∧ nondec 0 g.start = true) ∧ ∀ x < g.n, 1 ≤ g.cnt (x + 1) := by
    unfold SO.ok at hg
    simpa [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] using hg
  rcases h_all with ⟨⟨⟨⟨⟨⟨hm, hn⟩, hstrict⟩, hall⟩, hlen⟩, hnondec⟩, -⟩
  have hpos := strictInc_getD 0 g.gpt hstrict hi'
  rcases hpos with ⟨hleftpos, _⟩
  have hmem : g.gpt.getD i 0 ∈ g.gpt := by
    rw [List.getD_eq_getElem g.gpt 0 hi']
    exact List.getElem_mem hi'
  have hright' : g.gpt.getD i 0 < D := by
    have := hall (g.gpt.getD i 0) hmem
    simpa using this
  exact And.intro hleftpos hright'

/-- `D > 0` under the data conditions (`cnt_1 ≥ 1`, so `gpt[0] < D`). -/
theorem so_D_pos (hg : SO.ok D g = true) : 0 < D := by
  have h_all : (((((1 ≤ g.m ∧ 2 ≤ g.n) ∧ strictInc 0 g.gpt = true) ∧ ∀ x ∈ g.gpt, x < D) ∧
      g.start.length = g.n) ∧ nondec 0 g.start = true) ∧ ∀ x < g.n, 1 ≤ g.cnt (x + 1) := by
    unfold SO.ok at hg
    simpa [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] using hg
  have h1 : 1 ≤ g.cnt 1 := h_all.2 0 (by omega)
  have hJ : 0 < g.J := by have := g.s_add_cnt_le 1; omega
  have := g.so_ok_gpt D hg hJ
  omega

theorem so_ok_gpt_lt (hg : SO.ok D g = true) {i j : ℕ} (hij : i < j) (hj : j < g.J) :
    g.gpt.getD i 0 < g.gpt.getD j 0 := by
  have hg' : strictInc 0 g.gpt = true := by
    simp [SO.ok, Bool.and_eq_true] at hg
    exact hg.1.1.1.1.2
  have hi : i < g.gpt.length := by
    have : g.J = g.gpt.length := rfl
    omega
  have h := strictInc_getD 0 g.gpt hg' hi
  exact h.right j hij (by
    have : g.J = g.gpt.length := rfl
    omega)

theorem so_pt_of_lt {j : ℕ} (hj : j < g.J) : SO.pt D g j = g.gpt.getD j 0 := by
  unfold SO.pt
  rw [ite_eq_left hj]

theorem so_pt_of_ge {j : ℕ} (hj : g.J ≤ j) : SO.pt D g j = D := by
  unfold SO.pt
  rw [ite_eq_right (not_lt.mpr hj)]

theorem so_pt_pos (hg : SO.ok D g = true) (j : ℕ) : 0 < SO.pt D g j := by
  have hD : 0 < D := g.so_D_pos D hg
  by_cases hj : j < g.J
  · have hpos := (g.so_ok_gpt D hg hj).1
    rw [g.so_pt_of_lt D hj]
    exact hpos
  · have hle : g.J ≤ j := Nat.le_of_not_lt hj
    rw [g.so_pt_of_ge D hle]
    exact hD

theorem so_pt_le_D (hg : SO.ok D g = true) (j : ℕ) : SO.pt D g j ≤ D := by
  by_cases hj : j < g.J
  · rw [g.so_pt_of_lt D hj]
    exact Nat.le_of_lt ((g.so_ok_gpt D hg hj).2)
  · rw [g.so_pt_of_ge D (by omega)]

theorem so_pt_lt_D (hg : SO.ok D g = true) {j : ℕ} (hj : j < g.J) : SO.pt D g j < D := by
  rw [so_pt_of_lt g D hj]
  exact (so_ok_gpt g D hg hj).right

theorem so_pt_lt_pt (hg : SO.ok D g = true) {i j : ℕ} (hij : i < j) (hj : j ≤ g.J) : SO.pt D g i < SO.pt D g j := by
  by_cases hj' : j < g.J
  · have hi_lt_J : i < g.J := lt_trans hij hj'
    rw [g.so_pt_of_lt D hi_lt_J, g.so_pt_of_lt D hj']
    exact g.so_ok_gpt_lt D hg hij hj'
  · have hj_eq : j = g.J := by omega
    rw [hj_eq]
    rw [g.so_pt_of_ge D (le_refl g.J)]
    have hi_lt_J : i < g.J := by
      rw [hj_eq] at hij
      exact hij
    exact g.so_pt_lt_D D hg hi_lt_J

theorem so_pt_mono (hg : SO.ok D g = true) : Monotone (SO.pt D g) := by
  intro i j hij
  by_cases hj : g.J ≤ j
  · rw [g.so_pt_of_ge D hj]
    exact g.so_pt_le_D D hg i
  · have hj' : j < g.J := Nat.lt_of_not_ge hj
    by_cases hij' : i < j
    · have h := g.so_pt_lt_pt D hg hij' (Nat.le_of_lt hj')
      exact Nat.le_of_lt h
    · have heq : i = j := Nat.le_antisymm hij (Nat.le_of_not_gt hij')
      rw [heq]

/-! ## The local points of `G_t` -/

theorem so_pt_glob_lt (hg : SO.ok D g = true) {t k k' : ℕ} (h : k < k') (hk' : k' ≤ g.cnt t) :
    SO.pt D g (g.glob t k) < SO.pt D g (g.glob t k') := by
  exact so_pt_lt_pt g D hg (glob_lt_glob g h hk') (glob_le_J g t k')

theorem so_pt_glob_mono (hg : SO.ok D g = true) (t : ℕ) : Monotone fun k => SO.pt D g (g.glob t k) := by
  intro k k' h
  exact g.so_pt_mono D hg (g.glob_mono t h)

/-! ## `ceil_t` on global indices and on values -/

theorem so_ceilG_spec (hg : SO.ok D g = true) (t : ℕ) {j : ℕ} (hj : j ≤ g.J) :
    SO.pt D g j ≤ SO.pt D g (g.glob t (g.ceilG t j)) ∧ ∀ k < g.ceilG t j, SO.pt D g (g.glob t k) < SO.pt D g j := by
  have hsc : (g.wt t).s + g.cnt t ≤ g.J := g.s_add_cnt_le t
  have hmono : Monotone (SO.pt D g) := g.so_pt_mono D hg
  have hpt_le_D : ∀ j, SO.pt D g j ≤ D := fun j => g.so_pt_le_D D hg j
  have hpt_of_ge : ∀ {j}, g.J ≤ j → SO.pt D g j = D := fun h => g.so_pt_of_ge D h
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
    have hfirst : SO.pt D g j ≤ SO.pt D g (g.glob t ((g.wt t).cnt)) := by
      have hglob_c : g.glob t ((g.wt t).cnt) = g.J := hglob_ge (le_refl _)
      rw [hglob_c]
      rw [hpt_of_ge (le_refl g.J)]
      exact hpt_le_D j
    have hsecond : ∀ k < (g.wt t).cnt, SO.pt D g (g.glob t k) < SO.pt D g j := by
      intro k hk
      have hglob_k_lt_j : g.glob t k < j := by
        rw [hglob_eq hk, hJ]
        omega
      exact g.so_pt_lt_pt D hg hglob_k_lt_j hj
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
      have hfirst : SO.pt D g j ≤ SO.pt D g (g.glob t ((g.wt t).cnt)) := by
        have hcnt_le_c : (g.wt t).cnt ≤ (g.wt t).cnt := le_refl _
        have hglob_c : g.glob t ((g.wt t).cnt) = g.J := hglob_ge hcnt_le_c
        rw [hglob_c]
        rw [hpt_of_ge (le_refl g.J)]
        exact hpt_le_D j
      have hsecond : ∀ k < (g.wt t).cnt, SO.pt D g (g.glob t k) < SO.pt D g j := by
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
        have hfirst : SO.pt D g j ≤ SO.pt D g (g.glob t 0) := by
          have hpos : 0 < (g.wt t).cnt := Nat.pos_of_ne_zero hc0
          have hglob_0 : g.glob t 0 = (g.wt t).s := by
            unfold Grid.glob
            have hpos' : 0 < g.cnt t := hpos
            simp [hpos']
          rw [hglob_0]
          have hjs' : j ≤ (g.wt t).s := by omega
          exact hmono hjs'
        have hsecond : ∀ k < 0, SO.pt D g (g.glob t k) < SO.pt D g j := by
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
          have hfirst : SO.pt D g j ≤ SO.pt D g (g.glob t (j - (g.wt t).s)) := by
            have h_sub_lt : j - (g.wt t).s < (g.wt t).cnt := by omega
            have hglob_sub : g.glob t (j - (g.wt t).s) = (g.wt t).s + (j - (g.wt t).s) := by
              unfold Grid.glob
              have h_sub_lt' : j - (g.wt t).s < g.cnt t := h_sub_lt
              simp [h_sub_lt']
            rw [hglob_sub]
            have : (g.wt t).s + (j - (g.wt t).s) = j := by omega
            rw [this]
          have hsecond : ∀ k < j - (g.wt t).s, SO.pt D g (g.glob t k) < SO.pt D g j := by
            intro k hk
            have hk_lt_c : k < (g.wt t).cnt := by omega
            have hglob_k : g.glob t k = (g.wt t).s + k := hglob_eq hk_lt_c
            rw [hglob_k]
            have h_lt_j : (g.wt t).s + k < j := by omega
            exact g.so_pt_lt_pt D hg h_lt_j hj
          exact And.intro hfirst hsecond
        · -- ceilG = (g.wt t).cnt
          have hceil : (if j == g.J || (g.wt t).cnt == 0 then (g.wt t).cnt
            else if j < (g.wt t).s then 0
            else if j < (g.wt t).s + (g.wt t).cnt then j - (g.wt t).s
            else (g.wt t).cnt) = (g.wt t).cnt := by
            simp [hJ, hc0, hjs, hjsc]
          rw [hceil]
          have hfirst : SO.pt D g j ≤ SO.pt D g (g.glob t ((g.wt t).cnt)) := by
            have hglob_c : g.glob t ((g.wt t).cnt) = g.J := hglob_ge (le_refl _)
            rw [hglob_c]
            rw [hpt_of_ge (le_refl g.J)]
            exact hpt_le_D j
          have hsecond : ∀ k < (g.wt t).cnt, SO.pt D g (g.glob t k) < SO.pt D g j := by
            intro k hk
            have hglob_k : g.glob t k = (g.wt t).s + k := hglob_eq hk
            rw [hglob_k]
            have h_lt_j : (g.wt t).s + k < j := by
              have : (g.wt t).s + k < (g.wt t).s + (g.wt t).cnt := by omega
              omega
            exact g.so_pt_lt_pt D hg h_lt_j hj
          exact And.intro hfirst hsecond

theorem so_ceilR_le_cnt (t : ℕ) (y : ℝ) : SO.ceilR D g t y ≤ g.cnt t := by
  unfold SO.ceilR
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact le_rfl

theorem so_ceilR_eq_iff (hD : 0 < D) (t : ℕ) {y : ℝ} (hy : y ≤ 1) {k : ℕ} (hk : k ≤ g.cnt t) :
    SO.ceilR D g t y = k ↔
      y * D ≤ SO.pt D g (g.glob t k) ∧ ∀ k' < k, (SO.pt D g (g.glob t k') : ℝ) < y * D := by
  classical
  have hDpos : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hex : ∃ k', k' ≤ g.cnt t ∧ y * (D : ℝ) ≤ (SO.pt D g (g.glob t k') : ℝ) := by
    refine ⟨g.cnt t, le_rfl, ?_⟩
    have hglob : g.glob t (g.cnt t) = g.J := g.glob_of_ge (le_refl _)
    have hpt : SO.pt D g g.J = D := g.so_pt_of_ge D (le_refl _)
    calc
      y * (D : ℝ) ≤ 1 * (D : ℝ) := by nlinarith
      _ = (D : ℝ) := by ring
      _ = (SO.pt D g g.J : ℝ) := by simp [hpt]
      _ = (SO.pt D g (g.glob t (g.cnt t)) : ℝ) := by rw [hglob]
  unfold SO.ceilR
  rw [dite_eq_left hex]
  rw [Nat.find_eq_iff hex]
  constructor
  · rintro ⟨⟨hle, hge⟩, hforall⟩
    refine ⟨hge, ?_⟩
    intro k' hk'
    have hk'cnt : k' ≤ g.cnt t := Nat.le_trans (Nat.le_of_lt hk') hk
    have hnot := hforall k' hk'
    have hnot' : ¬ (y * (D : ℝ) ≤ (SO.pt D g (g.glob t k') : ℝ)) := by
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

theorem so_le_pt_ceilR (hD : 0 < D) (t : ℕ) {y : ℝ} (hy : y ≤ 1) : y * D ≤ SO.pt D g (g.glob t (SO.ceilR D g t y)) := by
  have h_exists : ∃ k, k ≤ g.cnt t ∧ y * (D : ℝ) ≤ (SO.pt D g (g.glob t k) : ℝ) := by
    refine ⟨g.cnt t, le_rfl, ?_⟩
    have hglob : g.glob t (g.cnt t) = g.J := glob_of_ge g le_rfl
    have hpt : SO.pt D g (g.J) = D := so_pt_of_ge g D le_rfl
    have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
    have hyD : y * (D : ℝ) ≤ (D : ℝ) := by
      nlinarith
    calc
      y * (D : ℝ) ≤ (D : ℝ) := hyD
      _ = (SO.pt D g (g.J) : ℝ) := by rw [hpt]
      _ = (SO.pt D g (g.glob t (g.cnt t)) : ℝ) := by rw [hglob]
  unfold SO.ceilR
  rw [dite_eq_left h_exists]
  exact (Nat.find_spec h_exists).2

theorem so_ceilR_mono (t : ℕ) : Monotone (SO.ceilR D g t) := by
  intro y y' h
  unfold SO.ceilR
  split
  · rename_i h
    have hy_spec := Nat.find_spec h
    rcases hy_spec with ⟨hle, hy_pt⟩
    split
    · rename_i h'
      have hy'_spec := Nat.find_spec h'
      have hyD : y * (D : ℝ) ≤ y' * (D : ℝ) := by
        nlinarith
      have hy_pt' : y * (D : ℝ) ≤ SO.pt D g (g.glob t (Nat.find h')) := by
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
      have hy_pt' : y * (D : ℝ) ≤ SO.pt D g (g.glob t (Nat.find h')) := by
        linarith
      exfalso
      exact h ⟨Nat.find h', hle', hy_pt'⟩
    · rfl

theorem so_ceilR_of_nonpos (hD : 0 < D) (t : ℕ) {y : ℝ} (hy : y ≤ 0) : SO.ceilR D g t y = 0 := by
  have hDpos : 0 < D := hD
  have hDposℝ : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hyD : y * (D : ℝ) ≤ 0 := by
    nlinarith
  have hpt_nonneg (k : ℕ) : (0 : ℝ) ≤ (SO.pt D g (g.glob t k) : ℝ) := by
    exact_mod_cast Nat.zero_le (SO.pt D g (g.glob t k))
  have h_exists : ∃ k, k ≤ g.cnt t ∧ y * (D : ℝ) ≤ (SO.pt D g (g.glob t k) : ℝ) := by
    refine ⟨0, Nat.zero_le _, ?_⟩
    have h0 : (0 : ℝ) ≤ (SO.pt D g (g.glob t 0) : ℝ) := hpt_nonneg 0
    nlinarith
  unfold SO.ceilR
  split_ifs
  · -- Goal: Nat.find h_exists = 0
    -- Using Nat.find_eq_zero: Nat.find h = 0 ↔ p 0
    rw [Nat.find_eq_zero]
    -- Goal: 0 ≤ g.cnt t ∧ y * (D : ℝ) ≤ (SO.pt D g (g.glob t 0) : ℝ)
    refine ⟨Nat.zero_le _, ?_⟩
    have h0pt : (0 : ℝ) ≤ (SO.pt D g (g.glob t 0) : ℝ) := hpt_nonneg 0
    nlinarith

theorem so_ceilR_one (hg : SO.ok D g = true) (t : ℕ) : SO.ceilR D g t 1 = g.cnt t := by
  have hD : 0 < D := g.so_D_pos D hg
  have h_one_le_one : (1 : ℝ) ≤ 1 := le_rfl
  have h_cnt_le : g.cnt t ≤ g.cnt t := le_rfl
  rw [g.so_ceilR_eq_iff D hD t h_one_le_one h_cnt_le]
  have h_glob_cnt : g.glob t (g.cnt t) = g.J := by
    simp [Grid.glob]
  have h_pt_glob_cnt : (SO.pt D g (g.glob t (g.cnt t)) : ℝ) = (D : ℝ) := by
    rw [h_glob_cnt]
    have h_pt_J : SO.pt D g g.J = D := g.so_pt_of_ge D (le_rfl : g.J ≤ g.J)
    simp [h_pt_J]
  constructor
  · rw [h_pt_glob_cnt]
    simp
  · intro k' hk'
    have h_glob_lt_J : g.glob t k' < g.J := g.glob_lt_J hk'
    have h_pt_lt_D : SO.pt D g (g.glob t k') < D := g.so_pt_lt_D D hg h_glob_lt_J
    have h_cast : (SO.pt D g (g.glob t k') : ℝ) < (D : ℝ) := by exact_mod_cast h_pt_lt_D
    calc
      (SO.pt D g (g.glob t k') : ℝ) < (D : ℝ) := h_cast
      _ = (1 : ℝ) * (D : ℝ) := by simp

theorem so_ceilR_pt (hg : SO.ok D g = true) (t : ℕ) {j : ℕ} (hj : j ≤ g.J) :
    SO.ceilR D g t ((SO.pt D g j : ℝ) / D) = g.ceilG t j := by
  have hD : 0 < D := g.so_D_pos D hg
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast hD
  have hy_le_one : (SO.pt D g j : ℝ) / (D : ℝ) ≤ 1 := by
    have hpt_le_D : (SO.pt D g j : ℝ) ≤ (D : ℝ) := by exact mod_cast g.so_pt_le_D D hg j
    exact (div_le_one hDpos).mpr hpt_le_D
  have hk_le_cnt : g.ceilG t j ≤ g.cnt t := g.ceilG_le_cnt t j
  refine ((g.so_ceilR_eq_iff D hD t hy_le_one hk_le_cnt).mpr ?_)
  constructor
  · calc
      (SO.pt D g j : ℝ) / (D : ℝ) * (D : ℝ) = (SO.pt D g j : ℝ) := by
        field_simp [hDpos.ne.symm]
      _ ≤ (SO.pt D g (g.glob t (g.ceilG t j)) : ℝ) := by
        exact mod_cast (g.so_ceilG_spec D hg t hj).1
  · intro k' hk'
    have h_lt_nat : SO.pt D g (g.glob t k') < SO.pt D g j := (g.so_ceilG_spec D hg t hj).2 k' hk'
    have h_lt : (SO.pt D g (g.glob t k') : ℝ) < (SO.pt D g j : ℝ) := by exact mod_cast h_lt_nat
    calc
      (SO.pt D g (g.glob t k') : ℝ) < (SO.pt D g j : ℝ) := h_lt
      _ = ((SO.pt D g j : ℝ) / (D : ℝ)) * (D : ℝ) := by field_simp [hDpos.ne.symm]

theorem so_measurable_ceilR (t : ℕ) : Measurable (SO.ceilR D g t) := by
  have h_mono : Monotone (SO.ceilR D g t) := g.so_ceilR_mono D t
  exact h_mono.measurable

/-! ## The cells of `P_t` -/

theorem so_cp_zero (t : ℕ) : SO.cp D g t 0 = 0 := by
  unfold SO.cp; simp

theorem so_cp_of_pos {t i : ℕ} (hi : 1 ≤ i) : SO.cp D g t i = SO.pt D g ((g.cellPts t).getD (i - 1) 0) := by
  simp [SO.cp, show i ≠ 0 from by omega]

theorem so_cp_L (t : ℕ) : SO.cp D g t (g.L t) = D := by
  have hL := g.one_le_L t
  have hcell := g.cellPts_last t
  have hpt := g.so_pt_of_ge D (le_refl g.J)
  calc
    SO.cp D g t (g.L t) = SO.pt D g ((g.cellPts t).getD (g.L t - 1) 0) := by
      rw [g.so_cp_of_pos D hL]
    _ = SO.pt D g g.J := by rw [hcell]
    _ = D := hpt

theorem so_cp_le_D (hg : SO.ok D g = true) (t i : ℕ) : SO.cp D g t i ≤ D := by
  by_cases hi : i = 0
  · rw [hi, g.so_cp_zero D t]
    exact Nat.zero_le _
  · have hi_pos : 1 ≤ i := Nat.one_le_of_lt (Nat.pos_of_ne_zero hi)
    rw [g.so_cp_of_pos D hi_pos]
    exact g.so_pt_le_D D hg _

theorem so_cp_lt_cp (hg : SO.ok D g = true) {t i i' : ℕ} (h : i < i') (hi' : i' ≤ g.L t) :
    SO.cp D g t i < SO.cp D g t i' := by
  have hD : 0 < D := g.so_D_pos D hg
  unfold Grid.L Grid.cellPts at hi'
  have hi'_pos : 1 ≤ i' := by omega
  have hi'_lt_len : i' - 1 < ((List.range (g.J + 1)).filter fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j).length := by
    omega
  by_cases hi0 : i = 0
  · rw [hi0, g.so_cp_zero D t, g.so_cp_of_pos D hi'_pos]
    exact g.so_pt_pos D hg _
  · have hi_pos : 1 ≤ i := by omega
    rw [g.so_cp_of_pos D hi_pos, g.so_cp_of_pos D hi'_pos]
    have h_getD_lt : ((List.range (g.J + 1)).filter fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j).getD (i - 1) 0 <
        ((List.range (g.J + 1)).filter fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j).getD (i' - 1) 0 := by
      refine filterRange_getD_lt_getD (g.J + 1) (fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j) ?_ ?_
      · omega
      · exact hi'_lt_len
    have h_getD_mem : ((List.range (g.J + 1)).filter fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j).getD (i' - 1) 0 ≤ g.J := by
      have hmem := filterRange_getD_mem (g.J + 1) (fun j => j == g.J || g.inWin t j || g.inWin (t + 1) j) hi'_lt_len
      omega
    exact g.so_pt_lt_pt D hg h_getD_lt h_getD_mem

theorem so_cp_mono (hg : SO.ok D g = true) {t i i' : ℕ} (h : i ≤ i') (hi' : i' ≤ g.L t) :
    SO.cp D g t i ≤ SO.cp D g t i' := by
  rcases h.eq_or_lt with (rfl | hlt)
  · rfl
  · exact (g.so_cp_lt_cp D hg hlt hi').le

theorem so_cp_lt_D (hg : SO.ok D g = true) {t i : ℕ} (hi : i < g.L t) : SO.cp D g t i < D := by
  have hDpos : 0 < D := g.so_D_pos D hg
  unfold SO.cp
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
    unfold SO.pt
    rw [if_pos h_lt_J]
    have hgpt_all : g.gpt.all (· < D) = true := by
      unfold SO.ok at hg
      simp at hg
      rw [List.all_eq_true]
      intro x hx
      have hx_lt_D := hg.1.1.1.2 x hx
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

theorem so_cp_pos {t k : ℕ} (hk : k ≤ g.cnt t) : SO.cp D g t (g.pos t k) = SO.pt D g (g.glob t k) := by
  have h := g.pos_spec hk
  rcases h with ⟨hpos, _, hget⟩
  have hne0 : g.pos t k ≠ 0 := by omega
  unfold SO.cp
  simp [hne0]
  -- hget: (g.cellPts t).getD (g.pos t k - 1) 0 = g.glob t k
  -- goal: SO.pt D g ((g.cellPts t)[g.pos t k - 1]?.getD 0) = SO.pt D g (g.glob t k)
  simpa [List.getD] using congrArg (SO.pt D g) hget

theorem so_pos_mono (hg : SO.ok D g = true) {t k k' : ℕ} (h : k ≤ k') (hk' : k' ≤ g.cnt t) :
    g.pos t k ≤ g.pos t k' := by
  by_contra! H
  have hk : k ≤ g.cnt t := Nat.le_trans h hk'
  have hposk := (g.pos_spec hk).2.1
  have hposk' := (g.pos_spec hk').2.1
  have cp_lt : SO.cp D g t (g.pos t k') < SO.cp D g t (g.pos t k) :=
    g.so_cp_lt_cp D hg H hposk
  have cp_eq : SO.cp D g t (g.pos t k') = SO.pt D g (g.glob t k') := g.so_cp_pos D hk'
  have cp_eq' : SO.cp D g t (g.pos t k) = SO.pt D g (g.glob t k) := g.so_cp_pos D hk
  rw [cp_eq, cp_eq'] at cp_lt
  have hpt : SO.pt D g (g.glob t k) ≤ SO.pt D g (g.glob t k') := (so_pt_glob_mono g D hg t) h
  linarith

theorem so_le_pt_iff_of_cell (hg : SO.ok D g = true) {t i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ g.L t) {j : ℕ}
    (hj : j ∈ g.cellPts t) {x : ℝ} (hxa : (SO.cp D g t (i - 1) : ℝ) < x * D)
    (hxb : x * D ≤ SO.cp D g t i) : x * D ≤ SO.pt D g j ↔ SO.cp D g t i ≤ SO.pt D g j := by
  constructor
  · -- (→) x * D ≤ SO.pt D g j → SO.cp D g t i ≤ SO.pt D g j
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
    have hcp_eq : SO.cp D g t i = SO.pt D g (l.getD (i - 1) 0) := by
      rw [g.so_cp_of_pos D hi1, hl_def]
    rw [hcp_eq]
    set j0 := l.getD (i - 1) 0 with hj0_def
    by_cases h_j0_le_j : j0 ≤ j
    · exact g.so_pt_mono D hg h_j0_le_j
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
      have h_pt_j_le : SO.pt D g j ≤ SO.pt D g (l.getD (i - 2) 0) := g.so_pt_mono D hg h_j_le
      have h_cp_pred_eq : SO.cp D g t (i - 1) = SO.pt D g (l.getD (i - 2) 0) := by
        rw [g.so_cp_of_pos D hi_ge2, hl_def]
        have h_sub : (i - 1) - 1 = i - 2 := by omega
        rw [h_sub]
      rw [← h_cp_pred_eq] at h_pt_j_le
      have h_pt_j_le' : (SO.pt D g j : ℝ) ≤ (SO.cp D g t (i - 1) : ℝ) := by exact_mod_cast h_pt_j_le
      have hxptj' : x * (D : ℝ) ≤ (SO.pt D g j : ℝ) := hxptj
      linarith
  · -- (←) SO.cp D g t i ≤ SO.pt D g j → x * D ≤ SO.pt D g j
    intro hcpij
    have hcpij' : (SO.cp D g t i : ℝ) ≤ (SO.pt D g j : ℝ) := by exact_mod_cast hcpij
    exact le_trans hxb hcpij'

theorem so_lt_iff_pos_lt (hg : SO.ok D g = true) {t i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ g.L t) {k : ℕ}
    (hk : k ≤ g.cnt t) {x : ℝ} (hxa : (SO.cp D g t (i - 1) : ℝ) < x * D)
    (hxb : x * D ≤ SO.cp D g t i) : (SO.pt D g (g.glob t k) : ℝ) < x * D ↔ g.pos t k < i := by
  have hj : g.glob t k ∈ g.cellPts t := glob_mem_cellPts g hk
  have h_cell := so_le_pt_iff_of_cell g D hg hi1 hiL hj hxa hxb
  have h_pos_spec := pos_spec g hk
  rcases h_pos_spec with ⟨h_pos1, h_posL, _⟩
  have h_pt_eq : (SO.cp D g t (g.pos t k) : ℝ) = (SO.pt D g (g.glob t k) : ℝ) := by
    simpa using congrArg (fun n : ℕ => (n : ℝ)) (so_cp_pos g D hk)
  have h_iff : (SO.cp D g t (g.pos t k) : ℝ) < (SO.cp D g t i : ℝ) ↔ g.pos t k < i := by
    constructor
    · intro h_lt
      by_contra! h_ge
      have h_cp_le : SO.cp D g t i ≤ SO.cp D g t (g.pos t k) := so_cp_mono g D hg h_ge h_posL
      have h_le' : (SO.cp D g t i : ℝ) ≤ (SO.cp D g t (g.pos t k) : ℝ) := by exact_mod_cast h_cp_le
      linarith
    · intro h_lt_pos
      have h_cp_lt : SO.cp D g t (g.pos t k) < SO.cp D g t i := so_cp_lt_cp g D hg h_lt_pos hiL
      exact_mod_cast h_cp_lt
  have h_not_iff := h_cell.not
  constructor
  · intro h_lt_pt
    have h_not_A : ¬ (x * D ≤ (SO.pt D g (g.glob t k) : ℝ)) := by linarith
    have h_not_B_nat : ¬ (SO.cp D g t i ≤ SO.pt D g (g.glob t k)) := h_not_iff.mp h_not_A
    have h_lt_cp_nat : SO.pt D g (g.glob t k) < SO.cp D g t i := Nat.lt_of_not_ge h_not_B_nat
    have h_lt_cp : (SO.pt D g (g.glob t k) : ℝ) < (SO.cp D g t i : ℝ) := by exact_mod_cast h_lt_cp_nat
    rw [← h_pt_eq] at h_lt_cp
    exact h_iff.mp h_lt_cp
  · intro h_lt_pos
    have h_lt_cp : (SO.cp D g t (g.pos t k) : ℝ) < (SO.cp D g t i : ℝ) := h_iff.mpr h_lt_pos
    rw [h_pt_eq] at h_lt_cp
    have h_not_B : ¬ ((SO.cp D g t i : ℝ) ≤ (SO.pt D g (g.glob t k) : ℝ)) := by linarith
    have h_not_B_nat : ¬ (SO.cp D g t i ≤ SO.pt D g (g.glob t k)) := by
      intro h; apply h_not_B; exact_mod_cast h
    have h_not_A : ¬ (x * D ≤ (SO.pt D g (g.glob t k) : ℝ)) := h_not_iff.mpr h_not_B_nat
    linarith

theorem so_ceilR_of_cell (hg : SO.ok D g = true) {t i : ℕ} (hi1 : 1 ≤ i) (hiL : i ≤ g.L t) {x : ℝ}
    (hxa : (SO.cp D g t (i - 1) : ℝ) < x * D) (hxb : x * D ≤ SO.cp D g t i) :
    SO.ceilR D g (t + 1) x = g.nxt t i := by
  have hD : 0 < D := g.so_D_pos D hg
  set j0 := (g.cellPts t).getD (i - 1) 0 with hj0
  have hcp_eq : SO.cp D g t i = SO.pt D g j0 := by
    rw [hj0]
    exact g.so_cp_of_pos D hi1
  have hnxt_eq : g.nxt t i = g.ceilG (t + 1) j0 := by
    unfold Grid.nxt
    rw [hj0]
  have hDpos_nat : 0 < D := hD
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast hDpos_nat
  have hcpD : SO.cp D g t i ≤ D := g.so_cp_le_D D hg t i
  have hcpD' : (SO.cp D g t i : ℝ) ≤ (D : ℝ) := by exact_mod_cast hcpD
  have hx1 : x ≤ 1 := by
    nlinarith
  have hk_le : g.ceilG (t + 1) j0 ≤ g.cnt (t + 1) := g.ceilG_le_cnt (t + 1) j0
  rw [hnxt_eq]
  apply ((g.so_ceilR_eq_iff D hD (t + 1) hx1 hk_le).mpr ?_)
  constructor
  · -- first goal: x * D ≤ SO.pt D g (g.glob (t + 1) (g.ceilG (t + 1) j0))
    have hmem : j0 ∈ g.cellPts t := by
      rw [hj0]
      have hlen_eq : (g.cellPts t).length = g.L t := rfl
      have hlt : i - 1 < (g.cellPts t).length := by
        rw [hlen_eq]
        omega
      rw [List.getD_eq_getElem (g.cellPts t) 0 hlt]
      exact List.get_mem (g.cellPts t) ⟨i - 1, hlt⟩
    have hj0_le_J : j0 ≤ g.J := ((g.mem_cellPts).mp hmem).1
    have hceilG_spec := g.so_ceilG_spec D hg (t + 1) hj0_le_J
    rcases hceilG_spec with ⟨hle_pt, hlt_pt⟩
    have hx_le_pt_j0 : x * (D : ℝ) ≤ (SO.pt D g j0 : ℝ) := by
      have hle : SO.cp D g t i ≤ SO.pt D g j0 := by
        rw [hcp_eq]
      exact ((g.so_le_pt_iff_of_cell D hg hi1 hiL hmem hxa hxb).mpr hle)
    exact le_trans hx_le_pt_j0 (by exact_mod_cast hle_pt)
  · -- second goal: ∀ k' < g.ceilG (t + 1) j0, (SO.pt D g (g.glob (t + 1) k') : ℝ) < x * D
    intro k' hk'
    have hk'_le_cnt : k' ≤ g.cnt (t + 1) := by
      have hceilG_le_cnt : g.ceilG (t + 1) j0 ≤ g.cnt (t + 1) := g.ceilG_le_cnt (t + 1) j0
      omega
    have hmem' : g.glob (t + 1) k' ∈ g.cellPts t :=
      g.glob_succ_mem_cellPts hk'_le_cnt
    have hle_iff := g.so_le_pt_iff_of_cell D hg hi1 hiL hmem' hxa hxb
    have hlt_nat : SO.pt D g (g.glob (t + 1) k') < SO.pt D g j0 := by
      have hmem : j0 ∈ g.cellPts t := by
        rw [hj0]
        have hlen_eq : (g.cellPts t).length = g.L t := rfl
        have hlt : i - 1 < (g.cellPts t).length := by
          rw [hlen_eq]
          omega
        rw [List.getD_eq_getElem (g.cellPts t) 0 hlt]
        exact List.get_mem (g.cellPts t) ⟨i - 1, hlt⟩
      have hj0_le_J : j0 ≤ g.J := ((g.mem_cellPts).mp hmem).1
      have hceilG_spec := g.so_ceilG_spec D hg (t + 1) hj0_le_J
      rcases hceilG_spec with ⟨_, hlt_pt⟩
      exact hlt_pt k' hk'
    have hlt_real : (SO.pt D g (g.glob (t + 1) k') : ℝ) < (SO.pt D g j0 : ℝ) := by exact_mod_cast hlt_nat
    have hlt_real' : (SO.pt D g (g.glob (t + 1) k') : ℝ) < (SO.cp D g t i : ℝ) := by
      simpa [hcp_eq] using hlt_real
    have h_not_le_nat : ¬ (SO.cp D g t i ≤ SO.pt D g (g.glob (t + 1) k')) := by
      rw [← hcp_eq] at hlt_nat
      omega
    have h_not_xD_le : ¬ (x * (D : ℝ) ≤ (SO.pt D g (g.glob (t + 1) k') : ℝ)) :=
      mt hle_iff.mp h_not_le_nat
    exact lt_of_not_ge h_not_xD_le

theorem so_exists_cell (hD : 0 < D) (t : ℕ) {i0 : ℕ} {x : ℝ} (hx0 : 0 < x)
    (hx : x * D ≤ SO.cp D g t i0) :
    ∃ i, 1 ≤ i ∧ i ≤ i0 ∧ (SO.cp D g t (i - 1) : ℝ) < x * D ∧ x * D ≤ SO.cp D g t i := by
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast hD
  have hcp0 : (SO.cp D g t 0 : ℝ) = 0 := by exact_mod_cast g.so_cp_zero D t
  have hxDpos : 0 < x * (D : ℝ) := by
    nlinarith
  let S : ℕ → Prop := λ i => i ≤ i0 ∧ x * (D : ℝ) ≤ (SO.cp D g t i : ℝ)
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
  have h_not_S : ¬ ((i - 1 ≤ i0) ∧ x * (D : ℝ) ≤ (SO.cp D g t (i - 1) : ℝ)) :=
    hi_min (i - 1) h_lt
  have h_le_i0 : i - 1 ≤ i0 := by
    omega
  have h_lt_cp : ¬ (x * (D : ℝ) ≤ (SO.cp D g t (i - 1) : ℝ)) := by
    intro hle
    apply h_not_S
    exact ⟨h_le_i0, hle⟩
  refine ⟨i, hi_pos, hi_spec.1, lt_of_not_ge h_lt_cp, hi_spec.2⟩

end Grid

end Robbins.Cert
