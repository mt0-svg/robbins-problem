import Robbins.Cert.SO.LS.Vec
import Robbins.Cert.SO.LS.Kc

/-!
# The lanes step: counting, sorted tuples, the prefix vectors

`cnt`, the tuples `tupR` over `List.range R`, the slot vectors `tupV` and `slotInc` built by
concatenation (`catV`), and the rank sums `rankV` on lanes.
-/

namespace Robbins.Cert.SO.L

open Robbins.Cert Robbins.Cert.K Robbins.Cert.SO.K Robbins.Lanes

/-! ## Counting -/

/-- The product formula of `binK` is the binomial coefficient. -/
theorem binK_eq (a b : ℕ) : binK a b = a.choose b := by
  have key : ∀ b j, (@Nat.rec (fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
      (fun _ ih j acc => ih (Nat.succ j) (Nat.div (Nat.mul acc (Nat.sub a j)) (Nat.succ j))) b j
      (a.choose j)) = a.choose (j + b) := by
    intro b
    induction b with
    | zero => intro j; rfl
    | succ b ih =>
      intro j
      show (@Nat.rec (fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
        (fun _ ih j acc => ih (Nat.succ j) (Nat.div (Nat.mul acc (Nat.sub a j)) (Nat.succ j))) b (j + 1)
        (a.choose j * (a - j) / (j + 1))) = _
      have e : a.choose j * (a - j) / (j + 1) = a.choose (j + 1) := by
        rw [← Nat.choose_succ_right_eq]
        exact Nat.mul_div_cancel _ (Nat.succ_pos j)
      rw [e, ih (j + 1)]
      congr 1
      omega
  have := key b 0
  simp only [Nat.choose_zero_right, zero_add] at this
  exact this

theorem cnt_eq' (k n : ℕ) : cnt k n = (n + k - 1).choose k := by
  unfold cnt
  rw [binK_eq]
  rfl

theorem cnt_zero (n : ℕ) : cnt 0 n = 1 := by
  rw [cnt_eq', Nat.choose_zero_right]

theorem cnt_succ_zero (k : ℕ) : cnt (k + 1) 0 = 0 := by
  rw [cnt_eq']
  exact Nat.choose_eq_zero_of_lt (by omega)

/-- Pascal's rule for `cnt`. -/
theorem cnt_succ (k n : ℕ) : cnt (k + 1) (n + 1) = cnt (k + 1) n + cnt k (n + 1) := by
  rw [cnt_eq', cnt_eq', cnt_eq']
  rcases k with _ | k
  · simp
  · have e1 : n + 1 + (k + 1 + 1) - 1 = (n + k + 1) + 1 := by omega
    have e2 : n + (k + 1 + 1) - 1 = n + k + 1 := by omega
    have e3 : n + 1 + (k + 1) - 1 = n + k + 1 := by omega
    rw [e1, e2, e3, Nat.choose_succ_succ]
    ring

theorem cnt_mono (k : ℕ) {a b : ℕ} (h : a ≤ b) : cnt k a ≤ cnt k b := by
  rw [cnt_eq', cnt_eq']
  exact Nat.choose_le_choose k (by omega)

/-- The tuples have `cnt` elements. -/
theorem tupR_length_cnt {α : Type} (k : ℕ) (xs : List α) : (tupR k xs).length = cnt k xs.length := by
  rw [tupR_length, cnt_eq']

/-- `cnt k (j + 1) = Σ_{v ≤ j} cnt (k - 1) (v + 1)`: the tuples by their largest entry. -/
theorem cnt_succ_sum (k j : ℕ) : cnt (k + 1) j = ∑ v ∈ Finset.range j, cnt k (v + 1) := by
  induction j with
  | zero => simp [cnt_succ_zero]
  | succ j ih => rw [cnt_succ, ih, Finset.sum_range_succ]

/-- The tuples over `xs` are the first ones over `xs ++ ys`. -/
theorem tupR_append' {α : Type} (k : ℕ) (xs ys : List α) : ∃ R, tupR k (xs ++ ys) = tupR k xs ++ R := by
  rcases k with _ | k
  · exact ⟨[], by simp [tupR_zero]⟩
  · exact tupR_append k xs ys

/-- The tuple `cnt (k + 1) j + l` of `tupR (k + 1) xs`, for `l < cnt k (j + 1)`: `xs[j]` before the
tuple `l` of `tupR k xs`. -/
theorem tupR_block {α : Type} (k : ℕ) (xs : List α) (j l : ℕ) (hj : j < xs.length)
    (hl : l < cnt k (j + 1)) :
    (tupR (k + 1) xs)[cnt (k + 1) j + l]? = some (xs[j] :: (tupR k xs).getD l []) := by
  obtain ⟨R1, hR1⟩ := tupR_append' (k + 1) (xs.take (j + 1)) (xs.drop (j + 1))
  obtain ⟨R2, hR2⟩ := tupR_append' k (xs.take (j + 1)) (xs.drop (j + 1))
  rw [List.take_append_drop] at hR1 hR2
  have htake : xs.take (j + 1) = xs.take j ++ [xs[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]
    rfl
  have hlenA : (tupR (k + 1) (xs.take j)).length = cnt (k + 1) j := by
    rw [tupR_length_cnt, List.length_take, min_eq_left (by omega)]
  have hlenB : (tupR k (xs.take (j + 1))).length = cnt k (j + 1) := by
    rw [tupR_length_cnt, List.length_take, min_eq_left (by omega)]
  have hget : (tupR k xs).getD l [] = (tupR k (xs.take (j + 1))).getD l [] := by
    rw [hR2, List.getD_append _ _ _ _ (by omega)]
  rw [hget, hR1, htake, tupR_snoc, ← htake, List.append_assoc,
    List.getElem?_append_right (by omega), hlenA, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by rw [List.length_map]; omega), List.getElem?_map,
    List.getElem?_eq_getElem (by omega), List.getD_eq_getElem _ _ (by omega)]
  rfl

/-! ## Sorted tuples -/

/-- `tupR` commutes with `map`. -/
theorem tupR_map {α β : Type} (k : ℕ) (g : α → β) (xs : List α) :
    tupR k (xs.map g) = (tupR k xs).map (List.map g) := by
  induction k generalizing xs with
  | zero =>
    simp [tupR_zero]
  | succ k ih_k =>
    induction xs using List.reverseRecOn with
    | nil =>
      simp [tupR_nil]
    | append_singleton xs y ih_xs =>
      simp only [List.map_append, List.map_singleton]
      rw [tupR_snoc k (xs.map g) (g y)]
      rw [tupR_snoc k xs y]
      rw [List.map_append]
      rw [ih_xs]
      have hk := ih_k (xs ++ [y])
      rw [List.map_append, List.map_singleton] at hk
      rw [hk]
      rw [List.map_map (f := List.map g) (g := fun x => g y :: x)]
      rw [List.map_map (f := fun x => y :: x) (g := List.map g)]
      simp [List.map_cons]

/-- Every tuple of `tupR k` has `k` entries. -/
theorem tupR_mem_length {α : Type} (k : ℕ) (xs : List α) : ∀ tp ∈ tupR k xs, tp.length = k := by
  induction k generalizing xs with
  | zero =>
      intro tp h
      rw [tupR_zero xs] at h
      simp at h
      rcases h with (rfl | ⟨⟩)
      rfl
  | succ k ih_k =>
      intro tp h
      refine List.reverseRecOn xs ?_ ?_ tp h
      · intro tp h
        rw [tupR_nil k] at h
        simp at h
      · intro ys y ih_xs tp h
        rw [tupR_snoc k ys y] at h
        rw [List.mem_append] at h
        rcases h with (h' | h')
        · exact ih_xs tp h'
        · rcases List.mem_map.mp h' with ⟨t, ht, rfl⟩
          have ht_len : t.length = k := ih_k (ys ++ [y]) t ht
          simp [ht_len]

/-- The tuples over `range R`, largest entry first: nonincreasing, entries below `R`. -/
theorem tupR_range_mem (k R : ℕ) :
    ∀ tp ∈ tupR k (List.range R), tp.Pairwise (· ≥ ·) ∧ ∀ x ∈ tp, x < R := by
  induction' k with k ih generalizing R
  · -- k = 0
    intro tp h
    rw [tupR_zero (List.range R)] at h
    have htp : tp = [] := by simpa using h
    rcases htp with rfl
    refine ⟨?_, ?_⟩
    · exact List.Pairwise.nil
    · intro x hx; exact absurd hx (by simp)
  · -- k = k+1
    intro tp h
    induction' R with R ihR generalizing tp
    · -- R = 0, List.range 0 = []
      rw [List.range_zero] at h
      rw [tupR_nil k] at h
      exact absurd h (by simp)
    · -- R = R+1
      have hrange : List.range (R + 1) = List.range R ++ [R] :=
        List.range_succ (n := R)
      rw [hrange] at h
      rw [tupR_snoc k (List.range R) R] at h
      rcases List.mem_append.mp h with (h | h)
      · -- tp ∈ tupR (k+1) (List.range R)
        rcases ihR tp h with ⟨hpw, hlt⟩
        refine ⟨hpw, ?_⟩
        intro x hx
        have hxlt : x < R := hlt x hx
        exact Nat.lt_of_lt_of_le hxlt (Nat.le_succ R)
      · -- tp ∈ (tupR k (List.range R ++ [R])).map (R :: ·)
        rcases List.mem_map.mp h with ⟨t, ht, rfl⟩
        rw [← hrange] at ht
        rcases ih (R + 1) t ht with ⟨hpw_t, hlt_t⟩
        have hpw_cons : (R :: t).Pairwise (· ≥ ·) := by
          rw [List.pairwise_cons]
          refine ⟨?_, hpw_t⟩
          intro a ha
          have ha_lt : a < R + 1 := hlt_t a ha
          exact Nat.le_of_lt_succ ha_lt
        have hlt_cons : ∀ x ∈ (R :: t), x < R + 1 := by
          intro x hx
          rcases (List.mem_cons.mp hx) with (hx_eq | hx')
          · rw [hx_eq]
            exact Nat.lt_succ_self R
          · exact hlt_t x hx'
        exact ⟨hpw_cons, hlt_cons⟩

/-- The tuples over `range v` are the first ones over `range R`, `v ≤ R`. -/
theorem tupR_range_prefix (k v R : ℕ) (hv : v ≤ R) :
    tupR k (List.range v) <+: tupR k (List.range R) := by
  rcases Nat.exists_eq_add_of_le hv with ⟨d, hR⟩
  rw [hR]
  induction' k with k ih
  · simp [tupR_zero]
  · rw [List.range_add]
    rcases tupR_append k (List.range v) (List.map (fun x => v + x) (List.range d)) with ⟨R', h⟩
    rw [h]
    exact ⟨R', rfl⟩

/-- The tuples of `k + 1` entries over `range R`, grouped by their largest entry `v`. -/
theorem tupR_succ_range (k R : ℕ) :
    tupR (k + 1) (List.range R) =
      (List.range R).flatMap fun v => (tupR k (List.range (v + 1))).map (v :: ·) := by
  induction' R with R ih
  · simp [tupR_nil]
  · rw [List.range_succ, tupR_snoc, List.flatMap_append, List.flatMap_singleton, ih, List.range_succ]

/-! ## Slot vectors -/

/-- A list of lane values as a pack. -/
noncomputable def pk (L : List ℕ) : ℕ := pack LW L.length fun l => L.getD l 0

/-- `catV` concatenates the packs of the lists `Lv v`, `v < R`, of `cnt k (v + 1)` lanes each. -/
theorem catV_eq (R k : ℕ) (g : ℕ → ℕ) (Lv : ℕ → List ℕ)
    (hlen : ∀ v < R, (Lv v).length = cnt k (v + 1)) (hg : ∀ v < R, g v = pk (Lv v)) :
    catV R k g = pk ((List.range R).flatMap Lv) := by
  -- Helper lemma: frc2 is identity
  have frc2_eq (a b : ℕ) (k' : ℕ → ℕ → ℕ) : frc2 a b k' = k' a b := by
    unfold frc2 cnd
    cases h : Nat.beq a 0 with
    | false =>
        cases hb : Nat.beq b 0 with
        | false => rfl
        | true =>
            have hb0 : b = 0 := Nat.eq_of_beq_eq_true hb
            subst hb0
            rfl
    | true =>
        cases hb : Nat.beq b 0 with
        | false =>
            have ha0 : a = 0 := Nat.eq_of_beq_eq_true h
            subst ha0
            rfl
        | true =>
            have ha0 : a = 0 := Nat.eq_of_beq_eq_true h
            have hb0 : b = 0 := Nat.eq_of_beq_eq_true hb
            subst ha0; subst hb0
            rfl
  -- Helper lemma: pk_append
  have pk_append (L1 L2 : List ℕ) : pk L1 + pk L2 <<< (LW * L1.length) = pk (L1 ++ L2) := by
    unfold pk
    rw [List.length_append]
    have h_app := app_pack LW L1.length L2.length (fun l => L1.getD l 0) (fun l => L2.getD l 0)
    have h_congr : pack LW (L1.length + L2.length) (fun l => if l < L1.length then L1.getD l 0 else L2.getD (l - L1.length) 0) =
      pack LW (L1.length + L2.length) (fun l => (L1 ++ L2).getD l 0) := by
      apply pack_congr LW (L1.length + L2.length)
      intro l hl
      by_cases hl1 : l < L1.length
      · rw [List.getD_append L1 L2 0 l hl1]
        simp [hl1]
      · have hl1' : L1.length ≤ l := by omega
        rw [List.getD_append_right L1 L2 0 l hl1']
        simp [hl1]
    simpa [app] using h_app.trans h_congr
  -- Unfold catV and simplify using frc2_eq
  unfold catV
  simp [frc2_eq]
  -- Now the goal is:
  -- Nat.rec (motive := fun x => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
  --   (fun _ ih v o acc => ih (v + 1) (o + cnt k (v + 1)) (acc + g v <<< (LW * o))) R 0 0 0 = pk ((List.range R).flatMap Lv)
  -- Set up abbreviations for base and step
  set base : ℕ → ℕ → ℕ → ℕ := fun _ _ acc => acc with hbase
  set step' : ℕ → (ℕ → ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ → ℕ :=
    fun _ ih v o acc => ih (v + 1) (o + cnt k (v + 1)) (acc + g v <<< (LW * o)) with hstep'
  -- The goal is: Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) base step' R 0 0 0 = pk ((List.range R).flatMap Lv)
  -- We prove a generalized statement by induction on r
  have h_aux : ∀ (r v o acc : ℕ), v + r ≤ R →
      o = ((List.range v).flatMap Lv).length → acc = pk ((List.range v).flatMap Lv) →
      (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) base step' r) v o acc = pk ((List.range (v + r)).flatMap Lv) := by
    intro r
    induction' r with r ih
    · -- r = 0
      intro v o acc hv ho hacc
      simp [base, ho, hacc]
    · -- r = r+1
      intro v o acc hv ho hacc
      -- hv : v + (r+1) ≤ R
      -- We need to compute Nat.rec base step' (r+1) v o acc
      -- By definition: Nat.rec base step' (r+1) = step' r (Nat.rec base step' r)
      -- So: (Nat.rec base step' (r+1)) v o acc = (Nat.rec base step' r) (v+1) (o + cnt k (v+1)) (acc + g v <<< (LW * o))
      have h_rec : (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) base step' (r + 1)) v o acc =
        (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) base step' r) (v + 1) (o + cnt k (v + 1)) (acc + g v <<< (LW * o)) := by
        rfl
      rw [h_rec]
      -- Now apply the IH with v := v+1
      have h_ih := ih (v + 1) (o + cnt k (v + 1)) (acc + g v <<< (LW * o)) (by omega) ?_ ?_
      · -- h_ih : Nat.rec ... r (v+1) (o + cnt k (v+1)) (acc + g v <<< (LW * o)) = pk ((List.range ((v+1) + r)).flatMap Lv)
        rw [h_ih]
        -- Goal: pk ((List.range ((v+1) + r)).flatMap Lv) = pk ((List.range (v + (r+1))).flatMap Lv)
        -- (v+1)+r = v+(r+1) by omega
        have h_eq : (v + 1) + r = v + (r + 1) := by omega
        rw [h_eq]
      · -- o + cnt k (v+1) = ((List.range (v+1)).flatMap Lv).length
        rw [ho]
        -- Goal: ((List.range v).flatMap Lv).length + cnt k (v + 1) = ((List.range (v+1)).flatMap Lv).length
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append]
        rw [hlen v (by omega)]
      · -- acc + g v <<< (LW * o) = pk ((List.range (v+1)).flatMap Lv)
        rw [hacc, hg v (by omega), ho]
        -- Goal: pk ((List.range v).flatMap Lv) + pk (Lv v) <<< (LW * ((List.range v).flatMap Lv).length) = pk ((List.range (v+1)).flatMap Lv)
        rw [pk_append]
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
  -- Apply h_aux to the goal
  have h_result := h_aux R 0 0 0 (by omega) (by simp) (by unfold pk; rfl)
  -- h_result : Nat.rec ... R 0 0 0 = pk ((List.range (0 + R)).flatMap Lv)
  -- We need: pk ((List.range (0 + R)).flatMap Lv) = pk ((List.range R).flatMap Lv)
  simpa [zero_add] using h_result

theorem pre_pk_prefix (L1 L2 : List ℕ) (h : L1 <+: L2) (hb : ∀ x ∈ L2, x < 2 ^ 144) :
    pre LW L1.length (pk L2) = pk L1 := by
  unfold pk
  rw [pre_eq L2.length L1.length _ (fun l hl => by
    rw [List.getD_eq_getElem _ _ hl]; exact hb _ (List.getElem_mem hl)) h.length_le]
  apply pack_congr
  intro l hl
  obtain ⟨t, rfl⟩ := h
  rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ (by simp; omega),
    List.getElem_append_left hl]

theorem pk_replicate (n a : ℕ) : pk (List.replicate n a) = a * ones LW n := by
  unfold pk
  rw [ones_eq LW n (by decide), pack_const_mul, List.length_replicate]
  apply pack_congr
  intro l hl
  rw [List.getD_eq_getElem _ _ (by simpa using hl)]
  simp

/-- The slot vectors of `f` over `tupR k (range R)`: slot `q` of the lane of a tuple is `f` of its
entry `q` (entry `0` the largest). -/
theorem tupV_eq (f : ℕ → ℕ) (R : ℕ) (hf : ∀ v < R, f v < 2 ^ 144) (k : ℕ) :
    tupV f R k = (List.range k).map fun q =>
      pk ((tupR k (List.range R)).map fun tp => f (tp.getD q 0)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show catV R k (fun v => Nat.mul (f v) (ones LW (cnt k (Nat.succ v)))) ::
      lmap (fun P => catV R k (fun v => pre LW (cnt k (Nat.succ v)) P)) (tupV f R k) = _
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, tupR_succ_range]
    congr 1
    · refine (catV_eq R k _ (fun v => List.replicate (cnt k (v + 1)) (f v))
        (fun v _ => List.length_replicate) (fun v _ => (pk_replicate _ _).symm)).trans ?_
      congr 1
      rw [List.map_flatMap]
      congr 1
      funext v
      rw [List.map_map]
      have : ((fun tp : List ℕ => f (tp.getD 0 0)) ∘ (v :: ·)) = fun _ => f v := by
        funext tp; simp
      rw [this, List.map_const', tupR_length_cnt, List.length_range]
    · rw [lmap_eq, ih, List.map_map]
      apply List.map_congr_left
      intro q hq
      rw [List.mem_range] at hq
      simp only [Function.comp]
      rw [catV_eq R k _ (fun v => (tupR k (List.range (v + 1))).map fun tp => f (tp.getD q 0))
        (fun v _ => by rw [List.length_map, tupR_length_cnt, List.length_range])]
      · congr 1
        rw [List.map_flatMap]
        congr 1
        funext v
        rw [List.map_map]
        rfl
      · intro v hv
        have hpre : (tupR k (List.range (v + 1))).map (fun tp => f (tp.getD q 0)) <+:
            (tupR k (List.range R)).map (fun tp => f (tp.getD q 0)) :=
          (tupR_range_prefix k (v + 1) R hv).map _
        have hl : ((tupR k (List.range (v + 1))).map (fun tp => f (tp.getD q 0))).length =
            cnt k (v + 1) := by rw [List.length_map, tupR_length_cnt, List.length_range]
        show pre LW (cnt k (v + 1)) _ = _
        rw [← hl]
        apply pre_pk_prefix _ _ hpre
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨tp, htp, rfl⟩ := hx
        have hlen := tupR_mem_length k _ tp htp
        have hq' : q < tp.length := by omega
        rw [List.getD_eq_getElem _ _ hq']
        exact hf _ ((tupR_range_mem k R tp htp).2 _ (List.getElem_mem hq'))

/-! ## Rank sums -/

/-- `rankV1` on a cons. -/
theorem rankV1_cons (u : ℕ) (us vs : List ℕ) (C : ℕ) :
    rankV.rankV1 (u :: us) vs C = C :: rankV.rankV1 us (tl vs) (Nat.add (Nat.sub C (hd vs)) u) := rfl

theorem rankV1_nil (vs : List ℕ) (C : ℕ) : rankV.rankV1 [] vs C = [C] := rfl

theorem rankV1_length (us vs : List ℕ) (C : ℕ) : (rankV.rankV1 us vs C).length = us.length + 1 := by
  induction us generalizing vs C with
  | nil => rfl
  | cons u us ih => rw [rankV1_cons, List.length_cons, ih, List.length_cons]

/-- `rankV1` from `C = X + Σ v`. -/
theorem rankV1_getD (us vs : List ℕ) (h : us.length = vs.length) (X C : ℕ)
    (hC : C = X + ∑ q ∈ Finset.range vs.length, vs.getD q 0) (b : ℕ) (hb : b ≤ us.length) :
    (rankV.rankV1 us vs C).getD b 0 =
      X + ∑ q ∈ Finset.range b, us.getD q 0 + ∑ q ∈ Finset.Ico b us.length, vs.getD q 0 := by
  induction us generalizing vs C X b with
  | nil =>
    have hv : vs = [] := List.eq_nil_of_length_eq_zero h.symm
    subst hv
    have hb0 : b = 0 := by simpa using hb
    subst hb0
    simp [rankV1_nil, hC]
  | cons u us ih =>
    rcases vs with _ | ⟨v, vs⟩
    · simp at h
    · have h' : us.length = vs.length := by simpa using h
      rw [rankV1_cons]
      simp only [hd_eq, tl_eq, List.headD_cons, List.tail_cons, Nat.sub_eq, Nat.add_eq]
      have hsum : ∑ q ∈ Finset.range (v :: vs).length, (v :: vs).getD q 0 =
          v + ∑ q ∈ Finset.range vs.length, vs.getD q 0 := by
        rw [List.length_cons, Finset.sum_range_succ']
        simp [add_comm]
      rcases b with _ | b
      · simp only [List.getD_cons_zero, Finset.range_zero, Finset.sum_empty, add_zero]
        rw [hC, hsum, ← Finset.range_eq_Ico, List.length_cons, Finset.sum_range_succ']
        simp only [List.getD_cons_succ, List.getD_cons_zero, h']
        ring
      · simp only [List.getD_cons_succ]
        rw [ih vs h' (X + u) _ (by rw [hC, hsum]; omega) b (by simpa using hb)]
        rw [Finset.sum_range_succ', List.length_cons]
        simp only [List.getD_cons_succ, List.getD_cons_zero]
        rw [← Finset.sum_Ico_add' (fun q => (v :: vs).getD q 0) b us.length 1]
        simp only [List.getD_cons_succ]
        ring

theorem foldr_add_eq_sum_getD (vs : List ℕ) :
    List.foldr Nat.add 0 vs = ∑ q ∈ Finset.range vs.length, vs.getD q 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [List.foldr_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

/-- `rankV` in closed form: entry `b` is `Σ_{q < b} u_q + Σ_{b ≤ q < d} v_q`. -/
theorem rankV_getD (us vs : List ℕ) (h : us.length = vs.length) (b : ℕ) (hb : b ≤ us.length) :
    (rankV us vs).getD b 0 =
      ∑ q ∈ Finset.range b, us.getD q 0 + ∑ q ∈ Finset.Ico b us.length, vs.getD q 0 := by
  rw [rankV, rankV1_getD us vs h 0 _ (by rw [lfoldr_eq, foldr_add_eq_sum_getD, zero_add]) b hb, zero_add]

theorem rankV_length (us vs : List ℕ) : (rankV us vs).length = us.length + 1 := by
  rw [rankV, rankV1_length]

/-- `rankV` on lanes is `rankV` on each lane. -/
theorem rankV_pack (n d : ℕ) (U V : ℕ → ℕ → ℕ) (_hd : d < 2 ^ 40) (_hU : ∀ q < d, ∀ l < n, U q l < 2 ^ 100)
    (_hV : ∀ q < d, ∀ l < n, V q l < 2 ^ 100) :
    rankV ((List.range d).map fun q => pack LW n (U q)) ((List.range d).map fun q => pack LW n (V q)) =
      (List.range (d + 1)).map fun b => pack LW n fun l =>
        ∑ q ∈ Finset.range b, U q l + ∑ q ∈ Finset.Ico b d, V q l := by
  let us := (List.range d).map fun q => pack LW n (U q)
  let vs := (List.range d).map fun q => pack LW n (V q)
  have hus_len : us.length = d := by simp [us]
  have hvs_len : vs.length = d := by simp [vs]
  have h_len_eq : us.length = vs.length := by rw [hus_len, hvs_len]
  have h_sum_pack (f : ℕ → ℕ → ℕ) (s : Finset ℕ) :
      ∑ q ∈ s, pack LW n (f q) = pack LW n (fun l => ∑ q ∈ s, f q l) := by
    refine Finset.induction_on s ?_ ?_
    · simp [pack]
    · intro a s' has ih
      rw [Finset.sum_insert has, ih, pack_add]
      congr
      ext l
      simp [Finset.sum_insert has]
  have h_getD_us (q : ℕ) (hq : q < d) : us.getD q 0 = pack LW n (U q) := by
    have hq_len : q < us.length := by rwa [hus_len]
    rw [List.getD_eq_getElem us 0 hq_len]
    rw [List.getElem_map]
    simp
  have h_getD_vs (q : ℕ) (hq : q < d) : vs.getD q 0 = pack LW n (V q) := by
    have hq_len : q < vs.length := by rwa [hvs_len]
    rw [List.getD_eq_getElem vs 0 hq_len]
    rw [List.getElem_map]
    simp
  have h_len_rank : (rankV us vs).length = d + 1 := by rw [rankV_length, hus_len]
  have h_len_rhs : ((List.range (d + 1)).map fun b =>
      pack LW n fun l => ∑ q ∈ Finset.range b, U q l + ∑ q ∈ Finset.Ico b d, V q l).length = d + 1 := by
    simp
  let rhs := (List.range (d + 1)).map fun b =>
    pack LW n fun l => ∑ q ∈ Finset.range b, U q l + ∑ q ∈ Finset.Ico b d, V q l
  have h_len_rhs' : rhs.length = d + 1 := by simp [rhs]
  have h_max_len : Nat.max (rankV us vs).length rhs.length = d + 1 := by
    rw [h_len_rank, h_len_rhs']
    simp
  apply List.ext_getElem?
  intro k
  by_cases hk_lt : k < d + 1
  · -- k < d+1: both sides are some
    have hk_le_d : k ≤ d := by omega
    have hk_le_us_len : k ≤ us.length := by rwa [hus_len]
    rw [List.getElem?_map]
    have h_range_get : (List.range (d + 1))[k]? = some k := by
      simp [hk_lt]
    rw [h_range_get]
    simp
    -- Goal: (rankV us vs)[k]? = some (pack LW n fun l => ∑ q ∈ Finset.range k, U q l + ∑ q ∈ Finset.Ico k d, V q l)
    have h_getD : (rankV us vs).getD k 0 = pack LW n (fun l => ∑ q ∈ Finset.range k, U q l + ∑ q ∈ Finset.Ico k d, V q l) := by
      rw [rankV_getD us vs h_len_eq k hk_le_us_len]
      have h_sum1 : ∑ q ∈ Finset.range k, us.getD q 0 = pack LW n (fun l => ∑ q ∈ Finset.range k, U q l) := by
        rw [← h_sum_pack U (Finset.range k)]
        refine Finset.sum_congr rfl (fun q hq => ?_)
        rw [Finset.mem_range] at hq
        have hq_d : q < d := lt_of_lt_of_le hq hk_le_d
        rw [h_getD_us q hq_d]
      have h_sum2 : ∑ q ∈ Finset.Ico k d, vs.getD q 0 = pack LW n (fun l => ∑ q ∈ Finset.Ico k d, V q l) := by
        rw [← h_sum_pack V (Finset.Ico k d)]
        refine Finset.sum_congr rfl (fun q hq => ?_)
        rw [Finset.mem_Ico] at hq
        have hq_d : q < d := hq.2
        rw [h_getD_vs q hq_d]
      rw [h_sum1, hus_len]
      rw [h_sum2, ← pack_add]
    -- Now relate (rankV us vs)[k]? to (rankV us vs).getD k 0
    rw [List.getElem?_eq_some_iff]
    have h_len_rank' : k < (rankV us vs).length := by rwa [h_len_rank]
    refine ⟨h_len_rank', ?_⟩
    rw [← List.getD_eq_getElem (rankV us vs) 0 h_len_rank']
    exact h_getD
  · -- k ≥ d+1: both sides are none
    have hk_ge : d + 1 ≤ k := by omega
    have hk_ge_rank : (rankV us vs).length ≤ k := by rwa [h_len_rank]
    have hk_ge_rhs_len : (List.range (d + 1)).length ≤ k := by
      simp
      omega
    rw [List.getElem?_eq_none_iff.mpr hk_ge_rank]
    rw [List.getElem?_map]
    rw [List.getElem?_eq_none_iff.mpr hk_ge_rhs_len]
    rfl

theorem rankCs2_cons (p : ℕ × ℕ) (uv : List (ℕ × ℕ)) (C : ℕ) :
    rankCs.rankCs2 (p :: uv) C = C :: rankCs.rankCs2 uv (Nat.add (Nat.sub C p.2) p.1) := rfl

/-- `rankCs2` on the pairs of the records from index `k`, from `C = X + Σ v`. -/
theorem rankCs2_getD (rs : List SR) (k X C : ℕ)
    (hC : C = X + ∑ q ∈ Finset.range rs.length,
      lget (rs.getD q (SR.mk 0 0 0 0 true 0 0 0 0 [] 0)).bs (k + q + 1)) (b : ℕ) (hb : b ≤ rs.length) :
    (rankCs.rankCs2 (mapIdxFrom (fun l r => (lget r.bs l, lget r.bs (Nat.succ l))) k rs) C).getD b 0 =
      X + ∑ q ∈ Finset.range b, lget (rs.getD q (SR.mk 0 0 0 0 true 0 0 0 0 [] 0)).bs (k + q) +
        ∑ q ∈ Finset.Ico b rs.length, lget (rs.getD q (SR.mk 0 0 0 0 true 0 0 0 0 [] 0)).bs (k + q + 1) := by
  induction rs generalizing k X C b with
  | nil =>
    have hb0 : b = 0 := by simpa using hb
    subst hb0
    simp [mapIdxFrom, hC, rankCs.rankCs2]
  | cons r rs ih =>
    rw [mapIdxFrom, rankCs2_cons]
    simp only [Nat.sub_eq, Nat.add_eq, Nat.succ_eq_add_one]
    have hsum : ∑ q ∈ Finset.range (r :: rs).length,
        lget ((r :: rs).getD q (SR.mk 0 0 0 0 true 0 0 0 0 [] 0)).bs (k + q + 1) =
        lget r.bs (k + 1) + ∑ q ∈ Finset.range rs.length,
          lget (rs.getD q (SR.mk 0 0 0 0 true 0 0 0 0 [] 0)).bs (k + 1 + q + 1) := by
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      congr 1
      omega
    rcases b with _ | b
    · simp only [List.getD_cons_zero, Finset.range_zero, Finset.sum_empty, add_zero]
      rw [hC, hsum, ← Finset.range_eq_Ico, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
      rw [add_comm (lget r.bs (k + 1))]
      congr 2
      refine Finset.sum_congr rfl fun q _ => ?_
      congr 1
      omega
    · simp only [List.getD_cons_succ]
      rw [ih (k + 1) (X + lget r.bs k) _ (by rw [hC, hsum]; omega) b (by simpa using hb)]
      rw [Finset.sum_range_succ', List.length_cons]
      rw [← Finset.sum_Ico_add' (fun q => lget ((r :: rs).getD q (SR.mk 0 0 0 0 true 0 0 0 0 [] 0)).bs (k + q + 1))
        b rs.length 1]
      simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
      have e1 : ∑ q ∈ Finset.range b, lget (rs.getD q (SR.mk 0 0 0 0 true 0 0 0 0 [] 0)).bs (k + 1 + q) =
          ∑ q ∈ Finset.range b, lget (rs.getD q (SR.mk 0 0 0 0 true 0 0 0 0 [] 0)).bs (k + (q + 1)) :=
        Finset.sum_congr rfl fun q _ => by congr 1; omega
      have e2 : ∑ q ∈ Finset.Ico b rs.length, lget (rs.getD q (SR.mk 0 0 0 0 true 0 0 0 0 [] 0)).bs (k + 1 + q + 1) =
          ∑ q ∈ Finset.Ico b rs.length, lget (rs.getD q (SR.mk 0 0 0 0 true 0 0 0 0 [] 0)).bs (k + (q + 1) + 1) :=
        Finset.sum_congr rfl fun q _ => by congr 1; omega
      rw [e1, e2]
      ring

theorem lfoldr_pairs (rs : List SR) (k : ℕ) :
    lfoldr (fun p a => Nat.add p.2 a) 0 (mapIdxFrom (fun l r => (lget r.bs l, lget r.bs (Nat.succ l))) k rs) =
      ∑ q ∈ Finset.range rs.length, lget (rs.getD q (SR.mk 0 0 0 0 true 0 0 0 0 [] 0)).bs (k + q + 1) := by
  rw [lfoldr_eq]
  induction rs generalizing k with
  | nil => rfl
  | cons r rs ih =>
    rw [mapIdxFrom, List.foldr_cons, ih (k + 1), List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero, Nat.add_eq]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    omega

/-- `rankCs` in closed form. -/
theorem rankCs_getD (rs : List SR) (b : ℕ) (hb : b ≤ rs.length) :
    (rankCs rs).getD b 0 =
      ∑ q ∈ Finset.range b, lget (rs.getD q (SR.mk 0 0 0 0 true 0 0 0 0 [] 0)).bs q +
        ∑ q ∈ Finset.Ico b rs.length, lget (rs.getD q (SR.mk 0 0 0 0 true 0 0 0 0 [] 0)).bs (q + 1) := by
  show (rankCs.rankCs2 (lmapIdx _ 0 rs) (lfoldr _ 0 (lmapIdx _ 0 rs))).getD b 0 = _
  rw [lmapIdx_eq, lfoldr_pairs, rankCs2_getD rs 0 0 _ (by rw [zero_add]) b hb]
  simp only [zero_add]

theorem rankCs_length (rs : List SR) : (rankCs rs).length = rs.length + 1 := by
  have lmapIdx_length {α β : Type} (f : Nat → α → β) (k : Nat) (l : List α) : (lmapIdx f k l).length = l.length := by
    induction l generalizing k with
    | nil => simp [lmapIdx]
    | cons a l ih =>
      simp [lmapIdx]
      simpa [lmapIdx] using ih (k + 1)
  have rankCs2_length (uv : List (Nat × Nat)) (C0 : Nat) : (rankCs.rankCs2 uv C0).length = uv.length + 1 := by
    induction uv generalizing C0 with
    | nil =>
      simp [rankCs.rankCs2]
    | cons p ps ih =>
      simp [rankCs.rankCs2, rankCs.rankCs3]
      have h := ih (C0 - p.2 + p.1)
      have hlen : (rankCs.rankCs2 ps (C0 - p.2 + p.1)).length = (List.rec (motive := fun x => ℕ → List ℕ) (fun x => []) (fun p x ih C => (C - p.2 + p.1) :: ih (C - p.2 + p.1)) ps (C0 - p.2 + p.1)).length + 1 := by
        simp [rankCs.rankCs2, rankCs.rankCs3]
      omega
  calc
    (rankCs rs).length = (rankCs.rankCs1 (lmapIdx (fun l r => (lget r.bs l, lget r.bs (l + 1))) 0 rs)).length := by
      rfl
    _ = (rankCs.rankCs2 (lmapIdx (fun l r => (lget r.bs l, lget r.bs (l + 1))) 0 rs) (lfoldr (fun p a => p.2 + a) 0 (lmapIdx (fun l r => (lget r.bs l, lget r.bs (l + 1))) 0 rs))).length := by
      rfl
    _ = (lmapIdx (fun l r => (lget r.bs l, lget r.bs (l + 1))) 0 rs).length + 1 := by
      rw [rankCs2_length]
    _ = rs.length + 1 := by
      rw [lmapIdx_length]

end Robbins.Cert.SO.L
