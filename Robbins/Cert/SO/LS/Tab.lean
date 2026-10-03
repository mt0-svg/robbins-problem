import Robbins.Cert.SO.LS.Net
import Robbins.Lanes.DecLit

/-!
# The lanes step: the claimed tables

Aligned literals (`litsOK`): every literal but the last holds 16 states, the last 1 to 16. Their
concatenation (`litCat`, a balanced merge of runs) is the pack of the decoded states, and the fields
of `n` concatenated states (`fields`) are compactions of the masked lanes.
-/

namespace Robbins.Cert.SO.L

open Robbins.Cert Robbins.Cert.K Robbins.Cert.SO.K Robbins.Lanes

/-! ## Digits -/

/-- `x` modulo `2 ^ (W k)` is the pack of its first `k` digits in base `2 ^ W`. -/
theorem mod_pow_pack (W k x : ℕ) : x % 2 ^ (W * k) = pack W k fun i => x / 2 ^ (W * i) % 2 ^ W := by
  induction k with
  | zero =>
    simp [pack_zero, Nat.mod_one]
  | succ k ih =>
    rw [pack_succ]
    rw [← ih]
    have h_pow : 2 ^ (W * (k + 1)) = 2 ^ (W * k) * 2 ^ W := by
      rw [show W * (k + 1) = W * k + W by ring, pow_add, mul_comm]
    rw [h_pow]
    set M := 2 ^ (W * k) with hM
    set N := 2 ^ W with hN
    have hMpos : 0 < M := by
      rw [hM]
      positivity
    have hNpos : 0 < N := by
      rw [hN]
      positivity
    have hN_one_le : 1 ≤ N := by
      rw [hN]
      exact calc
        1 ≤ 2 ^ 0 := by simp
        _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (Nat.zero_le _)
    -- Goal: x % (M * N) = x % M + (x / M % N) * M
    have hmod2 : ((x / M) * M) % (M * N) = ((x / M) % N) * M := by
      set q := x / M with hq
      have hq_mod_eq : q ≡ q % N [MOD N] := by
        simp [Nat.ModEq]
      have h_mul_mod_eq : q * M ≡ (q % N) * M [MOD M * N] := by
        have h := Nat.ModEq.mul_right' M hq_mod_eq
        rw [mul_comm N M] at h
        exact h
      have h_lt : (q % N) * M < M * N := by
        have hq_lt : q % N < N := Nat.mod_lt _ hNpos
        have : (q % N) * M < N * M := Nat.mul_lt_mul_of_pos_right hq_lt hMpos
        rwa [mul_comm N M] at this
      rw [Nat.mod_eq_of_modEq h_mul_mod_eq h_lt]
    have hx : x = x % M + (x / M) * M := by
      have h := Nat.div_add_mod x M
      -- h: M * (x / M) + x % M = x
      -- we want: x = x % M + (x / M) * M
      linarith
    -- Use hx to rewrite only the LHS
    have hx_mod := congrArg (· % (M * N)) hx
    -- hx_mod: x % (M * N) = (x % M + (x / M) * M) % (M * N)
    rw [hx_mod]
    -- Goal: (x % M + (x / M) * M) % (M * N) = x % M + (x / M % N) * M
    rw [Nat.add_mod]
    -- Goal: ((x % M) % (M * N) + ((x / M) * M) % (M * N)) % (M * N) = x % M + (x / M % N) * M
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt x hMpos) (by
      calc
        M = M * 1 := by simp
        _ ≤ M * N := Nat.mul_le_mul_left M hN_one_le))]
    -- Goal: (x % M + ((x / M) * M) % (M * N)) % (M * N) = x % M + (x / M % N) * M
    rw [hmod2]
    -- Goal: (x % M + (x / M % N) * M) % (M * N) = x % M + (x / M % N) * M
    have h_lt : x % M + ((x / M) % N) * M < M * N := by
      have h1 : x % M < M := Nat.mod_lt _ hMpos
      have h2 : (x / M) % N < N := Nat.mod_lt _ hNpos
      nlinarith
    rw [Nat.mod_eq_of_lt h_lt]

/-- A literal with `k` states under its leading `1` (`x / 2 ^ (k Ws) = 1`, `1 ≤ k ≤ 16`): its states
are its first `k` digits. -/
theorem litStates_eq (Ws x k : ℕ) (hWs : 0 < Ws) (_hk1 : 1 ≤ k) (hk : k ≤ 16) (hx : x / 2 ^ (k * Ws) = 1) :
    litStates Ws 16 x = (List.range k).map fun i => x / 2 ^ (Ws * i) % 2 ^ Ws := by
  -- We prove a generalized statement by induction on j, generalizing over k and x.
  -- For all j, k, x, if x / 2^(k*Ws) = 1 and k ≤ j, then
  -- litStates Ws j x = (List.range k).map fun i => x / 2^(Ws*i) % 2^Ws
  have h_gen : ∀ (j : ℕ), ∀ (k x : ℕ), x / 2 ^ (k * Ws) = 1 → k ≤ j →
      litStates Ws j x = (List.range k).map fun i => x / 2 ^ (Ws * i) % 2 ^ Ws := by
    intro j
    induction' j with j ih
    · intro k x hx hkj
      have hk0 : k = 0 := by omega
      subst hk0
      -- hx : x / 2^(0*Ws) = 1, i.e., x / 1 = 1, so x = 1
      simp at hx
      subst hx
      simp [litStates]
    · intro k x hx hkj
      by_cases hk0 : k = 0
      · subst hk0
        have hx1 : x = 1 := by simpa using hx
        subst hx1
        simp [litStates]
      · have hk_ge_one : 1 ≤ k := by omega
        have hx_gt_one : 1 < x := by
          have hpos : 0 < 2 ^ (k * Ws) := Nat.two_pow_pos (k * Ws)
          have hx_ge : 2 ^ (k * Ws) ≤ x := by
            by_contra! hlt
            have hzero : x / 2 ^ (k * Ws) = 0 := Nat.div_eq_of_lt hlt
            rw [hzero] at hx
            linarith
          have h_two_pow_ge_two : 2 ≤ 2 ^ (k * Ws) := by
            have h_exp_pos : 1 ≤ k * Ws := by
              have : 0 < k * Ws := mul_pos (by omega) hWs
              omega
            calc
              2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (k * Ws) := Nat.pow_le_pow_right (by norm_num) h_exp_pos
          omega
        have hx_not_le_one : ¬ x ≤ 1 := by omega
        rw [litStates]
        simp [hx_not_le_one]
        have hk_sub_le_j : k - 1 ≤ j := by omega
        have h_div_eq_one : (x / 2 ^ Ws) / 2 ^ ((k - 1) * Ws) = 1 := by
          calc
            (x / 2 ^ Ws) / 2 ^ ((k - 1) * Ws) = x / (2 ^ Ws * 2 ^ ((k - 1) * Ws)) := by
              rw [Nat.div_div_eq_div_mul]
            _ = x / (2 ^ (Ws + (k - 1) * Ws)) := by rw [pow_add]
            _ = x / (2 ^ (k * Ws)) := by
              rw [show Ws + (k - 1) * Ws = k * Ws by
                calc
                  Ws + (k - 1) * Ws = Ws * 1 + Ws * (k - 1) := by ring
                  _ = Ws * (1 + (k - 1)) := by rw [Nat.mul_add]
                  _ = Ws * k := by rw [Nat.add_sub_cancel' hk_ge_one]
                  _ = k * Ws := by ring
                ]
            _ = 1 := hx
        have h_ih := ih (k - 1) (x / 2 ^ Ws) h_div_eq_one hk_sub_le_j
        rw [h_ih]
        -- Now: x % 2^Ws :: (List.range (k-1)).map (fun i => (x/2^Ws)/2^(Ws*i) % 2^Ws)
        -- = (List.range k).map (fun i => x/2^(Ws*i) % 2^Ws)
        have h_range : (List.range k : List ℕ) = 0 :: List.map (· + 1) (List.range (k - 1)) := by
          rw [← Nat.sub_add_cancel hk_ge_one, List.range_succ_eq_map]
          simp
        rw [h_range, List.map_cons]
        -- Goal: x % 2^Ws :: ... = (x / 2^(Ws*0) % 2^Ws) :: ...
        -- First simplify the head: x / 2^(Ws*0) % 2^Ws = x % 2^Ws
        have h_head : x / 2 ^ (Ws * 0) % 2 ^ Ws = x % 2 ^ Ws := by simp
        rw [h_head]
        -- Now we need equality of the tails
        rw [List.map_map]
        -- Goal: x % 2^Ws :: ... = x % 2^Ws :: ...
        -- Apply List.map_congr_left to the tail
        congr 1
        -- Goal: List.map (fun i => x / 2 ^ Ws / 2 ^ (Ws * i) % 2 ^ Ws) (List.range (k - 1))
        -- = List.map ((fun i => x / 2 ^ (Ws * i) % 2 ^ Ws) ∘ (fun x => x + 1)) (List.range (k - 1))
        -- Simplify the RHS function
        have h_fun_eq : (fun i : ℕ => x / 2 ^ (Ws * i) % 2 ^ Ws) ∘ (fun x => x + 1) =
                        fun i : ℕ => x / 2 ^ (Ws * (i + 1)) % 2 ^ Ws := by
          ext i; simp
        rw [h_fun_eq]
        -- Now: List.map f l = List.map g l
        refine List.map_congr_left ?_
        intro a ha
        calc
          x / 2 ^ Ws / 2 ^ (Ws * a) % 2 ^ Ws = (x / 2 ^ Ws) / 2 ^ (Ws * a) % 2 ^ Ws := rfl
          _ = x / (2 ^ Ws * 2 ^ (Ws * a)) % 2 ^ Ws := by rw [Nat.div_div_eq_div_mul]
          _ = x / (2 ^ (Ws + Ws * a)) % 2 ^ Ws := by rw [pow_add]
          _ = x / (2 ^ (Ws * (a + 1))) % 2 ^ Ws := by
            rw [show Ws + Ws * a = Ws * (a + 1) by
              calc
                Ws + Ws * a = Ws * 1 + Ws * a := by ring
                _ = Ws * (1 + a) := by rw [Nat.mul_add]
                _ = Ws * (a + 1) := by rw [add_comm]
              ]
          _ = x / 2 ^ (Ws * (a + 1)) % 2 ^ Ws := rfl
  exact h_gen 16 k x hx hk

/-- `lcount`, when positive, is at most `16` and marks the leading `1`. -/
theorem lcount_spec (Ws x : ℕ) (h : 0 < lcount Ws x) :
    lcount Ws x ≤ 16 ∧ x / 2 ^ (lcount Ws x * Ws) = 1 := by
  -- define the auxiliary recursion explicitly
  set f : ℕ → ℕ → ℕ := fun j k =>
    @Nat.rec (fun _ => ℕ → ℕ) (fun _ => 0)
      (fun _ ih k' => bsel (Nat.beq (Nat.shiftRight x (Nat.mul k' Ws)) 1) k' (ih (Nat.succ k'))) j k
  with hf
  have hf0 : ∀ k, f 0 k = 0 := by
    intro k
    simp [f]
  have hf_succ : ∀ j k, f (j + 1) k = bsel (Nat.beq (Nat.shiftRight x (Nat.mul k Ws)) 1) k (f j (k + 1)) := by
    intro j k
    simp [f]
  have h_lcount : lcount Ws x = f 16 1 := by
    simp [lcount, f]
  -- invariant: if f j k ≠ 0, then k ≤ f j k < k + j and x >>> (f j k * Ws) = 1
  have hinv : ∀ j k, f j k ≠ 0 → (k ≤ f j k ∧ f j k < k + j ∧ Nat.shiftRight x (Nat.mul (f j k) Ws) = 1) := by
    intro j
    induction' j with j ih
    · intro k hk
      simp [hf0] at hk
    · intro k hk
      rw [hf_succ j k] at hk
      by_cases hbit : Nat.shiftRight x (Nat.mul k Ws) = 1
      · -- then bsel returns k
        have hbsel : bsel (Nat.beq (Nat.shiftRight x (Nat.mul k Ws)) 1) k (f j (k + 1)) = k := by
          rw [bsel_eq]
          have hbeq : Nat.beq (Nat.shiftRight x (Nat.mul k Ws)) 1 = true := by
            rw [Nat.beq_eq, hbit]
          rw [hbeq]
          rfl
        rw [hbsel] at hk
        have h1 : k ≤ k := Nat.le_refl k
        have h2 : k < k + (j + 1) := by
          omega
        have h3 : Nat.shiftRight x (Nat.mul k Ws) = 1 := hbit
        -- need to return properties about f (j+1) k
        rw [hf_succ j k, hbsel]
        exact ⟨h1, h2, h3⟩
      · -- bsel returns f j (k+1)
        have hbsel : bsel (Nat.beq (Nat.shiftRight x (Nat.mul k Ws)) 1) k (f j (k + 1)) = f j (k + 1) := by
          rw [bsel_eq]
          have hbeq : Nat.beq (Nat.shiftRight x (Nat.mul k Ws)) 1 = false := by
            rw [Bool.eq_false_iff]
            intro htrue
            apply hbit
            rw [← Nat.beq_eq]
            exact htrue
          rw [hbeq]
          rfl
        rw [hbsel] at hk
        have ih_res := ih (k + 1) hk
        rcases ih_res with ⟨hle, hlt, hshift⟩
        have hle' : k ≤ f j (k + 1) := by
          omega
        have hlt' : f j (k + 1) < k + (j + 1) := by
          omega
        rw [hf_succ j k, hbsel]
        exact ⟨hle', hlt', hshift⟩
  -- now specialize to j = 16, k = 1
  rw [h_lcount] at h
  have hpos : f 16 1 ≠ 0 := by omega
  rcases hinv 16 1 hpos with ⟨hle, hlt, hshift⟩
  have hle16 : f 16 1 ≤ 16 := by omega
  have hdiv : x / 2 ^ (f 16 1 * Ws) = 1 := by
    rw [← Nat.shiftRight_eq_div_pow]
    exact hshift
  rw [h_lcount]
  exact ⟨hle16, hdiv⟩


lemma lcount_step (Ws x : Nat) (n : Nat) :
    @Nat.rec (fun _ => Nat → Nat) (fun _ => 0) (fun _ ih k' => bsel (Nat.beq (Nat.shiftRight x (Nat.mul k' Ws)) 1) k' (ih (Nat.succ k'))) (n + 1) =
    fun k' => bsel (Nat.beq (Nat.shiftRight x (Nat.mul k' Ws)) 1) k' (@Nat.rec (fun _ => Nat → Nat) (fun _ => 0) (fun _ ih k' => bsel (Nat.beq (Nat.shiftRight x (Nat.mul k' Ws)) 1) k' (ih (Nat.succ k'))) n k'.succ) :=
  Nat.rec_add_one (fun _ => 0) (fun (_n : Nat) (ih' : Nat → Nat) (k' : Nat) => bsel (Nat.beq (Nat.shiftRight x (Nat.mul k' Ws)) 1) k' (ih' (Nat.succ k'))) n

lemma lcount_aux (Ws x : Nat) (i k : Nat) (h_eq : Nat.shiftRight x ((k + i) * Ws) = 1) (h_lt : ∀ j, k ≤ j → j < k + i → Nat.shiftRight x (j * Ws) ≠ 1) :
    @Nat.rec (fun _ => Nat → Nat) (fun _ => 0) (fun _ ih k' => bsel (Nat.beq (Nat.shiftRight x (Nat.mul k' Ws)) 1) k' (ih (Nat.succ k'))) (i + 1) k = k + i := by
  induction' i with i ih generalizing k
  · -- i = 0: need to show f_1 k = k
    have h_eq' : Nat.shiftRight x (Nat.mul k Ws) = 1 := by
      simpa using h_eq
    have h_beq : (Nat.beq (Nat.shiftRight x (Nat.mul k Ws)) 1) = true := by
      rw [Nat.beq_eq]
      exact h_eq'
    rw [lcount_step Ws x 0]
    beta_reduce
    -- Goal: bsel (Nat.beq (Nat.shiftRight x (Nat.mul k Ws)) 1) k (Nat.rec ... 0 k.succ) = k
    -- Nat.rec ... 0 = fun _ => 0
    have h_base : (@Nat.rec (fun _ => Nat → Nat) (fun _ => 0) (fun _ ih k' => bsel (Nat.beq (Nat.shiftRight x (Nat.mul k' Ws)) 1) k' (ih (Nat.succ k'))) 0) = fun _ => 0 := rfl
    rw [h_base]
    simp
    -- Goal: bsel (Nat.beq (Nat.shiftRight x (Nat.mul k Ws)) 1) k 0 = k
    rw [bsel_eq]
    -- Goal: (if (x >>> (k * Ws)).beq 1 then k else 0) = k
    -- h_beq: (x.shiftRight (k.mul Ws)).beq 1 = true
    -- Create a version of h_beq that matches the goal syntax
    have h_beq' : (x >>> (k * Ws)).beq 1 = true := by
      simpa using h_beq
    rw [h_beq']
    rfl
  · -- i = i+1: need to show f_{i+2} k = k+(i+1)
    have hk_lt : k < k + (i + 1) := by omega
    have h_cond_k : Nat.shiftRight x (k * Ws) ≠ 1 := h_lt k (le_refl k) hk_lt
    have h_beq : (Nat.beq (Nat.shiftRight x (Nat.mul k Ws)) 1) = false := by
      by_contra h_ne_false
      have h_true : (Nat.beq (Nat.shiftRight x (Nat.mul k Ws)) 1) = true := Bool.eq_true_of_ne_false h_ne_false
      rw [Nat.beq_eq] at h_true
      exact h_cond_k h_true
    rw [lcount_step Ws x (i+1)]
    beta_reduce
    -- Goal: bsel (Nat.beq (Nat.shiftRight x (Nat.mul k Ws)) 1) k (Nat.rec ... (i+1) k.succ) = k+(i+1)
    rw [bsel_eq]
    -- Goal: (if Nat.beq (Nat.shiftRight x (Nat.mul k Ws)) 1 then k else Nat.rec ... (i+1) k.succ) = k+(i+1)
    -- The goal might have been normalized to (Nat.beq ... 1 = true)
    -- Use by_cases to handle both cases
    by_cases h_cond : Nat.beq (Nat.shiftRight x (Nat.mul k Ws)) 1 = true
    · -- h_cond: the condition is true
      rw [ite_eq_left h_cond]
      -- Goal: k = k+(i+1)
      -- But h_beq says the condition is false, contradiction
      rw [h_beq] at h_cond
      exact absurd h_cond (by decide)
    · -- h_cond: the condition is false
      rw [ite_eq_right h_cond]
      -- Goal: Nat.rec ... (i+1) k.succ = k+(i+1)
      -- k.succ = k+1, so we need: Nat.rec ... (i+1) (k+1) = k+(i+1)
      -- ih (k+1) gives: Nat.rec ... (i+1) (k+1) = (k+1)+i
      -- We need to relate (k+1)+i to k+(i+1)
      have h_ih := ih (k + 1) (by
        simpa [add_comm, add_left_comm, add_assoc] using h_eq) (by
        intro j hj_ge hj_lt
        apply h_lt j (le_trans (by omega) hj_ge) (by omega))
      -- h_ih : Nat.rec ... (i+1) (k+1) = (k+1)+i
      -- Goal: Nat.rec ... (i+1) k.succ = k+(i+1)
      -- k.succ = k+1
      simpa [add_comm, add_left_comm, add_assoc] using h_ih

/-- A full literal has `16` states. -/
theorem lcount_full (Ws x : ℕ) (hWs : 0 < Ws) (h : x / 2 ^ (16 * Ws) = 1) : lcount Ws x = 16 := by
  have hshift16 : Nat.shiftRight x (16 * Ws) = 1 := by
    -- h : x / 2 ^ (16 * Ws) = 1
    -- Nat.shiftRight_eq_div_pow: m >>> n = m / 2 ^ n
    -- We need to use this to relate shiftRight to division
    simpa [Nat.shiftRight_eq_div_pow] using h
  have hshift_lt : ∀ k, 1 ≤ k → k < 16 → Nat.shiftRight x (k * Ws) ≠ 1 := by
    intro k hk1 hk16
    have hpos : 0 < 2 ^ (16 * Ws) := pow_pos (by norm_num) (16 * Ws)
    have hx_ge : 2 ^ (16 * Ws) ≤ x := by
      by_contra! hlt
      have hdiv : x / 2 ^ (16 * Ws) = 0 := Nat.div_eq_of_lt hlt
      rw [hdiv] at h
      exact Nat.one_ne_zero h.symm
    have hpos2 : 0 < 2 ^ (k * Ws) := pow_pos (by norm_num) (k * Ws)
    have h_pow_ineq : 2 * 2 ^ (k * Ws) ≤ 2 ^ (16 * Ws) := by
      have hk' : k * Ws + 1 ≤ 16 * Ws := by
        have hk15 : k ≤ 15 := by omega
        have hWs1 : 1 ≤ Ws := by omega
        nlinarith
      calc
        2 * 2 ^ (k * Ws) = 2 ^ 1 * 2 ^ (k * Ws) := by norm_num
        _ = 2 ^ (k * Ws + 1) := by ring
        _ ≤ 2 ^ (16 * Ws) := Nat.pow_le_pow_right (by omega) hk'
    have hx_ge2 : 2 * 2 ^ (k * Ws) ≤ x :=
      le_trans h_pow_ineq hx_ge
    have hdiv_ge : 2 ≤ x / 2 ^ (k * Ws) := by
      rw [Nat.le_div_iff_mul_le hpos2]
      -- Need: 2 * 2^(k*Ws) ≤ x
      simpa [mul_comm] using hx_ge2
    -- Now: x / 2^(k*Ws) ≥ 2, so x / 2^(k*Ws) ≠ 1
    -- And Nat.shiftRight x (k*Ws) = x / 2^(k*Ws)
    have h_ne_one : x / 2 ^ (k * Ws) ≠ 1 := by omega
    simpa [Nat.shiftRight_eq_div_pow] using h_ne_one
  -- Now apply lcount_aux with i = 15, k = 1
  -- lcount_aux says: if cond (k+i) = 1 and cond j ≠ 1 for j ∈ [k, k+i), then f_{i+1} k = k+i
  -- We need f_16 1 = 16, so i+1 = 16, i = 15, k = 1
  -- k+i = 1+15 = 16
  have h_aux := lcount_aux Ws x 15 1 ?_ ?_
  · -- h_aux : @Nat.rec ... (15+1) 1 = 1+15
    -- Goal: lcount Ws x = 16
    dsimp [lcount]
    -- Goal: @Nat.rec ... 16 1 = 16
    -- h_aux: @Nat.rec ... (15+1) 1 = 1+15
    -- 15+1 = 16 and 1+15 = 16 definitionally
    exact h_aux
  · -- h_eq: cond (1 + 15) = 1, i.e., cond 16 = 1
    simpa [add_comm] using hshift16
  · -- h_lt: for j ∈ [1, 16), cond j ≠ 1
    intro j hj_ge hj_lt
    apply hshift_lt j hj_ge hj_lt

/-- `litsOK`: every literal but the last is full, the last has a leading `1` at `1` to `16` states. -/
theorem litsOK_iff (Ws : ℕ) (lits : List ℕ) :
    litsOK Ws lits = true ↔ ∀ i < lits.length,
      (i + 1 < lits.length → lits.getD i 0 / 2 ^ (16 * Ws) = 1) ∧
        (i + 1 = lits.length → 0 < lcount Ws (lits.getD i 0)) := by
  induction lits with
  | nil =>
      simp [litsOK]
  | cons x t ih =>
      by_cases h_empty : t = []
      · subst h_empty
        simp [litsOK]
      · have h_ne : t ≠ [] := h_empty
        -- Expand litsOK for x :: t using the definition
        simp only [litsOK, List.length_cons, List.getD, bsel_eq, Nat.beq_eq]
        -- Since t ≠ [], the inner List.rec returns false
        have h_inner_false : (List.rec true (fun _ _ _ => false) t) = false := by
          cases t with
          | nil => exact absurd rfl h_ne
          | cons a as => rfl
        rw [h_inner_false]
        simp
        -- The goal's LHS has List.rec true ... t = true which is litsOK Ws t = true
        -- Let's use the induction hypothesis ih
        -- ih: litsOK Ws t = true ↔ ∀ i < t.length, (i + 1 < t.length → t.getD i 0 / 2 ^ (16 * Ws) = 1) ∧ (i + 1 = t.length → 0 < lcount Ws (t.getD i 0))
        -- We need to relate: (x >>> (16*Ws) = 1 ∧ litsOK Ws t = true) ↔ (∀ i ≤ t.length, ...)
        -- Let's prove this by constructing the equivalence
        -- The goal is: (x >>> (16*Ws) = 1 ∧ litsOK Ws t = true) ↔ (∀ i ≤ t.length, ...)
        -- We'll prove this by constructing both directions
        constructor
        · rintro ⟨hx, ht⟩ i hi
          rcases Nat.lt_or_eq_of_le hi with (hi_lt | rfl)
          · -- i < t.length
            -- Need: (i < t.length → (x :: t)[i]?.getD 0 / 2 ^ (16 * Ws) = 1) ∧ (i = t.length → 0 < lcount Ws ((x :: t)[i]?.getD 0))
            -- The second part is vacuously true since i < t.length and i = t.length can't both hold
            -- We handle i = 0 and i > 0 separately
            by_cases hi_zero : i = 0
            · subst hi_zero
              -- i = 0: need x / 2^(16*Ws) = 1, which is hx
              have h_getD : (x :: t)[0]?.getD 0 = x := by simp
              refine ⟨?_, ?_⟩
              · intro; rw [h_getD]; rw [← Nat.shiftRight_eq_div_pow]; exact hx
              · intro h_eq; exfalso; omega
            · -- i > 0: write i = j+1
              have hi_pos : 0 < i := Nat.pos_of_ne_zero hi_zero
              obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hi_zero
              rw [hj]
              -- Now i = j+1, and j < t.length (since j+1 < t.length)
              have hj_lt : j < t.length := by omega
              -- (x :: t)[j+1]?.getD 0 = t[j]?.getD 0
              have h_getD : (x :: t)[j+1]?.getD 0 = t.getD j 0 := by simp
              -- From ih, we have for index j: (j+1 < t.length → t.getD j 0 / 2^(16*Ws) = 1) ∧ (j+1 = t.length → 0 < lcount Ws (t.getD j 0))
              have ht' : litsOK Ws t = true := by
                simpa [litsOK, bsel_eq, Nat.beq_eq, Nat.blt_eq] using ht
              have h_cond := (ih.mp ht') j hj_lt
              rcases h_cond with ⟨h1, h2⟩
              -- h1: j+1 < t.length → t.getD j 0 / 2^(16*Ws) = 1
              -- Since j+1 = i < t.length, we have j+1 < t.length
              have h_lt : j + 1 < t.length := by omega
              have h_eq1 := h1 h_lt
              refine ⟨?_, ?_⟩
              · intro; rw [h_getD]; exact h_eq1
              · intro h_eq; exfalso; omega
          · -- i = t.length
            -- Goal: (t.length < t.length → ...) ∧ (t.length = t.length → 0 < lcount Ws ((x :: t)[t.length]?.getD 0))
            -- The first part is trivially true
            -- For the second part, we need 0 < lcount Ws ((x :: t)[t.length]?.getD 0)
            -- (x :: t)[t.length] = last element of t = t[t.length-1]
            have h_len_pos : 0 < t.length := by
              by_contra! h
              have h_len0 : t.length = 0 := by omega
              have : t = [] := List.eq_nil_of_length_eq_zero h_len0
              exact h_ne this
            have h_last_idx : t.length - 1 < t.length := by omega
            have ht' : litsOK Ws t = true := by
              simpa [litsOK, bsel_eq, Nat.beq_eq, Nat.blt_eq] using ht
            have h_cond := (ih.mp ht') (t.length - 1) h_last_idx
            rcases h_cond with ⟨h1, h2⟩
            have h_eq : (t.length - 1) + 1 = t.length := by omega
            have h_lcount := h2 h_eq
            have h_getD : (x :: t)[t.length]?.getD 0 = t.getD (t.length - 1) 0 := by
              cases t with
              | nil =>
                -- t = [], but we know t ≠ [] from h_ne, so this case is impossible
                exfalso; exact h_ne rfl
              | cons a as =>
                simp [List.length_cons]
            refine ⟨?_, ?_⟩
            · intro h_lt; exfalso; omega
            · intro _; rw [h_getD]; exact h_lcount
        · intro h
          constructor
          · -- x >>> (16*Ws) = 1
            have h0 := h 0 (by omega)
            rcases h0 with ⟨h0_lt, h0_eq⟩
            have h_len_pos : 0 < t.length := by
              by_contra! h0_len
              have : t.length = 0 := by omega
              have : t = [] := List.eq_nil_of_length_eq_zero this
              exact h_ne this
            have h_val := h0_lt h_len_pos
            have h_getD : (x :: t)[0]?.getD 0 = x := by simp
            rw [h_getD] at h_val
            rw [Nat.shiftRight_eq_div_pow]
            exact h_val
          · -- litsOK Ws t = true
            -- We need to prove litsOK Ws t = true
            -- By ih, this is equivalent to B = ∀ i < t.length, (i + 1 < t.length → t.getD i 0 / 2 ^ (16 * Ws) = 1) ∧ (i + 1 = t.length → 0 < lcount Ws (t.getD i 0))
            -- We need to construct B from h
            -- The mapping: B i corresponds to C (i+1) for i < t.length-1, and B (t.length-1) corresponds to C t.length
            have h_lt : ∀ i < t.length, (i + 1 < t.length → t.getD i 0 / 2 ^ (16 * Ws) = 1) ∧ (i + 1 = t.length → 0 < lcount Ws (t.getD i 0)) := by
              intro i hi
              -- hi: i < t.length
              by_cases h_lt_i : i + 1 < t.length
              · -- i + 1 < t.length: need t.getD i 0 / 2 ^ (16 * Ws) = 1
                -- From C (i+1): (i+1 ≤ t.length → ((x :: t)[i+1]?.getD 0 / 2 ^ (16 * Ws) = 1) ∧ (i+1 = t.length → 0 < lcount Ws ((x :: t)[i+1]?.getD 0)))
                -- Since i+1 < t.length, i+1 ≤ t.length
                have hi1_le : i + 1 ≤ t.length := by omega
                have h_i1 := h (i + 1) hi1_le
                rcases h_i1 with ⟨h_i1_lt, h_i1_eq⟩
                -- h_i1_lt: i+1 < t.length → (x :: t)[i+1]?.getD 0 / 2 ^ (16 * Ws) = 1
                have h_val := h_i1_lt h_lt_i
                -- h_val: (x :: t)[i+1]?.getD 0 / 2 ^ (16 * Ws) = 1
                -- (x :: t)[i+1]?.getD 0 = t.getD i 0
                have h_getD : (x :: t)[i+1]?.getD 0 = t.getD i 0 := by simp
                rw [h_getD] at h_val
                constructor
                · intro; exact h_val
                · intro h_eq; exfalso; omega
              · -- i + 1 ≥ t.length, so i + 1 = t.length (since i < t.length)
                have h_eq_i : i + 1 = t.length := by omega
                -- Need: 0 < lcount Ws (t.getD i 0)
                -- From C t.length: (t.length ≤ t.length → ((x :: t)[t.length]?.getD 0 / 2 ^ (16 * Ws) = 1) ∧ (t.length = t.length → 0 < lcount Ws ((x :: t)[t.length]?.getD 0)))
                have h_tlen := h t.length (by omega)
                rcases h_tlen with ⟨_, h_tlen_eq⟩
                have h_lcount := h_tlen_eq rfl
                -- h_lcount: 0 < lcount Ws ((x :: t)[t.length]?.getD 0)
                -- (x :: t)[t.length]?.getD 0 = t.getD i 0 (since i = t.length - 1)
                have h_getD : (x :: t)[t.length]?.getD 0 = t.getD i 0 := by
                  have : i = t.length - 1 := by omega
                  cases t with
                  | nil => exfalso; exact h_ne rfl
                  | cons a as => simp [this]
                rw [h_getD] at h_lcount
                constructor
                · intro h_lt'; exfalso; omega
                · intro _; exact h_lcount
            -- Now use ih
            simpa [litsOK, bsel_eq, Nat.beq_eq, Nat.blt_eq] using (ih.mpr h_lt)


lemma litsOK_cons_eq (Ws x : ℕ) (xs : List ℕ) :
    litsOK Ws (x :: xs) =
    if xs = [] then Nat.blt 0 (lcount Ws x)
    else bsel (Nat.beq (Nat.shiftRight x (Nat.mul 16 Ws)) 1) (litsOK Ws xs) false := by
  cases xs with
  | nil => simp [litsOK]
  | cons y ys => simp [litsOK]

lemma litStates_getD_eq (Ws x k : ℕ) (hWs : 0 < Ws) (hk1 : 1 ≤ k) (hk16 : k ≤ 16) (hx : x / 2 ^ (k * Ws) = 1) (i : ℕ) (hi : i < k) :
    (litStates Ws 16 x).getD i 0 = x / 2 ^ (Ws * i) % 2 ^ Ws := by
  rw [litStates_eq Ws x k hWs hk1 hk16 hx]
  have hlen : i < ((List.range k).map fun i => x / 2 ^ (Ws * i) % 2 ^ Ws).length := by
    simpa [List.length_map, List.length_range] using hi
  rw [List.getD_eq_getElem _ _ hlen, List.getElem_map]
  have hi_range : i < (List.range k).length := by simpa [List.length_range] using hi
  simp [List.getElem_range hi_range]

/-- The decoded states of aligned literals: the state `idx` is the digit `idx % 16` of the literal
`idx / 16`. -/
theorem allStates_getD (Ws : ℕ) (hWs : 0 < Ws) (lits : List ℕ) (h : litsOK Ws lits = true) (idx : ℕ)
    (hidx : idx < (allStates Ws lits).length) :
    (allStates Ws lits).getD idx 0 = lits.getD (idx / 16) 0 / 2 ^ (Ws * (idx % 16)) % 2 ^ Ws := by
  revert h idx
  induction lits with
  | nil =>
      intro h idx hidx
      exfalso; exact Nat.not_lt_zero _ hidx
  | cons x xs ih =>
      intro h idx hidx
      rw [allStates, List.flatMap_cons] at hidx ⊢
      -- hidx : idx < (litStates Ws 16 x ++ allStates Ws xs).length
      -- Goal: (litStates Ws 16 x ++ allStates Ws xs).getD idx 0 = (x :: xs).getD (idx / 16) 0 / 2 ^ (Ws * (idx % 16)) % 2 ^ Ws
      -- The pretty printer shows allStates as List.flatMap, so we fold it back
      rw [← allStates]
      -- Goal: (litStates Ws 16 x ++ allStates Ws xs).getD idx 0 = (x :: xs).getD (idx / 16) 0 / 2 ^ (Ws * (idx % 16)) % 2 ^ Ws
      have hlits := (litsOK_iff Ws (x :: xs)).mp h
      have hhead := hlits 0 (by simp)
      have hhead' : (1 < (x :: xs).length → x / 2 ^ (16 * Ws) = 1) ∧ (1 = (x :: xs).length → 0 < lcount Ws x) := by
        simpa using hhead
      rcases hhead' with ⟨hfull, hlast⟩
      by_cases hxs_empty : xs = []
      · subst hxs_empty
        have hpos : 0 < lcount Ws x := hlast (by simp)
        have hk := lcount_spec Ws x hpos
        rcases hk with ⟨hk_le, hx_div⟩
        have hk1 : 1 ≤ lcount Ws x := by omega
        have hlen_ls : (litStates Ws 16 x).length = lcount Ws x := by
          rw [litStates_eq Ws x (lcount Ws x) hWs hk1 hk_le hx_div]
          simp
        by_cases hlt : idx < (litStates Ws 16 x).length
        · rw [List.getD_append _ _ _ idx hlt]
          rw [litStates_eq Ws x (lcount Ws x) hWs hk1 hk_le hx_div]
          have hidx_lt_16 : idx < 16 := by
            rw [hlen_ls] at hlt
            omega
          have hdiv : idx / 16 = 0 := Nat.div_eq_of_lt hidx_lt_16
          have hmod : idx % 16 = idx := Nat.mod_eq_of_lt hidx_lt_16
          rw [hdiv, hmod, List.getD_cons_zero]
          have hlen_map : idx < ((List.range (lcount Ws x)).map fun i => x / 2 ^ (Ws * i) % 2 ^ Ws).length := by
            rw [hlen_ls] at hlt
            simpa [List.length_map, List.length_range] using hlt
          rw [List.getD_eq_getElem _ _ hlen_map, List.getElem_map]
          have hi_range : idx < (List.range (lcount Ws x)).length := by
            rw [hlen_ls] at hlt
            simpa [List.length_range] using hlt
          simp [List.getElem_range hi_range]
        · rw [List.length_append, hlen_ls] at hidx
          -- hidx : idx < lcount Ws x + 0
          have : (List.flatMap (litStates Ws 16) []).length = 0 := by simp
          rw [this] at hidx
          omega
      · have hx_full : x / 2 ^ (16 * Ws) = 1 := hfull (by
          have : 1 < (x :: xs).length := by
            have hpos_len : 0 < xs.length := List.length_pos_of_ne_nil hxs_empty
            simpa [List.length_cons] using hpos_len
          exact this)
        have hlen_ls : (litStates Ws 16 x).length = 16 := by
          have h16pos : 1 ≤ 16 := by omega
          have h16le : 16 ≤ 16 := by omega
          rw [litStates_eq Ws x 16 hWs h16pos h16le hx_full]
          simp
        rw [List.length_append, hlen_ls] at hidx
        -- hidx : idx < 16 + (allStates Ws xs).length
        by_cases hlt : idx < 16
        · have h_lt : idx < (litStates Ws 16 x).length := by
            rw [hlen_ls]
            exact hlt
          rw [List.getD_append (litStates Ws 16 x) (allStates Ws xs) 0 idx h_lt]
          have hdiv : idx / 16 = 0 := Nat.div_eq_of_lt hlt
          have hmod : idx % 16 = idx := Nat.mod_eq_of_lt hlt
          rw [hdiv, hmod, List.getD_cons_zero]
          have h16pos : 1 ≤ 16 := by omega
          have h16le : 16 ≤ 16 := by omega
          rw [litStates_eq Ws x 16 hWs h16pos h16le hx_full]
          have hlen_map : idx < ((List.range 16).map fun i => x / 2 ^ (Ws * i) % 2 ^ Ws).length := by
            simpa [List.length_map, List.length_range] using hlt
          rw [List.getD_eq_getElem _ _ hlen_map, List.getElem_map]
          have hi_range : idx < (List.range 16).length := by
            simpa [List.length_range] using hlt
          simp [List.getElem_range hi_range]
        · have hle : 16 ≤ idx := by omega
          have hle' : (litStates Ws 16 x).length ≤ idx := by
            rw [hlen_ls]
            exact hle
          rw [List.getD_append_right (litStates Ws 16 x) (allStates Ws xs) 0 idx hle']
          -- Goal: (allStates Ws xs).getD (idx - (litStates Ws 16 x).length) 0 = (x :: xs).getD (idx / 16) 0 / 2 ^ (Ws * (idx % 16)) % 2 ^ Ws
          have hidx' : idx - 16 < (allStates Ws xs).length := by
            have : idx < 16 + (allStates Ws xs).length := by simpa [allStates] using hidx
            omega
          have hlits_xs : litsOK Ws xs = true := by
            rw [litsOK_cons_eq Ws x xs] at h
            split at h
            · exfalso; exact hxs_empty ‹_›
            · -- h: bsel (Nat.beq ... 1) (litsOK Ws xs) false = true
              have hbeq : Nat.beq (Nat.shiftRight x (Nat.mul 16 Ws)) 1 = true := by
                by_contra! hbeq'
                have hfalse : bsel (Nat.beq (Nat.shiftRight x (Nat.mul 16 Ws)) 1) (litsOK Ws xs) false = false := by
                  rw [Bool.eq_false_of_not_eq_true hbeq']
                  simp
                rw [hfalse] at h
                exact Bool.noConfusion h
              rw [hbeq] at h
              simpa using h
          -- Apply induction hypothesis
          have h_eq := ih hlits_xs (idx - 16) hidx'
          -- h_eq : (allStates Ws xs).getD (idx - 16) 0 = xs.getD ((idx - 16) / 16) 0 / 2 ^ (Ws * ((idx - 16) % 16)) % 2 ^ Ws
          -- Goal: (allStates Ws xs).getD (idx - (litStates Ws 16 x).length) 0 = (x :: xs).getD (idx / 16) 0 / 2 ^ (Ws * (idx % 16)) % 2 ^ Ws
          -- Rewrite (litStates Ws 16 x).length to 16
          rw [hlen_ls]
          -- Goal: (allStates Ws xs).getD (idx - 16) 0 = (x :: xs).getD (idx / 16) 0 / 2 ^ (Ws * (idx % 16)) % 2 ^ Ws
          -- Now rewrite the RHS using the arithmetic identities
          have hdiv_sub : (idx - 16) / 16 = idx / 16 - 1 := by omega
          have hmod_sub : (idx - 16) % 16 = idx % 16 := by omega
          rw [hdiv_sub, hmod_sub] at h_eq
          -- h_eq : (allStates Ws xs).getD (idx - 16) 0 = xs.getD (idx / 16 - 1) 0 / 2 ^ (Ws * (idx % 16)) % 2 ^ Ws
          -- Goal: (allStates Ws xs).getD (idx - 16) 0 = (x :: xs).getD (idx / 16) 0 / 2 ^ (Ws * (idx % 16)) % 2 ^ Ws
          -- Need to relate xs.getD (idx / 16 - 1) 0 to (x :: xs).getD (idx / 16) 0
          -- Since idx / 16 ≥ 1 (because idx ≥ 16)
          have hdiv_pos : 0 < idx / 16 := by omega
          rcases Nat.exists_eq_succ_of_ne_zero hdiv_pos.ne' with ⟨n, hn⟩
          -- hn : idx / 16 = n.succ
          -- Rewrite idx / 16 to n.succ in the goal
          rw [hn]
          -- Goal: (allStates Ws xs).getD (idx - 16) 0 = (x :: xs).getD n.succ 0 / 2 ^ (Ws * (idx % 16)) % 2 ^ Ws
          rw [List.getD_cons_succ]
          -- Goal: (allStates Ws xs).getD (idx - 16) 0 = xs.getD n 0 / 2 ^ (Ws * (idx % 16)) % 2 ^ Ws
          -- Now h_eq: (allStates Ws xs).getD (idx - 16) 0 = xs.getD (idx / 16 - 1) 0 / 2 ^ (Ws * (idx % 16)) % 2 ^ Ws
          -- Rewrite idx / 16 - 1 = n.succ - 1 = n
          have : idx / 16 - 1 = n := by omega
          rw [this] at h_eq
          -- h_eq: (allStates Ws xs).getD (idx - 16) 0 = xs.getD n 0 / 2 ^ (Ws * (idx % 16)) % 2 ^ Ws
          -- Now h_eq matches the goal
          exact h_eq

theorem length_litStates_le_k (Ws x k : ℕ) : List.length (litStates Ws k x) ≤ k := by
  induction k generalizing x with
  | zero =>
    unfold litStates
    rfl
  | succ k ih =>
    unfold litStates
    split
    · simp
    · simp
      have h := ih (x / 2 ^ Ws)
      omega

theorem length_litStates_of_full (Ws x : ℕ) (hWs : 0 < Ws) (hx : x / 2 ^ (16 * Ws) = 1) :
    List.length (litStates Ws 16 x) = 16 := by
  have h_eq := litStates_eq Ws x 16 hWs (by omega) (by omega) hx
  rw [h_eq]
  simp

theorem length_litStates_of_last (Ws x : ℕ) (hWs : 0 < Ws) (hpos : 0 < lcount Ws x) :
    List.length (litStates Ws 16 x) = lcount Ws x := by
  have hlc := lcount_spec Ws x hpos
  rcases hlc with ⟨hlc_le, hx⟩
  have h_eq := litStates_eq Ws x (lcount Ws x) hWs (by omega) hlc_le hx
  rw [h_eq]
  simp

theorem length_litStates_pos_of_last (Ws x : ℕ) (hWs : 0 < Ws) (hpos : 0 < lcount Ws x) :
    0 < List.length (litStates Ws 16 x) := by
  rw [length_litStates_of_last Ws x hWs hpos]
  exact hpos

theorem litsOK_cons_of_litsOK (Ws : ℕ) (x : ℕ) (xs : List ℕ) (h : litsOK Ws (x :: xs) = true) : litsOK Ws xs = true := by
  have h_iff := (litsOK_iff Ws (x :: xs)).mp h
  apply (litsOK_iff Ws xs).mpr
  intro i hi
  have hi_succ : i + 1 < (x :: xs).length := by
    have : (x :: xs).length = xs.length + 1 := by simp
    rw [this]
    omega
  have h_cond := h_iff (i + 1) hi_succ
  rcases h_cond with ⟨h_not_last, h_last⟩
  constructor
  · intro h_lt
    have h_lt' : (i + 1) + 1 < (x :: xs).length := by
      have : (x :: xs).length = xs.length + 1 := by simp
      rw [this]
      omega
    have h_get : (x :: xs).getD (i + 1) 0 = xs.getD i 0 := by simp
    have h_eq := h_not_last h_lt'
    simpa [h_get] using h_eq
  · intro h_eq_len
    have h_eq_len' : (i + 1) + 1 = (x :: xs).length := by
      have : (x :: xs).length = xs.length + 1 := by simp
      rw [this]
      omega
    have h_get : (x :: xs).getD (i + 1) 0 = xs.getD i 0 := by simp
    have h_pos := h_last h_eq_len'
    simpa [h_get] using h_pos

/-- The number of decoded states of aligned literals: `16` per literal but the last. -/
theorem allStates_length (Ws : ℕ) (hWs : 0 < Ws) (lits : List ℕ) (h : litsOK Ws lits = true) :
    (allStates Ws lits).length ≤ 16 * lits.length ∧ 16 * (lits.length - 1) < (allStates Ws lits).length + 1 := by
  induction lits with
  | nil =>
    simp [allStates]
  | cons x xs ih =>
    have h_xs : litsOK Ws xs = true := litsOK_cons_of_litsOK Ws x xs h
    rcases ih h_xs with ⟨ih_upper, ih_lower⟩
    have h_iff := (litsOK_iff Ws (x :: xs)).mp h
    have h_first := h_iff 0 (by simp)
    rcases h_first with ⟨h_not_last, h_last⟩
    have h_allStates : allStates Ws (x :: xs) = (litStates Ws 16 x) ++ (allStates Ws xs) := by
      simp [allStates, List.flatMap_cons]
    rw [h_allStates, List.length_append]
    have hx_len : List.length (litStates Ws 16 x) ≤ 16 := length_litStates_le_k Ws x 16
    have h_upper : List.length (litStates Ws 16 x) + (allStates Ws xs).length ≤ 16 * (xs.length + 1) := by
      by_cases hxs : xs = []
      · subst hxs; simp; exact hx_len
      · have hx_full : x / 2 ^ (16 * Ws) = 1 := by
          apply h_not_last
          have hlen_pos : 0 < xs.length := (List.length_pos_iff_ne_nil.mpr hxs)
          -- Need: 0 + 1 < (x :: xs).length = xs.length + 1
          simpa [add_comm] using Nat.succ_lt_succ hlen_pos
        have hx_len_eq : List.length (litStates Ws 16 x) = 16 :=
          length_litStates_of_full Ws x hWs hx_full
        rw [hx_len_eq]
        have h : 16 + (allStates Ws xs).length ≤ 16 + 16 * xs.length :=
          Nat.add_le_add_left ih_upper 16
        -- 16 + 16 * xs.length = 16 * (xs.length + 1)
        simpa [mul_add, add_comm, add_left_comm, add_assoc] using h
    have h_lower : 16 * ((xs.length + 1) - 1) < List.length (litStates Ws 16 x) + (allStates Ws xs).length + 1 := by
      have h_sub : (xs.length + 1) - 1 = xs.length := by omega
      rw [h_sub]
      by_cases hxs : xs = []
      · subst xs
        simp
      · have hx_full : x / 2 ^ (16 * Ws) = 1 := by
          apply h_not_last
          have hlen_pos : 0 < xs.length := (List.length_pos_iff_ne_nil.mpr hxs)
          simpa [add_comm] using Nat.succ_lt_succ hlen_pos
        have hx_len_eq : List.length (litStates Ws 16 x) = 16 :=
          length_litStates_of_full Ws x hWs hx_full
        rw [hx_len_eq]
        -- Goal: 16 * xs.length < 16 + (allStates Ws xs).length + 1
        -- Have: 16 * (xs.length - 1) < (allStates Ws xs).length + 1
        have hpos : 1 ≤ xs.length := by
          have hlen_pos : 0 < xs.length := (List.length_pos_iff_ne_nil.mpr hxs)
          omega
        have h_mul : 16 * xs.length = 16 * (xs.length - 1) + 16 := by
          have hle : 16 ≤ 16 * xs.length := by
            calc
              16 = 16 * 1 := by simp
              _ ≤ 16 * xs.length := Nat.mul_le_mul_left 16 hpos
          calc
            16 * xs.length = (16 * xs.length - 16) + 16 := by rw [Nat.sub_add_cancel hle]
            _ = 16 * (xs.length - 1) + 16 := by rw [Nat.mul_sub_left_distrib, mul_one]
        rw [h_mul]
        have h_ineq : 16 * (xs.length - 1) + 16 < ((allStates Ws xs).length + 1) + 16 :=
          Nat.add_lt_add_right ih_lower 16
        simpa [add_comm, add_left_comm, add_assoc] using h_ineq
    exact And.intro h_upper h_lower

/-! ## Concatenation -/

/-- A run of states: their pack and their number. -/
noncomputable def run (Ws : ℕ) (L : List ℕ) : ℕ × ℕ := (pack Ws L.length fun l => L.getD l 0, L.length)

theorem catR_run (Ws : ℕ) (L1 L2 : List ℕ) : catR Ws (run Ws L1) (run Ws L2) = run Ws (L1 ++ L2) := by
  unfold catR run
  simp
  calc
    (pack Ws L1.length fun l => L1.getD l 0) + (pack Ws L2.length fun l => L2.getD l 0) <<< (Ws * L1.length)
        = app Ws L1.length (pack Ws L1.length (fun l => L1.getD l 0)) (pack Ws L2.length (fun l => L2.getD l 0)) := rfl
    _ = pack Ws (L1.length + L2.length) (fun l => if l < L1.length then L1.getD l 0 else L2.getD (l - L1.length) 0) := by rw [app_pack']
    _ = pack Ws (L1.length + L2.length) (fun l => (L1 ++ L2).getD l 0) := by
      apply pack_congr
      intro l hl
      by_cases h : l < L1.length
      · rw [ite_eq_left h, List.getD_append L1 L2 0 l h]
      · rw [ite_eq_right h]
        have hle : L1.length ≤ l := Nat.le_of_not_lt h
        rw [List.getD_append_right L1 L2 0 l hle]

/-- Adjacent pairs of lists joined, a last odd one kept. -/
def joinP : List (List ℕ) → List (List ℕ)
  | a :: b :: t => (a ++ b) :: joinP t
  | l => l

theorem mergeP_run (Ws : ℕ) (Ls : List (List ℕ)) : mergeP Ws (Ls.map (run Ws)) = (joinP Ls).map (run Ws) := by
  match Ls with
  | [] => rfl
  | [a] => simp [mergeP, joinP]
  | a :: b :: bs =>
      simp [mergeP, joinP, catR_run]
      simpa [mergeP] using mergeP_run Ws bs

theorem joinP_flatten (Ls : List (List ℕ)) : (joinP Ls).flatten = Ls.flatten := by
  induction Ls using joinP.induct with
  | case1 l b t ih =>
    simp [joinP, ih, List.flatten_cons]
  | case2 l h =>
    -- h : ∀ (a b : List ℕ) (t : List (List ℕ)), l = a :: b :: t → False
    -- l has 0 or 1 element
    cases l with
    | nil => rfl
    | cons a as =>
      cases as with
      | nil => rfl
      | cons b bs =>
        exfalso
        exact h a b bs rfl

theorem joinP_length (Ls : List (List ℕ)) : (joinP Ls).length = (Ls.length + 1) / 2 := by
  match Ls with
  | [] => rfl
  | [a] => simp [joinP]
  | a :: b :: bs =>
    simp [joinP, List.length_cons]
    have ih := joinP_length bs
    rw [ih]
    omega

/-- A literal with a leading `1` is the run of its states. -/
theorem litBC_run (Ws x : ℕ) (hWs : 0 < Ws) (h : 0 < lcount Ws x) : litBC Ws x = run Ws (litStates Ws 16 x) := by
  set k := lcount Ws x with hk_def
  have hk_pos : 1 ≤ k := by omega
  have hk_le : k ≤ 16 := (lcount_spec Ws x h).1
  have hdiv : x / 2 ^ (k * Ws) = 1 := (lcount_spec Ws x h).2
  have hlit_eq : litStates Ws 16 x = (List.range k).map fun i => x / 2 ^ (Ws * i) % 2 ^ Ws :=
    litStates_eq Ws x k hWs hk_pos hk_le hdiv
  have hlen : (litStates Ws 16 x).length = k := by
    rw [hlit_eq]
    simp
  have hget : ∀ i, i < k → (litStates Ws 16 x).getD i 0 = x / 2 ^ (Ws * i) % 2 ^ Ws := by
    intro i hi
    rw [hlit_eq]
    simp [hi]
  have hx_eq : x = 2 ^ (k * Ws) + x % 2 ^ (k * Ws) := by
    have h := Nat.div_add_mod x (2 ^ (k * Ws))
    rw [hdiv] at h
    omega
  have hpack_eq : pack Ws k (fun i => (litStates Ws 16 x).getD i 0) = pack Ws k (fun i => x / 2 ^ (Ws * i) % 2 ^ Ws) := by
    apply pack_congr Ws k
    intro i hi
    exact hget i hi
  calc
    litBC Ws x = (Nat.sub x (Nat.shiftLeft 1 (Nat.mul k Ws)), k) := rfl
    _ = (Nat.sub x (1 * 2 ^ (k * Ws)), k) := by
      simpa using congrArg (fun t => (Nat.sub x t, k)) (Nat.shiftLeft_eq 1 (k * Ws))
    _ = (Nat.sub x (2 ^ (k * Ws)), k) := by simp
    _ = (x % 2 ^ (k * Ws), k) := by
      have hsub : Nat.sub x (2 ^ (k * Ws)) = x % 2 ^ (k * Ws) := by
        rw [hx_eq]
        simp
      rw [hsub]
    _ = (x % 2 ^ (Ws * k), k) := by rw [mul_comm Ws k]
    _ = (pack Ws k fun i => x / 2 ^ (Ws * i) % 2 ^ Ws, k) := by rw [mod_pow_pack]
    _ = (pack Ws k fun i => (litStates Ws 16 x).getD i 0, k) := by rw [hpack_eq]
    _ = (pack Ws ((litStates Ws 16 x).length) fun i => (litStates Ws 16 x).getD i 0, (litStates Ws 16 x).length) := by rw [hlen]
    _ = run Ws (litStates Ws 16 x) := rfl

theorem litCat_natrec (Ws : ℕ) (s : List (ℕ × ℕ)) (k : ℕ) :
    @Nat.rec (fun _ => List (ℕ × ℕ)) s (fun _ ih => mergeP Ws ih) k = (mergeP Ws)^[k] s := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ← ih]

theorem mergeP_iter_run (Ws k : ℕ) (Ls : List (List ℕ)) :
    (mergeP Ws)^[k] (Ls.map (run Ws)) = (joinP^[k] Ls).map (run Ws) := by
  induction k generalizing Ls with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, mergeP_run, ih]

theorem joinP_iter_flatten (k : ℕ) (Ls : List (List ℕ)) : (joinP^[k] Ls).flatten = Ls.flatten := by
  induction k generalizing Ls with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih, joinP_flatten]

theorem joinP_iter_length (k : ℕ) (Ls : List (List ℕ)) (h : Ls.length ≤ 2 ^ k) :
    (joinP^[k] Ls).length ≤ 1 := by
  induction k generalizing Ls with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    rw [joinP_length, pow_succ] at *
    omega

theorem depth_ge_len (len : ℕ) (h : 1 ≤ len) : len ≤ 2 ^ depth len := by
  have hlog := Nat.lt_log2_self (n := 2 * len - 1)
  have hineq : 2 * len - 1 < 2 ^ (depth len + 1) := by
    simpa [depth] using hlog
  have hpow : 2 ^ (depth len + 1) = 2 * 2 ^ depth len := by
    simp [pow_succ, mul_comm]
  rw [hpow] at hineq
  omega

/-- The concatenation of aligned literals is the run of their decoded states. -/
theorem litCat_run (Ws : ℕ) (hWs : 0 < Ws) (lits : List ℕ) (h : litsOK Ws lits = true) :
    litCat Ws lits = run Ws (allStates Ws lits) := by
  have hall : ∀ x ∈ lits, 0 < lcount Ws x := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hc := (litsOK_iff Ws lits).mp h i hi
    have hg : lits.getD i 0 = lits[i] := by rw [List.getD_eq_getElem]
    rcases Nat.lt_or_ge (i + 1) lits.length with h1 | h1
    · rw [← hg, lcount_full Ws _ hWs (hc.1 h1)]; norm_num
    · rw [← hg]; exact hc.2 (by omega)
  have hmap : lmap (litBC Ws) lits = (lits.map (litStates Ws 16)).map (run Ws) := by
    rw [lmap_eq, List.map_map]
    exact List.map_congr_left fun x hx => litBC_run Ws x hWs (hall x hx)
  show litCat.litCat1 (@Nat.rec (fun _ => List (ℕ × ℕ)) (lmap (litBC Ws) lits) (fun _ ih => mergeP Ws ih)
    (depth lits.length)) = _
  rw [litCat_natrec, hmap, mergeP_iter_run]
  have hlen : (joinP^[depth lits.length] (lits.map (litStates Ws 16))).length ≤ 1 := by
    apply joinP_iter_length
    rw [List.length_map]
    rcases Nat.eq_zero_or_pos lits.length with h0 | h0
    · rw [h0]; exact Nat.zero_le _
    · exact depth_ge_len _ h0
  have hflat := joinP_iter_flatten (depth lits.length) (lits.map (litStates Ws 16))
  have hall2 : allStates Ws lits = (lits.map (litStates Ws 16)).flatten := by
    rw [allStates, List.flatMap_def]
  rw [hall2, ← hflat]
  generalize joinP^[depth lits.length] (lits.map (litStates Ws 16)) = J at hlen ⊢
  rcases J with _ | ⟨L, _ | ⟨L2, J⟩⟩
  · simp [run, pack_zero]
    rfl
  · simp
    rfl
  · simp at hlen

/-! ## Fields -/

/-- A field of every lane: shift right by `s`, keep `k` bits. -/
theorem shr_land_pack (W n s k : ℕ) (f : ℕ → ℕ) (hsk : s + k ≤ W) (hf : ∀ l < n, f l < 2 ^ W) :
    Nat.land (Nat.shiftRight (pack W n f) s) (pack W n fun _ => 2 ^ k - 1) =
      pack W n fun l => f l / 2 ^ s % 2 ^ k := by
  by_cases hW0 : W = 0
  · subst hW0
    have hf0 : ∀ l < n, f l = 0 := by
      intro l hl
      have h := hf l hl
      simp at h
      omega
    have hpack0 : pack 0 n f = 0 := by
      unfold pack
      apply Finset.sum_eq_zero
      intro l hl
      have hl' : l < n := Finset.mem_range.1 hl
      simp [hf0 l hl']
    have hpackRHS : pack 0 n (fun l => f l / 2 ^ s % 2 ^ k) = 0 := by
      unfold pack
      apply Finset.sum_eq_zero
      intro l hl
      have hl' : l < n := Finset.mem_range.1 hl
      simp [hf0 l hl']
    simp [Nat.land_eq, hpack0, hpackRHS]
  · have hWpos : 0 < W := Nat.pos_of_ne_zero hW0
    have hmask : ∀ l < n, (2 ^ k - 1) < 2 ^ W := by
      intro l hl
      have hk : k ≤ W := by omega
      have hpow : 2 ^ k ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hk
      have hsub : 2 ^ k - 1 < 2 ^ k := by
        by_cases hk0 : k = 0
        · subst hk0; simp
        · exact Nat.sub_lt (Nat.one_le_two_pow) (by omega)
      omega
    have hfmod : ∀ l < n, (f l / 2 ^ s % 2 ^ k) < 2 ^ W := by
      intro l hl
      have hdiv : f l / 2 ^ s < 2 ^ W :=
        lt_of_le_of_lt (Nat.div_le_self _ _) (hf l hl)
      have hmod : (f l / 2 ^ s) % 2 ^ k < 2 ^ k :=
        Nat.mod_lt _ (by positivity)
      have hk : 2 ^ k ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.land_eq]
    rw [Nat.testBit_land]
    simp [Nat.shiftRight_eq_div_pow]
    rw [Nat.testBit_div_two_pow]
    rw [add_comm i s]
    rw [testBit_pack W n f hWpos hf (s + i)]
    rw [testBit_pack W n (fun _ => 2 ^ k - 1) hWpos hmask i]
    rw [testBit_pack W n (fun l => f l / 2 ^ s % 2 ^ k) hWpos hfmod i]
    by_cases hi : i / W < n
    · simp [hi]
      by_cases hrk : i % W < k
      · have hsum_lt : i % W + s < W := by
          omega
        have hdiv_eq : (s + i) / W = i / W := by
          have hdivmod := Nat.div_add_mod i W
          have h : s + i = (i % W + s) + W * (i / W) := by
            linarith
          rw [h]
          rw [Nat.add_mul_div_left _ _ hWpos]
          have hdiv : (i % W + s) / W = 0 := Nat.div_eq_of_lt hsum_lt
          rw [hdiv, zero_add]
        have hmod_eq : (s + i) % W = i % W + s := by
          have hdivmod := Nat.div_add_mod i W
          have h : s + i = (i % W + s) + W * (i / W) := by
            linarith
          rw [h]
          rw [Nat.add_mul_mod_self_left]
          rw [Nat.mod_eq_of_lt hsum_lt]
        simp [hdiv_eq, hmod_eq, hrk, hi]
        rw [Nat.testBit_div_two_pow]
      · simp [hrk]
    · simp [hi]

/-- Lanes of `W a` bits as `a` lanes of `W` bits each. -/
theorem repack (W a n : ℕ) (f : ℕ → ℕ) (hf : ∀ s < n, f s < 2 ^ (W * a)) :
    pack (W * a) n f = pack W (a * n) fun l => f (l / a) / 2 ^ (W * (l % a)) % 2 ^ W := by
  induction n with
  | zero => simp [pack_zero]
  | succ n ih =>
    rw [pack_succ, ih (fun s hs => hf s (by omega)), Nat.mul_succ,
      pack_split W (a * n + a) (a * n) _ (by omega), Nat.add_sub_cancel_left]
    congr 1
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      have h0 := hf n (by omega)
      rw [Nat.mul_zero, pow_zero] at h0
      have h00 : f n = 0 := by omega
      simp [h00, pack_zero]
    · have hblk : (pack W a fun l => f ((l + a * n) / a) / 2 ^ (W * ((l + a * n) % a)) % 2 ^ W) = f n := by
        rw [← Nat.mod_eq_of_lt (hf n (by omega)), mod_pow_pack]
        apply pack_congr
        intro l hl
        rw [Nat.add_mul_div_left _ _ ha, Nat.div_eq_of_lt hl, zero_add, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt hl]
      rw [hblk]
      ring

/-- One field of `n` states through a compaction that keeps lane `ls * j`. -/
theorem fields_one (m n ls f : ℕ) (h3 : 3 * ls = m + 1) (hf : f ≤ m) (st : ℕ → ℕ)
    (hst : ∀ s < n, st s < 2 ^ (48 * (m + 1))) (rt : Rt)
    (hroute : ∀ F : ℕ → ℕ, (∀ s < ls * n, F s < 2 ^ 100) →
      route rt (pack LW (ls * n) F) = pack LW n fun j => F (ls * j)) :
    route rt (Nat.land (Nat.shiftRight (pack (48 * (m + 1)) n st) (48 * f))
        (pack (48 * (m + 1)) n fun _ => 2 ^ 48 - 1)) =
      pack LW n fun s => st s / 2 ^ (48 * f) % 2 ^ 48 := by
  have hls : 0 < ls := by omega
  rw [shr_land_pack (48 * (m + 1)) n (48 * f) 48 st (by omega) hst]
  have hW : 48 * (m + 1) = LW * ls := by show _ = 144 * ls; omega
  rw [hW, repack LW ls n _ (fun s hs => ?_)]
  · rw [hroute _ (fun s _ => ?_)]
    · apply pack_congr
      intro j _
      rw [Nat.mul_div_cancel_left j hls, Nat.mul_mod_right, Nat.mul_zero, pow_zero, Nat.div_one]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
        (by show 2 ^ 48 ≤ 2 ^ 144; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)))
    · refine lt_of_le_of_lt (Nat.mod_le _ _) (lt_of_le_of_lt (Nat.div_le_self _ _) ?_)
      exact lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  · exact lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
      (Nat.pow_le_pow_right (by norm_num) (by show 48 ≤ 144 * ls; omega))

/-- The fields of `n` concatenated states, one lane per state, when the compaction test passes. -/
theorem fields_spec_gen (m n : ℕ) (hn : n ≤ B32) (hm : m ≤ 32) (st : ℕ → ℕ)
    (hst : ∀ s < n, st s < 2 ^ Nat.mul 48 (Nat.succ m))
    (hok : (fields m (pack (Nat.mul 48 (Nat.succ m)) n st) n).2.2 = true) :
    (fields m (pack (Nat.mul 48 (Nat.succ m)) n st) n).1 = pack LW n (fun s => st s % 2 ^ 48) ∧
      (fields m (pack (Nat.mul 48 (Nat.succ m)) n st) n).2.1 =
        (List.range m).map fun f => pack LW n fun s => st s / 2 ^ (48 * (f + 1)) % 2 ^ 48 := by
  have hIv : Nat.mul (Nat.div (Nat.succ m) 3) (Nat.sub (iota1 n) (ones LW n)) =
      pack LW n (fun j => (m + 1) / 3 * j) := by
    show (m + 1) / 3 * (iota1 n - ones LW n) = _
    rw [iota1_eq, ones_eq LW n (by decide), pack_sub _ _ _ _ (fun l _ => by omega), pack_const_mul]
    exact pack_congr _ _ _ _ fun l _ => by simp
  have hEV : Nat.mul 281474976710655 (ones (Nat.mul 48 (Nat.succ m)) n) =
      pack (48 * (m + 1)) n (fun _ => 2 ^ 48 - 1) := by
    show 281474976710655 * ones (48 * (m + 1)) n = _
    rw [ones_eq _ _ (by omega), pack_const_mul]
    exact pack_congr _ _ _ _ fun l _ => by norm_num
  have hF : fields m (pack (Nat.mul 48 (Nat.succ m)) n st) n =
      fields.fields1 m (pack (48 * (m + 1)) n st) ((m + 1) / 3)
        (mkRt ((m + 1) / 3 * n) n (pack LW n (fun j => (m + 1) / 3 * j)))
        (pack (48 * (m + 1)) n (fun _ => 2 ^ 48 - 1)) := by
    unfold fields; rw [hIv, hEV]; rfl
  rw [hF] at hok ⊢
  simp only [fields.fields1, bsel_eq] at hok ⊢
  split_ifs at hok with h3
  have h3' : 3 * ((m + 1) / 3) = m + 1 := Nat.eq_of_beq_eq_true h3
  have hls : (m + 1) / 3 ≤ 11 := by omega
  have hB : n ≤ 4294967296 := hn
  have hNS : (m + 1) / 3 * n < 2 ^ 40 :=
    lt_of_le_of_lt (Nat.mul_le_mul hls hB) (by norm_num)
  obtain ⟨_, hroute⟩ := route_spec_gen ((m + 1) / 3 * n) n (fun j => (m + 1) / 3 * j) hNS
    (fun j hj => lt_of_le_of_lt (Nat.mul_le_mul hls hj.le) (by omega)) hok
  have hst' : ∀ s < n, st s < 2 ^ (48 * (m + 1)) := hst
  refine ⟨?_, ?_⟩
  · have h0 := fields_one m n ((m + 1) / 3) 0 h3' (by omega) st hst' _ hroute
    rw [Nat.mul_zero, pow_zero] at h0
    simp only [Nat.div_one] at h0
    rw [← h0]
    rfl
  · rw [lmap_eq, List.range'_eq_map_range, List.map_map]
    refine List.map_congr_left fun f hf => ?_
    have hf' : f < m := List.mem_range.mp hf
    have h1 := fields_one m n ((m + 1) / 3) (1 + f) h3' (by omega) st hst' _ hroute
    simp only [Function.comp_apply]
    rw [show Nat.add (Nat.mul 144 (Nat.div (1 + f) 3)) (Nat.mul 48 (Nat.mod (1 + f) 3)) = 48 * (1 + f) by
      show 144 * ((1 + f) / 3) + 48 * ((1 + f) % 3) = _; omega]
    rw [h1, show 1 + f = f + 1 by omega]

end Robbins.Cert.SO.L
