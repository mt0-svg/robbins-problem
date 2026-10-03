import Robbins.Cert.SO.LS.Vec

/-!
# The lanes step: the chord and the crossing terms on lanes

`chordV` is the scalar chord `chord.chord1` on the lanes of its mask when its saturation check
passes; `crossV` and `crossT` are the crossing terms of `cell2`, lane by lane.
-/

namespace Robbins.Cert.SO.L

open Robbins.Cert Robbins.Cert.K Robbins.Cert.SO.K Robbins.Lanes

/-- The lower component `lo` of the chord on lanes. -/
theorem chordLO_eq (n h : ℕ) (beta kk A0 A1 q1 r1 : ℕ → ℕ) (hh : h ≤ DS)
    (hbeta : ∀ l < n, beta l < 2 ^ 92) (hkk : ∀ l < n, kk l < 2 ^ 50) (hA0 : ∀ l < n, A0 l < 2 ^ 92)
    (hA1 : ∀ l < n, A1 l < 2 ^ 92) (hq1 : ∀ l < n, q1 l < 2 ^ 37) (hr1 : ∀ l < n, r1 l < 2 ^ 92) :
    sl (ge (mkVC n) (pack LW n A0) (pack LW n beta))
        (Nat.mul h (Nat.add (tsub (mkVC n) (pack LW n A0) (pack LW n beta))
          (tsub (mkVC n) (pack LW n A1) (pack LW n beta))))
        (mulv (mkVC n) 37 (Nat.add (tsub (mkVC n) (pack LW n kk) (pack LW n r1))
            (tsub (mkVC n) (pack LW n A1) (pack LW n beta)))
          (tsub (mkVC n) (tsub (mkVC n) (bc (mkVC n) h) (pack LW n q1)) (mkVC n).O)) =
      pack LW n fun l => if beta l ≤ A0 l then h * ((A0 l - beta l) + (A1 l - beta l))
        else ((kk l - r1 l) + (A1 l - beta l)) * (h - q1 l - 1) := by
  -- Numeric bounds
  have hDS_eq : DS = (2 : ℕ)^36 := by unfold DS; norm_num
  have h2_92_lt_143 : (2 : ℕ)^92 < (2 : ℕ)^143 := by norm_num
  have h2_37_lt_143 : (2 : ℕ)^37 < (2 : ℕ)^143 := by norm_num
  have h2_36_lt_143 : (2 : ℕ)^36 < (2 : ℕ)^143 := by norm_num
  have hDS_lt_143 : DS < (2 : ℕ)^143 := by rw [hDS_eq]; exact h2_36_lt_143
  have h37_le_144 : (37 : ℕ) ≤ 144 := by norm_num
  -- Bounds for each function to < 2^143 (required by tsub_eq, ge_eq)
  have hA0_lt_143 : ∀ l < n, A0 l < (2 : ℕ)^143 := fun l hl =>
    lt_trans (hA0 l hl) h2_92_lt_143
  have hbeta_lt_143 : ∀ l < n, beta l < (2 : ℕ)^143 := fun l hl =>
    lt_trans (hbeta l hl) h2_92_lt_143
  have hA1_lt_143 : ∀ l < n, A1 l < (2 : ℕ)^143 := fun l hl =>
    lt_trans (hA1 l hl) h2_92_lt_143
  have hkk_lt_143 : ∀ l < n, kk l < (2 : ℕ)^143 := fun l hl =>
    have h50 : (2 : ℕ)^50 < (2 : ℕ)^143 := by norm_num
    lt_trans (hkk l hl) h50
  have hr1_lt_143 : ∀ l < n, r1 l < (2 : ℕ)^143 := fun l hl =>
    lt_trans (hr1 l hl) h2_92_lt_143
  have hq1_lt_143 : ∀ l < n, q1 l < (2 : ℕ)^143 := fun l hl =>
    have h37 : (2 : ℕ)^37 < (2 : ℕ)^143 := by norm_num
    lt_trans (hq1 l hl) h37
  have hh_lt_143 : h < (2 : ℕ)^143 := lt_of_le_of_lt hh hDS_lt_143
  -- h ≤ 2^36 for later use
  have hh_le_2_36 : h ≤ (2 : ℕ)^36 := by rw [← hDS_eq]; exact hh
  -- Bounds for mulv_eq first argument: (kk l - r1 l) + (A1 l - beta l) < 2^93
  have hmulv_a_lt_93 : ∀ l < n, (kk l - r1 l) + (A1 l - beta l) < (2 : ℕ)^93 := by
    intro l hl
    have hsub1 : kk l - r1 l < (2 : ℕ)^50 := by
      have : kk l - r1 l ≤ kk l := Nat.sub_le _ _
      exact lt_of_le_of_lt this (hkk l hl)
    have hsub2 : A1 l - beta l < (2 : ℕ)^92 := by
      have : A1 l - beta l ≤ A1 l := Nat.sub_le _ _
      exact lt_of_le_of_lt this (hA1 l hl)
    have hsum : (kk l - r1 l) + (A1 l - beta l) < (2 : ℕ)^50 + (2 : ℕ)^92 :=
      Nat.add_lt_add hsub1 hsub2
    have hlt : (2 : ℕ)^50 + (2 : ℕ)^92 < (2 : ℕ)^93 := by norm_num
    exact lt_trans hsum hlt
  -- Bounds for mulv_eq first argument times 2^j
  have hmulv_a_mul_lt : ∀ l < n, ∀ j < 37, ((kk l - r1 l) + (A1 l - beta l)) * (2 : ℕ)^j < (2 : ℕ)^144 := by
    intro l hl j hj
    have hbase : (kk l - r1 l) + (A1 l - beta l) < (2 : ℕ)^93 := hmulv_a_lt_93 l hl
    have hpow_le : (2 : ℕ)^j ≤ (2 : ℕ)^37 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpow_pos : 0 < (2 : ℕ)^j := pow_pos (by norm_num) j
    have hprod : ((kk l - r1 l) + (A1 l - beta l)) * (2 : ℕ)^j < (2 : ℕ)^93 * (2 : ℕ)^37 :=
      mul_lt_mul hbase hpow_le hpow_pos (by positivity)
    have hlt : (2 : ℕ)^93 * (2 : ℕ)^37 < (2 : ℕ)^144 := by norm_num
    exact lt_trans hprod hlt
  -- Bounds for mulv_eq second argument: (h - q1 l) - 1 < 2^144
  have hmulv_b_lt_144 : ∀ l < n, (h - q1 l) - 1 < (2 : ℕ)^144 := by
    intro l hl
    have : (h - q1 l) - 1 ≤ h := by
      calc
        (h - q1 l) - 1 ≤ h - q1 l := Nat.sub_le _ _
        _ ≤ h := Nat.sub_le _ _
    exact lt_of_le_of_lt this (lt_of_lt_of_le hh_lt_143 (by norm_num))
  -- Bounds for sl_eq first argument: h * ((A0 l - beta l) + (A1 l - beta l)) < 2^144
  have hsl_a_lt_144 : ∀ l < n, h * ((A0 l - beta l) + (A1 l - beta l)) < (2 : ℕ)^144 := by
    intro l hl
    have hsum : (A0 l - beta l) + (A1 l - beta l) < (2 : ℕ)^93 := by
      have hsub1 : A0 l - beta l < (2 : ℕ)^92 := by
        have : A0 l - beta l ≤ A0 l := Nat.sub_le _ _
        exact lt_of_le_of_lt this (hA0 l hl)
      have hsub2 : A1 l - beta l < (2 : ℕ)^92 := by
        have : A1 l - beta l ≤ A1 l := Nat.sub_le _ _
        exact lt_of_le_of_lt this (hA1 l hl)
      have hsum' : (A0 l - beta l) + (A1 l - beta l) < (2 : ℕ)^92 + (2 : ℕ)^92 :=
        Nat.add_lt_add hsub1 hsub2
      have : (2 : ℕ)^92 + (2 : ℕ)^92 = (2 : ℕ)^93 := by norm_num
      rw [this] at hsum'
      exact hsum'
    have hprod : h * ((A0 l - beta l) + (A1 l - beta l)) ≤ (2 : ℕ)^36 * (2 : ℕ)^93 :=
      Nat.mul_le_mul hh_le_2_36 (le_of_lt hsum)
    have hlt : (2 : ℕ)^36 * (2 : ℕ)^93 < (2 : ℕ)^144 := by norm_num
    exact lt_of_le_of_lt hprod hlt
  -- Bounds for sl_eq second argument: ((kk l - r1 l) + (A1 l - beta l)) * (h - q1 l - 1) < 2^144
  have hsl_b_lt_144 : ∀ l < n, ((kk l - r1 l) + (A1 l - beta l)) * (h - q1 l - 1) < (2 : ℕ)^144 := by
    intro l hl
    have hfirst : (kk l - r1 l) + (A1 l - beta l) < (2 : ℕ)^93 := hmulv_a_lt_93 l hl
    have hsecond_le : h - q1 l - 1 ≤ (2 : ℕ)^36 := by
      have : h - q1 l - 1 ≤ h := by
        calc
          h - q1 l - 1 ≤ h - q1 l := Nat.sub_le _ _
          _ ≤ h := Nat.sub_le _ _
      exact le_trans this hh_le_2_36
    have hprod : ((kk l - r1 l) + (A1 l - beta l)) * (h - q1 l - 1) ≤ (2 : ℕ)^93 * (2 : ℕ)^36 :=
      Nat.mul_le_mul (le_of_lt hfirst) hsecond_le
    have hlt : (2 : ℕ)^93 * (2 : ℕ)^36 < (2 : ℕ)^144 := by norm_num
    exact lt_of_le_of_lt hprod hlt
  -- Step 1: rewrite bc and O
  rw [bc_eq n h, mkVC_O n]
  -- Step 2: rewrite all tsubs
  rw [tsub_eq n A0 beta hA0_lt_143 hbeta_lt_143]
  rw [tsub_eq n A1 beta hA1_lt_143 hbeta_lt_143]
  rw [tsub_eq n kk r1 hkk_lt_143 hr1_lt_143]
  -- For the nested tsub: first rewrite the inner one
  have hinner_tsub : tsub (mkVC n) (pack LW n (fun _ : ℕ => h)) (pack LW n q1) =
      pack LW n (fun l => h - q1 l) :=
    tsub_eq n (fun _ => h) q1 (fun l _ => hh_lt_143) hq1_lt_143
  rw [hinner_tsub]
  -- Now the outer tsub
  have hsub_hq1_lt : ∀ l < n, h - q1 l < (2 : ℕ)^143 := by
    intro l hl
    have : h - q1 l ≤ h := Nat.sub_le _ _
    exact lt_of_le_of_lt this hh_lt_143
  rw [tsub_eq n (fun l => h - q1 l) (fun _ => 1) hsub_hq1_lt (fun l _ => by norm_num)]
  -- Step 3: rewrite Nat.add of packs using pack_add
  -- The goal has .add which is Nat.add; we need to show the + form
  show sl (ge (mkVC n) (pack LW n A0) (pack LW n beta))
    (h * ((pack LW n (fun l => A0 l - beta l)) + (pack LW n (fun l => A1 l - beta l))))
    (mulv (mkVC n) 37 ((pack LW n (fun l => kk l - r1 l)) + (pack LW n (fun l => A1 l - beta l)))
      (pack LW n (fun l => h - q1 l - 1))) =
    pack LW n fun l => if beta l ≤ A0 l then h * ((A0 l - beta l) + (A1 l - beta l))
      else ((kk l - r1 l) + (A1 l - beta l)) * (h - q1 l - 1)
  rw [pack_add LW n (fun l => A0 l - beta l) (fun l => A1 l - beta l)]
  rw [pack_add LW n (fun l => kk l - r1 l) (fun l => A1 l - beta l)]
  -- Step 4: rewrite Nat.mul h of pack using pack_const_mul
  rw [pack_const_mul LW n h (fun l => (A0 l - beta l) + (A1 l - beta l))]
  -- Step 5: rewrite mulv using mulv_eq
  have hmulv_mod : ∀ l < n, ((h - q1 l) - 1) % (2 : ℕ)^37 = (h - q1 l) - 1 := by
    intro l hl
    have hlt : (h - q1 l) - 1 < (2 : ℕ)^37 := by
      have : (h - q1 l) - 1 ≤ h := by
        calc
          h - q1 l - 1 ≤ h - q1 l := Nat.sub_le _ _
          _ ≤ h := Nat.sub_le _ _
      have hh_lt_2_37 : h < (2 : ℕ)^37 := lt_of_le_of_lt hh_le_2_36 (by norm_num)
      exact lt_of_le_of_lt this hh_lt_2_37
    exact Nat.mod_eq_of_lt hlt
  rw [mulv_eq n 37 (fun l => (kk l - r1 l) + (A1 l - beta l)) (fun l => (h - q1 l) - 1)
    h37_le_144 hmulv_a_mul_lt hmulv_b_lt_144]
  -- Now we have: pack LW n (fun l => ((kk l - r1 l) + (A1 l - beta l)) * (((h - q1 l) - 1) % 2^37))
  -- Simplify the mod using pack_congr
  have hmod_eq : pack LW n (fun l => ((kk l - r1 l) + (A1 l - beta l)) * (((h - q1 l) - 1) % (2 : ℕ)^37)) =
      pack LW n (fun l => ((kk l - r1 l) + (A1 l - beta l)) * ((h - q1 l) - 1)) :=
    pack_congr LW n (fun l => ((kk l - r1 l) + (A1 l - beta l)) * (((h - q1 l) - 1) % (2 : ℕ)^37))
      (fun l => ((kk l - r1 l) + (A1 l - beta l)) * ((h - q1 l) - 1)) (fun l hl => by rw [hmulv_mod l hl])
  rw [hmod_eq]
  -- Step 6: rewrite ge using ge_eq
  rw [ge_eq n A0 beta hA0_lt_143 hbeta_lt_143]
  -- Step 7: rewrite sl using sl_eq
  rw [sl_eq n (fun l => beta l ≤ A0 l) (fun l => h * ((A0 l - beta l) + (A1 l - beta l)))
    (fun l => ((kk l - r1 l) + (A1 l - beta l)) * (h - q1 l - 1))
    hsl_a_lt_144 hsl_b_lt_144]
  -- The result is exactly the RHS

/-- The numerator of the chord on lanes, `(q2, r2)` the quotient and remainder of `(beta + S - A0) / kk`. -/
theorem chordN_eq (n h : ℕ) (beta S kk A1 LO q2 r2 : ℕ → ℕ) (hh : h ≤ DS)
    (hbeta : ∀ l < n, beta l < 2 ^ 92) (hS : ∀ l < n, S l < 2 ^ 92) (hkk : ∀ l < n, kk l < 2 ^ 50)
    (hA1 : ∀ l < n, A1 l < 2 ^ 92) (hLO : ∀ l < n, LO l < 2 ^ 131) (hq2 : ∀ l < n, q2 l < 2 ^ 37)
    (hr2 : ∀ l < n, r2 l < 2 ^ 93) :
    sl (ge (mkVC n) (Nat.add (pack LW n beta) (pack LW n S)) (pack LW n A1)) (pack LW n LO)
        (tsub (mkVC n)
          (Nat.add (pack LW n LO)
            (mulv (mkVC n) 37 (pack LW n r2) (tsub (mkVC n) (bc (mkVC n) h) (pack LW n q2))))
          (Nat.add
            (mulv (mkVC n) 37 (tsub (mkVC n) (pack LW n A1) (Nat.add (pack LW n beta) (pack LW n S)))
              (tsub (mkVC n) (bc (mkVC n) h) (pack LW n q2)))
            (Nat.add (pack LW n kk) (pack LW n kk)))) =
      pack LW n fun l => if A1 l ≤ beta l + S l then LO l
        else (LO l + r2 l * (h - q2 l)) - ((A1 l - (beta l + S l)) * (h - q2 l) + (kk l + kk l)) := by
  have hDS_eq : DS = 2 ^ 36 := by unfold DS; rfl
  have h_h_le_2pow36 : h ≤ 2 ^ 36 := by rwa [hDS_eq] at hh
  have h_h_lt_143 : h < 2 ^ 143 := by
    have h36_143 : 2 ^ 36 < 2 ^ 143 := by norm_num
    exact Nat.lt_of_le_of_lt h_h_le_2pow36 h36_143
  have hq2_lt_143 : ∀ l < n, q2 l < 2 ^ 143 := by
    intro l hl
    have hq2l := hq2 l hl
    have h37_143 : 2 ^ 37 ≤ 2 ^ 143 := by norm_num
    exact Nat.lt_of_lt_of_le hq2l h37_143
  have hA1_lt_143 : ∀ l < n, A1 l < 2 ^ 143 := by
    intro l hl
    have hA1l := hA1 l hl
    have h92_143 : 2 ^ 92 ≤ 2 ^ 143 := by norm_num
    exact Nat.lt_of_lt_of_le hA1l h92_143
  have hbetaS_lt_143 : ∀ l < n, beta l + S l < 2 ^ 143 := by
    intro l hl
    have hb := hbeta l hl
    have hS' := hS l hl
    have hsum : beta l + S l < 2 ^ 92 + 2 ^ 92 := Nat.add_lt_add hb hS'
    have h92s_143 : 2 ^ 92 + 2 ^ 92 ≤ 2 ^ 143 := by norm_num
    exact Nat.lt_of_lt_of_le hsum h92s_143
  have hkkl_lt_143 : ∀ l < n, kk l + kk l < 2 ^ 143 := by
    intro l hl
    have hkk' := hkk l hl
    have hsum : kk l + kk l < 2 ^ 50 + 2 ^ 50 := Nat.add_lt_add hkk' hkk'
    have h50s_143 : 2 ^ 50 + 2 ^ 50 ≤ 2 ^ 143 := by norm_num
    exact Nat.lt_of_lt_of_le hsum h50s_143
  have hLO_lt_144 : ∀ l < n, LO l < 2 ^ 144 := by
    intro l hl
    have hLO' := hLO l hl
    have h131_144 : 2 ^ 131 ≤ 2 ^ 144 := by norm_num
    exact Nat.lt_of_lt_of_le hLO' h131_144
  have hr2_mul_bound : ∀ l < n, ∀ j < 37, r2 l * 2 ^ j < 2 ^ 144 := by
    intro l hl j hj
    have hr2' := hr2 l hl
    have hpow : 2 ^ j ≤ 2 ^ 36 :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_of_lt_succ hj)
    have h93_36_eq_129 : 2 ^ 93 * 2 ^ 36 = 2 ^ 129 := by ring
    have h129_144 : 2 ^ 129 < 2 ^ 144 := by norm_num
    have h : r2 l * 2 ^ 36 < 2 ^ 144 := by
      have hle : r2 l * 2 ^ 36 ≤ 2 ^ 93 * 2 ^ 36 :=
        Nat.mul_le_mul (Nat.le_of_lt hr2') (by rfl)
      rw [h93_36_eq_129] at hle
      exact Nat.lt_of_le_of_lt hle h129_144
    have hle2 : r2 l * 2 ^ j ≤ r2 l * 2 ^ 36 :=
      Nat.mul_le_mul_left _ hpow
    exact Nat.lt_of_le_of_lt hle2 h
  have hsub_hq2_lt_144 : ∀ l < n, h - q2 l < 2 ^ 144 := by
    intro l hl
    have h_lt : h < 2 ^ 144 := by
      have h36_144 : 2 ^ 36 < 2 ^ 144 := by norm_num
      exact Nat.lt_of_le_of_lt h_h_le_2pow36 h36_144
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) h_lt
  have hsub_A1_betaS_lt_144 : ∀ l < n, A1 l - (beta l + S l) < 2 ^ 144 := by
    intro l hl
    have hA1' := hA1 l hl
    have h92_144 : 2 ^ 92 ≤ 2 ^ 144 := by norm_num
    have h_lt : A1 l < 2 ^ 144 := Nat.lt_of_lt_of_le hA1' h92_144
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) h_lt
  have hsub_A1_betaS_mul_bound : ∀ l < n, ∀ j < 37, (A1 l - (beta l + S l)) * 2 ^ j < 2 ^ 144 := by
    intro l hl j hj
    have hA1' := hA1 l hl
    have hsub : A1 l - (beta l + S l) ≤ A1 l := Nat.sub_le _ _
    have h1 : (A1 l - (beta l + S l)) * 2 ^ j ≤ A1 l * 2 ^ j :=
      Nat.mul_le_mul hsub (by rfl)
    have hpow : 2 ^ j ≤ 2 ^ 36 :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_of_lt_succ hj)
    have hA1_le : A1 l ≤ 2 ^ 92 := Nat.le_of_lt hA1'
    have h2 : A1 l * 2 ^ j ≤ 2 ^ 92 * 2 ^ 36 :=
      Nat.mul_le_mul hA1_le hpow
    have h92_36_eq_128 : 2 ^ 92 * 2 ^ 36 = 2 ^ 128 := by ring
    have h128_144 : 2 ^ 128 < 2 ^ 144 := by norm_num
    have h4 : A1 l * 2 ^ j < 2 ^ 144 := by
      rw [h92_36_eq_128] at h2
      exact Nat.lt_of_le_of_lt h2 h128_144
    exact Nat.lt_of_le_of_lt h1 h4
  have h_mod : ∀ l < n, (h - q2 l) % 2 ^ 37 = h - q2 l := by
    intro l hl
    apply Nat.mod_eq_of_lt
    have h_lt : h < 2 ^ 37 := by
      have h36_37 : 2 ^ 36 < 2 ^ 37 := by norm_num
      exact Nat.lt_of_le_of_lt h_h_le_2pow36 h36_37
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) h_lt
  -- Step 1: bc (mkVC n) h = pack LW n (fun _ => h)
  rw [bc_eq n h]
  -- Step 2: tsub (mkVC n) (pack LW n (fun _ => h)) (pack LW n q2)
  rw [tsub_eq n (fun _ => h) q2 (by
    intro l hl
    exact h_h_lt_143) (hq2_lt_143)]
  -- Step 3: mulv (mkVC n) 37 (pack LW n r2) (pack LW n (fun l => h - q2 l))
  rw [mulv_eq n 37 r2 (fun l => h - q2 l) (by norm_num) hr2_mul_bound hsub_hq2_lt_144]
  -- Simplify (h - q2 l) % 2 ^ 37
  have hpack_mul1 : pack LW n (fun l => r2 l * ((h - q2 l) % 2 ^ 37)) =
      pack LW n (fun l => r2 l * (h - q2 l)) := by
    refine pack_congr _ _ _ _ fun l hl => ?_
    rw [h_mod l hl]
  rw [hpack_mul1]
  -- Step 4: Nat.add (pack LW n LO) (pack LW n (fun l => r2 l * (h - q2 l)))
  rw [show (pack LW n LO).add (pack LW n (fun l => r2 l * (h - q2 l))) =
      pack LW n (fun l => LO l + (r2 l * (h - q2 l))) by
    simpa [Nat.add] using pack_add LW n LO (fun l => r2 l * (h - q2 l))]
  -- Step 5: Rewrite the second branch: tsub (mkVC n) (pack LW n A1) (Nat.add (pack LW n beta) (pack LW n S))
  rw [show (pack LW n beta).add (pack LW n S) =
      pack LW n (fun l => beta l + S l) by
    simpa [Nat.add] using pack_add LW n beta S]
  rw [tsub_eq n A1 (fun l => beta l + S l) hA1_lt_143 hbetaS_lt_143]
  -- Step 6: Second mulv
  erw [mulv_eq n 37 (fun l => A1 l - (beta l + S l)) (fun l => h - q2 l) (by norm_num)
    hsub_A1_betaS_mul_bound hsub_hq2_lt_144]
  -- Simplify (h - q2 l) % 2 ^ 37 again
  have hpack_mul2 : pack LW n (fun l => (A1 l - (beta l + S l)) * ((h - q2 l) % 2 ^ 37)) =
      pack LW n (fun l => (A1 l - (beta l + S l)) * (h - q2 l)) := by
    refine pack_congr _ _ _ _ fun l hl => ?_
    rw [h_mod l hl]
  erw [hpack_mul2]
  -- Step 7: Nat.add (pack LW n kk) (pack LW n kk)
  rw [show (pack LW n kk).add (pack LW n kk) =
      pack LW n (fun l => kk l + kk l) by
    simpa [Nat.add] using pack_add LW n kk kk]
  -- Step 8: Nat.add (pack LW n (fun l => (A1 l - (beta l + S l)) * (h - q2 l)))
  --   (pack LW n (fun l => kk l + kk l))
  rw [show (pack LW n (fun l => (A1 l - (beta l + S l)) * (h - q2 l))).add
      (pack LW n (fun l => kk l + kk l)) =
      pack LW n (fun l => ((A1 l - (beta l + S l)) * (h - q2 l)) + (kk l + kk l)) by
    simpa [Nat.add] using pack_add LW n (fun l => (A1 l - (beta l + S l)) * (h - q2 l)) (fun l => kk l + kk l)]
  -- Step 8b: Rewrite tsub in the third argument of sl
  have h_tsub_arg1_lt_143 : ∀ l < n, LO l + r2 l * (h - q2 l) < 2 ^ 143 := by
    intro l hl
    have h1 : LO l < 2 ^ 131 := hLO l hl
    have h2 : r2 l * (h - q2 l) < 2 ^ 129 := by
      have h_le : h - q2 l ≤ 2 ^ 36 :=
        Nat.le_trans (Nat.sub_le _ _) h_h_le_2pow36
      have h_lt_mul : r2 l * 2 ^ 36 < 2 ^ 93 * 2 ^ 36 :=
        Nat.mul_lt_mul_of_lt_of_le (hr2 l hl) (le_refl _) (by norm_num : 0 < 2 ^ 36)
      have h93_36_eq_129 : 2 ^ 93 * 2 ^ 36 = 2 ^ 129 := by ring
      rw [h93_36_eq_129] at h_lt_mul
      have hle : r2 l * (h - q2 l) ≤ r2 l * 2 ^ 36 :=
        Nat.mul_le_mul_left _ h_le
      exact Nat.lt_of_le_of_lt hle h_lt_mul
    have hsum : LO l + r2 l * (h - q2 l) < 2 ^ 131 + 2 ^ 129 :=
      Nat.add_lt_add h1 h2
    have h131_129_143 : 2 ^ 131 + 2 ^ 129 < 2 ^ 143 := by norm_num
    exact Nat.lt_trans hsum h131_129_143
  have h_tsub_arg2_lt_143 : ∀ l < n, ((A1 l - (beta l + S l)) * (h - q2 l)) + (kk l + kk l) < 2 ^ 143 := by
    intro l hl
    have hA1' := hA1 l hl
    have hkk' := hkk l hl
    have h_mul : (A1 l - (beta l + S l)) * (h - q2 l) < 2 ^ 128 := by
      have h_le_A1 : A1 l - (beta l + S l) ≤ A1 l := Nat.sub_le _ _
      have h_le_h : h - q2 l ≤ 2 ^ 36 :=
        Nat.le_trans (Nat.sub_le _ _) h_h_le_2pow36
      have h_mul_le : (A1 l - (beta l + S l)) * (h - q2 l) ≤ A1 l * 2 ^ 36 :=
        Nat.mul_le_mul h_le_A1 h_le_h
      have h_lt : A1 l * 2 ^ 36 < 2 ^ 92 * 2 ^ 36 :=
        Nat.mul_lt_mul_of_pos_right (hA1 l hl) (by norm_num : 0 < 2 ^ 36)
      have h92_36_eq_128 : 2 ^ 92 * 2 ^ 36 = 2 ^ 128 := by ring
      rw [h92_36_eq_128] at h_lt
      exact Nat.lt_of_le_of_lt h_mul_le h_lt
    have h_kk : kk l + kk l < 2 ^ 51 := by
      have h50s_51 : 2 ^ 50 + 2 ^ 50 = 2 ^ 51 := by ring
      have hsum : kk l + kk l < 2 ^ 50 + 2 ^ 50 := Nat.add_lt_add hkk' hkk'
      rw [h50s_51] at hsum
      exact hsum
    have hsum : ((A1 l - (beta l + S l)) * (h - q2 l)) + (kk l + kk l) < 2 ^ 128 + 2 ^ 51 :=
      Nat.add_lt_add h_mul h_kk
    have h128_51_143 : 2 ^ 128 + 2 ^ 51 < 2 ^ 143 := by norm_num
    exact Nat.lt_trans hsum h128_51_143
  rw [tsub_eq n (fun l => LO l + r2 l * (h - q2 l))
    (fun l => ((A1 l - (beta l + S l)) * (h - q2 l)) + (kk l + kk l))
    h_tsub_arg1_lt_143 h_tsub_arg2_lt_143]
  -- Step 9: ge (mkVC n) (pack LW n (fun l => beta l + S l)) (pack LW n A1)
  rw [ge_eq n (fun l => beta l + S l) A1 hbetaS_lt_143 hA1_lt_143]
  -- Step 10: sl
  rw [sl_eq n (fun l => A1 l ≤ beta l + S l) LO
    (fun l => LO l + r2 l * (h - q2 l) - ((A1 l - (beta l + S l)) * (h - q2 l) + (kk l + kk l)))
    hLO_lt_144 (by
      intro l hl
      have hsum : LO l + r2 l * (h - q2 l) < 2 ^ 144 := by
        have h1 : LO l < 2 ^ 131 := hLO l hl
        have h2 : r2 l * (h - q2 l) < 2 ^ 129 := by
          have h_le : h - q2 l ≤ 2 ^ 36 :=
            Nat.le_trans (Nat.sub_le _ _) h_h_le_2pow36
          have h_lt_mul : r2 l * 2 ^ 36 < 2 ^ 93 * 2 ^ 36 :=
            Nat.mul_lt_mul_of_lt_of_le (hr2 l hl) (le_refl _) (by norm_num : 0 < 2 ^ 36)
          have h93_36_eq_129 : 2 ^ 93 * 2 ^ 36 = 2 ^ 129 := by ring
          rw [h93_36_eq_129] at h_lt_mul
          have hle : r2 l * (h - q2 l) ≤ r2 l * 2 ^ 36 :=
            Nat.mul_le_mul_left _ h_le
          exact Nat.lt_of_le_of_lt hle h_lt_mul
        have hsum' : LO l + r2 l * (h - q2 l) < 2 ^ 131 + 2 ^ 129 :=
          Nat.add_lt_add h1 h2
        have h131_129_144 : 2 ^ 131 + 2 ^ 129 < 2 ^ 144 := by norm_num
        exact Nat.lt_trans hsum' h131_129_144
      apply Nat.lt_of_le_of_lt (Nat.sub_le _ _)
      exact hsum)]

/-- The scalar chord as the lanes compute it, on a lane of `use`. -/
theorem chord1_lane (pa h B S kk A0 A1 q1 r1 q2 r2 LO : ℕ) (hA : A1 = A0 + kk * h) (hB : B < A1)
    (hA0 : A0 < B + S) (_hS : 0 < S) (hq : A0 < B → q1 = (B - A0) / kk ∧ r1 = (B - A0) % kk)
    (hq2 : B + S < A1 → q2 = (B + S - A0) / kk ∧ r2 = (B + S - A0) % kk)
    (hLO : LO = if B ≤ A0 then h * ((A0 - B) + (A1 - B)) else ((kk - r1) + (A1 - B)) * (h - q1 - 1)) :
    chord.chord1 pa (pa + h) B S kk A0 A1 =
      (if A1 ≤ B + S then LO else (LO + r2 * (h - q2)) - ((A1 - (B + S)) * (h - q2) + (kk + kk))) /
        (S + S) := by
  unfold chord.chord1 chord.chord2 chord.chord3 chord.chordLo
  simp only [bsel_eq, Nat.ble_eq]
  have h_not_A1_le_B : ¬ (A1 ≤ B) := by omega
  have h_not_BS_le_A0 : ¬ (B + S ≤ A0) := by omega
  simp [h_not_A1_le_B, h_not_BS_le_A0]
  have h2S : (2 : ℕ) * S = S + S := by omega
  have h2kk : (2 : ℕ) * kk = kk + kk := by omega
  -- Bridges between .mod/.div and %/
  have mod_bridge (a b : ℕ) : a.mod b = a % b := rfl
  have div_bridge (a b : ℕ) : a.div b = a / b := rfl
  by_cases h_B_le_A0 : B ≤ A0
  · -- B ≤ A0: the inner if reduces to h * ((A0 - B) + (A1 - B))
    simp only [h_B_le_A0, reduceIte]
    rw [hLO, ite_eq_left h_B_le_A0]
    by_cases h_A1_le_BS : A1 ≤ B + S
    · -- A1 ≤ B + S: both sides are h * ((A0-B)+(A1-B)) / (S+S)
      simp [h_A1_le_BS, h2S, div_bridge, mul_comm]
    · -- B + S < A1
      have h_BS_lt_A1 : B + S < A1 := by omega
      have hq2' : q2 = (B + S - A0) / kk ∧ r2 = (B + S - A0) % kk := hq2 h_BS_lt_A1
      rcases hq2' with ⟨hq2', hr2⟩
      have hsub2 : pa + h - (pa + q2) = h - q2 := by omega
      -- Rewrite .mod/.div to %/, then the if, then the hypotheses
      simp [mod_bridge, div_bridge, h_A1_le_BS, h2S, h2kk]
      -- Now the goal has (B+S-A0)%kk and (B+S-A0)/kk; replace with r2, q2
      rw [← hr2, ← hq2', hsub2]
      -- Now: ((A0-B+(A1-B))*h + r2*(h-q2) - ...) / (S+S) = (h*(A0-B+(A1-B)) + r2*(h-q2) - ...) / (S+S)
      rw [mul_comm (A0 - B + (A1 - B)) h]
  · -- A0 < B
    have hA0_lt_B : A0 < B := by omega
    have hq1' : q1 = (B - A0) / kk ∧ r1 = (B - A0) % kk := hq hA0_lt_B
    rcases hq1' with ⟨hq1', hr1'⟩
    simp only [h_B_le_A0, reduceIte]
    have hsub_inner : pa + h - (pa + (B - A0) / kk) - 1 = h - q1 - 1 := by
      rw [hq1']
      omega
    by_cases h_A1_le_BS : A1 ≤ B + S
    · -- A1 ≤ B + S: both sides are LO / (S+S)
      simp [mod_bridge, div_bridge, h_A1_le_BS, ← hr1', ← hq1', hLO, ite_eq_right h_B_le_A0, h2S]
      -- Goal: (kk - r1 + (A1 - B)) * (pa + h - (pa + q1) - 1) / (S+S) = (kk - r1 + (A1 - B)) * (h - q1 - 1) / (S+S)
      -- hsub_inner uses (B-A0)/kk; rewrite it to use q1
      rw [← hq1'] at hsub_inner
      rw [hsub_inner]
    · -- B + S < A1
      have h_BS_lt_A1 : B + S < A1 := by omega
      have hq2' : q2 = (B + S - A0) / kk ∧ r2 = (B + S - A0) % kk := hq2 h_BS_lt_A1
      rcases hq2' with ⟨hq2', hr2⟩
      have hsub2 : pa + h - (pa + q2) = h - q2 := by omega
      simp [mod_bridge, div_bridge, h_A1_le_BS, ← hr1', ← hq1', ← hr2, ← hq2', hLO, ite_eq_right h_B_le_A0, h2S, h2kk]
      -- Goal: ((kk - r1 + (A1 - B)) * (pa + h - (pa + q1) - 1) + r2 * (pa + h - (pa + q2)) - ...) / (S+S) = ...
      -- hsub_inner uses (B-A0)/kk; rewrite it to use q1
      rw [← hq1'] at hsub_inner
      rw [hsub_inner, hsub2]

/-- The chord on the lanes of `use` (`beta < A1`, `A0 < beta + S`, `S > 0` there, `A1 = A0 + kk h`,
`(q1, r1)` the quotient and remainder of `(beta - A0) / kk` where `beta > A0`): the scalar chord
with `pb = pa + h`, when no quotient saturates; the chord is then at most `QMX`. -/
theorem chordV_spec (n h pa : ℕ) (beta S kk A0 A1 q1 r1 : ℕ → ℕ) (use : ℕ → Prop)
    [DecidablePred use] (hh : h ≤ DS) (hbeta : ∀ l < n, beta l < 2 ^ 92)
    (hS : ∀ l < n, S l < 2 ^ 92) (hkk : ∀ l < n, kk l < 2 ^ 50) (hA0 : ∀ l < n, A0 l < 2 ^ 92)
    (hA1 : ∀ l < n, A1 l < 2 ^ 92) (hq1 : ∀ l < n, q1 l < 2 ^ 37) (hr1 : ∀ l < n, r1 l < 2 ^ 92)
    (hA : ∀ l < n, use l → A1 l = A0 l + kk l * h)
    (huse : ∀ l < n, use l → beta l < A1 l ∧ A0 l < beta l + S l ∧ 0 < S l)
    (hq : ∀ l < n, use l → A0 l < beta l →
      q1 l = (beta l - A0 l) / kk l ∧ r1 l = (beta l - A0 l) % kk l)
    (hok : (chordV (mkVC n) h (pack LW n beta) (pack LW n S) (pack LW n kk) (pack LW n A0)
      (pack LW n A1) (pack LW n q1) (pack LW n r1) (pack LW n fun l => if use l then 2 ^ 143 else 0)).2 =
        true) :
    (chordV (mkVC n) h (pack LW n beta) (pack LW n S) (pack LW n kk) (pack LW n A0) (pack LW n A1)
      (pack LW n q1) (pack LW n r1) (pack LW n fun l => if use l then 2 ^ 143 else 0)).1 =
      (pack LW n fun l => if use l then chord.chord1 pa (pa + h) (beta l) (S l) (kk l) (A0 l) (A1 l)
        else 0) ∧
      ∀ l < n, use l → chord.chord1 pa (pa + h) (beta l) (S l) (kk l) (A0 l) (A1 l) ≤ QMX := by
  have hDS : DS = 2 ^ 36 := rfl
  -- the lower component
  set LOf : ℕ → ℕ := fun l => if beta l ≤ A0 l then h * ((A0 l - beta l) + (A1 l - beta l))
    else ((kk l - r1 l) + (A1 l - beta l)) * (h - q1 l - 1) with hLOf
  have hLOb : ∀ l < n, LOf l < 2 ^ 131 := by
    intro l hl
    have h1 := hbeta l hl; have h2 := hA0 l hl; have h3 := hA1 l hl; have h4 := hkk l hl
    simp only [hLOf]
    split_ifs
    · calc h * ((A0 l - beta l) + (A1 l - beta l)) ≤ 2 ^ 36 * 2 ^ 93 :=
            Nat.mul_le_mul (by omega) (by omega)
        _ < 2 ^ 131 := by norm_num
    · calc ((kk l - r1 l) + (A1 l - beta l)) * (h - q1 l - 1) ≤ 2 ^ 93 * 2 ^ 36 :=
            Nat.mul_le_mul (by omega) (by omega)
        _ < 2 ^ 131 := by norm_num
  -- the first division
  set a2 : ℕ → ℕ := fun l => beta l + S l - A0 l with ha2
  set q2f : ℕ → ℕ := fun l => if kk l = 0 then 2 ^ 37 - 1 else min (a2 l / kk l) (2 ^ 37 - 1) with hq2f
  set r2f : ℕ → ℕ := fun l => a2 l - kk l * q2f l with hr2f
  have hq2b : ∀ l < n, q2f l < 2 ^ 37 := fun l _ => by
    simp only [hq2f]; split_ifs <;> omega
  have hr2b : ∀ l < n, r2f l < 2 ^ 93 := fun l hl => by
    have := hbeta l hl; have := hS l hl
    simp only [hr2f, ha2]; omega
  have hbS : Nat.add (pack LW n beta) (pack LW n S) = pack LW n fun l => beta l + S l := pack_add _ _ _ _
  have hdiv1 : divQR LW 37 (mkVC n).G (tsub (mkVC n) (Nat.add (pack LW n beta) (pack LW n S)) (pack LW n A0))
      (pack LW n kk) = (pack LW n q2f, pack LW n r2f) := by
    rw [hbS, tsub_eq n _ A0 (fun l hl => by have := hbeta l hl; have := hS l hl; omega)
      (fun l hl => by have := hA0 l hl; omega)]
    rw [divQR_eq n _ kk (fun l hl => by have := hbeta l hl; have := hS l hl; omega)
      (fun l hl j hj => by
        have := hkk l hl
        calc kk l * 2 ^ j < 2 ^ 50 * 2 ^ 37 :=
              Nat.mul_lt_mul_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) hj.le) (by positivity)
          _ ≤ 2 ^ 143 := by norm_num)]
  -- the numerator
  set Nf : ℕ → ℕ := fun l => if A1 l ≤ beta l + S l then LOf l
    else (LOf l + r2f l * (h - q2f l)) - ((A1 l - (beta l + S l)) * (h - q2f l) + (kk l + kk l)) with hNf
  have hNb : ∀ l < n, Nf l < 2 ^ 132 := by
    intro l hl
    have h1 := hLOb l hl; have h2 := hr2b l hl
    simp only [hNf]
    split_ifs
    · omega
    · have : r2f l * (h - q2f l) ≤ 2 ^ 93 * 2 ^ 36 := Nat.mul_le_mul (by omega) (by omega)
      have : (2 : ℕ) ^ 93 * 2 ^ 36 = 2 ^ 129 := by norm_num
      omega
  have hN := chordN_eq n h beta S kk A1 LOf q2f r2f hh hbeta hS hkk hA1 hLOb hq2b hr2b
  -- the second division
  set qf : ℕ → ℕ := fun l => if S l + S l = 0 then 2 ^ 37 - 1 else min (Nf l / (S l + S l)) (2 ^ 37 - 1)
    with hqf
  have hdiv2 : divQR LW 37 (mkVC n).G (pack LW n Nf) (Nat.add (pack LW n S) (pack LW n S)) =
      (pack LW n qf, pack LW n fun l => Nf l - (S l + S l) * qf l) := by
    rw [show Nat.add (pack LW n S) (pack LW n S) = pack LW n fun l => S l + S l from pack_add _ _ _ _]
    exact divQR_eq n Nf _ (fun l hl => lt_trans (hNb l hl) (by norm_num))
      (fun l hl j hj => by
        have := hS l hl
        calc (S l + S l) * 2 ^ j < 2 ^ 93 * 2 ^ 37 :=
              Nat.mul_lt_mul_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by norm_num) hj.le) (by positivity)
          _ ≤ 2 ^ 143 := by norm_num)
  -- the closed form of chordV
  have hqfb : ∀ l < n, qf l < 2 ^ 144 := fun l _ => by
    simp only [hqf]; split_ifs <;> omega
  have hform : chordV (mkVC n) h (pack LW n beta) (pack LW n S) (pack LW n kk) (pack LW n A0) (pack LW n A1)
      (pack LW n q1) (pack LW n r1) (pack LW n fun l => if use l then 2 ^ 143 else 0) =
      (pack LW n (fun l => if use l then qf l else 0),
        allGe (mkVC n).G (bc (mkVC n) QMX) (pack LW n (fun l => if use l then qf l else 0))) := by
    unfold chordV chordV.chordV1 chordV.chordV2 chordV.chordV3 chordV.chordV4
    have hLO' : sl (ge (mkVC n) (pack LW n A0) (pack LW n beta))
        (Nat.mul h (Nat.add (tsub (mkVC n) (pack LW n A0) (pack LW n beta))
          (tsub (mkVC n) (pack LW n A1) (pack LW n beta))))
        (mulv (mkVC n) 37 (Nat.add (tsub (mkVC n) (pack LW n kk) (pack LW n r1))
            (tsub (mkVC n) (pack LW n A1) (pack LW n beta)))
          (tsub (mkVC n) (tsub (mkVC n) (bc (mkVC n) h) (pack LW n q1)) (mkVC n).O)) = pack LW n LOf :=
      chordLO_eq n h beta kk A0 A1 q1 r1 hh hbeta hkk hA0 hA1 hq1 hr1
    rw [hLO', hdiv1]
    dsimp only
    rw [hN, hdiv2]
    dsimp only
    rw [msk_eq n use qf hqfb]
  rw [hform] at hok ⊢
  dsimp only at hok ⊢
  rw [bc_eq, allGe_eq n _ _ (fun _ _ => by norm_num [QMX])
    (fun l hl => by
      split_ifs
      · have : qf l < 2 ^ 37 := by simp only [hqf]; split_ifs <;> omega
        omega
      · norm_num)] at hok
  -- lane by lane
  have hlane : ∀ l < n, use l →
      chord.chord1 pa (pa + h) (beta l) (S l) (kk l) (A0 l) (A1 l) = qf l ∧ qf l ≤ QMX := by
    intro l hl hu
    have hok' := hok l hl
    rw [ite_eq_left hu] at hok'
    obtain ⟨hB, hA0', hS0⟩ := huse l hl hu
    have hS2 : S l + S l ≠ 0 := by omega
    have hmin : min (Nf l / (S l + S l)) (2 ^ 37 - 1) = Nf l / (S l + S l) := by
      have : qf l = min (Nf l / (S l + S l)) (2 ^ 37 - 1) := by simp only [hqf]; rw [ite_eq_right hS2]
      rw [this] at hok'
      have hQMX : QMX = 2 ^ 37 - 2 := rfl
      rw [hQMX] at hok'
      exact min_eq_left (by omega)
    have hqfl : qf l = Nf l / (S l + S l) := by simp only [hqf]; rw [ite_eq_right hS2, hmin]
    refine ⟨?_, hok'⟩
    rw [hqfl]
    have hAl := hA l hl hu
    refine chord1_lane pa h (beta l) (S l) (kk l) (A0 l) (A1 l) (q1 l) (r1 l) (q2f l) (r2f l) (LOf l)
      hAl hB hA0' hS0 (hq l hl hu) (fun hlt => ?_) rfl
    have hk0 : kk l ≠ 0 := by
      intro hk
      rw [hk, zero_mul, add_zero] at hAl
      omega
    have hlt2 : a2 l < kk l * h := by simp only [ha2]; omega
    have hdiv : a2 l / kk l < h := (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hk0)).2 (by
      rw [mul_comm]; exact hlt2)
    have hq2e : q2f l = a2 l / kk l := by
      simp only [hq2f]
      rw [ite_eq_right hk0]
      exact min_eq_left (by omega)
    refine ⟨hq2e, ?_⟩
    simp only [hr2f]
    rw [hq2e, Nat.mod_eq_sub_mul_div]
  refine ⟨pack_congr _ _ _ _ fun l hl => ?_, fun l hl hu => ?_⟩
  · by_cases hu : use l
    · rw [ite_eq_left hu, ite_eq_left hu, (hlane l hl hu).1]
    · rw [ite_eq_right hu, ite_eq_right hu]
  · rw [(hlane l hl hu).1]
    exact (hlane l hl hu).2

/-- The crossing terms of a cell `i ≤ im`, lane by lane. -/
theorem crossV_spec (n a1 : ℕ) (c : CV) (a0 sig kk beta q1 : ℕ → ℕ) (ha0 : c.a0 = pack LW n a0)
    (hsig : c.sig = pack LW n sig) (hkk : c.kk = pack LW n kk) (ha1 : a1 < 2 ^ 47)
    (hpa : c.pa ≤ DS) (hh : c.h ≤ DS) (hpb2 : c.pb2 ≤ DS2) (ha0b : ∀ l < n, a0 l < 2 ^ 80)
    (hsigb : ∀ l < n, sig l < 2 ^ 48) (_hkkb : ∀ l < n, kk l < 2 ^ 50)
    (hbeta : ∀ l < n, beta l < 2 ^ 92) (hq1 : ∀ l < n, q1 l < 2 ^ 37) :
    crossV (mkVC n) a1 c (pack LW n beta) (pack LW n q1) =
      (pack LW n fun l => (a0 l + a0 l + a1 * (c.pa + c.pa + q1 l)) * q1 l + 2 * (beta l * (c.h - q1 l)),
        pack LW n fun l =>
          (c.pb2 - (c.pa + q1 l) * ((c.pa + q1 l) % 2 ^ 37)) * sig l + (kk l + kk l)) := by
  unfold crossV
  rw [ha0, hsig, hkk]
  simp only [bc_eq n]
  have hQ37 : 37 ≤ 144 := by decide
  have hQ48 : 48 ≤ 144 := by decide
  -- bounds for tsub_eq: c.h < 2^143 and q1 l < 2^143
  have hch_lt : ∀ l < n, c.h < 2 ^ 143 := by
    intro l hl
    have hDS_lt : DS < 2 ^ 143 := by unfold DS; norm_num
    exact lt_of_le_of_lt hh hDS_lt
  have hq1_lt143 : ∀ l < n, q1 l < 2 ^ 143 := by
    intro l hl
    have h37_lt_143 : 2 ^ 37 < 2 ^ 143 := by norm_num
    exact lt_trans (hq1 l hl) h37_lt_143
  -- bounds for mulv_eq (Q=37) first occurrence
  have h_mulv1_a : ∀ l < n, ∀ j < 37, (a0 l + a0 l + a1 * (c.pa + c.pa + q1 l)) * 2 ^ j < 2 ^ 144 := by
    intro l hl j hj
    have ha0l : a0 l < 2 ^ 80 := ha0b l hl
    have hpa' : c.pa ≤ 2 ^ 36 := hpa
    have hq1l : q1 l < 2 ^ 37 := hq1 l hl
    have ha1' : a1 < 2 ^ 47 := ha1
    -- c.pa + c.pa + q1 l < 2^36 + 2^36 + 2^37 = 3*2^36 < 4*2^36 = 2^38
    have hsum : c.pa + c.pa + q1 l < 2 ^ 38 := by
      have hle : c.pa + c.pa ≤ 2 ^ 36 + 2 ^ 36 := Nat.add_le_add hpa' hpa'
      have h1 : (c.pa + c.pa) + q1 l ≤ (2 ^ 36 + 2 ^ 36) + q1 l := Nat.add_le_add_right hle (q1 l)
      have h2 : (2 ^ 36 + 2 ^ 36) + q1 l < (2 ^ 36 + 2 ^ 36) + 2 ^ 37 :=
        Nat.add_lt_add_left hq1l (2 ^ 36 + 2 ^ 36)
      have hlt : (c.pa + c.pa) + q1 l < (2 ^ 36 + 2 ^ 36) + 2 ^ 37 :=
        lt_of_le_of_lt h1 h2
      have h3 : (2 ^ 36 + 2 ^ 36) + 2 ^ 37 = 2 ^ 38 := by norm_num
      rw [h3] at hlt
      exact hlt
    -- a1 * (c.pa + c.pa + q1 l) < 2^47 * 2^38 = 2^85
    have hprod : a1 * (c.pa + c.pa + q1 l) < 2 ^ 85 := by
      have h : a1 * (c.pa + c.pa + q1 l) < 2 ^ 47 * 2 ^ 38 :=
        Nat.mul_lt_mul_of_lt_of_le (c := 2 ^ 47) (d := 2 ^ 38) ha1' (Nat.le_of_lt hsum) (by positivity)
      simpa [show 2 ^ 47 * 2 ^ 38 = 2 ^ 85 by norm_num] using h
    -- a0 l + a0 l < 2^80 + 2^80 = 2^81
    -- a0 l + a0 l + a1 * (...) < 2^81 + 2^85 < 2^87
    have hmain : a0 l + a0 l + a1 * (c.pa + c.pa + q1 l) < 2 ^ 87 := by
      have hsum_lt : a0 l + a0 l < 2 ^ 81 := by
        have h : a0 l + a0 l < 2 ^ 80 + 2 ^ 80 := Nat.add_lt_add ha0l ha0l
        have h_eq : 2 ^ 80 + 2 ^ 80 = 2 ^ 81 := by norm_num
        omega
      have hsum' : a0 l + a0 l + a1 * (c.pa + c.pa + q1 l) < 2 ^ 81 + 2 ^ 85 :=
        Nat.add_lt_add hsum_lt hprod
      have h_lt : 2 ^ 81 + 2 ^ 85 < 2 ^ 87 := by norm_num
      exact lt_trans hsum' h_lt
    have h2j : 2 ^ j < 2 ^ 37 := Nat.pow_lt_pow_right (by norm_num) hj
    have hprod2 : (a0 l + a0 l + a1 * (c.pa + c.pa + q1 l)) * 2 ^ j < 2 ^ 87 * 2 ^ 37 :=
      Nat.mul_lt_mul_of_lt_of_le hmain (Nat.le_of_lt h2j) (by positivity)
    have : 2 ^ 87 * 2 ^ 37 < 2 ^ 144 := by norm_num
    omega
  have h_mulv1_b : ∀ l < n, q1 l < 2 ^ 144 := by
    intro l hl
    have h37_144 : 2 ^ 37 < 2 ^ 144 := by norm_num
    exact lt_trans (hq1 l hl) h37_144
  -- bounds for mulv_eq (Q=37) second occurrence: (c.pa + q1 l)
  have h_mulv2_a : ∀ l < n, ∀ j < 37, (c.pa + q1 l) * 2 ^ j < 2 ^ 144 := by
    intro l hl j hj
    have hsum : c.pa + q1 l < 2 ^ 38 := by
      have hpa' : c.pa ≤ 2 ^ 36 := hpa
      have hq1l : q1 l < 2 ^ 37 := hq1 l hl
      omega
    have h2j : 2 ^ j < 2 ^ 37 := Nat.pow_lt_pow_right (by norm_num) hj
    have hprod : (c.pa + q1 l) * 2 ^ j < 2 ^ 38 * 2 ^ 37 :=
      Nat.mul_lt_mul_of_lt_of_le hsum (Nat.le_of_lt h2j) (by positivity)
    have : 2 ^ 38 * 2 ^ 37 < 2 ^ 144 := by norm_num
    omega
  have h_mulv2_b : ∀ l < n, (c.pa + q1 l) < 2 ^ 144 := by
    intro l hl
    have hpa' : c.pa ≤ 2 ^ 36 := hpa
    have hq1l : q1 l < 2 ^ 37 := hq1 l hl
    have : 2 ^ 36 + 2 ^ 37 < 2 ^ 144 := by norm_num
    omega
  -- bounds for mulv_eq (Q=48): (c.pb2 - (c.pa + q1 l) * ((c.pa + q1 l) % 2 ^ 37))
  have h_mulv3_a : ∀ l < n, ∀ j < 48, (c.pb2 - (c.pa + q1 l) * ((c.pa + q1 l) % 2 ^ 37)) * 2 ^ j < 2 ^ 144 := by
    intro l hl j hj
    have hsub_le : c.pb2 - (c.pa + q1 l) * ((c.pa + q1 l) % 2 ^ 37) ≤ c.pb2 := Nat.sub_le _ _
    have hpb2_le : c.pb2 ≤ 2 ^ 72 := hpb2
    have hmain : c.pb2 - (c.pa + q1 l) * ((c.pa + q1 l) % 2 ^ 37) < 2 ^ 73 := by omega
    have h2j : 2 ^ j < 2 ^ 48 := Nat.pow_lt_pow_right (by norm_num) hj
    have hprod : (c.pb2 - (c.pa + q1 l) * ((c.pa + q1 l) % 2 ^ 37)) * 2 ^ j < 2 ^ 73 * 2 ^ 48 :=
      Nat.mul_lt_mul_of_lt_of_le hmain (Nat.le_of_lt h2j) (by positivity)
    have : 2 ^ 73 * 2 ^ 48 < 2 ^ 144 := by norm_num
    omega
  have h_mulv3_b : ∀ l < n, sig l < 2 ^ 144 := by
    intro l hl
    have h48_144 : 2 ^ 48 < 2 ^ 144 := by norm_num
    exact lt_trans (hsigb l hl) h48_144
  -- First component
  have h_first : Nat.add
      (mulv (mkVC n) 37
        (Nat.add (Nat.add (pack LW n a0) (pack LW n a0))
          (Nat.mul a1 (Nat.add (pack LW n (fun _ => c.pa + c.pa)) (pack LW n q1)))) (pack LW n q1))
      (Nat.mul 2 (mulv (mkVC n) 37 (pack LW n beta)
        (tsub (mkVC n) (pack LW n (fun _ => c.h)) (pack LW n q1)))) =
    pack LW n (fun l => (a0 l + a0 l + a1 * (c.pa + c.pa + q1 l)) * q1 l + 2 * (beta l * (c.h - q1 l))) := by
    have h_arg1 : Nat.add (Nat.add (pack LW n a0) (pack LW n a0))
        (Nat.mul a1 (Nat.add (pack LW n (fun _ => c.pa + c.pa)) (pack LW n q1))) =
        pack LW n (fun l => a0 l + a0 l + a1 * (c.pa + c.pa + q1 l)) := by
      simp [pack_add, pack_const_mul, add_comm, add_left_comm, add_assoc]
    rw [h_arg1]
    rw [mulv_eq n 37 (fun l => a0 l + a0 l + a1 * (c.pa + c.pa + q1 l)) q1 hQ37 h_mulv1_a h_mulv1_b]
    have h_mod_q1 : ∀ l < n, q1 l % 2 ^ 37 = q1 l := fun l hl => Nat.mod_eq_of_lt (hq1 l hl)
    have h_mul_q1 : pack LW n (fun l => (a0 l + a0 l + a1 * (c.pa + c.pa + q1 l)) * (q1 l % 2 ^ 37)) =
        pack LW n (fun l => (a0 l + a0 l + a1 * (c.pa + c.pa + q1 l)) * q1 l) := by
      refine pack_congr LW n _ _ fun l hl => ?_
      rw [h_mod_q1 l hl]
    rw [h_mul_q1]
    have h_tsub : tsub (mkVC n) (pack LW n (fun _ => c.h)) (pack LW n q1) =
        pack LW n (fun l => c.h - q1 l) := by
      rw [tsub_eq n (fun _ => c.h) q1 hch_lt hq1_lt143]
    rw [h_tsub]
    have h_sub_lt : ∀ l < n, c.h - q1 l < 2 ^ 144 := by
      intro l hl
      have : c.h ≤ 2 ^ 36 := hh
      have hq1l : q1 l < 2 ^ 37 := hq1 l hl
      have hle : c.h - q1 l ≤ c.h := Nat.sub_le _ _
      have : 2 ^ 36 < 2 ^ 144 := by norm_num
      omega
    have h_beta_ha : ∀ l < n, ∀ j < 37, beta l * 2 ^ j < 2 ^ 144 := by
      intro l hl j hj
      have hbeta_l : beta l < 2 ^ 92 := hbeta l hl
      have h2j : 2 ^ j < 2 ^ 37 := Nat.pow_lt_pow_right (by norm_num) hj
      have hprod : beta l * 2 ^ j < 2 ^ 92 * 2 ^ 37 :=
        Nat.mul_lt_mul_of_lt_of_le hbeta_l (Nat.le_of_lt h2j) (by positivity)
      have : 2 ^ 92 * 2 ^ 37 < 2 ^ 144 := by norm_num
      omega
    rw [mulv_eq n 37 beta (fun l => c.h - q1 l) hQ37 h_beta_ha h_sub_lt]
    have h_mod_hsubq1 : ∀ l < n, (c.h - q1 l) % 2 ^ 37 = c.h - q1 l := by
      intro l hl
      apply Nat.mod_eq_of_lt
      have : c.h ≤ 2 ^ 36 := hh
      have hq1l : q1 l < 2 ^ 37 := hq1 l hl
      omega
    have h_mul_sub : pack LW n (fun l => beta l * ((c.h - q1 l) % 2 ^ 37)) =
        pack LW n (fun l => beta l * (c.h - q1 l)) := by
      refine pack_congr LW n _ _ fun l hl => ?_
      rw [h_mod_hsubq1 l hl]
    rw [h_mul_sub]
    simp [pack_add, pack_const_mul]
  -- Second component
  have h_second : Nat.add
      (mulv (mkVC n) 48
        (tsub (mkVC n) (pack LW n (fun _ => c.pb2))
          (mulv (mkVC n) 37
            (Nat.add (pack LW n (fun _ => c.pa)) (pack LW n q1))
            (Nat.add (pack LW n (fun _ => c.pa)) (pack LW n q1)))) (pack LW n sig))
      (Nat.add (pack LW n kk) (pack LW n kk)) =
    pack LW n (fun l => (c.pb2 - (c.pa + q1 l) * ((c.pa + q1 l) % 2 ^ 37)) * sig l + (kk l + kk l)) := by
    have h_inner_arg : Nat.add (pack LW n (fun _ => c.pa)) (pack LW n q1) =
        pack LW n (fun l => c.pa + q1 l) := by
      simp [pack_add]
    rw [h_inner_arg]
    rw [mulv_eq n 37 (fun l => c.pa + q1 l) (fun l => c.pa + q1 l) hQ37 h_mulv2_a h_mulv2_b]
    have h_pb2_lt : c.pb2 < 2 ^ 143 := by
      have hDS2_lt : DS2 < 2 ^ 143 := by unfold DS2; norm_num
      exact lt_of_le_of_lt hpb2 hDS2_lt
    have h_mod_operand_lt : ∀ l < n, (c.pa + q1 l) * ((c.pa + q1 l) % 2 ^ 37) < 2 ^ 143 := by
      intro l hl
      have hsum : c.pa + q1 l < 2 ^ 38 := by
        have hpa' : c.pa ≤ 2 ^ 36 := hpa
        have hq1l : q1 l < 2 ^ 37 := hq1 l hl
        omega
      have hmod : (c.pa + q1 l) % 2 ^ 37 < 2 ^ 37 := Nat.mod_lt _ (by norm_num)
      have hprod : (c.pa + q1 l) * ((c.pa + q1 l) % 2 ^ 37) < 2 ^ 38 * 2 ^ 37 :=
      Nat.mul_lt_mul_of_lt_of_le hsum (Nat.le_of_lt hmod) (by positivity)
      have : 2 ^ 38 * 2 ^ 37 < 2 ^ 143 := by norm_num
      omega
    have h_tsub2 : tsub (mkVC n) (pack LW n (fun _ => c.pb2))
        (pack LW n (fun l => (c.pa + q1 l) * ((c.pa + q1 l) % 2 ^ 37))) =
        pack LW n (fun l => c.pb2 - (c.pa + q1 l) * ((c.pa + q1 l) % 2 ^ 37)) :=
      tsub_eq n (fun _ => c.pb2) (fun l => (c.pa + q1 l) * ((c.pa + q1 l) % 2 ^ 37))
        (fun _ _ => h_pb2_lt) h_mod_operand_lt
    rw [h_tsub2]
    rw [mulv_eq n 48 (fun l => c.pb2 - (c.pa + q1 l) * ((c.pa + q1 l) % 2 ^ 37)) sig hQ48 h_mulv3_a h_mulv3_b]
    have h_mod_sig : ∀ l < n, sig l % 2 ^ 48 = sig l := fun l hl => Nat.mod_eq_of_lt (hsigb l hl)
    have h_mod_sig' : ∀ l < n, sig l % 281474976710656 = sig l := by
      intro l hl
      simpa using h_mod_sig l hl
    have h_first_pack : pack LW n (fun l =>
        (c.pb2 - (c.pa + q1 l) * ((c.pa + q1 l) % 2 ^ 37)) * (sig l % 2 ^ 48)) =
        pack LW n (fun l => (c.pb2 - (c.pa + q1 l) * ((c.pa + q1 l) % 2 ^ 37)) * sig l) := by
      refine pack_congr LW n _ _ fun l hl => ?_
      simp [h_mod_sig' l hl]
    have h_kk_pack : (pack LW n kk).add (pack LW n kk) = pack LW n (fun l => kk l + kk l) := by
      simp [pack_add]
    rw [h_first_pack, h_kk_pack]
    exact pack_add LW n (fun l => (c.pb2 - (c.pa + q1 l) * ((c.pa + q1 l) % 2 ^ 37)) * sig l) (fun l => kk l + kk l)
  exact Prod.ext h_first h_second

/-- The crossing terms of a tail cell, lane by lane. -/
theorem crossT_spec (n a1 a0 sig kk : ℕ) (cl : SC) (beta q1 : ℕ → ℕ) (ha1 : a1 < 2 ^ 47)
    (ha0 : a0 < 2 ^ 80) (_hsig : sig < 2 ^ 48) (_hkk : kk < 2 ^ 50) (hpa : cl.pa ≤ DS)
    (hpb : cl.pb ≤ DS) (hh : cl.h ≤ DS) (hbeta : ∀ l < n, beta l < 2 ^ 92)
    (hq1 : ∀ l < n, q1 l < 2 ^ 37) :
    crossT (mkVC n) a1 a0 sig kk cl (pack LW n beta) (pack LW n q1) =
      (pack LW n fun l => (a0 + a0 + a1 * (cl.pa + cl.pa + q1 l)) * q1 l + 2 * (beta l * (cl.h - q1 l)),
        pack LW n fun l =>
          sig * (cl.pb * cl.pb - (cl.pa + q1 l) * ((cl.pa + q1 l) % 2 ^ 37)) + (kk + kk)) := by
  have hDS_val : DS = 2 ^ 36 := by unfold DS; norm_num
  have hQle : 37 ≤ 144 := by norm_num
  have hq1_lt_37 : ∀ l < n, q1 l < 2 ^ 37 := hq1
  have hq1_lt_144 : ∀ l < n, q1 l < 2 ^ 144 := by
    intro l hl
    have h := hq1 l hl
    have hpow : 2 ^ 37 < 2 ^ 144 := by norm_num
    exact Nat.lt_trans h hpow
  have hclh_lt_143 : cl.h < 2 ^ 143 := by
    have h := hh; rw [hDS_val] at h; omega
  have hclpa_lt_143 : cl.pa < 2 ^ 143 := by
    have h := hpa; rw [hDS_val] at h; omega
  have hclpb_lt_143 : cl.pb < 2 ^ 143 := by
    have h := hpb; rw [hDS_val] at h; omega
  have hclpb_sq_lt_143 : cl.pb * cl.pb < 2 ^ 143 := by
    have h := hpb; rw [hDS_val] at h
    have hsq : cl.pb * cl.pb ≤ 2 ^ 36 * 2 ^ 36 := Nat.mul_le_mul h h
    have h72 : 2 ^ 36 * 2 ^ 36 = 2 ^ 72 := by norm_num
    have h72_143 : 2 ^ 72 < 2 ^ 143 := by norm_num
    have : cl.pb * cl.pb ≤ 2 ^ 72 := by
      rw [← h72]; exact hsq
    omega
  have hbeta_lt_144 : ∀ l < n, beta l < 2 ^ 144 := by
    intro l hl
    have h := hbeta l hl
    have hpow : 2 ^ 92 < 2 ^ 144 := by norm_num
    exact Nat.lt_trans h hpow
  have hbeta_mul_bound : ∀ l < n, ∀ j < 37, beta l * 2 ^ j < 2 ^ 144 := by
    intro l hl j hj
    have h := hbeta l hl
    have hpow : 2 ^ j < 2 ^ 37 := Nat.pow_lt_pow_right (by norm_num) hj
    have h_mul : beta l * 2 ^ j < 2 ^ 92 * 2 ^ 37 := Nat.mul_lt_mul_of_lt_of_lt h hpow
    have : 2 ^ 92 * 2 ^ 37 < 2 ^ 144 := by norm_num
    exact Nat.lt_trans h_mul this
  have h_sub_bound : ∀ l < n, cl.h - q1 l < 2 ^ 144 := by
    intro l hl
    have hclh := hh; rw [hDS_val] at hclh
    have hq1l := hq1 l hl
    have hle : cl.h - q1 l ≤ cl.h := Nat.sub_le _ _
    have : 2 ^ 36 < 2 ^ 144 := by norm_num
    omega
  have h_sub_lt_37 : ∀ l < n, cl.h - q1 l < 2 ^ 37 := by
    intro l hl
    have hclh := hh; rw [hDS_val] at hclh
    have hq1l := hq1 l hl
    omega
  have h_paq_bound : ∀ l < n, cl.pa + q1 l < 2 ^ 144 := by
    intro l hl
    have hclpa := hpa; rw [hDS_val] at hclpa
    have hq1l := hq1 l hl
    have : 2 ^ 36 + 2 ^ 37 < 2 ^ 144 := by norm_num
    omega
  have h_paq_mul_bound : ∀ l < n, ∀ j < 37, (cl.pa + q1 l) * 2 ^ j < 2 ^ 144 := by
    intro l hl j hj
    have hsum : cl.pa + q1 l < 2 ^ 38 := by
      have hclpa := hpa; rw [hDS_val] at hclpa; have hq1l := hq1 l hl; omega
    have hpow : 2 ^ j < 2 ^ 37 := Nat.pow_lt_pow_right (by norm_num) hj
    have h_mul : (cl.pa + q1 l) * 2 ^ j < 2 ^ 38 * 2 ^ 37 := Nat.mul_lt_mul_of_lt_of_lt hsum hpow
    have : 2 ^ 38 * 2 ^ 37 < 2 ^ 144 := by norm_num
    exact Nat.lt_trans h_mul this
  have h_mul_bound : ∀ l < n, ∀ j < 37, (a0 + a0 + a1 * (cl.pa + cl.pa + q1 l)) * 2 ^ j < 2 ^ 144 := by
    intro l hl j hj
    have hsum : cl.pa + cl.pa + q1 l < 2 ^ 38 := by
      have hclpa := hpa; rw [hDS_val] at hclpa; have hq1l := hq1 l hl; omega
    have hprod : a1 * (cl.pa + cl.pa + q1 l) < 2 ^ 85 :=
      calc
        a1 * (cl.pa + cl.pa + q1 l) < 2 ^ 47 * 2 ^ 38 := Nat.mul_lt_mul_of_lt_of_lt ha1 hsum
        _ = 2 ^ 85 := by norm_num
    have ha0a0 : a0 + a0 < 2 ^ 81 := by
      have h := Nat.add_lt_add ha0 ha0
      have : 2 ^ 80 + 2 ^ 80 = 2 ^ 81 := by norm_num
      omega
    have htotal : a0 + a0 + a1 * (cl.pa + cl.pa + q1 l) < 2 ^ 86 := by
      have h_add : a0 + a0 + a1 * (cl.pa + cl.pa + q1 l) < 2 ^ 81 + 2 ^ 85 := Nat.add_lt_add ha0a0 hprod
      have h_lt : 2 ^ 81 + 2 ^ 85 < 2 ^ 86 := by norm_num
      omega
    have hpow : 2 ^ j < 2 ^ 37 := Nat.pow_lt_pow_right (by norm_num) hj
    have h_mul : (a0 + a0 + a1 * (cl.pa + cl.pa + q1 l)) * 2 ^ j < 2 ^ 86 * 2 ^ 37 := Nat.mul_lt_mul_of_lt_of_lt htotal hpow
    have : 2 ^ 86 * 2 ^ 37 < 2 ^ 144 := by norm_num
    exact Nat.lt_trans h_mul this
  apply Prod.ext
  · -- First component
    unfold crossT
    simp [bc_eq n, pack_add, pack_const_mul]
    -- Goal: mulv ... + 2 * mulv ... = pack ... + 2 * pack ...
    have h_tsub_eq : tsub (mkVC n) (pack LW n (fun _ => cl.h)) (pack LW n q1) = pack LW n (fun l => cl.h - q1 l) := by
      simpa using tsub_eq n (fun _ => cl.h) q1 (fun l _ => hclh_lt_143) (fun l hl => by
        have h := hq1 l hl; omega)
    rw [h_tsub_eq]
    have h_mulv1 : mulv (mkVC n) 37 (pack LW n (fun l => a0 + a0 + a1 * (cl.pa + cl.pa + q1 l))) (pack LW n q1) =
        pack LW n (fun l => (a0 + a0 + a1 * (cl.pa + cl.pa + q1 l)) * q1 l) :=
      mulv_eq' n 37 (fun l => a0 + a0 + a1 * (cl.pa + cl.pa + q1 l)) q1 hQle h_mul_bound hq1_lt_37
    have h_mulv2 : mulv (mkVC n) 37 (pack LW n beta) (pack LW n (fun l => cl.h - q1 l)) =
        pack LW n (fun l => beta l * (cl.h - q1 l)) :=
      mulv_eq' n 37 beta (fun l => cl.h - q1 l) hQle hbeta_mul_bound h_sub_lt_37
    rw [h_mulv1, h_mulv2]
    simp [pack_add, pack_const_mul]
  · -- Second component
    unfold crossT
    simp [bc_eq n, pack_add]
    -- Goal: sig * tsub ... (mulv ...) + pack ... = pack ...
    have h_mulv3 : mulv (mkVC n) 37 (pack LW n (fun l => cl.pa + q1 l)) (pack LW n (fun l => cl.pa + q1 l)) =
        pack LW n (fun l => (cl.pa + q1 l) * ((cl.pa + q1 l) % 2 ^ 37)) :=
      mulv_eq n 37 (fun l => cl.pa + q1 l) (fun l => cl.pa + q1 l) hQle h_paq_mul_bound h_paq_bound
    rw [h_mulv3]
    have h_tsub_eq : tsub (mkVC n) (pack LW n (fun _ => cl.pb * cl.pb))
        (pack LW n (fun l => (cl.pa + q1 l) * ((cl.pa + q1 l) % 2 ^ 37))) =
        pack LW n (fun l => (cl.pb * cl.pb) - ((cl.pa + q1 l) * ((cl.pa + q1 l) % 2 ^ 37))) := by
      apply tsub_eq n (fun _ => cl.pb * cl.pb) (fun l => (cl.pa + q1 l) * ((cl.pa + q1 l) % 2 ^ 37))
      · intro l _; exact hclpb_sq_lt_143
      · intro l hl
        have hsum : cl.pa + q1 l < 2 ^ 38 := by
          have hclpa := hpa; rw [hDS_val] at hclpa; have hq1l := hq1 l hl; omega
        have hmod : (cl.pa + q1 l) % 2 ^ 37 < 2 ^ 37 := Nat.mod_lt _ (by norm_num)
        have h_mul : (cl.pa + q1 l) * ((cl.pa + q1 l) % 2 ^ 37) < 2 ^ 38 * 2 ^ 37 :=
          Nat.mul_lt_mul_of_lt_of_lt hsum hmod
        have : 2 ^ 38 * 2 ^ 37 < 2 ^ 144 := by norm_num
        omega
    rw [h_tsub_eq]
    simp [pack_add, pack_const_mul]

end Robbins.Cert.SO.L
