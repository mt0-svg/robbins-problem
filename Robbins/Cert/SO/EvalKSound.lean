import Mathlib
import Robbins.Cert.EvalM2Eq
import Robbins.Cert.SO.Spec
import Robbins.Cert.SO.EvalK
import Robbins.Cert.SO.EvalKDefs

/-!
# The kernel evaluator of the second-order step against its specification

Equations between the recursor-form functions of Robbins/Cert/SO/EvalK.lean and the list, `ℕ` and
`ℤ` functions of Robbins/Cert/SO/Spec.lean (with `D = DS = 2 ^ 36`): the cell integral and the
chord (natural pairs against the integers of the specification), the decoding of the packed
tables, the penalty tables, the binomial terms of the rank, the packed accumulators.
-/

namespace Robbins.Cert.SO.K

open Robbins.Cert Robbins.Cert.K

/-! ## Small combinators -/

theorem lget_eq (l : List ℕ) (i : ℕ) : lget l i = l.getD i 0 := by
  simp [lget, ldrop_eq, hd_eq]

theorem nmin2_eq (a b : ℕ) : nmin2 a b = min a b := by
  unfold nmin2
  rw [bsel_eq]
  split_ifs with h
  · have hle : a ≤ b := by
      rwa [Nat.ble_eq] at h
    omega
  · have hle : ¬ a ≤ b := by
      rwa [Nat.ble_eq] at h
    omega


theorem binoms_eq_aux1 (x k i : ℕ) : binomsAux x k i (Nat.choose (x + i) (i + 1)) = (List.range k).map fun j => (x + i + j).choose (i + j + 1) := by
  induction' k with k ih generalizing i
  · rfl
  · unfold binomsAux
    have h_eq : Nat.choose (x + i) (i + 1) * (x + i + 1) / (i + 2) = Nat.choose (x + i + 1) (i + 2) := by
      have h_mul := Nat.add_one_mul_choose_eq (x + i) (i + 1)
      have h_mul' : Nat.choose (x + i) (i + 1) * (x + i + 1) = Nat.choose (x + i + 1) (i + 2) * (i + 2) := by
        simpa [mul_comm] using h_mul
      rw [h_mul']
      exact Nat.mul_div_cancel (Nat.choose (x + i + 1) (i + 2)) (by omega)
    rw [h_eq]
    have h_goal : List.map (fun j => (x + i + j).choose (i + j + 1)) (List.range (k + 1)) =
        (x + i).choose (i + 1) :: List.map (fun j => (x + i + (j + 1)).choose (i + (j + 1) + 1)) (List.range k) := by
      simp [List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp, add_comm, add_left_comm, add_assoc]
    rw [h_goal]
    have h_ih := ih (i + 1)
    -- h_ih: binomsAux x k (i+1) ((x+(i+1)).choose(i+1+1)) = List.map (fun j => (x+(i+1)+j).choose(i+1+j+1)) (List.range k)
    -- need: binomsAux x k (i+1) ((x+i+1).choose(i+2)) = List.map (fun j => (x+i+(j+1)).choose(i+(j+1)+1)) (List.range k)
    simpa [add_comm, add_left_comm, add_assoc] using congrArg (fun t => (Nat.choose (x + i) (i + 1)) :: t) h_ih

theorem binoms_eq (m x : ℕ) : binoms m x = (List.range m).map fun j => (x + j).choose (j + 1) := by
  simpa [Robbins.Cert.SO.K.binoms, Nat.choose_one_right] using binoms_eq_aux1 x m 0

theorem dot_eq (xs ys : List ℕ) : dot xs ys = (List.zipWith (· * ·) xs ys).sum := by
  unfold dot
  rw [lfoldr_eq, lzipWith_eq]
  have h_add : (Nat.add : ℕ → ℕ → ℕ) = (· + ·) := by
    ext x y; rfl
  have h_mul : (Nat.mul : ℕ → ℕ → ℕ) = (· * ·) := by
    ext x y; rfl
  simpa [h_add, h_mul] using (List.sum_eq_foldr (l := List.zipWith (· * ·) xs ys)).symm

/-! ## Cell integral and chord (section 5.1, 5.2) -/

theorem cell2_eq (pa pb a0 a1 b0 b1 rp rn : ℕ) (hab : pa ≤ pb) (ha1 : 0 < a1) :
    ((cell2 pa pb a0 a1 b0 b1 rp rn).p : ℤ) - (cell2 pa pb a0 a1 b0 b1 rp rn).n =
      (rp : ℤ) - rn + SO.cell2 pa pb a0 a1 b0 b1 := by
  dsimp [cell2, cell2.cell2a, cell2.cell2b, cell2.cell2z, SO.cell2]
  simp only [bsel_eq, Nat.ble_eq]
  split
  · rename_i hA1b0
    -- hA1b0 : A1 ≤ b0
    simp [Nat.cast_sub hab]
    -- The SO.cell2 condition db ≤ 0 is equivalent to A1 ≤ b0, which we have
    have hdb : (a0 : ℤ) - (b0 : ℤ) + ((a1 : ℤ) + (b1 : ℤ)) * (pa : ℤ) + ((a1 : ℤ) + (b1 : ℤ)) * ((pb : ℤ) - (pa : ℤ)) ≤ 0 := by
      have h' : (a0 : ℤ) + ((a1 : ℤ) + (b1 : ℤ)) * (pb : ℤ) ≤ (b0 : ℤ) := by
        have := hA1b0
        exact mod_cast this
      linarith
    rw [ite_eq_left hdb]
    ring_nf
  · rename_i hA1b0
    -- hA1b0 : ¬ A1 ≤ b0
    -- Now split on b0 ≤ A0 for the kernel
    by_cases hb0A0 : b0 ≤ a0 + (a1 + b1) * pa
    · -- b0 ≤ A0
      simp [hb0A0]
      -- Now the kernel returns IB, and SO.cell2 also returns IB (since 0 ≤ da)
      have hsq : pa ^ 2 ≤ pb ^ 2 := Nat.pow_le_pow_left hab 2
      have hda : 0 ≤ (a0 : ℤ) - (b0 : ℤ) + ((a1 : ℤ) + (b1 : ℤ)) * (pa : ℤ) := by
        have h' : (b0 : ℤ) ≤ (a0 : ℤ) + ((a1 : ℤ) + (b1 : ℤ)) * (pa : ℤ) := by exact mod_cast hb0A0
        linarith
      have hdb : ¬ ((a0 : ℤ) - (b0 : ℤ) + ((a1 : ℤ) + (b1 : ℤ)) * (pa : ℤ) + ((a1 : ℤ) + (b1 : ℤ)) * ((pb : ℤ) - (pa : ℤ)) ≤ 0) := by
        intro h
        apply hA1b0
        have h'' : (a0 : ℤ) + ((a1 : ℤ) + (b1 : ℤ)) * (pb : ℤ) ≤ (b0 : ℤ) := by linarith
        exact mod_cast h''
      rw [ite_eq_right hdb, ite_eq_left hda]
      have hsq' : pa * pa ≤ pb * pb := by
        -- pa^2 ≤ pb^2 implies pa*pa ≤ pb*pb
        simpa [sq] using hsq
      simp [Nat.cast_sub hab, Nat.cast_sub hsq']
      ring_nf
    · -- ¬ b0 ≤ A0
      simp [hb0A0]
      -- Now the kernel returns cell2z, and SO.cell2 returns crossing (since ¬ 0 ≤ da)
      have hda : ¬ (0 ≤ (a0 : ℤ) - (b0 : ℤ) + ((a1 : ℤ) + (b1 : ℤ)) * (pa : ℤ)) := by
        intro h
        apply hb0A0
        have h' : (b0 : ℤ) ≤ (a0 : ℤ) + ((a1 : ℤ) + (b1 : ℤ)) * (pa : ℤ) := by linarith
        exact mod_cast h'
      have hdb : ¬ ((a0 : ℤ) - (b0 : ℤ) + ((a1 : ℤ) + (b1 : ℤ)) * (pa : ℤ) + ((a1 : ℤ) + (b1 : ℤ)) * ((pb : ℤ) - (pa : ℤ)) ≤ 0) := by
        intro h
        apply hA1b0
        have h'' : (a0 : ℤ) + ((a1 : ℤ) + (b1 : ℤ)) * (pb : ℤ) ≤ (b0 : ℤ) := by linarith
        exact mod_cast h''
      rw [ite_eq_right hdb, ite_eq_right hda]
      -- Now we have the crossing case equality
      -- Key inequality: z = pa + (b0 - A0) / kk < pb
      have hkk : 0 < a1 + b1 := by omega
      have hA0_lt_b0 : a0 + (a1 + b1) * pa < b0 := by omega
      have hb0_lt_A1 : b0 < a0 + (a1 + b1) * pb := by omega
      have h_sub_pos : b0 - (a0 + (a1 + b1) * pa) < (a1 + b1) * (pb - pa) := by
        -- b0 - A0 ≤ b0 < A1 = A0 + kk*(pb-pa), so b0 - A0 < kk*(pb-pa)
        have h : b0 < a0 + (a1 + b1) * pa + (a1 + b1) * (pb - pa) := by
          have hA1 : a0 + (a1 + b1) * pb = a0 + (a1 + b1) * pa + (a1 + b1) * (pb - pa) := by
            calc
              a0 + (a1 + b1) * pb = a0 + (a1 + b1) * (pa + (pb - pa)) := by
                rw [Nat.add_sub_cancel' hab]
              _ = a0 + ((a1 + b1) * pa + (a1 + b1) * (pb - pa)) := by rw [Nat.mul_add]
              _ = a0 + (a1 + b1) * pa + (a1 + b1) * (pb - pa) := by rw [Nat.add_assoc]
          omega
        omega
      have h_div_lt : (b0 - (a0 + (a1 + b1) * pa)).div (a1 + b1) < pb - pa :=
        (Nat.div_lt_iff_lt_mul hkk).mpr (by
          -- h_sub_pos: b0 - A0 < (a1+b1) * (pb-pa)
          -- Nat.div_lt_iff_lt_mul expects: b0 - A0 < (pb-pa) * (a1+b1)
          -- So we need to commute
          rw [mul_comm (a1 + b1) (pb - pa)] at h_sub_pos
          exact h_sub_pos)
      have hz_pa_le_pb : pa + (b0 - (a0 + (a1 + b1) * pa)).div (a1 + b1) ≤ pb := by
        omega
      -- Now push all the Nat.cast inside using Int.natCast_div (no divisibility needed)
      set z := (b0 - (a0 + (a1 + b1) * pa)).div (a1 + b1) with hz
      have hz_sub : (pa + z : ℕ) ≤ pb := hz_pa_le_pb
      have hz_sq_sub : ((pa + z : ℕ) ^ 2 : ℕ) ≤ pb ^ 2 := Nat.pow_le_pow_left hz_sub 2
      -- Now push casts inside
      rw [Nat.cast_sub hz_sub]
      -- Goal: ... ↑(pb * pb - (pa + z) * (pa + z)) ...
      -- Rewrite (pa+z)*(pa+z) = (pa+z)^2 and pb*pb = pb^2
      have h_sq1 : (pa + z) * (pa + z) = (pa + z) ^ 2 := by ring
      have h_sq2 : pb * pb = pb ^ 2 := by ring
      rw [h_sq1, h_sq2]
      -- Now: ↑(pb ^ 2 - (pa + z) ^ 2)
      -- We know (pa+z)^2 ≤ pb^2 from hz_sq_sub
      rw [Nat.cast_sub hz_sq_sub]
      -- Now push all remaining Nat.cast inside
      push_cast
      -- Now the goal is a ring equation, but the RHS has division by (a1+b1)
      -- We know z = (b0 - A0) / kk in ℤ
      have hz_eq : (z : ℤ) = ((b0 : ℤ) - ((a0 : ℤ) + ((a1 : ℤ) + (b1 : ℤ)) * (pa : ℤ))) / ((a1 : ℤ) + (b1 : ℤ)) := by
        rw [hz]
        have hsub : a0 + (a1 + b1) * pa ≤ b0 := by omega
        have h := Int.natCast_div (b0 - (a0 + (a1 + b1) * pa)) (a1 + b1)
        -- h: ↑((b0 - A0) / kk) = ↑(b0 - A0) / ↑kk
        -- Goal: ↑((b0 - A0).div kk) = (↑b0 - (↑a0 + (↑a1 + ↑b1) * ↑pa)) / (↑a1 + ↑b1)
        -- LHS of h is definitionally equal to goal LHS, so use h.trans
        apply h.trans
        -- Now goal: ↑(b0 - A0) / ↑kk = (↑b0 - (↑a0 + (↑a1 + ↑b1) * ↑pa)) / (↑a1 + ↑b1)
        simp [Nat.cast_sub hsub, Nat.cast_add, Nat.cast_mul]
      -- The division expression on the RHS equals z
      -- Note: the goal has (-k*pa + (b0-a0))/k, but hz_eq has (b0-(a0+k*pa))/k
      -- These are equal by ring, and both equal z
      have hz_eq2 : (-((a1 : ℤ) + (b1 : ℤ)) * (pa : ℤ) + ((b0 : ℤ) - (a0 : ℤ))) / ((a1 : ℤ) + (b1 : ℤ)) = (z : ℤ) := by
        rw [hz_eq]
        congr 1
        ring
      -- Now rewrite the division to z
      rw [← hz_eq2]
      ring_nf

theorem chord_eq_aux1 (X Y n : ℕ) :
    (((X - Y) / n : ℕ) : ℤ) = if 0 < (X : ℤ) - Y then ((X : ℤ) - Y) / n else 0 := by
  split_ifs with h
  · rw [Int.natCast_div, Nat.cast_sub (by omega)]
  · rw [Nat.sub_eq_zero_of_le (by omega), Nat.zero_div, Nat.cast_zero]

theorem chord_eq_aux2 (Pa Pb da k c q r : ℤ) (hk : 0 < k) (hr0 : 0 ≤ r) (hr : r < k)
    (hac : da - c = -(k * q + r)) (hpos : 0 < k * q + r) (hbc : 0 < da - c + k * (Pb - Pa)) :
    SO.pos2 Pa Pb da k c = ((-r + k + (da - c + k * (Pb - Pa))) * (Pb - (Pa + q) - 1),
      (-r + (da - c + k * (Pb - Pa))) * (Pb - (Pa + q)) + 2 * k) := by
  have hdiv : -(da - c) / k = q := by
    rw [hac, neg_neg, show k * q + r = r + k * q by ring, Int.add_mul_ediv_left _ _ hk.ne',
      Int.ediv_eq_zero_of_lt hr0 hr, zero_add]
  unfold SO.pos2
  simp only
  rw [ite_eq_right (not_le.mpr hbc), ite_eq_right (not_le.mpr (by linarith)), hdiv]
  ext
  · linear_combination (Pb - (Pa + q) - 1) * hac
  · linear_combination (Pb - (Pa + q)) * hac

theorem chord_eq_aux3 (pa pb b0 S kk A0 A1 : ℕ) (hab : pa ≤ pb) (hkk : 0 < kk)
    (hA : A1 = A0 + kk * (pb - pa)) :
    (chord.chord1 pa pb b0 S kk A0 A1 : ℤ) =
      if ((A0 : ℤ) - b0) + (kk : ℤ) * ((pb : ℤ) - pa) ≤ 0 then 0
      else if (S : ℤ) ≤ (A0 : ℤ) - b0 then (pb : ℤ) - pa
      else if 0 < (SO.pos2 pa pb ((A0 : ℤ) - b0) kk 0).1 - (SO.pos2 pa pb ((A0 : ℤ) - b0) kk S).2
        then ((SO.pos2 pa pb ((A0 : ℤ) - b0) kk 0).1 - (SO.pos2 pa pb ((A0 : ℤ) - b0) kk S).2) /
          (2 * S)
        else 0 := by
  have hdiv : ∀ x y : ℕ, Nat.div x y = x / y := fun _ _ => rfl
  have hmod : ∀ x y : ℕ, Nat.mod x y = x % y := fun _ _ => rfl
  have hAz : (A1 : ℤ) = A0 + kk * ((pb : ℤ) - pa) := by
    rw [hA]; push_cast [Nat.cast_sub hab]; ring
  have hA1 : ((A0 : ℤ) - b0) + (kk : ℤ) * ((pb : ℤ) - pa) = (A1 : ℤ) - b0 := by rw [hAz]; ring
  rw [hA1]
  unfold chord.chord1 chord.chord2 chord.chord3 chord.chordLo
  simp only [bsel_eq, Nat.ble_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq, hdiv, hmod]
  by_cases h1 : A1 ≤ b0
  · rw [ite_eq_left h1, ite_eq_left (show (A1 : ℤ) - b0 ≤ 0 by omega), Nat.cast_zero]
  rw [ite_eq_right h1, ite_eq_right (show ¬ ((A1 : ℤ) - b0 ≤ 0) by omega)]
  by_cases h2 : b0 + S ≤ A0
  · rw [ite_eq_left h2, ite_eq_left (show (S : ℤ) ≤ A0 - b0 by omega), Nat.cast_sub hab]
  rw [ite_eq_right h2, ite_eq_right (show ¬ ((S : ℤ) ≤ A0 - b0) by omega)]
  have hlo : (SO.pos2 pa pb ((A0 : ℤ) - b0) kk 0).1 =
      ((if b0 ≤ A0 then (A0 - b0 + (A1 - b0)) * (pb - pa)
        else (kk - (b0 - A0) % kk + (A1 - b0)) * (pb - (pa + (b0 - A0) / kk) - 1) : ℕ) : ℤ) := by
    split_ifs with h3
    · unfold SO.pos2
      simp only
      rw [ite_eq_right (not_le.mpr (by linarith)), ite_eq_left (by linarith)]
      push_cast [Nat.cast_sub hab, Nat.cast_sub h3, Nat.cast_sub (show b0 ≤ A1 by omega)]
      linear_combination (-((pb : ℤ) - pa)) * hAz
    · obtain ⟨q, hq_def⟩ : ∃ q, q = (b0 - A0) / kk := ⟨_, rfl⟩
      obtain ⟨r, hr_def⟩ : ∃ r, r = (b0 - A0) % kk := ⟨_, rfl⟩
      rw [← hq_def, ← hr_def]
      have hqr : b0 - A0 = kk * q + r := by rw [hq_def, hr_def]; exact (Nat.div_add_mod _ _).symm
      have hr : r < kk := hr_def ▸ Nat.mod_lt _ hkk
      have hq : q < pb - pa := by
        rw [hq_def, Nat.div_lt_iff_lt_mul hkk]
        have : kk * (pb - pa) = (pb - pa) * kk := Nat.mul_comm _ _
        omega
      have hb0 : (b0 : ℤ) = A0 + (kk * q + r) := by
        have : b0 = A0 + (kk * q + r) := by omega
        exact_mod_cast this
      have hA1b : (b0 : ℤ) < A1 := by exact_mod_cast (show b0 < A1 by omega)
      rw [chord_eq_aux2 pa pb ((A0 : ℤ) - b0) kk 0 q r (by exact_mod_cast hkk) (by positivity)
        (by exact_mod_cast hr) (by rw [hb0]; ring) (by have := hb0; omega)
        (by linarith)]
      push_cast [Nat.cast_sub hab, Nat.cast_sub hr.le, Nat.cast_sub (show b0 ≤ A1 by omega),
        Nat.cast_sub (show pa + q ≤ pb by omega), Nat.cast_sub (show 1 ≤ pb - (pa + q) by omega)]
      linear_combination (-((pb : ℤ) - (pa + q) - 1)) * hAz
  generalize (if b0 ≤ A0 then (A0 - b0 + (A1 - b0)) * (pb - pa)
    else (kk - (b0 - A0) % kk + (A1 - b0)) * (pb - (pa + (b0 - A0) / kk) - 1)) = lo at hlo ⊢
  rw [hlo]
  by_cases h4 : A1 ≤ b0 + S
  · rw [ite_eq_left h4]
    have hup : (SO.pos2 pa pb ((A0 : ℤ) - b0) kk S).2 = 0 := by
      unfold SO.pos2
      simp only
      rw [ite_eq_left (by linarith)]
    rw [hup, sub_zero]
    have := chord_eq_aux1 lo 0 (2 * S)
    simp only [Nat.sub_zero, Nat.cast_zero, sub_zero] at this
    rw [this]
    push_cast
    rfl
  · rw [ite_eq_right h4]
    obtain ⟨q, hq_def⟩ : ∃ q, q = (b0 + S - A0) / kk := ⟨_, rfl⟩
    obtain ⟨r, hr_def⟩ : ∃ r, r = (b0 + S - A0) % kk := ⟨_, rfl⟩
    rw [← hq_def, ← hr_def]
    have hqr : b0 + S - A0 = kk * q + r := by
      rw [hq_def, hr_def]; exact (Nat.div_add_mod _ _).symm
    have hr : r < kk := hr_def ▸ Nat.mod_lt _ hkk
    have hq : q < pb - pa := by
      rw [hq_def, Nat.div_lt_iff_lt_mul hkk]
      have : kk * (pb - pa) = (pb - pa) * kk := Nat.mul_comm _ _
      omega
    have hb0 : (b0 : ℤ) + S = A0 + (kk * q + r) := by
      have : b0 + S = A0 + (kk * q + r) := by omega
      exact_mod_cast this
    have hA1b : (b0 : ℤ) + S < A1 := by exact_mod_cast (show b0 + S < A1 by omega)
    rw [chord_eq_aux2 pa pb ((A0 : ℤ) - b0) kk S q r (by exact_mod_cast hkk) (by positivity)
      (by exact_mod_cast hr) (by linear_combination (-1 : ℤ) * hb0) (by have := hb0; omega)
      (by linarith)]
    rw [chord_eq_aux1]
    have e : ((lo + r * (pb - (pa + q)) : ℕ) : ℤ) - (((A1 - (b0 + S)) * (pb - (pa + q)) + 2 * kk : ℕ) : ℤ) =
        (lo : ℤ) - ((-r + ((A0 : ℤ) - b0 - S + kk * ((pb : ℤ) - pa))) * (pb - (pa + q)) + 2 * kk) := by
      push_cast [Nat.cast_sub (show b0 + S ≤ A1 by omega), Nat.cast_sub (show pa + q ≤ pb by omega)]
      linear_combination (-((pb : ℤ) - (pa + q))) * hAz
    rw [e]
    push_cast
    rfl

theorem chord_eq (pa pb a0 a1 b0 b1 S : ℕ) (hab : pa ≤ pb) (ha1 : 0 < a1) (hS : 0 < S) :
    (chord pa pb a0 a1 b0 b1 S : ℤ) = SO.chord pa pb a0 a1 b0 b1 S := by
  clear hS
  have hkk : 0 < a1 + b1 := by omega
  have hA : a0 + (a1 + b1) * pb = a0 + (a1 + b1) * pa + (a1 + b1) * (pb - pa) := by
    zify [hab]; ring
  show ((chord.chord1 pa pb b0 S (a1 + b1) (a0 + (a1 + b1) * pa) (a0 + (a1 + b1) * pb) : ℕ) : ℤ) = _
  rw [chord_eq_aux3 _ _ _ _ _ _ _ hab hkk hA]
  have key : ∀ k da : ℤ, k = (a1 : ℤ) + b1 → da = (a0 : ℤ) - b0 + k * pa →
      SO.chord pa pb a0 a1 b0 b1 S =
        if da + k * ((pb : ℤ) - pa) ≤ 0 then 0
        else if (S : ℤ) ≤ da then (pb : ℤ) - pa
        else if 0 < (SO.pos2 pa pb da k 0).1 - (SO.pos2 pa pb da k S).2
          then ((SO.pos2 pa pb da k 0).1 - (SO.pos2 pa pb da k S).2) / (2 * S)
          else 0 := by
    rintro k da rfl rfl
    rfl
  rw [key ((a1 + b1 : ℕ) : ℤ) (((a0 + (a1 + b1) * pa : ℕ) : ℤ) - b0) (by push_cast; ring)
    (by push_cast; ring)]

/-! ## Penalty tables (section 3) -/

theorem nextE_eq (gptD E : List ℕ) :
    nextE gptD E = List.zipWith (fun p e => e * (DS - p) / DS) gptD E := by
  unfold nextE
  rw [lzipWith_eq]
  rfl

theorem Eback_getD (gptD : List ℕ) (q j : ℕ) (hj : j < gptD.length) :
    (Eback gptD q).getD j 0 = SO.Epen DS (gptD.getD j 0) q := by
  have hlen : ∀ q, (Eback gptD q).length = gptD.length := by
    intro q
    induction' q with q ih
    · simp [Eback]
      rw [lmap_eq]
      simp
    · simp [Eback]
      rw [← Eback]
      rw [nextE_eq]
      rw [List.length_zipWith]
      rw [ih]
      simp
  induction' q with q ih
  · simp [Eback, SO.Epen, lmap_eq, hj]
  · rw [Eback, SO.Epen]
    simp
    have hEback_eq : Nat.rec (lmap (fun _ => DS) gptD) (fun x ih => SO.K.nextE gptD ih) q = Eback gptD q := by rfl
    rw [hEback_eq]
    rw [nextE_eq]
    have hzip_len : j < (List.zipWith (fun p e => e * (DS - p) / DS) gptD (Eback gptD q)).length := by
      rw [List.length_zipWith, hlen q, min_self]
      exact hj
    have hi_right : j < (Eback gptD q).length := by rw [hlen q]; exact hj
    rw [show (List.zipWith (fun p e => e * (DS - p) / DS) gptD (Eback gptD q))[j]?.getD 0 =
             (List.zipWith (fun p e => e * (DS - p) / DS) gptD (Eback gptD q)).getD j 0 by rfl]
    rw [List.getD_eq_getElem (List.zipWith (fun p e => e * (DS - p) / DS) gptD (Eback gptD q)) 0 hzip_len]
    rw [List.getElem_zipWith (f := fun p e => e * (DS - p) / DS) (l := gptD) (l' := Eback gptD q) (i := j) (h := hzip_len)]
    have hEback_get : (Eback gptD q)[j] = (Eback gptD q).getD j 0 := by
      simpa using (List.getD_eq_getElem (Eback gptD q) 0 hi_right).symm
    have hgpt_get : gptD[j] = gptD.getD j 0 := by
      simpa using (List.getD_eq_getElem gptD 0 hj).symm
    rw [hEback_get, hgpt_get]
    rw [ih]
    rfl

/-! ## Packed states -/

-- Helper lemma: list identity
theorem slopes_eq_aux1 (f : ℕ → ℕ) (m : ℕ) :
    (List.range (m + 1)).map f = f 0 :: (List.range m).map (fun i => f (i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.map_singleton]
      -- Goal: List.map f (List.range (m+1)) ++ [f (m+1)] = f 0 :: List.map (fun i => f (i+1)) (List.range (m+1))
      rw [ih]
      -- Goal: (f 0 :: List.map (fun i => f (i+1)) (List.range m)) ++ [f (m+1)] = f 0 :: List.map (fun i => f (i+1)) (List.range (m+1))
      rw [List.cons_append]
      -- Goal: f 0 :: (List.map (fun i => f (i+1)) (List.range m) ++ [f (m+1)]) = f 0 :: List.map (fun i => f (i+1)) (List.range (m+1))
      rw [List.range_succ, List.map_append, List.map_singleton]

theorem slopes_eq (m st : ℕ) :
    slopes m st = (List.range m).map fun l => st / 2 ^ (48 * (l + 1)) % 2 ^ 48 := by
  induction m generalizing st with
  | zero =>
      simp [slopes]
  | succ m ih =>
      simp only [slopes, slopes.slopes2]
      have h_first : (Nat.shiftRight st 48).land M48 = st / 2 ^ 48 % 2 ^ 48 := by
        change (st >>> 48).land M48 = st / 2 ^ 48 % 2 ^ 48
        rw [Nat.shiftRight_eq_div_pow, M48]
        exact Nat.and_two_pow_sub_one_eq_mod (x := st / 2 ^ 48) (n := 48)
      rw [h_first]
      have h_rec : Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
        (fun _ ih' x' => (Nat.shiftRight x' 48).land M48 :: ih' (Nat.shiftRight x' 48)) m (Nat.shiftRight st 48) =
        slopes m (Nat.shiftRight st 48) := by
        simp [slopes, slopes.slopes2]
      rw [h_rec]
      rw [ih (Nat.shiftRight st 48)]
      have h_map_eq : (fun (l : ℕ) => (st / 2 ^ 48) / 2 ^ (48 * (l + 1)) % 2 ^ 48) =
          (fun (l : ℕ) => st / 2 ^ (48 * (l + 1 + 1)) % 2 ^ 48) := by
        ext l
        calc
          (st / 2 ^ 48) / 2 ^ (48 * (l + 1)) % 2 ^ 48
              = st / ((2 ^ 48) * (2 ^ (48 * (l + 1)))) % 2 ^ 48 := by
            rw [Nat.div_div_eq_div_mul]
          _ = st / (2 ^ (48 + 48 * (l + 1))) % 2 ^ 48 := by rw [← pow_add, add_comm]
          _ = st / (2 ^ (48 * (l + 1 + 1))) % 2 ^ 48 := by
            rw [show (48 : ℕ) + 48 * (l + 1) = 48 * (l + 1 + 1) by omega]
      have h_target : (st / 2 ^ 48 % 2 ^ 48) :: List.map (fun l => (st / 2 ^ 48) / 2 ^ (48 * (l + 1)) % 2 ^ 48) (List.range m) =
          List.map (fun l => st / 2 ^ (48 * (l + 1)) % 2 ^ 48) (List.range (m + 1)) := by
        rw [h_map_eq]
        let f : ℕ → ℕ := fun l => st / 2 ^ (48 * (l + 1)) % 2 ^ 48
        simpa [f] using (slopes_eq_aux1 f m).symm
      simpa [Nat.shiftRight_eq_div_pow] using h_target

/-! ## Packed accumulators -/

theorem packF_field (xs : List ℕ) (h : ∀ x ∈ xs, x < 2 ^ 128) (l : ℕ) :
    packF xs / 2 ^ (128 * l) % 2 ^ 128 = xs.getD l 0 := by
  induction xs generalizing l with
  | nil =>
      simp [packF, lfoldr_eq]
  | cons x xs ih =>
      have hx : x < 2 ^ 128 := h x (by simp)
      have hxs : ∀ x ∈ xs, x < 2 ^ 128 := by
        intro y hy
        apply h y
        simp [hy]
      have hF128 : F128 = 2 ^ 128 := by norm_num [F128]
      have hpackF : packF (x :: xs) = x + packF xs * 2 ^ 128 := by
        dsimp [packF]
        rw [lfoldr_eq, List.foldr_cons, lfoldr_eq]
        simp [hF128]
      rw [hpackF]
      cases l with
      | zero =>
          simpa [Nat.add_mul_mod_self_right] using Nat.mod_eq_of_lt hx
      | succ l2 =>
          have hpos : 0 < 2 ^ 128 := by norm_num
          have hx_div : x / 2 ^ 128 = 0 := Nat.div_eq_of_lt hx
          have hp_add : 2 ^ (128 * (l2 + 1)) = 2 ^ 128 * 2 ^ (128 * l2) := by
            calc
              2 ^ (128 * (l2 + 1)) = 2 ^ (128 * l2 + 128) := by ring
              _ = 2 ^ (128 * l2) * 2 ^ 128 := by rw [pow_add]
              _ = 2 ^ 128 * 2 ^ (128 * l2) := by rw [mul_comm]
          rw [hp_add]
          calc
            (x + packF xs * 2 ^ 128) / (2 ^ 128 * 2 ^ (128 * l2)) % 2 ^ 128
                = ((x + packF xs * 2 ^ 128) / 2 ^ 128 / 2 ^ (128 * l2)) % 2 ^ 128 := by
              rw [Nat.div_div_eq_div_mul]
            _ = ((x / 2 ^ 128 + packF xs) / 2 ^ (128 * l2)) % 2 ^ 128 := by
              rw [Nat.add_mul_div_right _ _ hpos]
            _ = (packF xs / 2 ^ (128 * l2)) % 2 ^ 128 := by rw [hx_div, zero_add]
            _ = xs.getD l2 0 := ih hxs l2
            _ = (x :: xs).getD (l2 + 1) 0 := by simp

theorem ownLam_eq (M : ℕ) (own : List ℕ) (topF : ℕ) :
    ownLam M own topF =
      ((List.range own.length).map fun q => dq q M * own.getD q 0).sum + dq own.length M * topF := by
  have h : ∀ (q0 : ℕ), @List.rec Nat (fun _ => Nat → Nat) (fun q => dq q M * topF)
      (fun s _ ih q => Nat.add (Nat.mul (dq q M) s) (ih (Nat.succ q))) own q0 =
      ((List.range own.length).map fun q => dq (q0 + q) M * own.getD q 0).sum + dq (q0 + own.length) M * topF := by
    intro q0
    induction' own with s rest ih generalizing q0
    · simp
    · simp only [List.length_cons, List.range_succ_eq_map, List.sum_cons, List.map_cons,
        List.getD_cons_zero]
      have hrest := ih (q0 + 1)
      have hmap : (List.map (fun q => dq (q0 + q) M * (s :: rest).getD q 0)
          (List.map Nat.succ (List.range rest.length))).sum =
          ((List.range rest.length).map (fun r => dq ((q0 + 1) + r) M * rest.getD r 0)).sum := by
        rw [List.map_map]
        have h_eq : (fun q => dq (q0 + q) M * (s :: rest).getD q 0) ∘ Nat.succ =
            (fun r => dq ((q0 + 1) + r) M * rest.getD r 0) := by
          ext r
          simp [Function.comp_apply, add_comm, add_left_comm]
        rw [h_eq]
      rw [hmap, hrest]
      have h_add : q0 + 1 + rest.length = q0 + (rest.length + 1) := by omega
      simp [h_add]
      rw [add_assoc]
  simpa [ownLam] using h 0

theorem dq_le (q M : ℕ) : dq q M ≤ DS := by
  rw [dq, nmin2_eq, nmin2_eq]
  by_cases h1 : M ≤ q * DS
  · have hm1 : min (q.succ.mul DS) M = M := by
      apply Nat.min_eq_right
      exact le_trans h1 (Nat.mul_le_mul_right DS (Nat.le_succ q))
    have hm2 : min (q.mul DS) M = M := Nat.min_eq_right h1
    rw [hm1, hm2]
    simp
  · have h_gt : q * DS < M := Nat.lt_of_not_ge h1
    by_cases h2 : M ≤ q.succ * DS
    · have hm1 : min (q.succ.mul DS) M = M := Nat.min_eq_right h2
      have hm2 : min (q.mul DS) M = q * DS := Nat.min_eq_left (Nat.le_of_lt h_gt)
      rw [hm1, hm2]
      have hsub_eq : q.succ * DS - q * DS = DS := by
        have h : q.succ * DS = q * DS + DS := Nat.succ_mul q DS
        rw [h, Nat.add_sub_cancel_left]
      have hle : M - q * DS ≤ q.succ * DS - q * DS := Nat.sub_le_sub_right h2 _
      rw [hsub_eq] at hle
      exact hle
    · have hm1 : min (q.succ.mul DS) M = q.succ * DS := Nat.min_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge h2))
      have hm2 : min (q.mul DS) M = q * DS := Nat.min_eq_left (Nat.le_of_lt h_gt)
      rw [hm1, hm2]
      have hsub_eq : q.succ * DS - q * DS = DS := by
        have h : q.succ * DS = q * DS + DS := Nat.succ_mul q DS
        rw [h, Nat.add_sub_cancel_left]
      simp [hsub_eq]

/-! ## The prefix data (section 5.3) -/

theorem rankCs_eq_aux1 {α β : Type} (h : ℕ → α → β) {d : ℕ} (g : Fin d → α) (k : ℕ) :
    mapIdxFrom h k (List.ofFn g) = List.ofFn fun l : Fin d => h (k + l) (g l) := by
  induction d generalizing k with
  | zero => rfl
  | succ d ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [mapIdxFrom, Fin.val_zero, add_zero, Fin.val_succ]
    rw [ih (fun l => g l.succ) (k + 1)]
    congr 1
    congr 1
    funext l
    rw [Nat.add_assoc, Nat.add_comm 1]

theorem rankCs_eq_aux2 {d : ℕ} (u v : Fin d → ℕ) (a : ℕ) :
    @List.rec (ℕ × ℕ) (fun _ => ℕ → List ℕ) (fun _ => [])
      (fun p _ ih C => rankCs.rankCs3 ih (Nat.add (Nat.sub C p.2) p.1))
      (List.ofFn fun l => (u l, v l)) (a + ∑ l, v l) =
    (List.range d).map fun b => a + ∑ l : Fin d, if (l : ℕ) < b + 1 then u l else v l := by
  induction d generalizing a with
  | zero => rfl
  | succ d ih =>
    rw [List.ofFn_succ]
    have hC : Nat.add (Nat.sub (a + ∑ l, v l) (v 0)) (u 0) = (a + u 0) + ∑ l : Fin d, v l.succ := by
      rw [Fin.sum_univ_succ]
      show a + (v 0 + ∑ l : Fin d, v l.succ) - v 0 + u 0 = _
      omega
    show rankCs.rankCs3 _ (Nat.add (Nat.sub (a + ∑ l, v l) (v 0)) (u 0)) = _
    rw [hC]
    show _ :: _ = _
    rw [ih (fun l => u l.succ) (fun l => v l.succ) (a + u 0), List.range_succ_eq_map, List.map_cons,
      List.map_map]
    congr 1
    · rw [Fin.sum_univ_succ]
      simp [Nat.add_assoc]
    · refine List.map_congr_left fun b _ => ?_
      rw [Function.comp_apply, Fin.sum_univ_succ]
      have h0 : ((0 : Fin (d + 1)) : ℕ) < b.succ + 1 := by simp
      rw [ite_eq_left h0, Nat.add_assoc]
      congr 2
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h : (l : ℕ) < b + 1
      · rw [ite_eq_left h, ite_eq_left (by simp only [Fin.val_succ]; omega)]
      · rw [ite_eq_right h, ite_eq_right (by simp only [Fin.val_succ]; omega)]

theorem rankCs_eq_aux3 {d : ℕ} (w : Fin d → ℕ × ℕ) :
    lfoldr (fun p a => Nat.add p.2 a) 0 (List.ofFn w) = ∑ l, (w l).2 := by
  rw [lfoldr_eq]
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [List.ofFn_succ, List.foldr_cons, Fin.sum_univ_succ, ih (fun l => w l.succ)]
    rfl

/-- The rank sums `C_b = sum over l < b of bs_l[l] + sum over l ≥ b of bs_l[l + 1]`. -/
theorem rankCs_eq {d : ℕ} (f : Fin d → SR) :
    rankCs (List.ofFn f) = (List.range (d + 1)).map fun b =>
      ∑ l : Fin d, if (l : ℕ) < b then (f l).bs.getD l 0 else (f l).bs.getD (l + 1) 0 := by
  have huv : lmapIdx (fun l (r : SR) => (lget r.bs l, lget r.bs (Nat.succ l))) 0 (List.ofFn f) =
      List.ofFn fun l : Fin d => ((f l).bs.getD l 0, (f l).bs.getD (l + 1) 0) := by
    rw [lmapIdx_eq, rankCs_eq_aux1]
    simp only [zero_add, lget_eq]
  show rankCs.rankCs1 _ = _
  rw [huv]
  show rankCs.rankCs2 _ _ = _
  unfold rankCs.rankCs2
  rw [rankCs_eq_aux3, ← zero_add (∑ l : Fin d, _),
    rankCs_eq_aux2 (fun l => (f l).bs.getD l 0) (fun l => (f l).bs.getD (l + 1) 0) 0,
    List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · refine List.map_congr_left fun b _ => ?_
    simp only [Function.comp_apply, zero_add]

/-- `adv` pops the cuts below `i`. -/
theorem adv_eq {β : Type} (i : ℕ) (cuts Cs : List ℕ) (b : ℕ) (k : ℕ → List ℕ → List ℕ → β) :
    adv i cuts Cs b k = k (b + (cuts.takeWhile fun p => decide (p < i)).length)
      (cuts.dropWhile fun p => decide (p < i))
      (Cs.drop (cuts.takeWhile fun p => decide (p < i)).length) := by
  induction cuts generalizing b Cs with
  | nil =>
      simp [adv]
  | cons p ps ih =>
      simp only [adv]
      by_cases hle : i ≤ p
      · -- case i ≤ p
        have hble : Nat.ble i p = true := (Nat.ble_eq.mpr hle)
        have hdec : decide (p < i) = false := by
          rw [decide_eq_false]
          exact Nat.not_lt.mpr hle
        have hneg : ¬ decide (p < i) = true := by
          rw [hdec]
          exact Bool.false_ne_true
        rw [List.takeWhile_cons_of_neg (p := fun p => decide (p < i)) (a := p) (l := ps) hneg,
          List.dropWhile_cons_of_neg (p := fun p => decide (p < i)) (a := p) (l := ps) hneg]
        simp [hble, bsel_true]
      · -- case p < i
        have hlt : p < i := Nat.lt_of_not_ge hle
        have hble : Nat.ble i p = false :=
          Bool.eq_false_of_not_eq_true (mt Nat.ble_eq.mp hle)
        have hdec : decide (p < i) = true := decide_eq_true hlt
        simp only [hble, bsel_false]
        rw [List.takeWhile_cons_of_pos (p := fun p => decide (p < i)) (a := p) (l := ps) hdec,
          List.dropWhile_cons_of_pos (p := fun p => decide (p < i)) (a := p) (l := ps) hdec,
          List.length_cons]
        have hdrop : ∀ n, Cs.drop (n + 1) = (tl Cs).drop n := by
          intro n
          cases Cs with
          | nil => simp [tl_eq]
          | cons a l => simp [tl_eq, List.drop_succ_cons]
        rw [hdrop]
        -- Now the goal is: adv i ps (tl Cs) (b + 1) k = k (b + (len_ps + 1)) (dropWhile ... ps) ((tl Cs).drop len_ps)
        -- But LHS is unfolded. Let's fold it back.
        show adv i ps (tl Cs) (b + 1) k = _
        rw [ih]
        congr 1
        omega

theorem pass_eq_aux1 (a b : ℕ) : Nat.beq a b = (a == b) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  rw [Nat.beq_eq]

theorem pass_eq_aux2 {d : ℕ} (i b : ℕ) (f : Fin d → SR) (l0 : ℕ) (sl : List ℕ) :
    pass i b (List.ofFn f) l0 (F128 ^ l0) sl = PS.mk
      (∑ l : Fin d, sl.getD (if l0 + l < b ∨ b < l0 then l else l + 1) 0 * (f l).ev)
      (∑ l : Fin d, if (f l).fg || (f l).pos == i then 0
        else sl.getD (if l0 + l < b ∨ b < l0 then l else l + 1) 0 * (f l).dl)
      (∑ l : Fin d, if (f l).fg || (f l).pos == i then 0
        else sl.getD (if l0 + l < b ∨ b < l0 then l else l + 1) 0 * F128 ^ (l0 + l))
      (((List.finRange d).filter fun l => !(f l).fg && (f l).pos == i).map
        fun l : Fin d => F128 ^ (l0 + (l : ℕ))) := by
  induction d generalizing l0 sl with
  | zero => rfl
  | succ d ih =>
    rw [List.ofFn_succ]
    show pass.pass1 i (f 0) (F128 ^ l0) (bsel (Nat.beq l0 b) (tl sl) sl)
      (pass i b (List.ofFn fun j => f j.succ) (Nat.succ l0) (Nat.mul (F128 ^ l0) F128)) = _
    have hF : Nat.mul (F128 ^ l0) F128 = F128 ^ (Nat.succ l0) := (pow_succ F128 l0).symm
    rw [hF]
    unfold pass.pass1
    rw [ih]
    unfold passStep3
    have htl : ∀ (s : List ℕ) (j : ℕ), s.tail.getD j 0 = s.getD (j + 1) 0 := by
      intro s j; cases s <;> simp
    have hs0 : hd (bsel (Nat.beq l0 b) (tl sl) sl) =
        sl.getD (if l0 + 0 < b ∨ b < l0 then 0 else 0 + 1) 0 := by
      rw [hd_eq, bsel_eq, pass_eq_aux1]
      by_cases h : l0 = b
      · subst h
        simp [tl_eq]
      · rw [ite_eq_right (by simpa using h), ite_eq_left (by omega)]
        cases sl <;> rfl
    have hsj : ∀ j : ℕ, (tl (bsel (Nat.beq l0 b) (tl sl) sl)).getD
        (if Nat.succ l0 + j < b ∨ b < Nat.succ l0 then j else j + 1) 0 =
        sl.getD (if l0 + (j + 1) < b ∨ b < l0 then j + 1 else j + 1 + 1) 0 := by
      intro j
      rw [bsel_eq, pass_eq_aux1]
      by_cases h : l0 = b
      · subst h
        rw [ite_eq_left (by simp), ite_eq_left (by omega), ite_eq_right (by omega), tl_eq, tl_eq,
          htl, htl]
      · rw [ite_eq_right (by simpa using h), tl_eq, htl]
        by_cases hc : l0 + (j + 1) < b ∨ b < l0
        · rw [ite_eq_left hc, ite_eq_left (by omega)]
        · rw [ite_eq_right hc, ite_eq_right (by omega)]
    have hsel : ∀ (x y : Bool) (X B : ℕ),
        bsel (bsel x true y) X (B + X) = (if (x || y) = true then 0 else B) + X := by
      intro x y X B
      cases x <;> cases y <;> simp [bsel_eq]
    simp only [pass_eq_aux1] at hs0 hsj
    simp only [pass_eq_aux1, hsel, Nat.add_eq, Nat.mul_eq]
    congr 1
    · rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ]
      rw [hs0]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hsj]
    · rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ]
      rw [hs0]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hsj]
    · rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero]
      rw [hs0]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hsj, show Nat.succ l0 + (l : ℕ) = l0 + ((l : ℕ) + 1) by omega]
    · rw [List.finRange_succ, List.filter_cons, List.filter_map]
      cases (f 0).fg <;> cases ((f 0).pos == i) <;> simp [bsel_eq, List.map_map, Function.comp_def, Nat.succ_add, Nat.add_assoc]

/-- The pass of the prefix records over the slopes of `H_i`: the record `l` takes the slope `l` if
`l < b`, `l + 1` otherwise. -/
theorem pass_eq {d : ℕ} (i b : ℕ) (f : Fin d → SR) (sl : List ℕ) :
    pass i b (List.ofFn f) 0 1 sl = PS.mk
      (∑ l : Fin d, sl.getD (if (l : ℕ) < b then l else l + 1) 0 * (f l).ev)
      (∑ l : Fin d, if (f l).fg || (f l).pos == i then 0
        else sl.getD (if (l : ℕ) < b then l else l + 1) 0 * (f l).dl)
      (∑ l : Fin d, if (f l).fg || (f l).pos == i then 0
        else sl.getD (if (l : ℕ) < b then l else l + 1) 0 * F128 ^ (l : ℕ))
      (((List.finRange d).filter fun l => !(f l).fg && (f l).pos == i).map
        fun l => F128 ^ (l : ℕ)) := by
  have h := pass_eq_aux2 i b f 0 sl
  rw [pow_zero] at h
  rw [h]
  simp only [zero_add, Nat.not_lt_zero, or_false]
  congr 1
  simp only [List.bind_eq_flatMap, List.pure_def]
  rw [show ∀ L : List (Fin d), List.flatMap (fun a : Fin d => [(a : ℕ)]) L = L.map Fin.val from
    fun L => by induction L <;> simp_all, List.map_map]
  rfl

/-- The rank of `H_i`. -/
theorem rank_Hc (g : Grid) {d : ℕ} (t : ℕ) (c : Fin (d + 1) → Rec) (i : ℕ) :
    rank (Hc g d t c i) =
      (∑ l : Fin d, if (l : ℕ) < below d c i then ((c l.castSucc).map + l).choose (l + 1)
        else ((c l.castSucc).map + l + 1).choose (l + 2)) +
      (g.nxt t i + below d c i).choose (below d c i + 1) := by
  unfold rank
  rw [Fin.sum_univ_succAbove (fun l : Fin (d + 1) => (Hc g d t c i l + (l : ℕ)).choose ((l : ℕ) + 1))
    (belowF d c i)]
  have hp : ((belowF d c i : Fin (d + 1)) : ℕ) = below d c i := rfl
  have hHc_p : Hc g d t c i (belowF d c i) = g.nxt t i := by
    unfold Hc
    simp [hp]
  rw [hHc_p, hp, add_comm]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  by_cases hl : (l : ℕ) < below d c i
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; exact hl), ite_eq_left hl]
    simp only [Hc, Fin.val_castSucc, ite_eq_left hl]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp only [Fin.val_castSucc]; omega),
      ite_eq_right hl]
    have h1 : ¬ ((l.succ : Fin (d + 1)) : ℕ) < below d c i := by simp only [Fin.val_succ]; omega
    have h2 : ¬ ((l.succ : Fin (d + 1)) : ℕ) = below d c i := by simp only [Fin.val_succ]; omega
    have hv : Hc g d t c i l.succ = (c l.castSucc).map := by
      unfold Hc
      rw [ite_eq_right h1, ite_eq_right h2]
      congr 2
    rw [hv, Fin.val_succ, ← add_assoc]

/-! ## The cells of the last record (section 5.3) and the check (section 5.5) -/

/-- One cell `i ≤ im` of `topLoop`: `R` gains `cell2`, `acc` the chord times the packed
coefficients (when `S > 0`), `lam` the own-cell credits (when `A1 ≤ beta`). -/
theorem topCell_eq (a1 : ℕ) (tp : Tp) (pd : PD) (isTop : Bool) (beta : ℕ) (A : Acc)
    (hab : pd.pa ≤ pd.pb) (ha1 : 0 < a1) (hh : pd.h = pd.pb - pd.pa)
    (hh2 : pd.h2 = 2 * (pd.pb - pd.pa)) (hA0 : pd.A0 = pd.a0 + (a1 + pd.sig) * pd.pa)
    (hA1 : pd.A1 = pd.a0 + (a1 + pd.sig) * pd.pb)
    (hIA : pd.IA = pd.h2 * pd.a0 + a1 * (pd.pb * pd.pb - pd.pa * pd.pa))
    (hssq : pd.ssq = pd.sig * (pd.pb * pd.pb - pd.pa * pd.pa)) (hown : pd.hasOwn = !pd.own.isEmpty) :
    ((topCell a1 tp pd isTop beta A).rp : ℤ) - (topCell a1 tp pd isTop beta A).rn =
        (A.rp : ℤ) - A.rn + SO.cell2 pd.pa pd.pb pd.a0 a1 beta pd.sig ∧
      (topCell a1 tp pd isTop beta A).ac = A.ac +
        (if (if isTop then pd.sp else pd.sp + tp.PmW) = 0 then 0
          else chord pd.pa pd.pb pd.a0 a1 beta pd.sig (if isTop then pd.sp else pd.sp + tp.PmW)) *
          (if isTop then pd.cp else pd.cp + tp.PmF) ∧
      (topCell a1 tp pd isTop beta A).lm = A.lm +
        if pd.A1 ≤ beta then ownLam ((beta - pd.A1) / DS) pd.own (if isTop then tp.topF else 0)
        else 0 := by
  obtain ⟨S, hS⟩ : ∃ S, S = (if isTop then pd.sp else pd.sp + tp.PmW) := ⟨_, rfl⟩
  obtain ⟨cP, hcP⟩ : ∃ cP, cP = (if isTop then pd.cp else pd.cp + tp.PmF) := ⟨_, rfl⟩
  have hS' : bsel isTop pd.sp (Nat.add pd.sp tp.PmW) = S := by rw [hS, bsel_eq]; rfl
  have hcP' : bsel isTop pd.cp (Nat.add pd.cp tp.PmF) = cP := by rw [hcP, bsel_eq]; rfl
  rw [← hS, ← hcP]
  have hpp : pd.pa * pd.pa ≤ pd.pb * pd.pb := Nat.mul_le_mul hab hab
  have hA1z : (pd.A1 : ℤ) = pd.a0 + ((a1 : ℤ) + pd.sig) * pd.pb := by rw [hA1]; push_cast; ring
  have hA0z : (pd.A0 : ℤ) = pd.a0 + ((a1 : ℤ) + pd.sig) * pd.pa := by rw [hA0]; push_cast; ring
  have hdb : (pd.a0 : ℤ) - beta + ((a1 : ℤ) + pd.sig) * pd.pa +
      ((a1 : ℤ) + pd.sig) * ((pd.pb : ℤ) - pd.pa) = (pd.A1 : ℤ) - beta := by rw [hA1z]; ring
  have hda : (pd.a0 : ℤ) - beta + ((a1 : ℤ) + pd.sig) * pd.pa = (pd.A0 : ℤ) - beta := by
    rw [hA0z]; ring
  -- the kernel chord in its first two cases
  have hch1 : Nat.add pd.a0 (Nat.mul (Nat.add a1 pd.sig) pd.pb) = pd.A1 := by rw [hA1]; rfl
  have hch0 : Nat.add pd.a0 (Nat.mul (Nat.add a1 pd.sig) pd.pa) = pd.A0 := by rw [hA0]; rfl
  have hchord : chord pd.pa pd.pb pd.a0 a1 beta pd.sig S =
      chord.chord1 pd.pa pd.pb beta S (Nat.add a1 pd.sig) pd.A0 pd.A1 := by
    unfold chord
    rw [hch1, hch0]
  unfold topCell
  rw [hS', hcP', bsel_eq]
  by_cases hAB : pd.A1 ≤ beta
  · rw [ite_eq_left (by rw [Nat.ble_eq]; exact hAB)]
    unfold tcStop
    refine ⟨?_, ?_, ?_⟩
    · show (((A.rp + pd.IA : ℕ)) : ℤ) - A.rn = _
      unfold SO.cell2
      simp only
      rw [ite_eq_left (by rw [hdb]; omega), hIA, hh2]
      push_cast [Nat.cast_sub hab, Nat.cast_sub hpp]
      ring
    · show A.ac = A.ac + _
      have hc0 : chord pd.pa pd.pb pd.a0 a1 beta pd.sig S = 0 := by
        rw [hchord]
        unfold chord.chord1
        rw [bsel_eq, ite_eq_left (by rw [Nat.ble_eq]; exact hAB)]
      rw [hc0, ite_self, zero_mul, add_zero]
    · show bsel (bsel isTop true pd.hasOwn) _ A.lm = _
      rw [ite_eq_left hAB]
      cases isTop
      · rw [bsel_false, bsel_false]
        rcases hl : pd.own with _ | ⟨x, xs⟩
        · rw [hl] at hown
          rw [hown]
          simp [ownLam_eq]
        · rw [hl] at hown
          rw [hown]
          rfl
      · rfl
  · rw [ite_eq_right (by rw [Nat.ble_eq]; exact hAB)]
    have hq : qCont a1 pd beta S = chord pd.pa pd.pb pd.a0 a1 beta pd.sig S := by
      unfold qCont
      rw [hchord, bsel_eq]
      by_cases h : beta + S ≤ pd.A0
      · rw [ite_eq_left (by rw [Nat.ble_eq]; exact h)]
        unfold chord.chord1
        rw [bsel_eq (Nat.ble pd.A1 beta), ite_eq_right (by rw [Nat.ble_eq]; exact hAB), bsel_eq,
          ite_eq_left (by rw [Nat.ble_eq]; exact h), hh]
        rfl
      · rw [ite_eq_right (by rw [Nat.ble_eq]; exact h)]
    have hacc : accAdd a1 pd beta S cP A.ac =
        A.ac + (if S = 0 then 0 else chord pd.pa pd.pb pd.a0 a1 beta pd.sig S) * cP := by
      unfold accAdd
      rw [bsel_eq, hq]
      by_cases hS0 : S = 0
      · rw [ite_eq_left (by rw [Nat.beq_eq]; exact hS0), ite_eq_left hS0]
        simp
      · rw [ite_eq_right (by rw [Nat.beq_eq]; exact hS0), ite_eq_right hS0]
        rfl
    unfold topCell.tcRest
    rw [bsel_eq]
    by_cases hB0 : beta ≤ pd.A0
    · rw [ite_eq_left (by rw [Nat.ble_eq]; exact hB0)]
      refine ⟨?_, hacc, ?_⟩
      · show (((A.rp + pd.h2 * beta : ℕ)) : ℤ) - ((A.rn + pd.ssq : ℕ) : ℤ) = _
        unfold SO.cell2
        simp only
        rw [ite_eq_right (by rw [hdb]; omega), ite_eq_left (by rw [hda]; omega), hh2, hssq]
        push_cast [Nat.cast_sub hab, Nat.cast_sub hpp]
        ring
      · show A.lm = _
        rw [ite_eq_right hAB, add_zero]
    · rw [ite_eq_right (by rw [Nat.ble_eq]; exact hB0)]
      unfold topCell.tcCross
      refine ⟨?_, hacc, ?_⟩
      · exact cell2_eq _ _ _ _ _ _ _ _ hab ha1
      · show A.lm = _
        rw [ite_eq_right hAB, add_zero]

theorem lamSum_eq_aux1 {k : ℕ} (p : Fin (k + 1) → Bool) (l : Fin k) :
    (Finset.univ.filter fun l' : Fin (k + 1) => l' < l.succ ∧ p l' = true).card =
      (if p 0 = true then 1 else 0) +
        (Finset.univ.filter fun l' : Fin k => l' < l ∧ p l'.succ = true).card := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  congr 1
  · simp [Fin.succ_pos]
  · refine Finset.sum_congr rfl fun l' _ => ?_
    simp only [Fin.succ_lt_succ_iff]

theorem lamSum_eq_aux2 (g : ℕ → ℕ) (B : ℕ) (d : ℕ) (p : Fin (d + 1) → Bool) (c0 e : ℕ) :
    ∑ l : Fin (d + 1),
        (if p l then g (c0 + (Finset.univ.filter fun l' => l' < l ∧ p l' = true).card) else 0) *
          B ^ (e + l) =
      @List.rec ℕ (fun _ => ℕ → ℕ) (fun q => Nat.mul (g q) (if p (Fin.last d) then B ^ (e + d) else 0))
        (fun s _ ih q => Nat.add (Nat.mul (g q) s) (ih (Nat.succ q)))
        (((List.finRange d).filter fun l => p l.castSucc).map fun l : Fin d => B ^ (e + (l : ℕ))) c0 := by
  induction d generalizing c0 e with
  | zero =>
    rw [Fin.sum_univ_one]
    have h0 : (Finset.univ.filter fun l' : Fin 1 => l' < 0 ∧ p l' = true).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _ h
      exact absurd h.1 (by simp)
    rw [h0, Nat.add_zero]
    show _ = Nat.mul (g c0) (if p (Fin.last 0) then B ^ (e + 0) else 0)
    have hl : Fin.last 0 = 0 := rfl
    rw [hl]
    cases p 0 <;> simp
  | succ d ih =>
    have hc : ∀ l : Fin (d + 1),
        (if p l.succ then g (c0 + (Finset.univ.filter fun l' => l' < l.succ ∧ p l' = true).card)
          else 0) * B ^ (e + (l.succ : ℕ)) =
        (if (fun l => p l.succ) l then g ((c0 + if p 0 = true then 1 else 0) +
          (Finset.univ.filter fun l' => l' < l ∧ (fun l => p l.succ) l' = true).card) else 0) *
          B ^ ((e + 1) + l) := by
      intro l
      rw [lamSum_eq_aux1 p l, Fin.val_succ, Nat.add_assoc c0,
        show e + ((l : ℕ) + 1) = e + 1 + l by omega]
    rw [Fin.sum_univ_succ, Finset.sum_congr rfl fun l _ => hc l, ih (fun l => p l.succ)]
    have hL : (((List.finRange d).map Fin.succ).filter fun l => p l.castSucc).map
          (fun l : Fin (d + 1) => B ^ (e + (l : ℕ))) =
        ((List.finRange d).filter fun l => (fun l => p l.succ) l.castSucc).map
          fun l : Fin d => B ^ (e + 1 + (l : ℕ)) := by
      rw [List.filter_map, List.map_map]
      have h1 : ((fun l : Fin (d + 1) => B ^ (e + (l : ℕ))) ∘ Fin.succ) =
          fun l : Fin d => B ^ (e + 1 + (l : ℕ)) := by
        funext l
        simp only [Function.comp_apply, Fin.val_succ]
        rw [show e + ((l : ℕ) + 1) = e + 1 + l by omega]
      have h2 : ((fun l : Fin (d + 1) => p l.castSucc) ∘ Fin.succ) =
          fun l : Fin d => (fun l => p l.succ) l.castSucc := by
        funext l
        simp only [Function.comp_apply, Fin.succ_castSucc]
      rw [h1, h2]
    have hT : (if p (Fin.last (d + 1)) then B ^ (e + (d + 1)) else 0) =
        (if (fun l => p l.succ) (Fin.last d) then B ^ (e + 1 + d) else 0) := by
      rw [← Fin.succ_last, show e + (d + 1) = e + 1 + d by omega]
    rw [List.finRange_succ, List.filter_cons, Fin.castSucc_zero, hT]
    have h00 : (Finset.univ.filter fun l' : Fin (d + 2) => l' < 0 ∧ p l' = true).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _ h
      exact absurd h.1 (by simp)
    rw [h00]
    simp only [Fin.val_zero, Nat.add_zero]
    by_cases h0 : p 0 = true
    · simp only [h0, ite_true, List.map_cons]
      rw [hL]
      rfl
    · simp only [h0, ite_false, Bool.false_eq_true, zero_mul, zero_add, Nat.add_zero]
      rw [hL]

/-- The own-cell credits of one cell as `ownLam`: the record `l` with `p l` gets
`dq q M F ^ l`, `q` the number of the earlier records with `p`. -/
theorem lamSum_eq {d : ℕ} (p : Fin (d + 1) → Bool) (M : ℕ) :
    ∑ l : Fin (d + 1),
        (if p l then dq (Finset.univ.filter fun l' => l' < l ∧ p l' = true).card M else 0) *
          F128 ^ (l : ℕ) =
      ownLam M (((List.finRange d).filter fun l => p l.castSucc).map fun l => F128 ^ (l : ℕ))
        (if p (Fin.last d) then F128 ^ d else 0) := by
  have h := lamSum_eq_aux2 (fun q => dq q M) F128 d p 0 0
  simp only [zero_add] at h
  rw [h]
  unfold ownLam
  simp only [List.bind_eq_flatMap, List.pure_def]
  rw [show ∀ L : List (Fin d), List.flatMap (fun a : Fin d => [(a : ℕ)]) L = L.map Fin.val from
    fun L => by induction L <;> simp_all, List.map_map]
  rfl

/-- The packed list `sum over l of x_l F ^ l`. -/
theorem packF_eq (m : ℕ) (f : ℕ → ℕ) :
    packF ((List.range m).map f) = ∑ l ∈ Finset.range m, f l * F128 ^ l := by
  induction m generalizing f with
  | zero => simp [packF, lfoldr_eq]
  | succ m ih =>
    have hcons : packF ((List.range (m + 1)).map f) =
        f 0 + packF ((List.range m).map fun l => f (l + 1)) * F128 := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      unfold packF
      rw [lfoldr_eq, lfoldr_eq, List.foldr_cons]
      rfl
    rw [hcons, ih, Finset.sum_range_succ', Finset.sum_mul]
    rw [pow_zero, mul_one, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [pow_succ, Nat.mul_assoc]

theorem muOK_sound_aux1 : F128 = 2 ^ 128 := by
  unfold F128
  norm_num

theorem muOK_sound_aux2 : M128 = 2 ^ 128 - 1 := by
  unfold M128
  norm_num

theorem muOK_sound_aux3 {m : ℕ} (x : Fin (m + 1) → ℕ) (hx : ∀ l, x l < F128) :
    Nat.land (∑ l, x l * F128 ^ (l : ℕ)) M128 = x 0 ∧
      Nat.shiftRight (∑ l, x l * F128 ^ (l : ℕ)) 128 = ∑ l : Fin m, x l.succ * F128 ^ (l : ℕ) := by
  have hs : ∑ l, x l * F128 ^ (l : ℕ) = x 0 + F128 * ∑ l : Fin m, x l.succ * F128 ^ (l : ℕ) := by
    rw [Fin.sum_univ_succ, Finset.mul_sum, Fin.val_zero, pow_zero, Nat.mul_one]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Fin.val_succ, pow_succ]
    ring
  have h0 : x 0 < F128 := hx 0
  rw [hs]
  generalize ∑ l : Fin m, x l.succ * F128 ^ (l : ℕ) = R
  rw [muOK_sound_aux1] at h0 ⊢
  constructor
  · show (x 0 + 2 ^ 128 * R) &&& M128 = x 0
    rw [muOK_sound_aux2, Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt h0]
  · show (x 0 + 2 ^ 128 * R) >>> 128 = R
    rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt h0, zero_add]

/-- A passed `muOK` on packed accumulators with fields below `F`: `sg_l ≤ lam_l + acc_l / D`
(`0` for a forgotten record). -/
theorem muOK_sound {m : ℕ} (f : Fin m → SR) (sg : List ℕ) (a b : Fin m → ℕ)
    (ha : ∀ l, a l < F128) (hb : ∀ l, b l < F128)
    (h : muOK (List.ofFn f) sg (∑ l, a l * F128 ^ (l : ℕ)) (∑ l, b l * F128 ^ (l : ℕ)) = true) :
    ∀ l : Fin m, sg.getD l 0 ≤ if (f l).fg then 0 else b l + a l / DS := by
  induction m generalizing sg with
  | zero => intro l; exact l.elim0
  | succ m ih =>
    obtain ⟨ha0, ha1⟩ := muOK_sound_aux3 a ha
    obtain ⟨hb0, hb1⟩ := muOK_sound_aux3 b hb
    rw [List.ofFn_succ] at h
    cases sg with
    | nil => exact absurd h Bool.false_ne_true
    | cons s sg' =>
      change bsel (Nat.ble s (bsel (f 0).fg 0 (Nat.add (Nat.land (∑ l, b l * F128 ^ (l : ℕ)) M128)
          (Nat.div (Nat.land (∑ l, a l * F128 ^ (l : ℕ)) M128) DS))))
        (muOK (List.ofFn fun i => f i.succ) sg' (Nat.shiftRight (∑ l, a l * F128 ^ (l : ℕ)) 128)
          (Nat.shiftRight (∑ l, b l * F128 ^ (l : ℕ)) 128)) false = true at h
      rw [ha0, hb0, ha1, hb1, bsel_eq] at h
      split_ifs at h with h0
      have ih' := ih (fun i => f i.succ) sg' (fun i => a i.succ) (fun i => b i.succ)
        (fun i => ha _) (fun i => hb _) h
      intro l
      refine Fin.cases ?_ (fun l => ?_) l
      · have h0' := Nat.ble_eq.mp h0
        rw [bsel_eq] at h0'
        rw [Fin.val_zero, List.getD_cons_zero]
        exact h0'
      · rw [Fin.val_succ, List.getD_cons_succ]
        exact ih' l

/-- The last rank sum `C_{m-1} = sum over l of bs_l[l]`. -/
theorem llast_rankCs {d : ℕ} (f : Fin d → SR) :
    llast 0 (rankCs (List.ofFn f)) = ∑ l : Fin d, (f l).bs.getD l 0 := by
  rw [llast_eq 0]
  rw [rankCs_eq f]
  rw [List.getLastD_eq_getLast?, List.getLast?_map, List.getLast?_range]
  simp

/-- `Σ x_l y_l` of two lists of the same length. -/
theorem dot_ofFn {m : ℕ} (a b : Fin m → ℕ) : dot (List.ofFn a) (List.ofFn b) = ∑ l, a l * b l := by
  rw [dot_eq]
  induction' m with m ih
  · simp
  · rw [List.ofFn_succ, List.ofFn_succ]
    simp [List.zipWith_cons_cons, List.sum_cons, Fin.sum_univ_succ, ih]

/-- `dq` over the integers. -/
theorem dq_cast (q M : ℕ) :
    ((dq q M : ℕ) : ℤ) = min (((q + 1) * DS : ℕ) : ℤ) (M : ℤ) - min ((q * DS : ℕ) : ℤ) (M : ℤ) := by
  have hle : min (q * DS) M ≤ min ((q + 1) * DS) M := by
    apply min_le_min_right M
    apply Nat.mul_le_mul_right DS
    omega
  dsimp [dq]
  rw [nmin2_eq, nmin2_eq]
  rw [Nat.cast_sub hle]
  simp [Nat.cast_min]

/-! ## Bounds of the specification -/

/-- `E_{n-k} (z) (D + k) ≤ D ^ 2` for `1 ≤ z ≤ D`. -/
theorem Epen_mul_le (D z k : ℕ) (hz : 1 ≤ z) (hzD : z ≤ D) : SO.Epen D z k * (D + k) ≤ D * D := by
  induction' k with k IH
  · simp [SO.Epen]
  · have hDpos : 0 < D := by
      have h1D : 1 ≤ D := le_trans hz hzD
      exact Nat.lt_of_lt_of_le (by decide : 0 < 1) h1D
    set E := SO.Epen D z k with hE
    rw [SO.Epen]
    -- Goal: (E * (D - z) / D) * (D + k + 1) ≤ D * D
    have h_ineq : (D - z) * (D + k + 1) ≤ D * (D + k) := by
      have hz' : (1 : ℤ) ≤ (z : ℤ) := by exact_mod_cast hz
      have hzD' : (z : ℤ) ≤ (D : ℤ) := by exact_mod_cast hzD
      have hineq : ((D : ℤ) - (z : ℤ)) * ((D : ℤ) + (k : ℤ) + 1) ≤ (D : ℤ) * ((D : ℤ) + (k : ℤ)) := by
        nlinarith
      exact_mod_cast hineq
    have h_mul : E * (D - z) * (D + k + 1) ≤ E * D * (D + k) := by
      have htemp := Nat.mul_le_mul_left E h_ineq
      simpa [mul_assoc] using htemp
    have h_total : (E * (D - z) / D) * (D + k + 1) * D ≤ D * D * D := by
      calc
        (E * (D - z) / D) * (D + k + 1) * D = ((E * (D - z) / D) * D) * (D + k + 1) := by ring
        _ ≤ (E * (D - z)) * (D + k + 1) := by
          apply Nat.mul_le_mul_right (D + k + 1)
          exact Nat.div_mul_le_self (E * (D - z)) D
        _ = E * (D - z) * (D + k + 1) := rfl
        _ ≤ E * D * (D + k) := h_mul
        _ = D * (E * (D + k)) := by ring
        _ ≤ D * (D * D) := Nat.mul_le_mul_left D IH
        _ = D * D * D := by ring
    apply Nat.le_of_mul_le_mul_right h_total hDpos

/-- The chord of the specification is nonnegative on a cell. -/
theorem so_chord_nonneg {Pa Pb a0 a1 b0 b1 S : ℤ} (hab : Pa ≤ Pb) (hS : 0 < S) :
    0 ≤ SO.chord Pa Pb a0 a1 b0 b1 S := by
  simp only [SO.chord]
  split_ifs
  · rfl
  · exact sub_nonneg.mpr hab
  · next hnum =>
    exact Int.ediv_nonneg (by omega) (by omega)
  · rfl

/-- Telescoping over `(a, b]`. -/
theorem sum_Ioc_sub (f : ℕ → ℤ) {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ Finset.Ioc a b, (f i - f (i - 1)) = f b - f a := by
  refine Nat.le_induction ?base ?step b hab
  · -- base: b = a
    simp
  · -- step: assume for m, prove for m+1
    intro m hm hIH
    rw [Finset.sum_Ioc_succ_top hm (fun i => f i - f (i - 1))]
    rw [hIH]
    have hsub : (m + 1 : ℕ) - 1 = m := by omega
    rw [hsub]
    ring

/-- The coefficients are nonnegative. -/
theorem coefC_nonneg (D : ℕ) (g : Grid) (d : ℕ) (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ)
    (t : ℕ) (c : Fin (d + 1) → Rec) (i : ℕ) (l : Fin (d + 1)) : 0 ≤ coefC D g d Sg t c i l := by
  unfold coefC
  split
  · split
    · rfl
    · exact Nat.cast_nonneg _
  · dsimp
    split
    · rfl
    · split
      · exact Nat.cast_nonneg _
      · split
        · rfl
        · exact Nat.cast_nonneg _

/-- The own-cell credits are nonnegative. -/
theorem lamC_nonneg (D : ℕ) (g : Grid) (d : ℕ) (N : (Fin (d + 1) → ℕ) → ℕ)
    (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) (t : ℕ) (c : Fin (d + 1) → Rec) (i : ℕ)
    (l : Fin (d + 1)) : 0 ≤ lamC D g d N Sg t c i l := by
  dsimp [lamC]
  split
  · apply sub_nonneg.mpr
    refine min_le_min_right (MC D g d N Sg t c i) ?_
    have hcard : (Finset.univ.filter fun l' : Fin (d + 1) => l' < l ∧ (c l').pos = i ∧ (c l').forg = false).card ≤
        (Finset.univ.filter fun l' : Fin (d + 1) => l' < l ∧ (c l').pos = i ∧ (c l').forg = false).card + 1 := by omega
    have hcard' : ((Finset.univ.filter fun l' : Fin (d + 1) => l' < l ∧ (c l').pos = i ∧ (c l').forg = false).card : ℤ) ≤
        ((Finset.univ.filter fun l' : Fin (d + 1) => l' < l ∧ (c l').pos = i ∧ (c l').forg = false).card : ℤ) + 1 := by
      exact_mod_cast hcard
    have hD : (0 : ℤ) ≤ (D : ℤ) := Nat.cast_nonneg _
    nlinarith
  · exact le_refl (0 : ℤ)

/-- An own-cell credit is at most `D`. -/
theorem lamC_le (D : ℕ) (g : Grid) (d : ℕ) (N : (Fin (d + 1) → ℕ) → ℕ)
    (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) (t : ℕ) (c : Fin (d + 1) → Rec) (i : ℕ)
    (l : Fin (d + 1)) : lamC D g d N Sg t c i l ≤ D := by
  unfold lamC
  split
  · rename_i h
    dsimp
    set q := (Finset.univ.filter fun l' : Fin (d + 1) => l' < l ∧ (c l').pos = i ∧ (c l').forg = false).card with hq
    set M := MC D g d N Sg t c i with hM
    by_cases hMle : M ≤ (q : ℤ) * (D : ℤ)
    · have hmin1 : min ((q : ℤ) * (D : ℤ)) M = M := min_eq_right hMle
      have hmin2 : min (((q : ℤ) + 1) * (D : ℤ)) M = M := by
        apply min_eq_right
        have hineq : (q : ℤ) * (D : ℤ) ≤ ((q : ℤ) + 1) * (D : ℤ) := by
          nlinarith
        linarith
      rw [hmin1, hmin2, sub_self]
      exact Nat.cast_nonneg _
    · have hlt : (q : ℤ) * (D : ℤ) < M := lt_of_not_ge hMle
      by_cases hMle2 : M ≤ ((q : ℤ) + 1) * (D : ℤ)
      · have hmin1 : min ((q : ℤ) * (D : ℤ)) M = (q : ℤ) * (D : ℤ) := min_eq_left (by linarith)
        have hmin2 : min (((q : ℤ) + 1) * (D : ℤ)) M = M := min_eq_right hMle2
        rw [hmin1, hmin2]
        linarith
      · have hlt2 : ((q : ℤ) + 1) * (D : ℤ) < M := lt_of_not_ge hMle2
        have hmin1 : min ((q : ℤ) * (D : ℤ)) M = (q : ℤ) * (D : ℤ) := min_eq_left (by linarith)
        have hmin2 : min (((q : ℤ) + 1) * (D : ℤ)) M = ((q : ℤ) + 1) * (D : ℤ) := min_eq_left (by linarith)
        rw [hmin1, hmin2]
        ring_nf
        exact le_rfl
  · exact Nat.cast_nonneg _

/-- `lam_l ≤ D`: only the cell `pos_l` credits the record `l`. -/
theorem lam_le_D (D : ℕ) (g : Grid) (d : ℕ) (N : (Fin (d + 1) → ℕ) → ℕ)
    (Sg : (Fin (d + 1) → ℕ) → Fin (d + 1) → ℕ) (t : ℕ) (c : Fin (d + 1) → Rec)
    (l : Fin (d + 1)) : lam D g d N Sg t c l ≤ D := by
  unfold lam
  have hsum : (∑ i ∈ Finset.Icc 1 (im d c), lamC D g d N Sg t c i l) =
             (∑ i ∈ Finset.Icc 1 (im d c), if (c l).pos = i then lamC D g d N Sg t c i l else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    unfold lamC
    by_cases hpos : (c l).pos = i
    · simp [hpos]
    · simp [hpos]
  rw [hsum]
  rw [Finset.sum_ite_eq]
  split
  · exact lamC_le D g d N Sg t c ((c l).pos) l
  · exact Nat.cast_nonneg D

end Robbins.Cert.SO.K
