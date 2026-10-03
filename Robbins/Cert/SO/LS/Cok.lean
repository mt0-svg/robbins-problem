import Robbins.Cert.SO.LS.Vec
import Robbins.Cert.SO.LS.Kc

/-!
# The lanes step: the scalar conditions of a step, unpacked

`ctxOK` as propositions (`COK`), and list facts the step uses (`rget`, `mapIdxFrom`, the decoded
states of a table).
-/

namespace Robbins.Cert.SO.L

open Robbins.Cert Robbins.Cert.K Robbins.Cert.SO.K Robbins.Lanes

/-- The conditions of `ctxOK`. -/
structure COK (c : Ctx) : Prop where
  m2 : 2 ≤ c.m
  m32 : c.m ≤ 32
  newp : c.newp = []
  rcs : ∀ r ∈ c.recs, r.ev = 0 ∧ r.dl ≤ DS ∧ r.em ≤ DS ∧ r.etm ≤ DS ∧ r.val ≤ DS ∧
    r.pm ≤ 1024 * DS ∧ r.bsl ≤ B32 ∧ ∀ b ∈ r.bs, b ≤ B32
  pos : ∀ k (h : k < c.recs.length), c.recs[k].pos = k + 1
  r : c.r ≤ 1023
  len : c.cells.length = c.recs.length
  len4096 : c.recs.length ≤ 4096
  cell : ∀ cl ∈ c.cells, cl.pa ≤ cl.pb ∧ cl.pb ≤ DS ∧ cl.et ≤ DS ∧ cl.e1 ≤ DS ∧ cl.etm ≤ DS ∧
    cl.pn ≤ DS ∧ cl.h ≤ DS ∧ cl.h2 ≤ DS + DS ∧ cl.sqd ≤ DS2 ∧ cl.a1sq ≤ 1024 * (DS * DS2) ∧
    ∀ b ∈ cl.cb, b ≤ B32

theorem bsel_false (a b : Bool) : bsel a b false = (a && b) := by
  cases a <;> rfl

theorem posEq_iff (l : List SR) (p : ℕ) :
    ctxOK.posEq l p = true ↔ ∀ k (h : k < l.length), l[k].pos = p + k + 1 := by
  induction l generalizing p with
  | nil => simp [ctxOK.posEq]
  | cons r l ih =>
    show bsel (Nat.beq r.pos (Nat.succ p)) (ctxOK.posEq l (Nat.succ p)) false = true ↔ _
    rw [bsel_false, Bool.and_eq_true, Nat.beq_eq, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases k with _ | k
      · simpa using h1
      · have := h2 k (by simpa using hk)
        simp only [List.getElem_cons_succ]
        rw [this]
        omega
    · intro h
      have h0 := h 0 (by simp)
      simp only [List.getElem_cons_zero] at h0
      refine ⟨by omega, fun k hk => ?_⟩
      have := h (k + 1) (by simpa using hk)
      simp only [List.getElem_cons_succ] at this
      rw [this]
      omega

theorem cok_of_ctxOK (c : Ctx) (h : ctxOK c = true) : COK c := by
  unfold ctxOK ctxOK.cellOK at h
  simp only [bsel_false, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, lall_iff, posEq_iff] at h
  obtain ⟨⟨hm2, hm32⟩, hnp, hrec, hpos, ⟨⟨hr, hlen, h4096⟩, hcell⟩⟩ := h
  refine ⟨hm2, hm32, ?_, ?_, fun k hk => by simpa using hpos k hk, hr, hlen, h4096, ?_⟩
  · cases hc : c.newp with
    | nil => rfl
    | cons a l => rw [hc] at hnp; exact absurd hnp Bool.false_ne_true
  · intro r hr
    have := hrec r hr
    exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1,
      this.2.2.2.2.2.2.1, fun b hb => this.2.2.2.2.2.2.2 b hb⟩
  · intro cl hcl
    have := hcell cl hcl
    exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1,
      this.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.2.1,
      fun b hb => this.2.2.2.2.2.2.2.2.2.2 b hb⟩

/-! ## Lists -/

/-- The dummy record. -/
abbrev SR0 : SR := SR.mk 0 0 0 0 true 0 0 0 0 [] 0

theorem rget_eq (l : List SR) (k : ℕ) : rget l k = l.getD k SR0 := by
  unfold rget
  rw [ldrop_eq]
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    rcases k with _ | k
    · rfl
    · simpa using ih k

theorem rget_of_lt (l : List SR) (k : ℕ) (h : k < l.length) : rget l k = l[k] := by
  rw [rget_eq, List.getD_eq_getElem _ _ h]

theorem cget_of_lt (l : List CV) (k : ℕ) (h : k < l.length) : cget l k = l[k] := by
  unfold cget
  rw [ldrop_eq]
  induction l generalizing k with
  | nil => simp at h
  | cons a l ih =>
    rcases k with _ | k
    · rfl
    · simpa using ih k (by simpa using h)

theorem mapIdxFrom_length {α β : Type} (f : ℕ → α → β) (k : ℕ) (l : List α) :
    (mapIdxFrom f k l).length = l.length := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih => simp [mapIdxFrom, ih]

theorem mapIdxFrom_getElem {α β : Type} (f : ℕ → α → β) (k : ℕ) (l : List α) (i : ℕ)
    (hi : i < (mapIdxFrom f k l).length) :
    (mapIdxFrom f k l)[i] = f (k + i) (l[i]'(by rwa [mapIdxFrom_length] at hi)) := by
  induction l generalizing k i with
  | nil => simp [mapIdxFrom] at hi
  | cons a l ih =>
    rcases i with _ | i
    · rfl
    · simp only [mapIdxFrom, List.getElem_cons_succ]
      rw [ih]
      congr 1
      omega

theorem lmapIdx_length {α β : Type} (f : ℕ → α → β) (k : ℕ) (l : List α) :
    (lmapIdx f k l).length = l.length := by
  rw [lmapIdx_eq, mapIdxFrom_length]

theorem lmapIdx_getElem {α β : Type} (f : ℕ → α → β) (k : ℕ) (l : List α) (i : ℕ)
    (hi : i < (lmapIdx f k l).length) :
    (lmapIdx f k l)[i] = f (k + i) (l[i]'(by rwa [lmapIdx_length] at hi)) := by
  simp only [lmapIdx_eq]
  exact mapIdxFrom_getElem f k l i _

/-! ## Decoded states -/

theorem decLit_lt (W x : ℕ) (hW : 0 < W) (rest : List ℕ) (v : ℕ) (hv : v ∈ decLit W (2 ^ W - 1) x rest) :
    v ∈ rest ∨ v < 2 ^ W := by
  have e := chunkCheck_lall2_aux2 W (2 ^ W - 1) x [] rest
  simp only [List.nil_append] at e
  rw [e, List.mem_append] at hv
  rcases hv with hv | hv
  · right
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    have h0 := decLit_getD W x i hW hi
    rw [List.getD_eq_getElem _ _ hi] at h0
    rw [h0]
    exact Nat.mod_lt _ (by positivity)
  · left; exact hv

/-- Every decoded state of a table is below `2 ^ W`. -/
theorem decAll_lt (W : ℕ) (hW : 0 < W) (T : List ℕ) (v : ℕ) (hv : v ∈ lfoldr (decLit W (2 ^ W - 1)) [] T) :
    v < 2 ^ W := by
  rw [lfoldr_eq] at hv
  induction T with
  | nil => simp at hv
  | cons x T ih =>
    rw [List.foldr_cons] at hv
    rcases decLit_lt W x hW _ v hv with h | h
    · exact ih h
    · exact h

theorem decAll_getD_lt (W : ℕ) (hW : 0 < W) (T : List ℕ) (k : ℕ) :
    (lfoldr (decLit W (2 ^ W - 1)) [] T).getD k 0 < 2 ^ W := by
  rcases lt_or_ge k (lfoldr (decLit W (2 ^ W - 1)) [] T).length with hk | hk
  · rw [List.getD_eq_getElem _ _ hk]
    exact decAll_lt W hW T _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ hk]
    positivity

end Robbins.Cert.SO.L
