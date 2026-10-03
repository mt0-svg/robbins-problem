import Robbins.Cert.SO.Lanes
import Robbins.Lanes.Pack
import Robbins.Cert.SO.LS.Tab
import Robbins.Cert.SO.LS.Tup
import Robbins.Cert.SO.LS.Sel
import Robbins.Cert.SO.LS.Cok
import Robbins.Cert.SO.LS.Cell
import Robbins.Cert.SO.LS.TopV
import Robbins.Cert.SO.LS.Fin
import Robbins.Cert.SO.LS.TailV

/-!
# The lanes step implies the scalar step

The lanes check of a fixed-window step (`lanesRange`, `lanesStep`, Robbins/Cert/SO/Lanes.lean)
against the scalar check `checkStep` of Robbins/Cert/SO/EvalK.lean.

`checkStep_of_lanesRanges` is the statement the chain uses: ranges of top records `[cs_i, cs_{i+1})`
from `0` to at least the number of records, each passed by `lanesRange`, give `checkStep`;
`checkStep_of_lanesStep` is its case of one range, the whole step. The statements below them are the steps of
the proof.

The plan. A state of `checkStep` is a pair (prefix, top record); the states of the top `j` are the
block `[C (j + m - 1, m), C (j + m, m))` of the table, and their prefixes are the first
`C (j + m - 1, m - 1)` of `tupR (m - 1)` over the records (`stsS_get`). The lanes check keeps one
lane per prefix: lane `l` of every vector is the quantity of the prefix `prefS c l` (`PVRep`, the
prefix vectors; `CVRep`, the data of a cell, which are the fields of `pdAt`, the `PD` of the scalar
check; `LARep`, the accumulators, with the fields `acc_q`, `lam_q` of the packed scalar `Acc` as
separate lanes). The tables come in by `litCat_spec`, `fields_spec` and `lkS_eq`, the lookups of
`H_i` by `route_spec`. The bounds: `ctxOK` bounds every input (`D = 2 ^ 36`, `m ≤ 32`, at most
`4096` cells), every lane of a cell is below `2 ^ 87` or so, one cell adds at most `2 ^ 126` to an
accumulator lane (`LAGrow`), so the accumulators stay below `2 ^ 140` and every lane below `2 ^ 143`.
-/

namespace Robbins.Cert.SO.L

open Robbins.Cert Robbins.Cert.K Robbins.Cert.SO.K Robbins.Lanes

/-! ## The scalar side -/

/-- The width of a state, `48 (m + 1)`. -/
abbrev Wm (m : ℕ) : ℕ := Nat.mul 48 (Nat.succ m)

/-- The lookup of `checkStep` into the table `Nn` of time `t + 1`. -/
noncomputable def lkS (g : Grid) (Nn : List ℕ) : ℕ → SV :=
  lkF (lk0 (bld (depth Nn.length) Nn) (depth Nn.length) g.m (Wm g.m)
    (Nat.sub (Nat.shiftLeft 1 (Wm g.m)) 1))

/-- The states (prefix, top record) of `checkStep`, in rank order. -/
noncomputable def stsS (g : Grid) (t : ℕ) (Nn : List ℕ) : List (Pre × SR) :=
  states (mkCtx g t).recs (lmap (lmap fun tp => mkPre (mkCtx g t) (lkS g Nn) (lrevOnto tp []))
    (tupG (Nat.sub g.m 2) (mkCtx g t).recs))

/-- The decoded states of a claimed table. -/
noncomputable def decS (m : ℕ) (T : List ℕ) : List ℕ := lfoldr (decLit (Wm m) (2 ^ Wm m - 1)) [] T

/-- The state `k` of `checkStep` passes against the decoded claimed state `k`. -/
def StOK (g : Grid) (t : ℕ) (Nn Nt : List ℕ) (k : ℕ) : Prop :=
  ∀ h : k < (stsS g t Nn).length,
    checkState (mkCtx g t) (lkS g Nn) (stsS g t Nn)[k] ((decS g.m Nt).getD k 0) = true

/-- The prefix `l`: the records of the tuple `l` of `tupR (m - 1)`, increasing. -/
noncomputable def prefS (c : Ctx) (l : ℕ) : List SR :=
  lrevOnto ((tupR (Nat.sub c.m 1) c.recs).getD l []) []

/-- The cell `i` (`1 ≤ i ≤ L`; a dummy past the end). -/
noncomputable def cellS (c : Ctx) (i : ℕ) : SC :=
  (c.cells.drop (i - 1)).headD (SC.mk 0 0 0 [] 0 0 0 0 0 0 0)

/-- `below_i` of the prefix `l`: its records in a cell before `i`. -/
noncomputable def belowS (c : Ctx) (l i : ℕ) : ℕ := (prefS c l).countP fun r => decide (r.pos < i)

/-- The rank of `H_i` for the prefix `l`. -/
noncomputable def idxS (c : Ctx) (l i : ℕ) : ℕ :=
  lget (rankCs (prefS c l)) (belowS c l i) + lget (cellS c i).cb (belowS c l i)

/-- The slope of the slot of the record `q` of the prefix `l` in `H_i`: slot `q` below `below_i`,
`q + 1` from there. -/
noncomputable def slS (c : Ctx) (lk : ℕ → SV) (l i q : ℕ) : ℕ :=
  lget (lk (idxS c l i)).sl (if q < belowS c l i then q else q + 1)

/-- The coefficient of the record `q` of the prefix `l` in the cell `i`: `0` if it is forgotten or
its own cell is `i`, else its slot slope. -/
noncomputable def coS (c : Ctx) (lk : ℕ → SV) (l i q : ℕ) : ℕ :=
  if (rget (prefS c l) q).fg || (rget (prefS c l) q).pos == i then 0 else slS c lk l i q

/-- The record `q` of the prefix `l` gets its own-cell credit in the cell `i`. -/
noncomputable def ownS (c : Ctx) (l i q : ℕ) : Bool :=
  !(rget (prefS c l) q).fg && (rget (prefS c l) q).pos == i

/-- The data `PD` of the prefix `l` in the cell `i` (a dummy past the last cell). -/
noncomputable def pdAt (c : Ctx) (lk : ℕ → SV) (l i : ℕ) : PD :=
  ((mkPre c lk (prefS c l)).pd.drop (i - 1)).headD (PD.mk 0 0 0 0 0 0 0 0 0 0 0 0 0 [] false [])

/-- The lanes constants of the top record (`topCheck`). -/
noncomputable def tvOf (top : SR) : TV :=
  TV.mk (Nat.mul DS top.em) (bsel top.fg 0 (Nat.mul top.pm top.dl)) (bsel top.fg 0 top.pm)
    top.pos (bsel top.fg false true)

/-- The scalar constants of the top record (`evalTop`). -/
noncomputable def tpOf (c : Ctx) (top : SR) : Tp :=
  Tp.mk (Nat.mul DS top.em) (bsel top.fg 0 (Nat.mul top.pm top.dl))
    (bsel top.fg 0 (Nat.mul top.pm c.FT)) top.pos (bsel top.fg 0 c.FT)

/-- The facts of a step that `ctxOK` does not check and `mkCtx` fixes: `a1 = r D`, `FT = F ^ (m - 1)`,
`h = p_i - p_{i-1}` and `m` rank binomials in every cell. -/
def CtxX (c : Ctx) : Prop :=
  c.a1 = c.r * DS ∧ c.FT = F128 ^ (c.m - 1) ∧ ∀ cl ∈ c.cells, cl.h = cl.pb - cl.pa ∧ cl.cb.length = c.m

/-! ## The representations -/

/-- The prefix vectors on `n` lanes from the prefix `a`: lane `l` of slot `q` is the record `q` of
the prefix `a + l`, and lane `l` of `cs[b]` is `C_b` of the prefix `a + l` (`rankCs`). -/
structure PVRep (c : Ctx) (a n : ℕ) (pv : PV) : Prop where
  pos : pv.pos = (List.range (c.m - 1)).map fun q => pack LW n fun l => (rget (prefS c (a + l)) q).pos
  dl : pv.dl = (List.range (c.m - 1)).map fun q => pack LW n fun l => (rget (prefS c (a + l)) q).dl
  fg : pv.fg = (List.range (c.m - 1)).map fun q =>
    pack LW n fun l => if (rget (prefS c (a + l)) q).fg then 1 else 0
  cs : pv.cs = (List.range c.m).map fun b => pack LW n fun l => lget (rankCs (prefS c (a + l))) b

/-- The data of the cell `i` on `n` lanes from the prefix `a`: lane `l` is the prefix `a + l` (`pdAt`,
and the lookup of `H_i` by `lk`). -/
structure CVRep (c : Ctx) (lk : ℕ → SV) (a n i : ℕ) (cv : CV) : Prop where
  pa : cv.pa = (cellS c i).pa
  pb : cv.pb = (cellS c i).pb
  h : cv.h = (cellS c i).h
  h2 : cv.h2 = (cellS c i).h2
  pb2 : cv.pb2 = (cellS c i).pb * (cellS c i).pb
  B : cv.B = pack LW n fun l => belowS c (a + l) i
  sig : cv.sig = pack LW n fun l => (pdAt c lk (a + l) i).sig
  bet : cv.bet = pack LW n fun l => (pdAt c lk (a + l) i).bet
  sp : cv.sp = pack LW n fun l => (pdAt c lk (a + l) i).sp
  co : cv.co = (List.range (c.m - 1)).map fun q => pack LW n fun l => coS c lk (a + l) i q
  own : cv.own = (List.range (c.m - 1)).map fun q =>
    pack LW n fun l => if ownS c (a + l) i q then 2 ^ 143 else 0
  a0 : cv.a0 = pack LW n fun l => (pdAt c lk (a + l) i).a0
  kk : cv.kk = pack LW n fun l => c.a1 + (pdAt c lk (a + l) i).sig
  A0 : cv.A0 = pack LW n fun l => (pdAt c lk (a + l) i).A0
  A1 : cv.A1 = pack LW n fun l => (pdAt c lk (a + l) i).A1
  IA : cv.IA = pack LW n fun l => (pdAt c lk (a + l) i).IA
  ssq : cv.ssq = pack LW n fun l => (pdAt c lk (a + l) i).ssq
  idx : cv.idx = pack LW n fun l => idxS c (a + l) i
  gv : cv.gv = pack LW n fun l => (lk (idxS c (a + l) i)).V
  gs : cv.gs = (List.range c.m).map fun f => pack LW n fun l => lget (lk (idxS c (a + l) i)).sl f

/-- The accumulators on `n` lanes against one scalar `Acc` per lane: `rp`, `rn` lanewise, and the
fields `acc_q = af q l`, `lam_q = lf q l` of the packed scalar `ac`, `lm` (`F = 2 ^ 128`; a field may
exceed `F`, the identity is exact). -/
structure LARep (m n : ℕ) (A : LA) (As : ℕ → Acc) (af lf : ℕ → ℕ → ℕ) : Prop where
  rp : A.rp = pack LW n fun l => (As l).rp
  rn : A.rn = pack LW n fun l => (As l).rn
  ac : A.ac = (List.range m).map fun q => pack LW n (af q)
  lm : A.lm = (List.range m).map fun q => pack LW n (lf q)
  acS : ∀ l < n, (As l).ac = ∑ q ∈ Finset.range m, af q l * F128 ^ q
  lmS : ∀ l < n, (As l).lm = ∑ q ∈ Finset.range m, lf q l * F128 ^ q

/-- Every accumulator lane below `B`. -/
def LABound (m n : ℕ) (As : ℕ → Acc) (af lf : ℕ → ℕ → ℕ) (B : ℕ) : Prop :=
  ∀ l < n, (As l).rp < B ∧ (As l).rn < B ∧ ∀ q < m, af q l < B ∧ lf q l < B

/-- Every accumulator lane grows by at most `δ`. -/
def LAGrow (m n : ℕ) (As : ℕ → Acc) (af lf : ℕ → ℕ → ℕ) (As' : ℕ → Acc) (af' lf' : ℕ → ℕ → ℕ)
    (δ : ℕ) : Prop :=
  ∀ l < n, (As' l).rp ≤ (As l).rp + δ ∧ (As' l).rn ≤ (As l).rn + δ ∧
    ∀ q < m, af' q l ≤ af q l + δ ∧ lf' q l ≤ lf q l + δ

theorem binomsAux_length (x k i b : ℕ) : (binomsAux x k i b).length = k := by
  induction k generalizing i b with
  | zero => rfl
  | succ k ih => simp [binomsAux, ih]

theorem binoms_length (m x : ℕ) : (binoms m x).length = m := binomsAux_length x m 0 x

theorem mkCtx_recs_pos (g : Grid) (t : ℕ) : 1 ≤ (mkCtx g t).recs.length := by
  simp [mkCtx]

/-- The step data of a grid satisfy `CtxX`. -/
theorem mkCtx_X (g : Grid) (t : ℕ) : CtxX (mkCtx g t) := by
  refine ⟨rfl, rfl, ?_⟩
  intro cl hcl
  simp only [mkCtx, List.mem_map] at hcl
  obtain ⟨⟨j, pa, pb⟩, _, rfl⟩ := hcl
  exact ⟨rfl, binoms_length _ _⟩

/-- Every state of the lookup has its fields below `2 ^ 48`. -/
theorem lkS_bound (g : Grid) (Nn : List ℕ) (idx : ℕ) :
    (lkS g Nn idx).V < 2 ^ 48 ∧ ∀ f, lget (lkS g Nn idx).sl f < 2 ^ 48 := by
  unfold lkS
  rw [lkF_eq]
  show Nat.land _ M48 < 2 ^ 48 ∧ ∀ f, lget (slopes g.m _) f < 2 ^ 48
  refine ⟨?_, fun f => ?_⟩
  · show _ &&& (2 ^ 48 - 1) < _
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by norm_num)
  · rw [lget_eq, slopes_eq]
    rcases lt_or_ge f g.m with hf | hf
    · rw [List.getD_eq_getElem _ _ (by simpa using hf)]
      simp only [List.getElem_map, List.getElem_range]
      exact Nat.mod_lt _ (by norm_num)
    · rw [List.getD_eq_default _ _ (by simpa using hf)]
      norm_num

theorem lkS_length (g : Grid) (Nn : List ℕ) (idx : ℕ) : (lkS g Nn idx).sl.length = g.m := by
  unfold lkS
  rw [lkF_eq]
  show (slopes g.m _).length = g.m
  rw [slopes_eq]
  simp

/-- With no new point, a state is checked by `checkVar` alone. -/
theorem checkState_eq (c : Ctx) (hnp : c.newp = []) (lk : ℕ → SV) (st : Pre × SR) (x : ℕ) :
    checkState c lk st x = checkVar c lk (x % 2 ^ 48)
      ((List.range c.m).map fun f => x / 2 ^ (48 * (f + 1)) % 2 ^ 48) st.1 st.2 := by
  unfold checkState variants
  rw [hnp]
  have e : bsel st.2.fg (@List.rec SR (fun _ => Bool) true (fun _ _ _ => false) []) true = true := by
    cases st.2.fg <;> rfl
  rw [e]
  show bsel (checkVar c lk (Nat.land x M48) (slopes c.m x) st.1 st.2) true false = _
  rw [bsel_false, Bool.and_true, slopes_eq]
  congr 1
  show x &&& (2 ^ 48 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod x 48

/-! ## Counting and layout -/

/-- `cnt k n = C (n + k - 1, k)`, the number of nondecreasing `k`-tuples over `n` values. -/
theorem cnt_eq (k n : ℕ) : cnt k n = (n + k - 1).choose k := by
  exact cnt_eq' k n

/-- The number of states of a step. -/
theorem stsS_length (g : Grid) (t : ℕ) (Nn : List ℕ) (hm : 2 ≤ g.m) :
    (stsS g t Nn).length = cnt g.m (mkCtx g t).recs.length := by
  unfold stsS
  rw [show Nat.sub g.m 2 = g.m - 2 from rfl, states_tupG _ (g.m - 2) _ SR0, List.length_map,
    show g.m - 2 + 2 = g.m by omega, tupR_length_cnt]

/-- The states of the top `j`: the block at `C (j + m - 1, m)`, with the first
`C (j + m - 1, m - 1)` prefixes. -/
theorem stsS_get (g : Grid) (t : ℕ) (Nn : List ℕ) (hm : 2 ≤ g.m) (j l : ℕ)
    (hj : j < (mkCtx g t).recs.length) (hl : l < cnt (g.m - 1) (j + 1)) :
    (stsS g t Nn)[cnt g.m j + l]? =
      some (mkPre (mkCtx g t) (lkS g Nn) (prefS (mkCtx g t) l), rget (mkCtx g t).recs j) := by
  obtain ⟨m', hm'⟩ : ∃ m', g.m = m' + 1 := ⟨g.m - 1, by omega⟩
  unfold stsS
  rw [show Nat.sub g.m 2 = g.m - 2 from rfl, states_tupG _ (g.m - 2) _ SR0,
    show g.m - 2 + 2 = m' + 1 by omega, List.getElem?_map, hm',
    tupR_block m' _ j l hj (by rw [hm'] at hl; simpa using hl)]
  simp only [Option.map_some, List.tail_cons, List.headD_cons, rget_of_lt _ _ hj]
  unfold prefS
  rw [lrevOnto_eq, List.append_nil, show Nat.sub (mkCtx g t).m 1 = m' by show g.m - 1 = m'; omega]

/-- A chunk check from its pairs: aligned literals, as many decoded states as states, every pair
passed. -/
theorem chunkCheck_of_all {α : Type} (f : α → ℕ → Bool) (Ws : ℕ) (hWs : 0 < Ws) (lits : List ℕ)
    (hlits : litsOK Ws lits = true) (sts : List α)
    (hlen : (lfoldr (decLit Ws (2 ^ Ws - 1)) [] lits).length = sts.length)
    (h : ∀ k (hk : k < sts.length),
      f sts[k] ((lfoldr (decLit Ws (2 ^ Ws - 1)) [] lits).getD k 0) = true) :
    chunkCheck f Ws (2 ^ Ws - 1) lits sts = true := by
  induction lits generalizing sts with
  | nil =>
    rw [chunkCheck_nil]
    have : sts.length = 0 := by rw [← hlen]; rfl
    simp [List.length_eq_zero_iff.1 this]
  | cons x xs ih =>
    have hfold : lfoldr (decLit Ws (2 ^ Ws - 1)) [] (x :: xs) =
        decLit Ws (2 ^ Ws - 1) x [] ++ lfoldr (decLit Ws (2 ^ Ws - 1)) [] xs := by
      show decLit Ws (2 ^ Ws - 1) x (lfoldr (decLit Ws (2 ^ Ws - 1)) [] xs) = _
      exact decLit_append _ _ _ _
    have hle : (decLit Ws (2 ^ Ws - 1) x []).length ≤ 16 := decLit_length_le _ _ _
    have hxs : litsOK Ws xs = true ∧ (xs ≠ [] → (decLit Ws (2 ^ Ws - 1) x []).length = 16) := by
      rcases xs with _ | ⟨y, ys⟩
      · exact ⟨rfl, fun h => absurd rfl h⟩
      · have h' : bsel (Nat.beq (Nat.shiftRight x (Nat.mul 16 Ws)) 1) (litsOK Ws (y :: ys)) false = true :=
          hlits
        rw [bsel_false, Bool.and_eq_true, Nat.beq_eq] at h'
        refine ⟨h'.2, fun _ => ?_⟩
        have hx : x / 2 ^ (16 * Ws) = 1 := by
          rw [← Nat.shiftRight_eq_div_pow]; exact h'.1
        rw [decLit_eq, List.append_nil, litStates_eq Ws x 16 hWs (by norm_num) le_rfl hx]
        simp
    rw [hfold] at hlen h
    rw [List.length_append] at hlen
    rw [chunkCheck_cons, Bool.and_eq_true]
    have hE : (lfoldr (decLit Ws (2 ^ Ws - 1)) [] xs).length ≠ 0 →
        (decLit Ws (2 ^ Ws - 1) x []).length = 16 := by
      intro hne
      refine hxs.2 fun e => hne ?_
      subst e
      rfl
    constructor
    · rw [lall2_iff]
      refine ⟨?_, fun i h1 h2 => ?_⟩
      · rw [ltake_eq, List.length_take]
        by_cases hz : (lfoldr (decLit Ws (2 ^ Ws - 1)) [] xs).length = 0
        · omega
        · have := hE hz
          omega
      · rw [ltake_eq] at h1
        have hi : i < sts.length := lt_of_lt_of_le h1 (by simp)
        have := h i hi
        rw [List.getD_append _ _ _ _ h2, List.getD_eq_getElem _ _ h2] at this
        simpa only [ltake_eq, List.getElem_take] using this
    · refine ih hxs.1 (ldrop 16 sts) ?_ fun k hk => ?_
      · rw [ldrop_eq, List.length_drop]
        by_cases hz : (lfoldr (decLit Ws (2 ^ Ws - 1)) [] xs).length = 0
        · omega
        · have := hE hz
          omega
      · rw [ldrop_eq, List.length_drop] at hk
        have hz : (lfoldr (decLit Ws (2 ^ Ws - 1)) [] xs).length ≠ 0 := by
          intro hz; omega
        have h16 := hE hz
        have := h (16 + k) (by omega)
        rw [List.getD_append_right _ _ _ _ (by omega), h16, Nat.add_sub_cancel_left] at this
        simpa only [ldrop_eq, List.getElem_drop] using this

/-- The scalar check from its states: aligned literals, as many decoded states as states, and
every state passed. -/
theorem checkStep_of_StOK (g : Grid) (t : ℕ) (Nn Nt : List ℕ) (hlits : litsOK (Wm g.m) Nt = true)
    (hlen : (decS g.m Nt).length = (stsS g t Nn).length) (hst : ∀ k, StOK g t Nn Nt k) :
    checkStep g t Nn Nt = true := by
  have hW : 0 < Wm g.m := by show 0 < 48 * (g.m + 1); positivity
  have hMW : Nat.sub (Nat.shiftLeft 1 (Wm g.m)) 1 = 2 ^ Wm g.m - 1 := by
    show 1 <<< Wm g.m - 1 = _
    rw [Nat.shiftLeft_eq, one_mul]
  show chunkCheck (checkState (mkCtx g t) (lkS g Nn)) (Wm g.m) (Nat.sub (Nat.shiftLeft 1 (Wm g.m)) 1) Nt
    (stsS g t Nn) = true
  rw [hMW]
  exact chunkCheck_of_all _ _ hW Nt hlits _ hlen fun k hk => hst k hk

/-! ## Tables -/

/-- The concatenation of the literals of a table: its decoded states, `Ws` bits each. -/
theorem litCat_spec (Ws : ℕ) (hWs : 0 < Ws) (lits : List ℕ) (h : litsOK Ws lits = true) :
    litCat Ws lits = (pack Ws (lfoldr (decLit Ws (2 ^ Ws - 1)) [] lits).length
      (fun k => (lfoldr (decLit Ws (2 ^ Ws - 1)) [] lits).getD k 0),
      (lfoldr (decLit Ws (2 ^ Ws - 1)) [] lits).length) := by
  rw [lfoldr_decLit, litCat_run Ws hWs lits h]
  rfl

/-- The lookup of `checkStep` reads the decoded states of an aligned table. -/
theorem lkS_eq (g : Grid) (Nn : List ℕ) (hlits : litsOK (Wm g.m) Nn = true) (idx : ℕ)
    (hidx : idx < (decS g.m Nn).length) :
    lkS g Nn idx = SV.mk ((decS g.m Nn).getD idx 0 % 2 ^ 48)
      ((List.range g.m).map fun f => (decS g.m Nn).getD idx 0 / 2 ^ (48 * (f + 1)) % 2 ^ 48) := by
  have hW : 0 < Wm g.m := by show 0 < 48 * (g.m + 1); positivity
  unfold lkS
  unfold decS at hidx ⊢
  rw [lfoldr_decLit] at hidx ⊢
  rw [lkF_eq]
  have hlen := allStates_length (Wm g.m) hW Nn hlits
  have hNn : 1 ≤ Nn.length := by
    rcases Nn with _ | ⟨x, Nn⟩
    · simp [allStates] at hidx
    · simp
  have hd := depth_spec Nn.length hNn
  have hidx16 : idx / 16 < 2 ^ depth Nn.length := by omega
  have hMW : Nat.sub (Nat.shiftLeft 1 (Wm g.m)) 1 = 2 ^ Wm g.m - 1 := by
    show 1 <<< Wm g.m - 1 = _
    rw [Nat.shiftLeft_eq, one_mul]
  show SV.mk (Nat.land (lkSt _ _ _ _ idx) M48) (slopes g.m (lkSt _ _ _ _ idx)) = _
  rw [hMW, lkSt_eq _ _ _ hd idx hidx16, ← allStates_getD (Wm g.m) hW Nn hlits idx hidx, slopes_eq]
  congr 1
  show _ &&& (2 ^ 48 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

/-- A compaction that passes its two tests moves the source lane `Iv j` to the destination lane
`j`, for sources below `2 ^ 100` (no carry in the network). -/
theorem route_spec (NS ND : ℕ) (Iv : ℕ → ℕ) (hNS : NS < 2 ^ 40) (hIv : ∀ j < ND, Iv j < 2 ^ 40)
    (hok : (mkRt NS ND (pack LW ND Iv)).ok = true) :
    (∀ j < ND, Iv j < NS) ∧ ∀ f : ℕ → ℕ, (∀ s < NS, f s < 2 ^ 100) →
      route (mkRt NS ND (pack LW ND Iv)) (pack LW NS f) = pack LW ND fun j => f (Iv j) := by
  exact route_spec_gen NS ND Iv hNS hIv hok

/-- The fields of `n` concatenated states, one lane per state, when the compaction test passes. -/
theorem fields_spec (m n : ℕ) (hn : n ≤ B32) (hm : m ≤ 32) (st : ℕ → ℕ)
    (hst : ∀ s < n, st s < 2 ^ Wm m) (hok : (fields m (pack (Wm m) n st) n).2.2 = true) :
    (fields m (pack (Wm m) n st) n).1 = pack LW n (fun s => st s % 2 ^ 48) ∧
      (fields m (pack (Wm m) n st) n).2.1 =
        (List.range m).map fun f => pack LW n fun s => st s / 2 ^ (48 * (f + 1)) % 2 ^ 48 := by
  exact fields_spec_gen m n hn hm st hst hok

/-! ## Prefix vectors -/

/-- A list of records through `rget`. -/
theorem recs_eq_map (l : List SR) : l = (List.range l.length).map (rget l) := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [rget_of_lt _ _ h1]

/-- The prefix `l` through the tuples over `range R`. -/
theorem prefS_eq (c : Ctx) (l : ℕ) :
    prefS c l = (((tupR (c.m - 1) (List.range c.recs.length)).getD l []).map (rget c.recs)).reverse := by
  unfold prefS
  rw [lrevOnto_eq, List.append_nil]
  show ((tupR (c.m - 1) c.recs).getD l []).reverse = _
  conv_lhs => rw [recs_eq_map c.recs, tupR_map]
  congr 1
  rcases lt_or_ge l (tupR (c.m - 1) (List.range c.recs.length)).length with h | h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simpa using h), List.getD_eq_default _ _ h]
    rfl

/-- A prefix has `m - 1` records. -/
theorem prefS_length (c : Ctx) (l : ℕ) (hl : l < cnt (c.m - 1) c.recs.length) :
    (prefS c l).length = c.m - 1 := by
  rw [prefS_eq, List.length_reverse, List.length_map]
  have hl' : l < (tupR (c.m - 1) (List.range c.recs.length)).length := by
    rw [tupR_length_cnt, List.length_range]; exact hl
  rw [List.getD_eq_getElem _ _ hl']
  exact tupR_mem_length _ _ _ (List.getElem_mem hl')

/-- The records of a prefix are records of the step. -/
theorem prefS_mem (c : Ctx) (l : ℕ) : ∀ r ∈ prefS c l, r ∈ c.recs := by
  intro r hr
  rw [prefS_eq, List.mem_reverse, List.mem_map] at hr
  obtain ⟨k, hk, rfl⟩ := hr
  rcases lt_or_ge l (tupR (c.m - 1) (List.range c.recs.length)).length with h | h
  · rw [List.getD_eq_getElem _ _ h] at hk
    have := (tupR_range_mem _ _ _ (List.getElem_mem h)).2 k hk
    rw [rget_of_lt _ _ this]
    exact List.getElem_mem this
  · rw [List.getD_eq_default _ _ h] at hk
    simp at hk

/-- The records of a prefix are sorted by position. -/
theorem prefS_sorted (c : Ctx) (hc : ctxOK c = true) (l : ℕ) :
    ∀ p q, p ≤ q → q < (prefS c l).length →
      ((prefS c l).getD p SR0).pos ≤ ((prefS c l).getD q SR0).pos := by
  have hok := cok_of_ctxOK c hc
  intro p q hpq hq
  set tp := (tupR (c.m - 1) (List.range c.recs.length)).getD l [] with htp
  have hmem : tp.Pairwise (· ≥ ·) ∧ ∀ x ∈ tp, x < c.recs.length := by
    rcases lt_or_ge l (tupR (c.m - 1) (List.range c.recs.length)).length with h | h
    · rw [htp, List.getD_eq_getElem _ _ h]
      exact tupR_range_mem _ _ _ (List.getElem_mem h)
    · rw [htp, List.getD_eq_default _ _ h]
      simp
  have hpw : (prefS c l).Pairwise fun a b => a.pos ≤ b.pos := by
    rw [prefS_eq, ← htp, ← List.map_reverse, List.pairwise_map]
    have h2 : tp.reverse.Pairwise (· ≤ ·) := by
      rw [List.pairwise_reverse]; exact hmem.1
    refine h2.imp_of_mem fun {a b} ha hb hab => ?_
    have ha' := hmem.2 a (List.mem_reverse.1 ha)
    have hb' := hmem.2 b (List.mem_reverse.1 hb)
    rw [rget_of_lt _ _ ha', rget_of_lt _ _ hb', hok.pos _ ha', hok.pos _ hb']
    omega
  rcases eq_or_lt_of_le hpq with e | e
  · subst e; exact le_rfl
  · rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hq]
    exact List.pairwise_iff_getElem.1 hpw _ _ (by omega) hq e

/-- The slot vectors over the tuples of `tupR d (range R)`, slot `q` increasing (entry `d - 1 - q`
of a tuple, which is largest first). -/
theorem slotInc_spec (d R : ℕ) (f : ℕ → ℕ) (hf : ∀ k < R, f k < 2 ^ 143) :
    slotInc d f R = (List.range d).map fun q =>
      pack LW (cnt d R) fun l => f (((tupR d (List.range R)).getD l []).getD (d - 1 - q) 0) := by
  have hf' : ∀ v < R, f v < 2 ^ 144 := by
    intro v hv
    exact lt_of_lt_of_le (hf v hv) (by norm_num)
  unfold slotInc
  rw [lrevOnto_eq]
  simp
  rw [tupV_eq f R hf' d]
  rw [← List.map_reverse]
  apply List.ext_getElem
  · -- both sides have length d
    simp [List.length_map, List.length_range]
  · intro i hiL hiR
    have hi_len : i < d := by
      have hlen : ((List.range d).reverse.map (fun q => pk ((tupR d (List.range R)).map fun tp => f (tp.getD q 0)))).length = d := by
        simp [List.length_map, List.length_range]
      rw [hlen] at hiL
      exact hiL
    have h_rev_len : i < (List.range d).reverse.length := by
      simpa [List.length_range] using hi_len
    have h_range_len : d - 1 - i < (List.range d).length := by
      have : (List.range d).length = d := by simp
      rw [this]
      omega
    have h_rev_idx : ((List.range d).reverse)[i] = d - 1 - i := by
      rw [List.getElem_reverse h_rev_len]
      have hlen : (List.range d).length = d := by simp
      have h := List.getElem_range h_range_len
      -- h : (List.range d)[d - 1 - i] = d - 1 - i
      -- goal: (List.range d)[(List.range d).length - 1 - i] = d - 1 - i
      simp [hlen, h]
    rw [List.getElem_map, List.getElem_map, h_rev_idx]
    -- Goal: pk ((tupR d (List.range R)).map fun tp => f (tp.getD (d - 1 - i) 0)) =
    --        pack LW (cnt d R) fun l => f (((tupR d (List.range R)).getD l []).getD (d - 1 - i) 0)
    have hpk : pk ((tupR d (List.range R)).map fun tp => f (tp.getD (d - 1 - i) 0)) =
        pack LW (cnt d R) fun l => f (((tupR d (List.range R)).getD l []).getD (d - 1 - i) 0) := by
      unfold pk
      set len := ((tupR d (List.range R)).map fun tp => f (tp.getD (d - 1 - i) 0)).length with hlen_def
      have hlen_eq : len = cnt d R := by
        rw [hlen_def]
        simp [List.length_map, tupR_length_cnt, List.length_range]
      have htemp := pack_congr LW len
        (fun l => ((tupR d (List.range R)).map fun tp => f (tp.getD (d - 1 - i) 0)).getD l 0)
        (fun l => f (((tupR d (List.range R)).getD l []).getD (d - 1 - i) 0))
        (by
          intro l hl
          have hmem_len : l < (tupR d (List.range R)).length := by
            rw [tupR_length_cnt d (List.range R), List.length_range]
            rw [← hlen_eq]
            exact hl
          calc
            ((tupR d (List.range R)).map fun tp => f (tp.getD (d - 1 - i) 0)).getD l 0
                = ((tupR d (List.range R)).map fun tp => f (tp.getD (d - 1 - i) 0))[l] := by
              rw [List.getD_eq_getElem _ _ hl]
            _ = f (((tupR d (List.range R))[l]).getD (d - 1 - i) 0) := by
              rw [List.getElem_map]
            _ = f (((tupR d (List.range R)).getD l []).getD (d - 1 - i) 0) := by
              rw [List.getD_eq_getElem _ _ hmem_len])
      simpa [hlen_eq] using htemp
    have h_range_get_proof : i < (List.range d).length := by
      simpa [List.length_range] using hi_len
    have h_range_get : (List.range d)[i] = i :=
      List.getElem_range h_range_get_proof
    simpa [hpk, h_range_get]

/-- A slot vector of the records, restricted to `np` lanes: lane `l` of slot `q` is the record `q`
of the prefix `l`. -/
theorem mkPV_slot (c : Ctx) (np : ℕ) (hnp : np ≤ cnt (c.m - 1) c.recs.length) (f : SR → ℕ)
    (hf : ∀ r ∈ c.recs, f r < 2 ^ 143) :
    preL np (slotInc (c.m - 1) (fun k => f (rget c.recs k)) c.recs.length) =
      (List.range (c.m - 1)).map fun q => pack LW np fun l => f (rget (prefS c l) q) := by
  have hf' : ∀ k < c.recs.length, f (rget c.recs k) < 2 ^ 143 := fun k hk => by
    rw [rget_of_lt _ _ hk]; exact hf _ (List.getElem_mem hk)
  rw [slotInc_spec (c.m - 1) c.recs.length _ hf']
  unfold preL
  rw [lmap_eq, List.map_map]
  refine List.map_congr_left fun q hq => ?_
  have hq' : q < c.m - 1 := List.mem_range.1 hq
  have htp : ∀ l < cnt (c.m - 1) c.recs.length,
      ((tupR (c.m - 1) (List.range c.recs.length)).getD l []).length = c.m - 1 ∧
        ∀ x ∈ (tupR (c.m - 1) (List.range c.recs.length)).getD l [], x < c.recs.length := by
    intro l hl
    have hl' : l < (tupR (c.m - 1) (List.range c.recs.length)).length := by
      rw [tupR_length_cnt, List.length_range]; exact hl
    rw [List.getD_eq_getElem _ _ hl']
    exact ⟨tupR_mem_length _ _ _ (List.getElem_mem hl'),
      (tupR_range_mem _ _ _ (List.getElem_mem hl')).2⟩
  show pre LW np (pack LW (cnt (c.m - 1) c.recs.length) _) = _
  rw [pre_eq _ np _ (fun l hl => ?_) hnp]
  · refine pack_congr LW np _ _ fun l hl => ?_
    have hl' := lt_of_lt_of_le hl hnp
    obtain ⟨hlen, -⟩ := htp l hl'
    have hi : c.m - 1 - 1 - q < ((tupR (c.m - 1) (List.range c.recs.length)).getD l []).length := by
      omega
    rw [List.getD_eq_getElem _ _ hi]
    congr 1
    rw [prefS_eq]
    have hq2 : q < (((tupR (c.m - 1) (List.range c.recs.length)).getD l []).map
        (rget c.recs)).reverse.length := by
      simp only [List.length_reverse, List.length_map]; omega
    rw [rget_of_lt _ _ hq2, List.getElem_reverse, List.getElem_map]
    congr 1
    simp only [List.length_map, hlen]
  · obtain ⟨hlen, hlt⟩ := htp l hl
    have hi : c.m - 1 - 1 - q < ((tupR (c.m - 1) (List.range c.recs.length)).getD l []).length := by
      omega
    rw [List.getD_eq_getElem _ _ hi]
    exact lt_of_lt_of_le (hf' _ (hlt _ (List.getElem_mem hi))) (by norm_num)

/-- The slot vectors of the records on all the prefixes: lane `l` of slot `q` is the record `q` of
the prefix `l`. -/
theorem slotInc_prefS (c : Ctx) (f : SR → ℕ) (hf : ∀ r ∈ c.recs, f r < 2 ^ 143) :
    slotInc (c.m - 1) (fun k => f (rget c.recs k)) c.recs.length =
      (List.range (c.m - 1)).map fun q =>
        pack LW (cnt (c.m - 1) c.recs.length) fun l => f (rget (prefS c l) q) := by
  have hf' : ∀ k < c.recs.length, f (rget c.recs k) < 2 ^ 143 := fun k hk => by
    rw [rget_of_lt _ _ hk]; exact hf _ (List.getElem_mem hk)
  rw [slotInc_spec (c.m - 1) c.recs.length _ hf']
  refine List.map_congr_left fun q hq => ?_
  have hq' : q < c.m - 1 := List.mem_range.1 hq
  refine pack_congr LW _ _ _ fun l hl => ?_
  have hl' : l < (tupR (c.m - 1) (List.range c.recs.length)).length := by
    rw [tupR_length_cnt, List.length_range]; exact hl
  have hlen : ((tupR (c.m - 1) (List.range c.recs.length)).getD l []).length = c.m - 1 := by
    rw [List.getD_eq_getElem _ _ hl']
    exact tupR_mem_length _ _ _ (List.getElem_mem hl')
  have hi : c.m - 1 - 1 - q < ((tupR (c.m - 1) (List.range c.recs.length)).getD l []).length := by
    omega
  rw [List.getD_eq_getElem _ _ hi]
  congr 1
  rw [prefS_eq]
  have hq2 : q < (((tupR (c.m - 1) (List.range c.recs.length)).getD l []).map
      (rget c.recs)).reverse.length := by
    simp only [List.length_reverse, List.length_map]; omega
  rw [rget_of_lt _ _ hq2, List.getElem_reverse, List.getElem_map]
  congr 1
  simp only [List.length_map, hlen]

/-- The rank sums of the prefixes, restricted to `np` lanes. -/
theorem mkPV_cs (c : Ctx) (hm : 1 ≤ c.m) (hm32 : c.m ≤ 32) (np : ℕ)
    (hnp : np ≤ cnt (c.m - 1) c.recs.length) (hbs : ∀ r ∈ c.recs, ∀ b ∈ r.bs, b ≤ B32) :
    preL np (rankV
      (lmap (fun q => lget (slotInc (c.m - 1) (fun k => lget (rget c.recs k).bs q) c.recs.length) q)
        (List.range (c.m - 1)))
      (lmap (fun q => lget (slotInc (c.m - 1) (fun k => lget (rget c.recs k).bs (Nat.succ q))
        c.recs.length) q) (List.range (c.m - 1)))) =
      (List.range c.m).map fun b => pack LW np fun l => lget (rankCs (prefS c l)) b := by
  have hlget : ∀ (L : List ℕ) j, (∀ x ∈ L, x ≤ B32) → lget L j ≤ B32 := by
    intro L j hL
    rw [lget_eq]
    rcases lt_or_ge j L.length with h | h
    · rw [List.getD_eq_getElem _ _ h]; exact hL _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ h]; exact Nat.zero_le _
  have hterm : ∀ l q j, lget (rget (prefS c l) q).bs j ≤ B32 := by
    intro l q j
    rw [rget_eq]
    rcases lt_or_ge q (prefS c l).length with h | h
    · rw [List.getD_eq_getElem _ _ h]
      exact hlget _ _ (hbs _ (prefS_mem c l _ (List.getElem_mem h)))
    · rw [List.getD_eq_default _ _ h]
      exact hlget _ _ (by simp)
  have hbq : ∀ j, ∀ r ∈ c.recs, (fun r : SR => lget r.bs j) r < 2 ^ 143 := fun j r hr =>
    lt_of_le_of_lt (hlget _ _ (hbs r hr)) (by norm_num [B32])
  have hU : lmap (fun q => lget (slotInc (c.m - 1) (fun k => lget (rget c.recs k).bs q)
      c.recs.length) q) (List.range (c.m - 1)) =
      (List.range (c.m - 1)).map fun q =>
        pack LW (cnt (c.m - 1) c.recs.length) fun l => lget (rget (prefS c l) q).bs q := by
    rw [lmap_eq]
    refine List.map_congr_left fun q hq => ?_
    rw [slotInc_prefS c (fun r => lget r.bs q) (hbq q), lget_eq,
      List.getD_eq_getElem _ _ (by simpa using hq), List.getElem_map, List.getElem_range]
  have hV : lmap (fun q => lget (slotInc (c.m - 1) (fun k => lget (rget c.recs k).bs (Nat.succ q))
      c.recs.length) q) (List.range (c.m - 1)) =
      (List.range (c.m - 1)).map fun q =>
        pack LW (cnt (c.m - 1) c.recs.length) fun l => lget (rget (prefS c l) q).bs (q + 1) := by
    rw [lmap_eq]
    refine List.map_congr_left fun q hq => ?_
    rw [slotInc_prefS c (fun r => lget r.bs (q + 1)) (hbq (q + 1)), lget_eq,
      List.getD_eq_getElem _ _ (by simpa using hq), List.getElem_map, List.getElem_range]
  rw [hU, hV, rankV_pack _ (c.m - 1) (fun q l => lget (rget (prefS c l) q).bs q)
    (fun q l => lget (rget (prefS c l) q).bs (q + 1))
    (lt_of_le_of_lt (by omega : c.m - 1 ≤ 31) (by norm_num))
    (fun q _ l _ => lt_of_le_of_lt (hterm l q q) (by norm_num [B32]))
    (fun q _ l _ => lt_of_le_of_lt (hterm l q (q + 1)) (by norm_num [B32]))]
  rw [preL_eq (cnt (c.m - 1) c.recs.length) np (fun b l => ∑ q ∈ Finset.range b,
      lget (rget (prefS c l) q).bs q + ∑ q ∈ Finset.Ico b (c.m - 1), lget (rget (prefS c l) q).bs (q + 1))
      _ ?_ hnp]
  · rw [show c.m - 1 + 1 = c.m by omega]
    refine List.map_congr_left fun b hb => pack_congr LW np _ _ fun l hl => ?_
    have hb' : b < c.m := List.mem_range.1 hb
    have hlen := prefS_length c l (lt_of_lt_of_le hl hnp)
    rw [lget_eq, rankCs_getD _ b (by omega), hlen]
    simp only [rget_eq]
  · intro b hb l _
    have hb' : b < c.m - 1 + 1 := List.mem_range.1 hb
    have e1 : ∑ q ∈ Finset.range b, lget (rget (prefS c l) q).bs q ≤ b * B32 := by
      calc _ ≤ ∑ q ∈ Finset.range b, B32 := Finset.sum_le_sum fun q _ => hterm l q q
        _ = b * B32 := by simp
    have e2 : ∑ q ∈ Finset.Ico b (c.m - 1), lget (rget (prefS c l) q).bs (q + 1) ≤
        (c.m - 1 - b) * B32 := by
      calc _ ≤ ∑ q ∈ Finset.Ico b (c.m - 1), B32 := Finset.sum_le_sum fun q _ => hterm l q (q + 1)
        _ = (c.m - 1 - b) * B32 := by simp
    have e3 : b * B32 ≤ 32 * B32 := Nat.mul_le_mul_right _ (by omega)
    have e4 : (c.m - 1 - b) * B32 ≤ 32 * B32 := Nat.mul_le_mul_right _ (by omega)
    have e5 : 32 * B32 + 32 * B32 < 2 ^ 144 := by norm_num [B32]
    show _ + _ < _
    omega

/-- The prefix vectors of a step, restricted to `np` lanes (from the prefix `0`). -/
theorem mkPV_rep (c : Ctx) (hc : ctxOK c = true) (np : ℕ)
    (hnp : np ≤ cnt (Nat.sub c.m 1) c.recs.length) :
    PVRep c 0 np (PV.mk (preL np (mkPV c.recs (Nat.sub c.m 1)).pos)
      (preL np (mkPV c.recs (Nat.sub c.m 1)).dl) (preL np (mkPV c.recs (Nat.sub c.m 1)).fg)
      (preL np (mkPV c.recs (Nat.sub c.m 1)).cs)) := by
  have hok : COK c := cok_of_ctxOK c hc
  have hnp' : np ≤ cnt (c.m - 1) c.recs.length := hnp
  have hDS : DS < 2 ^ 143 := by unfold DS; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Nat.zero_add]
  · show preL np (slotInc (c.m - 1) (fun k => (rget c.recs k).pos) c.recs.length) = _
    refine mkPV_slot c np hnp' (fun r => r.pos) fun r hr => ?_
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
    rw [hok.pos k hk]
    have := hok.len4096
    exact lt_of_le_of_lt (by omega : k + 1 ≤ 4096) (by norm_num)
  · show preL np (slotInc (c.m - 1) (fun k => (rget c.recs k).dl) c.recs.length) = _
    exact mkPV_slot c np hnp' (fun r => r.dl) fun r hr => lt_of_le_of_lt (hok.rcs r hr).2.1 hDS
  · show preL np (slotInc (c.m - 1) (fun k => bsel (rget c.recs k).fg 1 0) c.recs.length) = _
    rw [mkPV_slot c np hnp' (fun r => bsel r.fg 1 0) fun r _ => by cases r.fg <;> norm_num [bsel]]
    refine List.map_congr_left fun q _ => ?_
    congr 1
    funext l
    cases (rget (prefS c l) q).fg <;> rfl
  · show preL np (rankV _ _) = _
    exact mkPV_cs c (by have := hok.m2; omega) hok.m32 np hnp'
      fun r hr => (hok.rcs r hr).2.2.2.2.2.2.2

/-! ## The cells -/

theorem nbeq_eq (a b : ℕ) : Nat.beq a b = (a == b) := by
  cases h : Nat.beq a b
  · have := Nat.ne_of_beq_eq_false h
    simp [this]
  · have := Nat.eq_of_beq_eq_true h
    simp [this]

theorem bsel_or (x y : Bool) : bsel x true y = (x || y) := by cases x <;> rfl

theorem bsel_andn (x y : Bool) : bsel x false y = (!x && y) := by cases x <;> rfl

theorem hd_drop (S : List ℕ) (k : ℕ) : hd (S.drop k) = lget S k := by
  unfold lget; rw [ldrop_eq]

theorem tl_drop {α : Type} (S : List α) (k : ℕ) : tl (S.drop k) = S.drop (k + 1) := by
  rw [tl_eq, List.tail_drop]

theorem pass_cons (i b : ℕ) (r : SR) (rs : List SR) (l Fl : ℕ) (sl : List ℕ) :
    pass i b (r :: rs) l Fl sl =
      passStep3 r Fl (hd (bsel (Nat.beq l b) (tl sl) sl)) (bsel r.fg false (Nat.beq r.pos i))
        (bsel r.fg true (Nat.beq r.pos i))
        (pass i b rs (l + 1) (Fl * F128) (tl (bsel (Nat.beq l b) (tl sl) sl))) := rfl

theorem pass_gen (i b : ℕ) (S : List ℕ) (rs : List SR) : ∀ l : ℕ,
    pass i b rs l (F128 ^ l) (S.drop (if l ≤ b then l else l + 1)) = PS.mk
      (∑ q ∈ Finset.range rs.length,
        lget S (if l + q < b then l + q else l + q + 1) * (rs.getD q SR0).ev)
      (∑ q ∈ Finset.range rs.length,
        if ((rs.getD q SR0).fg || (rs.getD q SR0).pos == i) = true then 0
        else lget S (if l + q < b then l + q else l + q + 1) * (rs.getD q SR0).dl)
      (∑ q ∈ Finset.range rs.length,
        if ((rs.getD q SR0).fg || (rs.getD q SR0).pos == i) = true then 0
        else lget S (if l + q < b then l + q else l + q + 1) * F128 ^ (l + q))
      (((List.range rs.length).filter fun q => !(rs.getD q SR0).fg && (rs.getD q SR0).pos == i).map
        (fun q => F128 ^ (l + q))) := by
  induction rs with
  | nil => intro l; rfl
  | cons r rs ih =>
    intro l
    have hsl : bsel (Nat.beq l b) (tl (S.drop (if l ≤ b then l else l + 1)))
        (S.drop (if l ≤ b then l else l + 1)) = S.drop (if l < b then l else l + 1) := by
      rw [bsel_eq, nbeq_eq]
      rcases lt_trichotomy l b with h | h | h
      · have h1 : (l == b) = false := by simp; omega
        rw [h1, ite_eq_right (by decide), ite_eq_left h.le, ite_eq_left h]
      · subst h
        simp [tl_drop]
      · have h1 : (l == b) = false := by simp; omega
        rw [h1, ite_eq_right (by decide), ite_eq_right (by omega), ite_eq_right (by omega)]
    have hsl2 : (if l < b then l else l + 1) + 1 = if l + 1 ≤ b then l + 1 else l + 1 + 1 := by
      split_ifs <;> omega
    rw [pass_cons, hsl, hd_drop, tl_drop, hsl2, ← pow_succ, ih (l + 1), bsel_or, bsel_andn, nbeq_eq]
    simp only [passStep3, List.length_cons, Nat.add_eq, Nat.mul_eq]
    congr 1
    · rw [Finset.sum_range_succ', Nat.add_comm (Finset.sum (Finset.range rs.length) _)]
      simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      rw [show l + (q + 1) = l + 1 + q by omega]
    · rw [Finset.sum_range_succ', bsel_eq]
      simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
      have hs : ∑ q ∈ Finset.range rs.length,
          (if ((rs.getD q SR0).fg || (rs.getD q SR0).pos == i) = true then 0
            else lget S (if l + 1 + q < b then l + 1 + q else l + 1 + q + 1) * (rs.getD q SR0).dl) =
          ∑ q ∈ Finset.range rs.length,
          (if ((rs.getD q SR0).fg || (rs.getD q SR0).pos == i) = true then 0
            else lget S (if l + (q + 1) < b then l + (q + 1) else l + (q + 1) + 1) * (rs.getD q SR0).dl) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [show l + (q + 1) = l + 1 + q by omega]
      rw [hs]
      cases (r.fg || r.pos == i) <;> simp [Nat.add_comm]
    · rw [Finset.sum_range_succ', bsel_eq]
      simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
      have hs : ∑ q ∈ Finset.range rs.length,
          (if ((rs.getD q SR0).fg || (rs.getD q SR0).pos == i) = true then 0
            else lget S (if l + 1 + q < b then l + 1 + q else l + 1 + q + 1) * F128 ^ (l + 1 + q)) =
          ∑ q ∈ Finset.range rs.length,
          (if ((rs.getD q SR0).fg || (rs.getD q SR0).pos == i) = true then 0
            else lget S (if l + (q + 1) < b then l + (q + 1) else l + (q + 1) + 1) * F128 ^ (l + (q + 1))) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [show l + (q + 1) = l + 1 + q by omega]
      rw [hs]
      cases (r.fg || r.pos == i) <;> simp [Nat.add_comm]
    · rw [bsel_eq, List.range_succ_eq_map, List.filter_cons, List.filter_map]
      simp only [Function.comp_def, Nat.succ_eq_add_one, List.getD_cons_succ, List.getD_cons_zero]
      have hm : List.map (fun x => F128 ^ (l + (x + 1)))
          (List.filter (fun q => !(rs.getD q SR0).fg && (rs.getD q SR0).pos == i) (List.range rs.length)) =
          List.map (fun q => F128 ^ (l + 1 + q))
          (List.filter (fun q => !(rs.getD q SR0).fg && (rs.getD q SR0).pos == i) (List.range rs.length)) := by
        apply List.map_congr_left
        intro q _
        rw [show l + (q + 1) = l + 1 + q by omega]
      cases (!r.fg && r.pos == i)
      · simp only [Bool.false_eq_true, ↓reduceIte, List.map_map, Function.comp_def, Nat.succ_eq_add_one]
        exact hm.symm
      · simp only [↓reduceIte, List.map_map, List.map_cons, Function.comp_def, Nat.succ_eq_add_one,
          Nat.add_zero]
        rw [hm]

/-- The pass of the prefix records of a cell in closed form: the record `q` takes the slope `q`
below `b`, `q + 1` from `b` on. -/
theorem pass_eq (i b : ℕ) (rs : List SR) (sl : List ℕ) :
    pass i b rs 0 1 sl = PS.mk
      (∑ q ∈ Finset.range rs.length, lget sl (if q < b then q else q + 1) * (rs.getD q SR0).ev)
      (∑ q ∈ Finset.range rs.length,
        if ((rs.getD q SR0).fg || (rs.getD q SR0).pos == i) = true then 0
        else lget sl (if q < b then q else q + 1) * (rs.getD q SR0).dl)
      (∑ q ∈ Finset.range rs.length,
        if ((rs.getD q SR0).fg || (rs.getD q SR0).pos == i) = true then 0
        else lget sl (if q < b then q else q + 1) * F128 ^ q)
      (((List.range rs.length).filter fun q => !(rs.getD q SR0).fg && (rs.getD q SR0).pos == i).map
        (F128 ^ ·)) := by
  have h := pass_gen i b sl rs 0
  rw [ite_eq_left (Nat.zero_le b), List.drop_zero, pow_zero] at h
  simp only [Nat.zero_add] at h
  exact h

theorem adv_eq (i : Nat) (cuts Cs : List Nat) (b : Nat) (k : Nat → List Nat → List Nat → List PD) :
    ∃ (b' : Nat) (cuts' Cs' : List Nat), adv i cuts Cs b k = k b' cuts' Cs' := by
  induction cuts generalizing b Cs with
  | nil => exact ⟨b, [], Cs, rfl⟩
  | cons p ps ih =>
    rcases ih (tl Cs) (Nat.succ b) with ⟨b', cuts', Cs', ih_eq⟩
    have h : adv i (p :: ps) Cs b k = bsel (Nat.ble i p) (k b (p :: ps) Cs) (k b' cuts' Cs') := by
      calc
        adv i (p :: ps) Cs b k = bsel (Nat.ble i p) (k b (p :: ps) Cs) (adv i ps (tl Cs) (Nat.succ b) k) := rfl
        _ = bsel (Nat.ble i p) (k b (p :: ps) Cs) (k b' cuts' Cs') := by rw [ih_eq]
    rw [h]
    rw [bsel_eq]
    split
    · exact ⟨b, p :: ps, Cs, rfl⟩
    · exact ⟨b', cuts', Cs', rfl⟩

/-- One `PD` per cell. -/
theorem pdLoop_length (a1 : ℕ) (lk : ℕ → SV) (rs : List SR) (cells : List SC) (i b : ℕ)
    (cuts Cs : List ℕ) : (pdLoop a1 lk rs cells i b cuts Cs).length = cells.length := by
  induction cells generalizing i b cuts Cs with
  | nil => rfl
  | cons cl rest ih =>
    have h_pdLoop : pdLoop a1 lk rs (cl :: rest) i b cuts Cs =
        adv i cuts Cs b fun b cuts Cs => pdCell a1 lk rs cl (cl :: rest) i b (hd Cs) :: pdLoop a1 lk rs rest (i + 1) b cuts Cs := rfl
    rw [h_pdLoop]
    rcases adv_eq i cuts Cs b (fun b cuts Cs => pdCell a1 lk rs cl (cl :: rest) i b (hd Cs) :: pdLoop a1 lk rs rest (i + 1) b cuts Cs) with ⟨b', cuts', Cs', h⟩
    rw [h]
    simp
    simpa [pdLoop] using ih (i + 1) b' cuts' Cs'

theorem adv_run {β : Type} (i : ℕ) (L C : List ℕ) (k : ℕ → List ℕ → List ℕ → β) :
    ∀ n b, L.length - b = n → b ≤ L.length → (∀ q < b, L.getD q 0 < i) →
    ∃ b', b ≤ b' ∧ b' ≤ L.length ∧ (∀ q < b', L.getD q 0 < i) ∧
      (b' < L.length → i ≤ L.getD b' 0) ∧
      adv i (L.drop b) (C.drop b) b k = k b' (L.drop b') (C.drop b') := by
  intro n
  induction n with
  | zero =>
    intro b hn hb hq
    have hbl : b = L.length := by omega
    refine ⟨b, le_rfl, hb, hq, fun h => absurd h (by omega), ?_⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ n ih =>
    intro b hn hb hq
    have hlt : b < L.length := by omega
    have hd : L.drop b = L.getD b 0 :: L.drop (b + 1) := by
      rw [List.getD_eq_getElem _ _ hlt]
      exact List.drop_eq_getElem_cons hlt
    have hstep : adv i (L.drop b) (C.drop b) b k =
        bsel (Nat.ble i (L.getD b 0)) (k b (L.drop b) (C.drop b))
          (adv i (L.drop (b + 1)) (tl (C.drop b)) (b + 1) k) := by
      rw [hd]; rfl
    rw [hstep, tl_drop, bsel_eq]
    by_cases hp : i ≤ L.getD b 0
    · have hb' : Nat.ble i (L.getD b 0) = true := Nat.ble_eq.mpr hp
      rw [hb', ite_eq_left rfl]
      exact ⟨b, le_rfl, hb, hq, fun _ => hp, rfl⟩
    · have hb' : Nat.ble i (L.getD b 0) = false := by
        cases h : Nat.ble i (L.getD b 0)
        · rfl
        · exact absurd (Nat.ble_eq.mp h) hp
      rw [hb', ite_eq_right (by decide)]
      obtain ⟨b', h1, h2, h3, h4, h5⟩ := ih (b + 1) (by omega) (by omega) (by
        intro q hq'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hq' with h | h
        · exact hq q h
        · subst h; omega)
      exact ⟨b', by omega, h2, h3, h4, h5⟩

theorem countP_sorted (L : List ℕ) (i b : ℕ)
    (hs : ∀ p q, p ≤ q → q < L.length → L.getD p 0 ≤ L.getD q 0) (hb : b ≤ L.length)
    (hq : ∀ q < b, L.getD q 0 < i) (hge : b < L.length → i ≤ L.getD b 0) :
    L.countP (fun p => decide (p < i)) = b := by
  rw [← List.take_append_drop b L, List.countP_append]
  have h1 : (L.take b).countP (fun p => decide (p < i)) = b := by
    rw [List.countP_eq_length.mpr, List.length_take, min_eq_left hb]
    intro x hx
    obtain ⟨q, hq', rfl⟩ := List.getElem_of_mem hx
    rw [List.length_take] at hq'
    have hqb : q < b := lt_of_lt_of_le hq' (min_le_left _ _)
    have := hq q hqb
    rw [List.getD_eq_getElem _ _ (by omega)] at this
    simpa [List.getElem_take] using this
  have h2 : (L.drop b).countP (fun p => decide (p < i)) = 0 := by
    rw [List.countP_eq_zero]
    intro x hx
    obtain ⟨q, hq', rfl⟩ := List.getElem_of_mem hx
    rw [List.length_drop] at hq'
    have hbl : b < L.length := by omega
    have hmono := hs b (b + q) (by omega) (by omega)
    have hgb := hge hbl
    rw [List.getD_eq_getElem _ _ (show b + q < L.length by omega), List.getD_eq_getElem _ _ hbl] at hmono
    rw [List.getD_eq_getElem _ _ hbl] at hgb
    simp only [List.getElem_drop, decide_eq_true_eq, not_lt]
    omega
  rw [h1, h2, Nat.add_zero]

theorem pdLoop_gen (a1 : ℕ) (lk : ℕ → SV) (rs : List SR) (L C : List ℕ)
    (hs : ∀ p q, p ≤ q → q < L.length → L.getD p 0 ≤ L.getD q 0) :
    ∀ (cells : List SC) (j b : ℕ), b ≤ L.length → (∀ q < b, L.getD q 0 < j) →
    ∀ t < cells.length, (pdLoop a1 lk rs cells j b (L.drop b) (C.drop b))[t]? =
      some (pdCell a1 lk rs ((cells.drop t).headD (SC.mk 0 0 0 [] 0 0 0 0 0 0 0)) (cells.drop t)
        (j + t) (L.countP fun p => decide (p < j + t))
        (lget C (L.countP fun p => decide (p < j + t)))) := by
  intro cells
  induction cells with
  | nil => intro j b _ _ t ht; exact absurd ht (by simp)
  | cons cl rest ih =>
    intro j b hb hq t ht
    have hloop : pdLoop a1 lk rs (cl :: rest) j b (L.drop b) (C.drop b) =
        adv j (L.drop b) (C.drop b) b fun b cuts Cs =>
          pdCell a1 lk rs cl (cl :: rest) j b (hd Cs) :: pdLoop a1 lk rs rest (j + 1) b cuts Cs := rfl
    obtain ⟨b', _, h2, h3, h4, h5⟩ := adv_run j L C (fun b cuts Cs =>
          pdCell a1 lk rs cl (cl :: rest) j b (hd Cs) :: pdLoop a1 lk rs rest (j + 1) b cuts Cs)
      (L.length - b) b rfl hb hq
    have hcnt := countP_sorted L j b' hs h2 h3 h4
    rw [hloop, h5]
    cases t with
    | zero =>
      simp only [List.getElem?_cons_zero, List.drop_zero, List.headD_cons, Nat.add_zero, hcnt,
        hd_drop]
    | succ t =>
      rw [List.getElem?_cons_succ, ih (j + 1) b' h2 (fun q hq' => Nat.lt_succ_of_lt (h3 q hq')) t
        (by simp at ht; omega)]
      rw [show j + 1 + t = j + (t + 1) by omega, List.drop_succ_cons]

/-- The cell `i` of the prefix data, for records sorted by position: `pdCell` with `below_i`
(the records before the cell `i`) and the rank sum `C_{below_i}`. -/
theorem pdLoop_get (a1 : ℕ) (lk : ℕ → SV) (rs : List SR) (cells : List SC)
    (hs : ∀ p q, p ≤ q → q < rs.length → (rs.getD p SR0).pos ≤ (rs.getD q SR0).pos)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ cells.length) :
    (pdLoop a1 lk rs cells 1 0 (lmap SR.pos rs) (rankCs rs))[i - 1]? =
      some (pdCell a1 lk rs ((cells.drop (i - 1)).headD (SC.mk 0 0 0 [] 0 0 0 0 0 0 0))
        (cells.drop (i - 1)) i (rs.countP fun r => decide (r.pos < i))
        (lget (rankCs rs) (rs.countP fun r => decide (r.pos < i)))) := by
  have hgd : ∀ q, (rs.map SR.pos).getD q 0 = (rs.getD q SR0).pos := fun q => by
    rw [show (0 : ℕ) = SR0.pos from rfl, List.getD_map]
  have hs' : ∀ p q, p ≤ q → q < (rs.map SR.pos).length →
      (rs.map SR.pos).getD p 0 ≤ (rs.map SR.pos).getD q 0 := by
    intro p q hpq hq
    rw [hgd, hgd]
    exact hs p q hpq (by simpa using hq)
  have h := pdLoop_gen a1 lk rs (rs.map SR.pos) (rankCs rs) hs' cells 1 0 (Nat.zero_le _)
    (fun q hq => absurd hq (Nat.not_lt_zero q)) (i - 1) (by omega)
  rw [List.drop_zero, List.drop_zero, show 1 + (i - 1) = i by omega, List.countP_map] at h
  rw [lmap_eq]
  exact h

theorem listRec_isEmpty (xs : List ℕ) :
    @List.rec ℕ (fun _ => Bool) false (fun _ _ _ => true) xs = !xs.isEmpty := by
  cases xs <;> rfl

theorem filter_isEmpty (p : ℕ → Bool) (xs : List ℕ) : (xs.filter p).isEmpty = !(xs.any p) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.filter_cons, List.any_cons]
    cases p a
    · simpa using ih
    · rfl

theorem pdAt_cell (c : Ctx) (hc : ctxOK c = true) (lk : ℕ → SV) (l i : ℕ) (hi1 : 1 ≤ i)
    (hi : i ≤ c.cells.length) :
    pdAt c lk l i = pdCell c.a1 lk (prefS c l) (cellS c i) (c.cells.drop (i - 1)) i (belowS c l i)
      (lget (rankCs (prefS c l)) (belowS c l i)) := by
  have h := pdLoop_get c.a1 lk (prefS c l) c.cells (prefS_sorted c hc l) i hi1 hi
  unfold pdAt
  rw [List.headD_eq_head?_getD, List.head?_drop]
  show (pdLoop c.a1 lk (prefS c l) c.cells 1 0 (lmap SR.pos (prefS c l))
    (rankCs (prefS c l)))[i - 1]?.getD _ = _
  rw [h]
  rfl

/-- The scalar data of the prefix `l` in the cell `i`. -/
theorem pdAt_eq (c : Ctx) (hc : ctxOK c = true) (lk : ℕ → SV) (l i : ℕ)
    (hl : l < cnt (c.m - 1) c.recs.length) (hi1 : 1 ≤ i) (hi : i ≤ c.cells.length) :
    (pdAt c lk l i).pa = (cellS c i).pa ∧ (pdAt c lk l i).pb = (cellS c i).pb ∧
      (pdAt c lk l i).h = (cellS c i).h ∧ (pdAt c lk l i).h2 = (cellS c i).h2 ∧
      (pdAt c lk l i).a0 = (belowS c l i + 1) * DS2 ∧
      (pdAt c lk l i).sig = lget (lk (idxS c l i)).sl (belowS c l i) ∧
      (pdAt c lk l i).bet = DS * (lk (idxS c l i)).V + (pdAt c lk l i).sig * (cellS c i).pn ∧
      (pdAt c lk l i).sp = ∑ q ∈ Finset.range (c.m - 1), coS c lk l i q * (rget (prefS c l) q).dl ∧
      (pdAt c lk l i).cp = ∑ q ∈ Finset.range (c.m - 1), coS c lk l i q * F128 ^ q ∧
      (pdAt c lk l i).A0 = (pdAt c lk l i).a0 + (c.a1 + (pdAt c lk l i).sig) * (cellS c i).pa ∧
      (pdAt c lk l i).A1 = (pdAt c lk l i).a0 + (c.a1 + (pdAt c lk l i).sig) * (cellS c i).pb ∧
      (pdAt c lk l i).IA = (cellS c i).h2 * (pdAt c lk l i).a0 + (cellS c i).a1sq ∧
      (pdAt c lk l i).ssq = (pdAt c lk l i).sig * (cellS c i).sqd ∧
      (pdAt c lk l i).own = ((List.range (c.m - 1)).filter fun q => ownS c l i q).map (F128 ^ ·) ∧
      (pdAt c lk l i).hasOwn = (List.range (c.m - 1)).any fun q => ownS c l i q := by
  have hok : COK c := cok_of_ctxOK c hc
  have hcell := pdAt_cell c hc lk l i hi1 hi
  have hlen : (prefS c l).length = c.m - 1 := prefS_length c l hl
  have hps := pass_eq i (belowS c l i) (prefS c l) (lk (idxS c l i)).sl
  rw [hlen] at hps
  have hes : (pass i (belowS c l i) (prefS c l) 0 1 (lk (idxS c l i)).sl).es = 0 := by
    rw [hps]
    show (∑ q ∈ Finset.range (c.m - 1), _) = 0
    apply Finset.sum_eq_zero
    intro q _
    have hev : ((prefS c l).getD q SR0).ev = 0 := by
      rcases lt_or_ge q (prefS c l).length with h | h
      · rw [List.getD_eq_getElem _ _ h]
        exact (hok.rcs _ (prefS_mem c l _ (List.getElem_mem h))).1
      · rw [List.getD_eq_default _ _ h]
    rw [hev, Nat.mul_zero]
  have hsp : (pdAt c lk l i).sp = (pass i (belowS c l i) (prefS c l) 0 1 (lk (idxS c l i)).sl).sp := by
    rw [hcell]; rfl
  have hcp : (pdAt c lk l i).cp = (pass i (belowS c l i) (prefS c l) 0 1 (lk (idxS c l i)).sl).cp := by
    rw [hcell]; rfl
  have hown : (pdAt c lk l i).own =
      (pass i (belowS c l i) (prefS c l) 0 1 (lk (idxS c l i)).sl).own := by
    rw [hcell]; rfl
  have hhas : (pdAt c lk l i).hasOwn = @List.rec ℕ (fun _ => Bool) false (fun _ _ _ => true)
      (pass i (belowS c l i) (prefS c l) 0 1 (lk (idxS c l i)).sl).own := by
    rw [hcell]; rfl
  have hbet : (pdAt c lk l i).bet = DS * (lk (idxS c l i)).V + (pdAt c lk l i).sig * (cellS c i).pn +
      (pass i (belowS c l i) (prefS c l) 0 1 (lk (idxS c l i)).sl).es := by
    rw [hcell]; rfl
  have hownL : (pass i (belowS c l i) (prefS c l) 0 1 (lk (idxS c l i)).sl).own =
      ((List.range (c.m - 1)).filter fun q => ownS c l i q).map (F128 ^ ·) := by
    rw [hps]
    show List.map _ (List.filter _ _) = _
    congr 2
    funext q
    unfold ownS
    rw [rget_eq]
  refine ⟨by rw [hcell]; rfl, by rw [hcell]; rfl, by rw [hcell]; rfl, by rw [hcell]; rfl,
    by rw [hcell]; rfl, by rw [hcell]; rfl, ?_, ?_, ?_, by rw [hcell]; rfl, by rw [hcell]; rfl,
    by rw [hcell]; rfl, by rw [hcell]; rfl, ?_, ?_⟩
  · rw [hbet, hes, Nat.add_zero]
  · rw [hsp, hps]
    show (∑ q ∈ Finset.range (c.m - 1), _) = _
    apply Finset.sum_congr rfl
    intro q _
    unfold coS slS
    rw [rget_eq]
    split <;> simp
  · rw [hcp, hps]
    show (∑ q ∈ Finset.range (c.m - 1), _) = _
    apply Finset.sum_congr rfl
    intro q _
    unfold coS slS
    rw [rget_eq]
    split <;> simp
  · rw [hown, hownL]
  · rw [hhas, hownL, listRec_isEmpty, List.isEmpty_map, filter_isEmpty, Bool.not_not]

/-- `below_i` on lanes: the number of slots with `pos < i`. -/
theorem mkCV_below (np d i : ℕ) (P : ℕ → ℕ → ℕ) (hP : ∀ q l, l < np → P q l < 2 ^ 100)
    (hi : i < 2 ^ 100) :
    lfoldr Nat.add 0 (lmap (fun P => ind LW (ge (mkVC np) (bc (mkVC np) i) (Nat.add P (mkVC np).O)))
      ((List.range d).map fun q => pack LW np (P q))) =
      pack LW np fun l => ∑ q ∈ Finset.range d, if P q l < i then 1 else 0 := by
  have hi143 : i < 2 ^ 143 := by
    have h : 2 ^ 100 < 2 ^ 143 := by norm_num
    omega
  have hP143 (q l : ℕ) (hl : l < np) : P q l + 1 < 2 ^ 143 := by
    have h := hP q l hl
    have h2 : 2 ^ 100 < 2 ^ 143 := by norm_num
    omega
  have h_inner (q : ℕ) : ind LW (ge (mkVC np) (bc (mkVC np) i) (Nat.add (pack LW np (P q)) (mkVC np).O)) =
      pack LW np (fun l => if P q l < i then 1 else 0) := by
    calc
      ind LW (ge (mkVC np) (bc (mkVC np) i) (Nat.add (pack LW np (P q)) (mkVC np).O))
          = ind LW (ge (mkVC np) (pack LW np (fun _ => i)) (Nat.add (pack LW np (P q)) (mkVC np).O)) := by
        rw [bc_eq]
      _ = ind LW (ge (mkVC np) (pack LW np (fun _ => i)) (pack LW np (fun l => P q l + 1))) := by
        rw [mkVC_O np, ← pack_add LW np (P q) (fun _ => 1)]
        rfl
      _ = ind LW (pack LW np (fun l => if (P q l + 1) ≤ i then 2 ^ 143 else 0)) := by
        rw [ge_eq np (fun _ => i) (fun l => P q l + 1) (by intro l hl; exact hi143) (fun l hl => hP143 q l hl)]
      _ = pack LW np (fun l => if (P q l + 1) ≤ i then 1 else 0) := by
        rw [ind_eq np (fun l => P q l + 1 ≤ i)]
      _ = pack LW np (fun l => if P q l < i then 1 else 0) := by
        refine pack_congr LW np (fun l => if (P q l + 1) ≤ i then 1 else 0) (fun l => if P q l < i then 1 else 0)
          (fun l hl => ?_)
        by_cases h : P q l < i
        · simp [h, show P q l + 1 ≤ i by omega]
        · simp [h, show ¬ (P q l + 1 ≤ i) by omega]
  rw [lfoldr_eq Nat.add 0, lmap_eq, List.map_map]
  have h_map : ((fun P => ind LW (ge (mkVC np) (bc (mkVC np) i) (P.add (mkVC np).O))) ∘ fun q => pack LW np (P q))
             = (fun q => pack LW np (fun l => if P q l < i then 1 else 0)) := by
    ext q
    simpa using h_inner q
  rw [h_map]
  have h_main : ∀ d, ((List.range d).map (fun q => pack LW np (fun l => if P q l < i then 1 else 0))).sum =
      pack LW np (fun l => ∑ q ∈ Finset.range d, if P q l < i then 1 else 0) := by
    intro d
    induction' d with d ih
    · simp [pack]
    · rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton, ih]
      rw [pack_add]
      have hsum : (fun l => ∑ q ∈ Finset.range (d+1), if P q l < i then 1 else 0) =
                 (fun l => (∑ q ∈ Finset.range d, if P q l < i then 1 else 0) + if P d l < i then 1 else 0) := by
        ext l; rw [Finset.sum_range_succ]
      rw [hsum]
  exact h_main d

theorem zipWith_eq_map_range_add_lget (np d : ℕ) (Cf : ℕ → ℕ → ℕ) (cb : List ℕ) (hcb : cb.length = d + 1) :
    lzipWith (fun C c' => Nat.add C (bc (mkVC np) c'))
      ((List.range (d + 1)).map fun b => pack LW np (Cf b)) cb =
    (List.range (d + 1)).map fun b => pack LW np (fun l => Cf b l + lget cb b) := by
  rw [lzipWith_eq]
  have hlen : List.length (List.zipWith (fun C c' => Nat.add C (bc (mkVC np) c'))
      ((List.range (d + 1)).map fun b => pack LW np (Cf b)) cb) = d + 1 := by
    simp [hcb]
  have hlen' : List.length ((List.range (d + 1)).map fun b => pack LW np (fun l => Cf b l + lget cb b)) = d + 1 := by
    simp
  apply List.ext_getElem
  · rw [hlen, hlen']
  intro i hi hi'
  have hi_len : i < d + 1 := by rwa [hlen] at hi
  have hi_cb : i < cb.length := by rwa [hcb]
  rw [List.getElem_zipWith, List.getElem_map, List.getElem_map]
  rw [List.getElem_range (by simpa [List.length_range] using hi_len)]
  rw [bc_eq, lget_eq, List.getD_eq_getElem _ _ hi_cb]
  simp [pack_add]

/-- The rank of `H_i` on lanes: `C_b + cb[b]` at `b = below_i`. -/
theorem mkCV_pickI (np d : ℕ) (Bf : ℕ → ℕ) (Cf : ℕ → ℕ → ℕ) (cb : List ℕ) (hcb : cb.length = d + 1)
    (hB : ∀ l < np, Bf l ≤ d) (hd : d < 2 ^ 100) (hC : ∀ b ≤ d, ∀ l < np, Cf b l < 2 ^ 140)
    (hcbb : ∀ x ∈ cb, x ≤ B32) :
    pickB (mkVC np) (pack LW np Bf)
        (lzipWith (fun C c' => Nat.add C (bc (mkVC np) c'))
          ((List.range (d + 1)).map fun b => pack LW np (Cf b)) cb) =
      pack LW np fun l => Cf (Bf l) l + lget cb (Bf l) := by
  rw [zipWith_eq_map_range_add_lget np d Cf cb hcb]
  apply pickB_eq np d Bf (fun b l => Cf b l + lget cb b) hB hd
  intro b hb l hl
  have hb_lt : b < cb.length := by
    rw [hcb]
    omega
  have hmem : cb[b] ∈ cb := List.get_mem cb ⟨b, hb_lt⟩
  have hle := hcbb _ hmem
  have hsum : Cf b l + lget cb b < 2 ^ 144 := by
    have hcbb_bound : lget cb b ≤ B32 := by
      rw [lget_eq, List.getD_eq_getElem _ _ hb_lt]
      exact hle
    have h_lt : 2 ^ 140 + B32 < 2 ^ 144 := by
      unfold B32
      nlinarith
    have hsum_lt : Cf b l + lget cb b < 2 ^ 140 + B32 := by
      have hCfb := hC b hb l hl
      nlinarith
    exact lt_trans hsum_lt h_lt
  exact hsum

/-- The masks of the slots: `zero` (forgotten, or own cell `i`) and `own` (own cell `i`, not
forgotten). -/
theorem mkCV_masks (np d i : ℕ) (P : ℕ → ℕ → ℕ) (fg : ℕ → ℕ → Bool) (hi : i < 2 ^ 143)
    (hP : ∀ q l, l < np → P q l < 2 ^ 143) :
    lzipWith (fun E F => Nat.lor E (Nat.shiftLeft F 143))
        (lmap (eqM (mkVC np) i) ((List.range d).map fun q => pack LW np (P q)))
        ((List.range d).map fun q => pack LW np fun l => if fg q l then 1 else 0) =
      (List.range d).map (fun q => pack LW np fun l =>
        if (fg q l || P q l == i) = true then 2 ^ 143 else 0) ∧
    lzipWith (fun E F => Nat.sub E (Nat.land E (Nat.shiftLeft F 143)))
        (lmap (eqM (mkVC np) i) ((List.range d).map fun q => pack LW np (P q)))
        ((List.range d).map fun q => pack LW np fun l => if fg q l then 1 else 0) =
      (List.range d).map (fun q => pack LW np fun l =>
        if (!fg q l && P q l == i) = true then 2 ^ 143 else 0) := by
  refine And.intro ?_ ?_
  · -- first equality
    rw [lmap_eq, List.map_map, lzipWith_eq]
    apply List.ext_getElem
    · simp
    · intro q hq1 hq2
      simp [List.getElem_map] at *
      have h_eqM : eqM (mkVC np) i (pack LW np (P q)) = pack LW np (fun l => if P q l = i then 2 ^ 143 else 0) := by
        apply eqM_eq np i (P q) hi (hP q)
      rw [h_eqM]
      rw [Nat.shiftLeft_eq]
      -- Goal: (pack ...) ||| ((pack ...) * 2 ^ 143) = pack ...
      have h_mul : pack LW np (fun l => if fg q l then 1 else 0) * 2 ^ 143 = pack LW np (fun l => if fg q l then 2 ^ 143 else 0) := by
        rw [mul_comm, pack_const_mul]
        refine pack_congr LW np _ _ fun l hl => ?_
        by_cases hfg : fg q l <;> simp [hfg]
      rw [h_mul]
      -- Goal: (pack ...) ||| (pack ...) = pack ...
      -- Use lor_gm
      have h_lor := lor_gm np (fun l => P q l = i) (fun l => fg q l)
      apply h_lor.trans
      -- Goal: pack ... (fun l => if (P q l = i) ∨ (fg q l = true) then ...) = pack ... (fun l => if (fg q l || P q l == i) = true then ...)
      refine pack_congr LW np _ _ fun l hl => ?_
      by_cases hPq : P q l = i <;> by_cases hfg : fg q l <;> simp [hPq, hfg]
  · -- second equality
    rw [lmap_eq, List.map_map, lzipWith_eq]
    apply List.ext_getElem
    · simp
    · intro q hq1 hq2
      simp [List.getElem_map] at *
      have h_eqM : eqM (mkVC np) i (pack LW np (P q)) = pack LW np (fun l => if P q l = i then 2 ^ 143 else 0) := by
        apply eqM_eq np i (P q) hi (hP q)
      rw [h_eqM]
      rw [Nat.shiftLeft_eq]
      -- Goal: (pack ...) - (Nat.land (pack ...) ((pack ...) * 2 ^ 143)) = pack ...
      have h_mul : pack LW np (fun l => if fg q l then 1 else 0) * 2 ^ 143 = pack LW np (fun l => if fg q l then 2 ^ 143 else 0) := by
        rw [mul_comm, pack_const_mul]
        refine pack_congr LW np _ _ fun l hl => ?_
        by_cases hfg : fg q l <;> simp [hfg]
      rw [h_mul]
      -- Goal: (pack ...) - ((pack ...) &&& (pack ...)) = pack ...
      -- Use land_gm
      have h_land := land_gm np (fun l => P q l = i) (fun l => fg q l)
      calc
        (pack LW np (fun l => if P q l = i then 2 ^ 143 else 0)) -
            ((pack LW np (fun l => if P q l = i then 2 ^ 143 else 0)) &&&
              (pack LW np (fun l => if fg q l = true then 2 ^ 143 else 0))) =
          (pack LW np (fun l => if P q l = i then 2 ^ 143 else 0)) -
            Nat.land (pack LW np (fun l => if P q l = i then 2 ^ 143 else 0)) (pack LW np (fun l => if fg q l = true then 2 ^ 143 else 0)) := rfl
        _ = (pack LW np (fun l => if P q l = i then 2 ^ 143 else 0)) -
            (pack LW np (fun l => if (P q l = i) ∧ (fg q l = true) then 2 ^ 143 else 0)) := by rw [h_land]
        _ = pack LW np (fun l => (if P q l = i then 2 ^ 143 else 0) - (if (P q l = i) ∧ (fg q l = true) then 2 ^ 143 else 0)) := by
          have h_sub : ∀ l < np, (if (P q l = i) ∧ (fg q l) then 2 ^ 143 else 0) ≤ (if P q l = i then 2 ^ 143 else 0) := by
            intro l hl
            by_cases hPq : P q l = i <;> by_cases hfg : fg q l <;> simp [hPq, hfg]
          rw [pack_sub LW np (fun l => if (P q l = i) ∧ (fg q l) then 2 ^ 143 else 0) (fun l => if P q l = i then 2 ^ 143 else 0) h_sub]
        _ = pack LW np (fun l => if fg q l = false ∧ P q l = i then 2 ^ 143 else 0) := by
          refine pack_congr LW np _ _ fun l hl => ?_
          by_cases hPq : P q l = i <;> by_cases hfg : fg q l <;> simp [hPq, hfg]

/-- The coefficients of the slots: `0` on `zero`, else the slot slope. -/
theorem mkCV_co (np d : ℕ) (Bf : ℕ → ℕ) (G : ℕ → ℕ → ℕ) (Z : ℕ → ℕ → Prop)
    [∀ q l, Decidable (Z q l)] (hB : ∀ l < np, Bf l < 2 ^ 100) (hd : d < 2 ^ 100)
    (hG : ∀ f ≤ d, ∀ l < np, G f l < 2 ^ 144) :
    lzipWith (fun Z s => sl Z 0 s)
        ((List.range d).map fun q => pack LW np fun l => if Z q l then 2 ^ 143 else 0)
        (slotS (mkVC np) (pack LW np Bf) ((List.range (d + 1)).map fun f => pack LW np (G f))) =
      (List.range d).map fun q => pack LW np fun l =>
        if Z q l then 0 else G (if q < Bf l then q else q + 1) l := by
  rw [slotS_eq np d Bf G hB hd hG]
  rw [lzipWith_eq (fun Z s => sl Z 0 s) ((List.range d).map fun q => pack LW np fun l => if Z q l then 2 ^ 143 else 0) ((List.range d).map fun q => pack LW np fun l => if q < Bf l then G q l else G (q + 1) l)]
  refine List.ext_getElem ?_ ?_
  · simp
  · intro i hi
    have hi' : i < d := by simpa [List.mem_range] using hi
    have ha : ∀ l < np, (0 : ℕ) < 2 ^ 144 := by
      intro l hl; norm_num
    have hb : ∀ l < np, (fun l' => if i < Bf l' then G i l' else G (i + 1) l') l < 2 ^ 144 := by
      intro l hl
      dsimp
      split_ifs with h
      · apply hG i (by omega) l hl
      · apply hG (i + 1) (by omega) l hl
    have hzero : pack LW np (fun _ => 0) = 0 := by simp [pack]
    simp
    have h := sl_eq np (Z i) (fun _ => 0) (fun l => if i < Bf l then G i l else G (i + 1) l) ha hb
    rw [hzero] at h
    intro hi
    apply h.trans
    refine congrArg (pack LW np) (funext fun l => ?_)
    split_ifs <;> rfl

theorem sum_zipWith_map_range (f : ℕ → ℕ → ℕ) (g h : ℕ → ℕ) (d : ℕ) :
    List.sum (List.zipWith f ((List.range d).map g) ((List.range d).map h)) =
    ∑ q ∈ Finset.range d, f (g q) (h q) := by
  induction' d with d ih
  · simp
  · have hlen : ((List.range d).map g).length = ((List.range d).map h).length := by simp
    rw [List.range_succ, List.map_append, List.map_append]
    simp
    have hzip := List.zipWith_append hlen (f := f) (l₁ := (List.range d).map g) (l₁' := [g d])
      (l₂ := (List.range d).map h) (l₂' := [h d])
    rw [hzip, List.sum_append]
    have hzip_singleton : List.zipWith f [g d] [h d] = [f (g d) (h d)] := by simp
    rw [hzip_singleton, List.sum_singleton]
    rw [ih, Finset.sum_range_succ]

theorem pack_sum (W L k : ℕ) (F : ℕ → ℕ → ℕ) :
    ∑ q ∈ Finset.range k, pack W L (F q) = pack W L fun l => ∑ q ∈ Finset.range k, F q l := by
  unfold pack
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => by rw [Finset.sum_mul]

/-- `S'` on lanes: the coefficients times the weights. -/
theorem mkCV_sp (np d : ℕ) (co w : ℕ → ℕ → ℕ) (hco : ∀ q l, l < np → co q l < 2 ^ 48)
    (hw : ∀ q l, l < np → w q l ≤ DS) :
    lfoldr Nat.add 0 (lzipWith (fun c w => mulv (mkVC np) 37 c w)
        ((List.range d).map fun q => pack LW np (co q)) ((List.range d).map fun q => pack LW np (w q))) =
      pack LW np fun l => ∑ q ∈ Finset.range d, co q l * w q l := by
  rw [lfoldr_eq, lzipWith_eq]
  change List.sum (List.zipWith (fun c w => mulv (mkVC np) 37 c w)
    ((List.range d).map fun q => pack LW np (co q)) ((List.range d).map fun q => pack LW np (w q))) = _
  rw [sum_zipWith_map_range]
  have hQ : 37 ≤ 144 := by decide
  have hsum : (∑ q ∈ Finset.range d, mulv (mkVC np) 37 (pack LW np (co q)) (pack LW np (w q))) =
             (∑ q ∈ Finset.range d, pack LW np (fun l => co q l * w q l)) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    apply mulv_eq' np 37 (co q) (w q) hQ
    · intro l hl j hj
      have hco' := hco q l hl
      have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
      have hpow : 2 ^ j ≤ 2 ^ 37 := Nat.pow_le_pow_right (by omega) (by omega)
      have h85_144 : 85 < 144 := by omega
      calc
        co q l * 2 ^ j < 2 ^ 48 * 2 ^ j := Nat.mul_lt_mul_of_pos_right hco' hpos
        _ ≤ 2 ^ 48 * 2 ^ 37 := Nat.mul_le_mul_left _ hpow
        _ = 2 ^ 85 := by ring
        _ < 2 ^ 144 := Nat.pow_lt_pow_right (by omega) h85_144
    · intro l hl
      have hw' := hw q l hl
      have hDS : DS = 2 ^ 36 := rfl
      rw [hDS] at hw'
      omega
  rw [hsum]
  rw [pack_sum]

theorem lget_le_of_forall (l : List ℕ) (B : ℕ) (h : ∀ x ∈ l, x ≤ B) (i : ℕ) : lget l i ≤ B := by
  rw [lget_eq]
  rcases lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]; exact Nat.zero_le _

theorem cellS_mem (c : Ctx) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ c.cells.length) :
    cellS c i ∈ c.cells := by
  unfold cellS
  rw [List.headD_eq_head?_getD, List.head?_drop, List.getElem?_eq_getElem (by omega)]
  exact List.getElem_mem _

theorem rget_prefS_dl (c : Ctx) (hc : ctxOK c = true) (l q : ℕ) : (rget (prefS c l) q).dl ≤ DS := by
  have hok := cok_of_ctxOK c hc
  rw [rget_eq]
  rcases lt_or_ge q (prefS c l).length with hq | hq
  · rw [List.getD_eq_getElem _ _ hq]; exact (hok.rcs _ (prefS_mem c l _ (List.getElem_mem hq))).2.1
  · rw [List.getD_eq_default _ _ hq]; exact Nat.zero_le _

theorem rankCs_le (rs : List SR) (hrs : ∀ r ∈ rs, ∀ b ∈ r.bs, b ≤ B32) (b : ℕ) :
    lget (rankCs rs) b ≤ rs.length * B32 := by
  have hb : ∀ q i, lget (rs.getD q (SR.mk 0 0 0 0 true 0 0 0 0 [] 0)).bs i ≤ B32 := by
    intro q i
    rw [lget_eq]
    have hmem : ∀ x ∈ (rs.getD q (SR.mk 0 0 0 0 true 0 0 0 0 [] 0)).bs, x ≤ B32 := by
      intro x hx
      rcases lt_or_ge q rs.length with hq | hq
      · rw [List.getD_eq_getElem _ _ hq] at hx
        exact hrs _ (List.getElem_mem hq) _ hx
      · rw [List.getD_eq_default _ _ hq] at hx
        simp at hx
    rcases lt_or_ge i (rs.getD q (SR.mk 0 0 0 0 true 0 0 0 0 [] 0)).bs.length with hi | hi
    · rw [List.getD_eq_getElem _ _ hi]; exact hmem _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ hi]; exact Nat.zero_le _
  rw [lget_eq]
  rcases le_or_gt b rs.length with h | h
  · rw [rankCs_getD rs b h]
    have e1 : ∑ q ∈ Finset.range b, lget (rs.getD q (SR.mk 0 0 0 0 true 0 0 0 0 [] 0)).bs q ≤ b * B32 := by
      calc _ ≤ ∑ q ∈ Finset.range b, B32 := Finset.sum_le_sum fun q _ => hb q q
        _ = b * B32 := by simp
    have e2 : ∑ q ∈ Finset.Ico b rs.length, lget (rs.getD q (SR.mk 0 0 0 0 true 0 0 0 0 [] 0)).bs (q + 1) ≤
        (rs.length - b) * B32 := by
      calc _ ≤ ∑ q ∈ Finset.Ico b rs.length, B32 := Finset.sum_le_sum fun q _ => hb q (q + 1)
        _ = (rs.length - b) * B32 := by simp
    have : b * B32 + (rs.length - b) * B32 = rs.length * B32 := by
      rw [← Nat.add_mul]; congr 1; omega
    omega
  · rw [List.getD_eq_default _ _ (by rw [rankCs_length]; omega)]
    exact Nat.zero_le _

theorem idxS_le (c : Ctx) (hc : ctxOK c = true) (l i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ c.cells.length) :
    idxS c l i ≤ (prefS c l).length * B32 + B32 := by
  have hok := cok_of_ctxOK c hc
  unfold idxS
  have h1 := rankCs_le (prefS c l)
    (fun r hr b hb => (hok.rcs r (prefS_mem c l r hr)).2.2.2.2.2.2.2 b hb) (belowS c l i)
  have h2 := lget_le_of_forall (cellS c i).cb B32
    (hok.cell _ (cellS_mem c i hi1 hi)).2.2.2.2.2.2.2.2.2.2 (belowS c l i)
  omega

theorem rget_prefS_pos (c : Ctx) (hc : ctxOK c = true) (l q : ℕ) :
    (rget (prefS c l) q).pos ≤ c.recs.length := by
  have hok := cok_of_ctxOK c hc
  rw [rget_eq]
  rcases lt_or_ge q (prefS c l).length with hq | hq
  · rw [List.getD_eq_getElem _ _ hq]
    obtain ⟨k, hk, he⟩ := List.getElem_of_mem (prefS_mem c l _ (List.getElem_mem hq))
    rw [← he, hok.pos k hk]
    omega
  · rw [List.getD_eq_default _ _ hq]
    exact Nat.zero_le _

theorem sum_ind_countP (rs : List SR) (i : ℕ) :
    ∑ q ∈ Finset.range rs.length, (if (rs.getD q SR0).pos < i then 1 else 0) =
      rs.countP fun r => decide (r.pos < i) := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.countP_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]
    by_cases h : r.pos < i <;> simp [h]

/-! ## Windows of prefix vectors -/

/-- The fields of the prefix `p` that the prefix vectors carry are below `2 ^ 144`. -/
theorem prefS_lane_lt (c : Ctx) (hc : ctxOK c = true) (p : ℕ)
    (hp : p < cnt (c.m - 1) c.recs.length) :
    (∀ q, (rget (prefS c p) q).pos < 2 ^ 144) ∧ (∀ q, (rget (prefS c p) q).dl < 2 ^ 144) ∧
      ∀ b, lget (rankCs (prefS c p)) b < 2 ^ 144 := by
  have hok := cok_of_ctxOK c hc
  refine ⟨fun q => ?_, fun q => ?_, fun b => ?_⟩
  · exact lt_of_le_of_lt (le_trans (rget_prefS_pos c hc p q) hok.len4096) (by norm_num)
  · exact lt_of_le_of_lt (rget_prefS_dl c hc p q) (by unfold DS; norm_num)
  · have h1 := rankCs_le (prefS c p)
      (fun r hr b hb => (hok.rcs r (prefS_mem c p r hr)).2.2.2.2.2.2.2 b hb) b
    rw [prefS_length c p hp] at h1
    have h2 : (c.m - 1) * B32 ≤ 32 * B32 := Nat.mul_le_mul_right _ (by have := hok.m32; omega)
    exact lt_of_le_of_lt (le_trans h1 h2) (by norm_num [B32])

/-- The `n` lanes from the lane `b` of a list of packed vectors. -/
theorem preL_drp_eq {ι : Type} (np b n : ℕ) (F : ι → ℕ → ℕ) (xs : List ι)
    (hF : ∀ i ∈ xs, ∀ l < np, F i l < 2 ^ 144) (h : b + n ≤ np) :
    preL n (lmap (drp LW b) (xs.map fun i => pack LW np (F i))) =
      xs.map fun i => pack LW n fun l => F i (b + l) := by
  unfold preL
  rw [lmap_eq, lmap_eq, List.map_map, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  show pre LW n (drp LW b (pack LW np (F i))) = _
  rw [drp_pack LW np b (F i) (hF i hi),
    pre_pack LW (np - b) n _ (fun l hl => hF i hi _ (by omega)) (by omega)]
  exact pack_congr _ _ _ _ fun l _ => by rw [Nat.add_comm]

/-- A window of a vector cut to its first `N` lanes is the window of the vector. -/
theorem win_pre (x N a w : ℕ) (h : a + w ≤ N) :
    pre LW w (drp LW a (pre LW N x)) = pre LW w (drp LW a x) := by
  have hpre : ∀ k P, pre LW k P = P % 2 ^ (LW * k) := by
    intro k P
    unfold pre
    simp [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod]
  have hdrp : ∀ P, drp LW a P = P / 2 ^ (LW * a) := fun P => Nat.shiftRight_eq_div_pow _ _
  rw [hpre, hpre, hdrp, hdrp, hpre]
  have e : 2 ^ (LW * N) = 2 ^ (LW * a) * 2 ^ (LW * (N - a)) := by
    rw [← pow_add, ← Nat.mul_add, Nat.add_sub_cancel' (by omega)]
  rw [e, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.mul_le_mul_left _ (by omega)))]

/-- The window lemma `win_pre` on a list of vectors. -/
theorem winL_preL (L : List ℕ) (N a w : ℕ) (h : a + w ≤ N) :
    preL w (lmap (drp LW a) (preL N L)) = preL w (lmap (drp LW a) L) := by
  unfold preL
  simp only [lmap_eq, List.map_map]
  exact List.map_congr_left fun x _ => win_pre x N a w h

/-- Prefix vectors restricted to their first lanes. -/
theorem PVRep_pre (c : Ctx) (hc : ctxOK c = true) (a np n : ℕ) (hn : n ≤ np)
    (hnp : a + np ≤ cnt (c.m - 1) c.recs.length) (pv : PV) (hpv : PVRep c a np pv) :
    PVRep c a n (PV.mk (preL n pv.pos) (preL n pv.dl) (preL n pv.fg) (preL n pv.cs)) := by
  have hB := fun l (hl : l < np) => prefS_lane_lt c hc (a + l) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · show preL n pv.pos = _
    rw [hpv.pos]
    exact preL_eq np n (fun q l => (rget (prefS c (a + l)) q).pos) _
      (fun q _ l hl => (hB l hl).1 q) hn
  · show preL n pv.dl = _
    rw [hpv.dl]
    exact preL_eq np n (fun q l => (rget (prefS c (a + l)) q).dl) _
      (fun q _ l hl => (hB l hl).2.1 q) hn
  · show preL n pv.fg = _
    rw [hpv.fg]
    exact preL_eq np n (fun q l => if (rget (prefS c (a + l)) q).fg then 1 else 0) _
      (fun q _ l _ => by split <;> norm_num) hn
  · show preL n pv.cs = _
    rw [hpv.cs]
    exact preL_eq np n (fun b l => lget (rankCs (prefS c (a + l))) b) _
      (fun b _ l hl => (hB l hl).2.2 b) hn

/-- A window of prefix vectors: the `n` lanes from the lane `b` are the prefixes from `a + b`. -/
theorem PVRep_win (c : Ctx) (hc : ctxOK c = true) (a np b n : ℕ) (hbn : b + n ≤ np)
    (hnp : a + np ≤ cnt (c.m - 1) c.recs.length) (pv : PV) (hpv : PVRep c a np pv) :
    PVRep c (a + b) n (PV.mk (preL n (lmap (drp LW b) pv.pos)) (preL n (lmap (drp LW b) pv.dl))
      (preL n (lmap (drp LW b) pv.fg)) (preL n (lmap (drp LW b) pv.cs))) := by
  have hB := fun l (hl : l < np) => prefS_lane_lt c hc (a + l) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · show preL n (lmap (drp LW b) pv.pos) = _
    rw [hpv.pos, preL_drp_eq np b n (fun q l => (rget (prefS c (a + l)) q).pos) _
      (fun q _ l hl => (hB l hl).1 q) hbn]
    simp only [Nat.add_assoc]
  · show preL n (lmap (drp LW b) pv.dl) = _
    rw [hpv.dl, preL_drp_eq np b n (fun q l => (rget (prefS c (a + l)) q).dl) _
      (fun q _ l hl => (hB l hl).2.1 q) hbn]
    simp only [Nat.add_assoc]
  · show preL n (lmap (drp LW b) pv.fg) = _
    rw [hpv.fg, preL_drp_eq np b n (fun q l => if (rget (prefS c (a + l)) q).fg then 1 else 0) _
      (fun q _ l _ => by split <;> norm_num) hbn]
    simp only [Nat.add_assoc]
  · show preL n (lmap (drp LW b) pv.cs) = _
    rw [hpv.cs, preL_drp_eq np b n (fun b l => lget (rankCs (prefS c (a + l))) b) _
      (fun b _ l hl => (hB l hl).2.2 b) hbn]
    simp only [Nat.add_assoc]

/-- `below_i` and the rank of `H_i` of the cell `i` on the lanes (`mkCV` down to `mkCV.mkCV3`). -/
theorem mkCV_BI (c : Ctx) (hc : ctxOK c = true) (hx : CtxX c) (hi : ℕ)
    (hhi : hi ≤ c.recs.length) (a np : ℕ) (hnp : a + np ≤ cnt (Nat.sub c.m 1) hi) (pv : PV)
    (hpv : PVRep c a np pv) (i : ℕ) (hi1 : 1 ≤ i) (hii : i ≤ hi) :
    lfoldr Nat.add 0 (lmap (fun P => ind LW (ge (mkVC np) (bc (mkVC np) i) (Nat.add P (mkVC np).O)))
        pv.pos) = (pack LW np fun l => belowS c (a + l) i) ∧
      pickB (mkVC np) (lfoldr Nat.add 0 (lmap (fun P => ind LW (ge (mkVC np) (bc (mkVC np) i)
          (Nat.add P (mkVC np).O))) pv.pos))
        (lzipWith (fun C c' => Nat.add C (bc (mkVC np) c')) pv.cs (cellS c i).cb) =
        (pack LW np fun l => idxS c (a + l) i) ∧
      ∀ l < np, idxS c (a + l) i < 2 ^ 40 := by
  have hok' : COK c := cok_of_ctxOK c hc
  have hm2 : 2 ≤ c.m := hok'.m2
  have hm32 : c.m ≤ 32 := hok'.m32
  have hlen := hok'.len
  have h4096 := hok'.len4096
  have hic : i ≤ c.cells.length := by omega
  have hcl : cellS c i ∈ c.cells := cellS_mem c i hi1 hic
  have hcb : (cellS c i).cb.length = c.m := (hx.2.2 _ hcl).2
  have hnpR : a + np ≤ cnt (c.m - 1) c.recs.length := le_trans hnp (cnt_mono _ hhi)
  have hlR : ∀ l < np, a + l < cnt (c.m - 1) c.recs.length := fun l hl => by omega
  have hplen : ∀ l < np, (prefS c (a + l)).length = c.m - 1 := fun l hl =>
    prefS_length c (a + l) (hlR l hl)
  have hmr : List.range c.m = List.range (c.m - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
  have hd100 : c.m - 1 < 2 ^ 100 := lt_of_le_of_lt (by omega : c.m - 1 ≤ 32) (by norm_num)
  have hB32 : B32 = 2 ^ 32 := by unfold B32; norm_num
  have hbelow : ∀ l < np, belowS c (a + l) i ≤ c.m - 1 := fun l hl => by
    rw [← hplen l hl]; exact List.countP_le_length
  have hidx : ∀ l < np, idxS c (a + l) i < 2 ^ 40 := by
    intro l hl
    have h1 := idxS_le c hc (a + l) i hi1 hic
    rw [hplen l hl, hB32] at h1
    have h2 : (c.m - 1) * 2 ^ 32 ≤ 31 * 2 ^ 32 := Nat.mul_le_mul_right _ (by omega)
    exact lt_of_le_of_lt h1 (by omega)
  have hrank : ∀ b, ∀ l < np, lget (rankCs (prefS c (a + l))) b < 2 ^ 140 := by
    intro b l hl
    have h1 := rankCs_le (prefS c (a + l))
      (fun r hr b hb => (hok'.rcs r (prefS_mem c (a + l) r hr)).2.2.2.2.2.2.2 b hb) b
    rw [hplen l hl, hB32] at h1
    have h2 : (c.m - 1) * 2 ^ 32 ≤ 31 * 2 ^ 32 := Nat.mul_le_mul_right _ (by omega)
    exact lt_of_le_of_lt h1 (by omega)
  have hiB : i ≤ 4096 := by omega
  have hBp : lfoldr Nat.add 0 (lmap (fun P => ind LW (ge (mkVC np) (bc (mkVC np) i)
      (Nat.add P (mkVC np).O))) pv.pos) = pack LW np fun l => belowS c (a + l) i := by
    rw [hpv.pos, mkCV_below np (c.m - 1) i (fun q l => (rget (prefS c (a + l)) q).pos)
      (fun q l _ => lt_of_le_of_lt (rget_prefS_pos c hc (a + l) q) (by omega)) (by omega)]
    apply pack_congr
    intro l hl
    have h := sum_ind_countP (prefS c (a + l)) i
    rw [hplen l hl] at h
    simp only [rget_eq]
    exact h
  refine ⟨hBp, ?_, hidx⟩
  rw [hBp, hpv.cs, hmr]
  exact mkCV_pickI np (c.m - 1) (fun l => belowS c (a + l) i)
    (fun b l => lget (rankCs (prefS c (a + l))) b)
    (cellS c i).cb (by rw [hcb]; omega) hbelow hd100 (fun b _ l hl => hrank b l hl)
    (hok'.cell _ hcl).2.2.2.2.2.2.2.2.2.2

/-- The cell `i` from `mkCV.mkCV4` on, given `below_i` and the rank of `H_i` on the lanes and the
lookups `gv`, `gs` of `H_i`: the part shared by `mkCV` and the window cells. -/
theorem mkCV4_rep (c : Ctx) (hc : ctxOK c = true) (_hx : CtxX c) (lk : ℕ → SV) (hi : ℕ)
    (hhi : hi ≤ c.recs.length) (a np : ℕ) (hnp : a + np ≤ cnt (Nat.sub c.m 1) hi) (pv : PV)
    (hpv : PVRep c a np pv) (i : ℕ) (hi1 : 1 ≤ i) (hii : i ≤ hi) (B I : ℕ)
    (hB0 : B = pack LW np fun l => belowS c (a + l) i) (hI0 : I = pack LW np fun l => idxS c (a + l) i)
    (ok : Bool) (gv : ℕ) (gs : List ℕ) (hgv0 : gv = pack LW np fun l => (lk (idxS c (a + l) i)).V)
    (hgs0 : gs = (List.range c.m).map fun f => pack LW np fun l => lget (lk (idxS c (a + l) i)).sl f)
    (hlkb : ∀ l < np, (lk (idxS c (a + l) i)).V < 2 ^ 48 ∧
      ∀ f < c.m, lget (lk (idxS c (a + l) i)).sl f < 2 ^ 48) :
    CVRep c lk a np i (mkCV.mkCV4 (mkVC np) pv c.a1 i (cellS c i) B I ok gv gs) := by
  have hok' : COK c := cok_of_ctxOK c hc
  have hm2 : 2 ≤ c.m := hok'.m2
  have hm32 : c.m ≤ 32 := hok'.m32
  have hlen := hok'.len
  have h4096 := hok'.len4096
  have hic : i ≤ c.cells.length := by omega
  have hnpR : a + np ≤ cnt (c.m - 1) c.recs.length := le_trans hnp (cnt_mono _ hhi)
  have hlR : ∀ l < np, a + l < cnt (c.m - 1) c.recs.length := fun l hl => by omega
  have hplen : ∀ l < np, (prefS c (a + l)).length = c.m - 1 := fun l hl =>
    prefS_length c (a + l) (hlR l hl)
  have hmr : List.range c.m = List.range (c.m - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
  have hd100 : c.m - 1 < 2 ^ 100 := lt_of_le_of_lt (by omega : c.m - 1 ≤ 32) (by norm_num)
  have hbelow : ∀ l < np, belowS c (a + l) i ≤ c.m - 1 := fun l hl => by
    rw [← hplen l hl]; exact List.countP_le_length
  set cv := mkCV.mkCV4 (mkVC np) pv c.a1 i (cellS c i) B I ok gv gs with hcv
  have hBp : cv.B = pack LW np fun l => belowS c (a + l) i := hB0
  have hIp : cv.idx = pack LW np fun l => idxS c (a + l) i := hI0
  have hgv : cv.gv = pack LW np fun l => (lk (idxS c (a + l) i)).V := hgv0
  have hgs : cv.gs = (List.range c.m).map fun f =>
      pack LW np fun l => lget (lk (idxS c (a + l) i)).sl f := hgs0
  -- `sigma`
  have hsig : cv.sig = pack LW np fun l => (pdAt c lk (a + l) i).sig := by
    show pickB (mkVC np) cv.B cv.gs = _
    rw [hBp, hgs, hmr, pickB_eq np (c.m - 1) (fun l => belowS c (a + l) i)
      (fun f l => lget (lk (idxS c (a + l) i)).sl f) hbelow hd100
      (fun b hb l hl => lt_trans ((hlkb l hl).2 b (by omega)) (by norm_num))]
    apply pack_congr
    intro l hl
    obtain ⟨-, -, -, -, -, hs, -⟩ := pdAt_eq c hc lk (a + l) i (hlR l hl) hi1 hic
    exact hs.symm
  -- the masks
  obtain ⟨hzero, hownm⟩ := mkCV_masks np (c.m - 1) i (fun q l => (rget (prefS c (a + l)) q).pos)
    (fun q l => (rget (prefS c (a + l)) q).fg) (by omega)
    (fun q l _ => lt_of_le_of_lt (rget_prefS_pos c hc (a + l) q) (by omega))
  have hown : cv.own = (List.range (c.m - 1)).map fun q =>
      pack LW np fun l => if ownS c (a + l) i q then 2 ^ 143 else 0 := by
    show lzipWith (fun E F => Nat.sub E (Nat.land E (Nat.shiftLeft F 143)))
      (lmap (eqM (mkVC np) i) pv.pos) pv.fg = _
    rw [hpv.pos, hpv.fg]
    exact hownm
  -- the coefficients
  have hco : cv.co = (List.range (c.m - 1)).map fun q => pack LW np fun l => coS c lk (a + l) i q := by
    show lzipWith (fun Z s => sl Z 0 s) (lzipWith (fun E F => Nat.lor E (Nat.shiftLeft F 143))
      (lmap (eqM (mkVC np) i) pv.pos) pv.fg) (slotS (mkVC np) cv.B cv.gs) = _
    rw [hpv.pos, hpv.fg, hzero, hBp, hgs, hmr]
    exact mkCV_co np (c.m - 1) (fun l => belowS c (a + l) i) (fun f l => lget (lk (idxS c (a + l) i)).sl f)
      (fun q l => ((rget (prefS c (a + l)) q).fg || (rget (prefS c (a + l)) q).pos == i) = true)
      (fun l hl => lt_of_le_of_lt (hbelow l hl) hd100) hd100
      (fun f hf l hl => lt_trans ((hlkb l hl).2 f (by omega)) (by norm_num))
  have hcoB : ∀ q l, l < np → coS c lk (a + l) i q < 2 ^ 48 := by
    intro q l hl
    unfold coS
    split
    · norm_num
    · rename_i hz
      unfold slS
      rcases lt_or_ge q (c.m - 1) with hq | hq
      · apply (hlkb l hl).2
        split <;> omega
      · exfalso
        apply hz
        rw [rget_eq, List.getD_eq_default _ _ (by rw [hplen l hl]; exact hq)]
        rfl
  -- `a0`, `kk`, `beta`, `S'`
  have ha0 : cv.a0 = pack LW np fun l => (pdAt c lk (a + l) i).a0 := by
    show Nat.mul DS2 (Nat.add cv.B (mkVC np).O) = _
    rw [hBp, mkVC_O, Nat.add_eq, pack_add, Nat.mul_eq, pack_const_mul]
    apply pack_congr
    intro l hl
    obtain ⟨-, -, -, -, h, -⟩ := pdAt_eq c hc lk (a + l) i (hlR l hl) hi1 hic
    rw [h, Nat.mul_comm]
  have hkk : cv.kk = pack LW np fun l => c.a1 + (pdAt c lk (a + l) i).sig := by
    show Nat.add (bc (mkVC np) c.a1) cv.sig = _
    rw [hsig, bc_eq, Nat.add_eq, pack_add]
  have hbet : cv.bet = pack LW np fun l => (pdAt c lk (a + l) i).bet := by
    show Nat.add (Nat.mul DS cv.gv) (Nat.mul (cellS c i).pn cv.sig) = _
    rw [hgv, hsig, Nat.mul_eq, Nat.mul_eq, Nat.add_eq, pack_const_mul, pack_const_mul, pack_add]
    apply pack_congr
    intro l hl
    obtain ⟨-, -, -, -, -, -, h, -⟩ := pdAt_eq c hc lk (a + l) i (hlR l hl) hi1 hic
    rw [h, Nat.mul_comm (cellS c i).pn]
  have hsp : cv.sp = pack LW np fun l => (pdAt c lk (a + l) i).sp := by
    show lfoldr Nat.add 0 (lzipWith (fun x y => mulv (mkVC np) 37 x y) cv.co pv.dl) = _
    rw [hco, hpv.dl, mkCV_sp np (c.m - 1) (fun q l => coS c lk (a + l) i q)
      (fun q l => (rget (prefS c (a + l)) q).dl) hcoB (fun q l _ => rget_prefS_dl c hc (a + l) q)]
    apply pack_congr
    intro l hl
    obtain ⟨-, -, -, -, -, -, -, h, -⟩ := pdAt_eq c hc lk (a + l) i (hlR l hl) hi1 hic
    rw [h]
  -- `A0`, `A1`, `IA`, `ssq`
  have hA0 : cv.A0 = pack LW np fun l => (pdAt c lk (a + l) i).A0 := by
    show Nat.add cv.a0 (Nat.mul (cellS c i).pa cv.kk) = _
    rw [ha0, hkk, Nat.mul_eq, Nat.add_eq, pack_const_mul, pack_add]
    apply pack_congr
    intro l hl
    obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := pdAt_eq c hc lk (a + l) i (hlR l hl) hi1 hic
    rw [h, Nat.mul_comm (cellS c i).pa]
  have hA1 : cv.A1 = pack LW np fun l => (pdAt c lk (a + l) i).A1 := by
    show Nat.add cv.a0 (Nat.mul (cellS c i).pb cv.kk) = _
    rw [ha0, hkk, Nat.mul_eq, Nat.add_eq, pack_const_mul, pack_add]
    apply pack_congr
    intro l hl
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := pdAt_eq c hc lk (a + l) i (hlR l hl) hi1 hic
    rw [h, Nat.mul_comm (cellS c i).pb]
  have hIA : cv.IA = pack LW np fun l => (pdAt c lk (a + l) i).IA := by
    show Nat.add (Nat.mul (cellS c i).h2 cv.a0) (bc (mkVC np) (cellS c i).a1sq) = _
    rw [ha0, bc_eq, Nat.mul_eq, Nat.add_eq, pack_const_mul, pack_add]
    apply pack_congr
    intro l hl
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := pdAt_eq c hc lk (a + l) i (hlR l hl) hi1 hic
    rw [h]
  have hssq : cv.ssq = pack LW np fun l => (pdAt c lk (a + l) i).ssq := by
    show Nat.mul (cellS c i).sqd cv.sig = _
    rw [hsig, Nat.mul_eq, pack_const_mul]
    apply pack_congr
    intro l hl
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := pdAt_eq c hc lk (a + l) i (hlR l hl) hi1 hic
    rw [h, Nat.mul_comm]
  exact ⟨rfl, rfl, rfl, rfl, rfl, hBp, hsig, hbet, hsp, hco, hown, ha0, hkk, hA0, hA1, hIA, hssq,
    hIp, hgv, hgs⟩

/-- The lanes of the cell `i` (`mkCV`) are the scalar data of the prefixes, when its compaction
test passes; `lk` is read through the fields `FV`, `FS` of the first `NS` states of the table of
time `t + 1`. -/
theorem mkCV_rep (c : Ctx) (hc : ctxOK c = true) (hx : CtxX c) (lk : ℕ → SV) (hi : ℕ)
    (hhi : hi ≤ c.recs.length) (a np : ℕ) (hnp : a + np ≤ cnt (Nat.sub c.m 1) hi) (pv : PV)
    (hpv : PVRep c a np pv) (NS : ℕ) (hNS : NS ≤ B32)
    (hlk : ∀ s < NS, (lk s).V < 2 ^ 48 ∧ ∀ f < c.m, lget (lk s).sl f < 2 ^ 48)
    (FV : ℕ) (hFV : FV = pack LW NS fun s => (lk s).V) (FS : List ℕ)
    (hFS : FS = (List.range c.m).map fun f => pack LW NS fun s => lget (lk s).sl f)
    (i : ℕ) (hi1 : 1 ≤ i) (hii : i ≤ hi)
    (hok : (mkCV (mkVC np) pv NS c.a1 FV FS i (cellS c i)).ok = true) :
    CVRep c lk a np i (mkCV (mkVC np) pv NS c.a1 FV FS i (cellS c i)) := by
  obtain ⟨hB, hI, hidx⟩ := mkCV_BI c hc hx hi hhi a np hnp pv hpv i hi1 hii
  have hB32 : B32 = 2 ^ 32 := by unfold B32; norm_num
  set cv := mkCV (mkVC np) pv NS c.a1 FV FS i (cellS c i) with hcv
  have hIp : cv.idx = pack LW np fun l => idxS c (a + l) i := hI
  have hrt : (mkRt NS np (pack LW np fun l => idxS c (a + l) i)).ok = true := by
    have e : cv.ok = (mkRt NS (mkVC np).n cv.idx).ok := rfl
    rw [e, hIp] at hok
    exact hok
  obtain ⟨hidxNS, hroute⟩ := route_spec NS np (fun l => idxS c (a + l) i)
    (lt_of_le_of_lt hNS (by rw [hB32]; norm_num)) hidx hrt
  have hgv : cv.gv = pack LW np fun l => (lk (idxS c (a + l) i)).V := by
    show route (mkRt NS (mkVC np).n cv.idx) FV = _
    rw [hIp, hFV]
    exact hroute (fun s => (lk s).V) (fun s hs => lt_trans (hlk s hs).1 (by norm_num))
  have hgs : cv.gs = (List.range c.m).map fun f =>
      pack LW np fun l => lget (lk (idxS c (a + l) i)).sl f := by
    show lmap (route (mkRt NS (mkVC np).n cv.idx)) FS = _
    rw [hIp, hFS, lmap_eq, List.map_map]
    apply List.map_congr_left
    intro f hf
    rw [List.mem_range] at hf
    exact hroute (fun s => lget (lk s).sl f) (fun s hs => lt_trans ((hlk s hs).2 f hf) (by norm_num))
  exact mkCV4_rep c hc hx lk hi hhi a np hnp pv hpv i hi1 hii cv.B cv.idx hB hI cv.ok cv.gv cv.gs
    hgv hgs fun l hl => hlk _ (hidxNS l hl)

/-- The lookups of `H_i` from the source lane `s0` on (the window cells): when every rank is at
least `s0` and the compaction of the ranks less `s0` passes, the routes from the lane `s0` of a
table read it at the ranks. -/
theorem route_spec_off (NS ND s0 : ℕ) (Iv : ℕ → ℕ) (hNS : NS < 2 ^ 40) (hIv : ∀ j < ND, Iv j < 2 ^ 40)
    (hs0 : s0 < 2 ^ 143)
    (hge : allGe (mkVC ND).G (pack LW ND Iv) (bc (mkVC ND) s0) = true)
    (hok : (mkRt (Nat.sub NS s0) ND (Nat.sub (pack LW ND Iv) (bc (mkVC ND) s0))).ok = true) :
    (∀ j < ND, Iv j < NS) ∧ ∀ f : ℕ → ℕ, (∀ s < NS, f s < 2 ^ 100) →
      route (mkRt (Nat.sub NS s0) ND (Nat.sub (pack LW ND Iv) (bc (mkVC ND) s0)))
        (drp LW s0 (pack LW NS f)) = pack LW ND fun j => f (Iv j) := by
  rw [bc_eq] at hge hok ⊢
  have hle : ∀ j < ND, s0 ≤ Iv j :=
    (allGe_eq ND Iv (fun _ => s0) (fun j hj => lt_trans (hIv j hj) (by norm_num)) fun _ _ => hs0).1 hge
  have esub : Nat.sub (pack LW ND Iv) (pack LW ND fun _ => s0) = pack LW ND fun j => Iv j - s0 :=
    pack_sub LW ND (fun _ => s0) Iv hle
  rw [esub] at hok ⊢
  obtain ⟨hlt, hroute⟩ := route_spec (Nat.sub NS s0) ND (fun j => Iv j - s0)
    (lt_of_le_of_lt (Nat.sub_le _ _) hNS) (fun j hj => lt_of_le_of_lt (Nat.sub_le _ _) (hIv j hj)) hok
  refine ⟨fun j hj => ?_, fun f hf => ?_⟩
  · have h1 := hlt j hj
    have h2 := hle j hj
    show Iv j < NS
    have : Iv j - s0 < NS - s0 := h1
    omega
  · rw [drp_pack LW NS s0 f (fun s hs => lt_trans (hf s hs) (by norm_num [LW]))]
    have := hroute (fun s => f (s + s0)) (fun s hs => hf _ (by
      have : s < NS - s0 := hs
      omega))
    refine this.trans (pack_congr _ _ _ _ fun j hj => ?_)
    show f (Iv j - s0 + s0) = f (Iv j)
    rw [Nat.sub_add_cancel (hle j hj)]

/-- A cell restricted to its first lanes. -/
theorem preCV_rep (c : Ctx) (hc : ctxOK c = true) (hx : CtxX c) (lk : ℕ → SV)
    (hlk : ∀ idx, (lk idx).V < 2 ^ 48 ∧ ∀ f, lget (lk idx).sl f < 2 ^ 48) (a np n i : ℕ)
    (hn : n ≤ np) (hnp : a + np ≤ cnt (c.m - 1) c.recs.length) (hi1 : 1 ≤ i) (hi : i ≤ c.cells.length)
    (cv : CV) (hcv : CVRep c lk a np i cv) : CVRep c lk a n i (preCV n cv) := by
  have hok : COK c := cok_of_ctxOK c hc
  have hcl := hok.cell _ (cellS_mem c i hi1 hi)
  have hpb : (cellS c i).pb ≤ DS := hcl.2.1
  have hpa : (cellS c i).pa ≤ DS := le_trans hcl.1 hpb
  have hpn : (cellS c i).pn ≤ DS := hcl.2.2.2.2.2.1
  have hh2 : (cellS c i).h2 ≤ DS + DS := hcl.2.2.2.2.2.2.2.1
  have hsqd : (cellS c i).sqd ≤ DS2 := hcl.2.2.2.2.2.2.2.2.1
  have ha1sq : (cellS c i).a1sq ≤ 1024 * (DS * DS2) := hcl.2.2.2.2.2.2.2.2.2.1
  have ha1 : c.a1 ≤ 1023 * DS := by rw [hx.1]; exact Nat.mul_le_mul_right _ hok.r
  have hm := hok.m32
  have hlen : ∀ l < np, (prefS c (a + l)).length = c.m - 1 := fun l hl =>
    prefS_length c (a + l) (by omega)
  have hbel : ∀ l < np, belowS c (a + l) i ≤ 31 := fun l hl => by
    have h1 : belowS c (a + l) i ≤ (prefS c (a + l)).length := List.countP_le_length
    have := hlen l hl
    omega
  have hpd := fun l (hl : l < np) => pdAt_eq c hc lk (a + l) i (by omega) hi1 hi
  have hsig : ∀ l < np, (pdAt c lk (a + l) i).sig < 2 ^ 48 := fun l hl => by
    rw [(hpd l hl).2.2.2.2.2.1]; exact (hlk _).2 _
  have hco : ∀ l q, coS c lk (a + l) i q < 2 ^ 48 := fun l q => by
    unfold coS slS
    split_ifs <;> first | positivity | exact (hlk _).2 _
  have hidx : ∀ l < np, idxS c (a + l) i ≤ 32 * B32 := fun l hl => by
    have h1 := idxS_le c hc (a + l) i hi1 hi
    rw [hlen l hl] at h1
    have h2 : (c.m - 1) * B32 ≤ 31 * B32 := Nat.mul_le_mul_right _ (by omega)
    omega
  have hB : ∀ l < np, belowS c (a + l) i < 2 ^ 144 := fun l hl =>
    lt_of_le_of_lt (hbel l hl) (by norm_num)
  have hS : ∀ l < np, (pdAt c lk (a + l) i).sig < 2 ^ 144 := fun l hl =>
    lt_of_lt_of_le (hsig l hl) (by norm_num)
  have hBet : ∀ l < np, (pdAt c lk (a + l) i).bet < 2 ^ 144 := fun l hl => by
    rw [(hpd l hl).2.2.2.2.2.2.1]
    calc _ ≤ DS * 2 ^ 48 + 2 ^ 48 * DS :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (hlk _).1.le) (Nat.mul_le_mul (hsig l hl).le hpn)
      _ < 2 ^ 144 := by norm_num [DS]
  have hSp : ∀ l < np, (pdAt c lk (a + l) i).sp < 2 ^ 144 := fun l hl => by
    rw [(hpd l hl).2.2.2.2.2.2.2.1]
    calc _ ≤ ∑ q ∈ Finset.range (c.m - 1), 2 ^ 48 * DS :=
          Finset.sum_le_sum fun q _ => Nat.mul_le_mul (hco l q).le (rget_prefS_dl c hc (a + l) q)
      _ = (c.m - 1) * (2 ^ 48 * DS) := by simp
      _ ≤ 31 * (2 ^ 48 * DS) := Nat.mul_le_mul_right _ (by omega)
      _ < 2 ^ 144 := by norm_num [DS]
  have ha0 : ∀ l < np, (pdAt c lk (a + l) i).a0 ≤ 32 * DS2 := fun l hl => by
    rw [(hpd l hl).2.2.2.2.1]
    exact Nat.mul_le_mul_right _ (by have := hbel l hl; omega)
  have hA0' : ∀ l < np, (pdAt c lk (a + l) i).a0 < 2 ^ 144 := fun l hl =>
    lt_of_le_of_lt (ha0 l hl) (by norm_num [DS2])
  have hkk' : ∀ l < np, c.a1 + (pdAt c lk (a + l) i).sig ≤ 1023 * DS + 2 ^ 48 := fun l hl =>
    Nat.add_le_add ha1 (hsig l hl).le
  have hKK : ∀ l < np, c.a1 + (pdAt c lk (a + l) i).sig < 2 ^ 144 := fun l hl =>
    lt_of_le_of_lt (hkk' l hl) (by norm_num [DS])
  have hAA0 : ∀ l < np, (pdAt c lk (a + l) i).A0 < 2 ^ 144 := fun l hl => by
    rw [(hpd l hl).2.2.2.2.2.2.2.2.2.1]
    calc _ ≤ 32 * DS2 + (1023 * DS + 2 ^ 48) * DS :=
          Nat.add_le_add (ha0 l hl) (Nat.mul_le_mul (hkk' l hl) hpa)
      _ < 2 ^ 144 := by norm_num [DS, DS2]
  have hAA1 : ∀ l < np, (pdAt c lk (a + l) i).A1 < 2 ^ 144 := fun l hl => by
    rw [(hpd l hl).2.2.2.2.2.2.2.2.2.2.1]
    calc _ ≤ 32 * DS2 + (1023 * DS + 2 ^ 48) * DS :=
          Nat.add_le_add (ha0 l hl) (Nat.mul_le_mul (hkk' l hl) hpb)
      _ < 2 ^ 144 := by norm_num [DS, DS2]
  have hIA : ∀ l < np, (pdAt c lk (a + l) i).IA < 2 ^ 144 := fun l hl => by
    rw [(hpd l hl).2.2.2.2.2.2.2.2.2.2.2.1]
    calc _ ≤ (DS + DS) * (32 * DS2) + 1024 * (DS * DS2) :=
          Nat.add_le_add (Nat.mul_le_mul hh2 (ha0 l hl)) ha1sq
      _ < 2 ^ 144 := by norm_num [DS, DS2]
  have hSsq : ∀ l < np, (pdAt c lk (a + l) i).ssq < 2 ^ 144 := fun l hl => by
    rw [(hpd l hl).2.2.2.2.2.2.2.2.2.2.2.2.1]
    calc _ ≤ 2 ^ 48 * DS2 := Nat.mul_le_mul (hsig l hl).le hsqd
      _ < 2 ^ 144 := by norm_num [DS2]
  have hIdx : ∀ l < np, idxS c (a + l) i < 2 ^ 144 := fun l hl =>
    lt_of_le_of_lt (hidx l hl) (by norm_num [B32])
  have hGv : ∀ l < np, (lk (idxS c (a + l) i)).V < 2 ^ 144 := fun l _ =>
    lt_of_lt_of_le (hlk _).1 (by norm_num)
  refine ⟨hcv.pa, hcv.pb, hcv.h, hcv.h2, hcv.pb2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · show pre LW n cv.B = _
    rw [hcv.B]; exact pre_eq np n _ hB hn
  · show pre LW n cv.sig = _
    rw [hcv.sig]; exact pre_eq np n _ hS hn
  · show pre LW n cv.bet = _
    rw [hcv.bet]; exact pre_eq np n _ hBet hn
  · show pre LW n cv.sp = _
    rw [hcv.sp]; exact pre_eq np n _ hSp hn
  · show preL n cv.co = _
    rw [hcv.co]
    exact preL_eq np n (fun q l => coS c lk (a + l) i q) _
      (fun q _ l _ => lt_of_lt_of_le (hco l q) (by norm_num)) hn
  · show preL n cv.own = _
    rw [hcv.own]
    exact preL_eq np n (fun q l => if ownS c (a + l) i q then 2 ^ 143 else 0) _
      (fun q _ l _ => by split_ifs <;> norm_num) hn
  · show pre LW n cv.a0 = _
    rw [hcv.a0]; exact pre_eq np n _ hA0' hn
  · show pre LW n cv.kk = _
    rw [hcv.kk]; exact pre_eq np n _ hKK hn
  · show pre LW n cv.A0 = _
    rw [hcv.A0]; exact pre_eq np n _ hAA0 hn
  · show pre LW n cv.A1 = _
    rw [hcv.A1]; exact pre_eq np n _ hAA1 hn
  · show pre LW n cv.IA = _
    rw [hcv.IA]; exact pre_eq np n _ hIA hn
  · show pre LW n cv.ssq = _
    rw [hcv.ssq]; exact pre_eq np n _ hSsq hn
  · show pre LW n cv.idx = _
    rw [hcv.idx]; exact pre_eq np n _ hIdx hn
  · show pre LW n cv.gv = _
    rw [hcv.gv]; exact pre_eq np n _ hGv hn
  · show preL n cv.gs = _
    rw [hcv.gs]
    exact preL_eq np n (fun f l => lget (lk (idxS c (a + l) i)).sl f) _
      (fun f _ l _ => lt_of_lt_of_le ((hlk _).2 f) (by norm_num)) hn

/-! ## The states of one top -/

/-- A cell `i ≤ im` of the top record on all lanes is `topCell` on each lane, and adds at most
`2 ^ 126` to an accumulator lane. -/
theorem topCellV_rep (c : Ctx) (hc : ctxOK c = true) (hx : CtxX c) (lk : ℕ → SV)
    (hlk : ∀ idx, (lk idx).V < 2 ^ 48 ∧ ∀ f, lget (lk idx).sl f < 2 ^ 48) (a n i : ℕ)
    (hn : a + n ≤ cnt (c.m - 1) c.recs.length) (hi1 : 1 ≤ i) (hi : i ≤ c.cells.length) (cv : CV)
    (hcv : CVRep c lk a n i cv) (top : SR) (htop : top ∈ c.recs) (_hit : i ≤ top.pos) (A : LA)
    (As : ℕ → Acc) (af lf : ℕ → ℕ → ℕ) (hA : LARep c.m n A As af lf)
    (_hB : LABound c.m n As af lf (2 ^ 141))
    (hok : (topCellV (mkVC n) c.a1 (tvOf top) cv (Nat.beq i top.pos) A).ok = true) :
    ∃ af' lf' : ℕ → ℕ → ℕ,
      LARep c.m n (topCellV (mkVC n) c.a1 (tvOf top) cv (Nat.beq i top.pos) A)
        (fun l => topCell c.a1 (tpOf c top) (pdAt c lk (a + l) i) (Nat.beq i top.pos)
          (Nat.add (pdAt c lk (a + l) i).bet (tpOf c top).DEm) (As l)) af' lf' ∧
      LAGrow c.m n As af lf
        (fun l => topCell c.a1 (tpOf c top) (pdAt c lk (a + l) i) (Nat.beq i top.pos)
          (Nat.add (pdAt c lk (a + l) i).bet (tpOf c top).DEm) (As l)) af' lf' (2 ^ 126) := by
  have hok0 := cok_of_ctxOK c hc
  obtain ⟨hxa1, hxFT, hxcell⟩ := hx
  have hcl := cellS_mem c i hi1 hi
  obtain ⟨hcpab, hcpbD, -, -, -, hcpn, hchD, hch2, hcsqd, hca1sq, -⟩ := hok0.cell _ hcl
  have hchd := (hxcell _ hcl).1
  obtain ⟨-, htdl, htem, -, -, htpm, -, -⟩ := hok0.rcs top htop
  have hDS : DS = 2 ^ 36 := rfl
  have hDS2 : DS2 = 2 ^ 72 := rfl
  have hm1 : c.m - 1 + 1 = c.m := by have := hok0.m2; omega
  have ha1 : c.a1 < 2 ^ 47 := by
    rw [hxa1, hDS]
    have := hok0.r
    calc c.r * 2 ^ 36 ≤ 1023 * 2 ^ 36 := Nat.mul_le_mul_right _ this
      _ < 2 ^ 47 := by norm_num
  have hPmL : bsel top.fg 0 top.pm < 2 ^ 47 := by
    rw [bsel_ite]
    split_ifs
    · positivity
    · exact lt_of_le_of_lt htpm (by rw [hDS]; norm_num)
  have hpd := fun l (hl : l < n) => pdAt_eq c hc lk (a + l) i (by omega) hi1 hi
  have hsigb : ∀ l < n, (pdAt c lk (a + l) i).sig < 2 ^ 48 := fun l hl => by
    rw [(hpd l hl).2.2.2.2.2.1]; exact (hlk _).2 _
  have hbel : ∀ l < n, belowS c (a + l) i ≤ c.m - 1 := fun l hl => by
    unfold belowS
    rw [← prefS_length c (a + l) (by omega)]
    exact List.countP_le_length
  have ha0b : ∀ l < n, (pdAt c lk (a + l) i).a0 < 2 ^ 78 := fun l hl => by
    rw [(hpd l hl).2.2.2.2.1, hDS2]
    have := hbel l hl
    have := hok0.m32
    calc (belowS c (a + l) i + 1) * 2 ^ 72 ≤ 32 * 2 ^ 72 := Nat.mul_le_mul_right _ (by omega)
      _ < 2 ^ 78 := by norm_num
  have hBb : ∀ l < n, Nat.add (pdAt c lk (a + l) i).bet (tpOf c top).DEm < 2 ^ 86 := fun l hl => by
    show (pdAt c lk (a + l) i).bet + DS * top.em < 2 ^ 86
    rw [(hpd l hl).2.2.2.2.2.2.1]
    have e1 : DS * (lk (idxS c (a + l) i)).V < 2 ^ 36 * 2 ^ 48 :=
      Nat.mul_lt_mul_of_le_of_lt (le_of_eq hDS) (hlk _).1 (by positivity)
    have e2 : (pdAt c lk (a + l) i).sig * (cellS c i).pn < 2 ^ 48 * 2 ^ 36 :=
      Nat.mul_lt_mul_of_lt_of_le (hsigb l hl) (hcpn.trans (le_of_eq hDS)) (by positivity)
    have e3 : DS * top.em ≤ 2 ^ 36 * 2 ^ 36 := Nat.mul_le_mul (le_of_eq hDS) (htem.trans (le_of_eq hDS))
    have : (2 : ℕ) ^ 36 * 2 ^ 48 + 2 ^ 48 * 2 ^ 36 + 2 ^ 36 * 2 ^ 36 ≤ 2 ^ 86 := by norm_num
    omega
  have hcob : ∀ q l, l < n → coS c lk (a + l) i q < 2 ^ 48 := fun q l _ => by
    unfold coS
    split_ifs
    · positivity
    · exact (hlk _).2 _
  have hspb : ∀ l < n, (pdAt c lk (a + l) i).sp < 2 ^ 89 := fun l hl => by
    rw [(hpd l hl).2.2.2.2.2.2.2.1]
    have e : ∀ q ∈ Finset.range (c.m - 1), coS c lk (a + l) i q * (rget (prefS c (a + l)) q).dl ≤ 2 ^ 84 :=
      fun q _ => (Nat.mul_le_mul (hcob q l hl).le ((rget_prefS_dl c hc (a + l) q).trans (le_of_eq hDS))).trans
        (by norm_num)
    have := Finset.sum_le_card_nsmul _ _ _ e
    rw [Finset.card_range, smul_eq_mul] at this
    have h32 := hok0.m32
    calc _ ≤ (c.m - 1) * 2 ^ 84 := this
      _ ≤ 31 * 2 ^ 84 := Nat.mul_le_mul_right _ (by omega)
      _ < 2 ^ 89 := by norm_num
  have hPmW : (tpOf c top).PmW ≤ 2 ^ 82 := by
    show bsel top.fg 0 (top.pm * top.dl) ≤ 2 ^ 82
    rw [bsel_ite]
    split_ifs
    · positivity
    · exact (Nat.mul_le_mul htpm htdl).trans (by rw [hDS]; norm_num)
  have hSb : ∀ l < n, tS (tpOf c top) (pdAt c lk (a + l) i) (Nat.beq i top.pos) < 2 ^ 91 := fun l hl => by
    unfold tS
    have := hspb l hl
    have : (2 : ℕ) ^ 89 + 2 ^ 82 < 2 ^ 91 := by norm_num
    split_ifs <;> omega
  have hKb : ∀ l < n, c.a1 + (pdAt c lk (a + l) i).sig < 2 ^ 50 := fun l hl => by
    have := hsigb l hl
    have : (2 : ℕ) ^ 47 + 2 ^ 48 ≤ 2 ^ 50 := by norm_num
    omega
  have hKpa : ∀ l < n, ∀ p ≤ DS, (c.a1 + (pdAt c lk (a + l) i).sig) * p < 2 ^ 86 := fun l hl p hp =>
    (Nat.mul_lt_mul_of_lt_of_le (hKb l hl) (hp.trans (le_of_eq hDS)) (by positivity)).trans_le
      (by norm_num)
  have hA0e : ∀ l < n, (pdAt c lk (a + l) i).A0 =
      (pdAt c lk (a + l) i).a0 + (c.a1 + (pdAt c lk (a + l) i).sig) * (cellS c i).pa :=
    fun l hl => (hpd l hl).2.2.2.2.2.2.2.2.2.1
  have hA1e : ∀ l < n, (pdAt c lk (a + l) i).A1 =
      (pdAt c lk (a + l) i).a0 + (c.a1 + (pdAt c lk (a + l) i).sig) * (cellS c i).pb :=
    fun l hl => (hpd l hl).2.2.2.2.2.2.2.2.2.2.1
  have hA0b : ∀ l < n, (pdAt c lk (a + l) i).A0 < 2 ^ 90 := fun l hl => by
    rw [hA0e l hl]
    have := ha0b l hl
    have := hKpa l hl _ (hcpab.trans hcpbD)
    have : (2 : ℕ) ^ 78 + 2 ^ 86 ≤ 2 ^ 90 := by norm_num
    omega
  have hA1b : ∀ l < n, (pdAt c lk (a + l) i).A1 < 2 ^ 90 := fun l hl => by
    rw [hA1e l hl]
    have := ha0b l hl
    have := hKpa l hl _ hcpbD
    have : (2 : ℕ) ^ 78 + 2 ^ 86 ≤ 2 ^ 90 := by norm_num
    omega
  have hIAb : ∀ l < n, (pdAt c lk (a + l) i).IA < 2 ^ 126 := fun l hl => by
    rw [(hpd l hl).2.2.2.2.2.2.2.2.2.2.2.1]
    have e1 : (cellS c i).h2 * (pdAt c lk (a + l) i).a0 < 2 ^ 37 * 2 ^ 78 :=
      Nat.mul_lt_mul_of_le_of_lt (hch2.trans (by rw [hDS]; norm_num)) (ha0b l hl) (by positivity)
    have e2 : (cellS c i).a1sq ≤ 2 ^ 118 := hca1sq.trans (by rw [hDS, hDS2]; norm_num)
    have : (2 : ℕ) ^ 37 * 2 ^ 78 + 2 ^ 118 ≤ 2 ^ 126 := by norm_num
    omega
  have hssqb : ∀ l < n, (pdAt c lk (a + l) i).ssq < 2 ^ 126 := fun l hl => by
    rw [(hpd l hl).2.2.2.2.2.2.2.2.2.2.2.2.1]
    exact (Nat.mul_lt_mul_of_lt_of_le (hsigb l hl) (hcsqd.trans (le_of_eq hDS2)) (by positivity)).trans_le
      (by norm_num)
  have hBe : Nat.add cv.bet (bc (mkVC n) (tvOf top).DEm) =
      pack LW n fun l => Nat.add (pdAt c lk (a + l) i).bet (tpOf c top).DEm := by
    rw [hcv.bet, bc_eq, Nat.add_eq, pack_add]
    rfl
  have hSe : bsel (Nat.beq i top.pos) cv.sp (Nat.add cv.sp (bc (mkVC n) (tvOf top).PmW)) =
      pack LW n fun l => tS (tpOf c top) (pdAt c lk (a + l) i) (Nat.beq i top.pos) := by
    rw [hcv.sp, bc_eq, Nat.add_eq, pack_add]
    unfold tS
    cases Nat.beq i top.pos
    · exact pack_congr _ _ _ _ fun l _ => (ite_eq_right Bool.false_ne_true).symm
    · exact pack_congr _ _ _ _ fun l _ => (ite_eq_left rfl).symm
  have hAac : A.ac = (List.range (c.m - 1 + 1)).map fun q => pack LW n (af q) := by
    rw [hm1]; exact hA.ac
  have hAlm : A.lm = (List.range (c.m - 1 + 1)).map fun q => pack LW n (lf q) := by
    rw [hm1]; exact hA.lm
  obtain ⟨hcore, hQ⟩ := topCellV_core n c.a1 (c.m - 1) (cellS c i).pa (cellS c i).pb (cellS c i).h
    (cellS c i).h2 (bsel top.fg 0 top.pm) (tvOf top) cv (Nat.beq i top.pos) A
    (fun l => Nat.add (pdAt c lk (a + l) i).bet (tpOf c top).DEm)
    (fun l => tS (tpOf c top) (pdAt c lk (a + l) i) (Nat.beq i top.pos))
    (fun l => (pdAt c lk (a + l) i).a0) (fun l => (pdAt c lk (a + l) i).sig) (fun l => (pdAt c lk (a + l) i).A0)
    (fun l => (pdAt c lk (a + l) i).A1) (fun l => (pdAt c lk (a + l) i).IA) (fun l => (pdAt c lk (a + l) i).ssq)
    (fun q l => coS c lk (a + l) i q) (fun q l => ownS c (a + l) i q = true) (fun l => (As l).rp)
    (fun l => (As l).rn) af lf hBe hSe hcv.pa hcv.h hcv.h2 hcv.pb2 hchd hcpab hcpbD hch2 ha1 rfl
    hPmL hcv.sig hcv.a0 hcv.kk hcv.A0 hcv.A1 hcv.IA hcv.ssq hcv.co hcv.own hA0e hA1e
    (fun l hl => (hBb l hl).trans (by norm_num)) hSb hsigb
    (fun l hl => (ha0b l hl).trans (by norm_num)) hA0b hA1b hIAb hssqb hcob
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_le_of_lt hok0.m32 (by norm_num)))
    hA.rp hA.rn hAac hAlm hok
  have hcl_l : ∀ l < n, topCell c.a1 (tpOf c top) (pdAt c lk (a + l) i) (Nat.beq i top.pos)
      (Nat.add (pdAt c lk (a + l) i).bet (tpOf c top).DEm) (As l) = Acc.mk
        ((As l).rp + tRP c.a1 (pdAt c lk (a + l) i) (Nat.add (pdAt c lk (a + l) i).bet (tpOf c top).DEm))
        ((As l).rn + tRN c.a1 (pdAt c lk (a + l) i) (Nat.add (pdAt c lk (a + l) i).bet (tpOf c top).DEm))
        ((As l).ac + ∑ q ∈ Finset.range (c.m - 1 + 1), tAC c.a1 (tpOf c top) (pdAt c lk (a + l) i)
          (Nat.beq i top.pos) (Nat.add (pdAt c lk (a + l) i).bet (tpOf c top).DEm) (c.m - 1)
          (fun q => coS c lk (a + l) i q) (bsel top.fg 0 top.pm) q * F128 ^ q)
        ((As l).lm + ∑ q ∈ Finset.range (c.m - 1 + 1), tLM (pdAt c lk (a + l) i) (Nat.beq i top.pos)
          (Nat.add (pdAt c lk (a + l) i).bet (tpOf c top).DEm) (c.m - 1) (fun q => ownS c (a + l) i q = true)
          (bsel top.fg 0 1) q * F128 ^ q) := fun l hl => by
    obtain ⟨e_pa, e_pb, e_h, -, -, -, -, -, e_cp, e_A0, e_A1, -, -, e_own, e_has⟩ := hpd l hl
    refine topCell_closed _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ e_cp ?_ ?_ ?_ ?_
    · rw [e_h, e_pb, e_pa]; exact hchd
    · rw [e_pa]; exact e_A0
    · rw [e_pb]; exact e_A1
    · show bsel top.fg 0 (Nat.mul top.pm c.FT) = _
      rw [hxFT]
      cases top.fg
      · rfl
      · exact (zero_mul _).symm
    · rw [e_own]
      congr 2
      funext q
      simp
    · rw [e_has]
      congr 1
      funext q
      simp
    · show bsel top.fg 0 c.FT = _
      rw [hxFT]
      cases top.fg
      · exact (one_mul _).symm
      · exact (zero_mul _).symm
  refine ⟨fun q l => af q l + tAC c.a1 (tpOf c top) (pdAt c lk (a + l) i) (Nat.beq i top.pos)
      (Nat.add (pdAt c lk (a + l) i).bet (tpOf c top).DEm) (c.m - 1) (fun q => coS c lk (a + l) i q)
      (bsel top.fg 0 top.pm) q,
    fun q l => lf q l + tLM (pdAt c lk (a + l) i) (Nat.beq i top.pos)
      (Nat.add (pdAt c lk (a + l) i).bet (tpOf c top).DEm) (c.m - 1) (fun q => ownS c (a + l) i q = true)
      (bsel top.fg 0 1) q, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hcore]
    refine pack_congr _ _ _ _ fun l hl => ?_
    rw [hcl_l l hl]
    obtain ⟨e_pa, -, e_h, e_h2, -⟩ := hpd l hl
    show _ = (As l).rp + _
    rw [tRP_lane c.a1 _ _ _ _ _ e_pa e_h e_h2]
  · rw [hcore]
    refine pack_congr _ _ _ _ fun l hl => ?_
    rw [hcl_l l hl]
    obtain ⟨e_pa, e_pb, -⟩ := hpd l hl
    show _ = (As l).rn + _
    rw [tRN_lane c.a1 _ _ _ _ e_pa e_pb]
  · rw [hcore]
    show List.map _ (List.range (c.m - 1 + 1)) = _
    rw [hm1]
    refine List.map_congr_left fun q _ => pack_congr _ _ _ _ fun l hl => ?_
    obtain ⟨e_pa, e_pb, e_h, -, -, -, -, -, -, e_A0, e_A1, -⟩ := hpd l hl
    show _ = af q l + _
    rw [tAC_lane c.a1 _ _ _ _ _ _ _ q (cellS c i).pa (cellS c i).h e_pa (by rw [e_pb]; omega) e_h
      (by rw [e_pa]; exact e_A0) (by rw [e_pb]; exact e_A1)]
  · rw [hcore]
    show List.map _ (List.range (c.m - 1 + 1)) = _
    rw [hm1]
    refine List.map_congr_left fun q _ => pack_congr _ _ _ _ fun l hl => ?_
    show _ = lf q l + _
    rw [tLM_lane _ _ (tvOf top).topOn _ _ _ _ q (by
      show bsel top.fg 0 1 = if bsel top.fg false true = true then 1 else 0
      cases top.fg
      · rfl
      · rfl)]
    unfold ownBefore
    rfl
  · intro l hl
    rw [hcl_l l hl]
    show (As l).ac + _ = _
    rw [hA.acS l hl, hm1, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => (add_mul _ _ _).symm
  · intro l hl
    rw [hcl_l l hl]
    show (As l).lm + _ = _
    rw [hA.lmS l hl, hm1, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => (add_mul _ _ _).symm
  · intro l hl
    beta_reduce
    rw [hcl_l l hl]
    obtain ⟨e_pa, e_pb, e_h, e_h2, -, -, -, -, -, e_A0, e_A1, -⟩ := hpd l hl
    have hAh : (pdAt c lk (a + l) i).A1 = (pdAt c lk (a + l) i).A0 + (c.a1 + (pdAt c lk (a + l) i).sig) * (pdAt c lk (a + l) i).h := by
      rw [e_A1, e_A0, e_h, hchd, Nat.mul_sub, add_assoc,
        Nat.add_sub_cancel' (Nat.mul_le_mul_left _ hcpab)]
    have hpb36 : (cellS c i).pb ≤ 2 ^ 36 := hcpbD.trans (le_of_eq hDS)
    refine ⟨Nat.add_le_add_left (tRP_le _ _ _ ha1 (hBb l hl) (ha0b l hl) (by rw [e_pa]; omega)
        (by rw [e_h]; omega) (by rw [e_h2]; exact hch2.trans (by rw [hDS]; norm_num)) (hIAb l hl) hAh) _,
      Nat.add_le_add_left (tRN_le _ _ _ ha1 (by rw [e_pb]; exact hpb36) (hsigb l hl) (hssqb l hl)) _,
      fun q _ => ⟨Nat.add_le_add_left (tAC_le c.a1 _ _ _ _ _ _ _ q (cellS c i).pa (cellS c i).h e_pa
        (by rw [e_pb]; omega) e_h (by rw [e_pa]; exact e_A0) (by rw [e_pb]; exact e_A1)
        (fun q => hcob q l hl) hPmL (by omega) (fun h1 h2 h3 => hQ l hl ⟨h1, h2, h3⟩)) _,
      Nat.add_le_add_left (tLM_le _ _ _ _ _ _ q (by rw [bsel_ite]; split_ifs <;> norm_num)) _⟩⟩

/-- The tail on the lanes of `act`: `tailCells` on those lanes, the others unchanged; it adds at
most `2 ^ 139` to an accumulator lane. -/
theorem tailV_rep (c : Ctx) (hc : ctxOK c = true) (hx : CtxX c) (n : ℕ) (_hn : n ≤ B32) (Uf Sf : ℕ → ℕ)
    (gf : ℕ → ℕ → ℕ) (hU : ∀ l < n, Uf l < 2 ^ 85) (hS : ∀ l < n, Sf l < 2 ^ 91)
    (hg : ∀ f l, l < n → gf f l < 2 ^ 48) (k pj etj etmj : ℕ) (hpj : pj ≤ DS) (het : etj ≤ DS)
    (hetm : etmj ≤ DS) (act : ℕ → Bool) (A : LA) (As : ℕ → Acc) (af lf : ℕ → ℕ → ℕ)
    (hA : LARep c.m n A As af lf) (_hB : LABound c.m n As af lf (2 ^ 140))
    (hok : (tailV (mkVC n) c.r c.a1 (Nat.mul (Nat.succ c.m) DS2) (pack LW n Uf) (pack LW n Sf)
      ((List.range c.m).map fun f => pack LW n (gf f)) (ldrop k c.cells) pj etj etmj
      (pack LW n fun l => if act l then 2 ^ 143 else 0) A).ok = true) :
    ∃ af' lf' : ℕ → ℕ → ℕ,
      LARep c.m n (tailV (mkVC n) c.r c.a1 (Nat.mul (Nat.succ c.m) DS2) (pack LW n Uf)
          (pack LW n Sf) ((List.range c.m).map fun f => pack LW n (gf f)) (ldrop k c.cells) pj etj
          etmj (pack LW n fun l => if act l then 2 ^ 143 else 0) A)
        (fun l => if act l then
          tailCells c.r c.a1 (Nat.mul (Nat.succ c.m) DS2) (Uf l) (Sf l)
            (packF ((List.range c.m).map fun f => gf f l)) (ldrop k c.cells) pj etj etmj (As l)
          else As l) af' lf' ∧
      LAGrow c.m n As af lf
        (fun l => if act l then
          tailCells c.r c.a1 (Nat.mul (Nat.succ c.m) DS2) (Uf l) (Sf l)
            (packF ((List.range c.m).map fun f => gf f l)) (ldrop k c.cells) pj etj etmj (As l)
          else As l) af' lf' (2 ^ 139) := by
  have hok' : COK c := cok_of_ctxOK c hc
  have hcs : ∀ cl ∈ ldrop k c.cells, cl.pa ≤ cl.pb ∧ cl.pb ≤ DS ∧ cl.h = cl.pb - cl.pa ∧ cl.et ≤ DS ∧
      cl.e1 ≤ DS ∧ cl.etm ≤ DS := by
    intro cl hcl
    rw [ldrop_eq] at hcl
    have hmem := List.mem_of_mem_drop hcl
    obtain ⟨c1, c2, c3, c4, c5, -⟩ := hok'.cell cl hmem
    exact ⟨c1, c2, (hx.2.2 cl hmem).1, c3, c4, c5⟩
  have ha0 : Nat.mul (Nat.succ c.m) DS2 < 2 ^ 80 := by
    have hm := hok'.m32
    show (c.m + 1) * DS2 < 2 ^ 80
    have hDS2 : DS2 = 2 ^ 72 := rfl
    rw [hDS2]
    calc (c.m + 1) * 2 ^ 72 ≤ 33 * 2 ^ 72 := Nat.mul_le_mul_right _ (by omega)
      _ < 2 ^ 80 := by norm_num
  have hL4096 : c.cells.length ≤ 4096 := by rw [hok'.len]; exact hok'.len4096
  have htD : tailD (ldrop k c.cells).length ≤ 2 ^ 139 := by
    rw [ldrop_eq, List.length_drop]
    unfold tailD
    have h1 : (c.cells.length - k) * 2 ^ 125 ≤ 4096 * 2 ^ 125 := Nat.mul_le_mul_right _ (by omega)
    have h2 : (4096 : ℕ) * 2 ^ 125 + 2 ^ 123 ≤ 2 ^ 139 := by norm_num
    exact (Nat.add_le_add_right h1 _).trans h2
  obtain ⟨rpf', rnf', af', hT, hL, hG⟩ := tailV_lanes n c.m c.r c.a1 (Nat.mul (Nat.succ c.m) DS2) Uf Sf gf
    hok'.r hx.1 ha0 hU hS hg (ldrop k c.cells) hcs pj etj etmj hpj het hetm (fun l => act l = true) A
    (fun l => (As l).rp) (fun l => (As l).rn) af hA.rp hA.rn hA.ac hok
  have hlane : ∀ l < n, (if act l = true then
      tailCells c.r c.a1 (Nat.mul (Nat.succ c.m) DS2) (Uf l) (Sf l)
        (packF ((List.range c.m).map fun f => gf f l)) (ldrop k c.cells) pj etj etmj (As l)
      else As l) = Acc.mk (rpf' l) (rnf' l) (∑ q ∈ Finset.range c.m, af' q l * F128 ^ q) (As l).lm :=
    fun l hl => hL l hl (As l) rfl rfl (hA.acS l hl)
  refine ⟨af', lf, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hT]
    exact pack_congr _ _ _ _ fun l hl => by rw [hlane l hl]
  · rw [hT]
    exact pack_congr _ _ _ _ fun l hl => by rw [hlane l hl]
  · rw [hT]
  · rw [hT]
    exact hA.lm
  · intro l hl
    rw [hlane l hl]
  · intro l hl
    rw [hlane l hl]
    exact hA.lmS l hl
  · intro l hl
    obtain ⟨g1, g2, g3⟩ := hG l hl
    beta_reduce
    rw [hlane l hl]
    exact ⟨g1.trans (Nat.add_le_add_left htD _), g2.trans (Nat.add_le_add_left htD _),
      fun q hq => ⟨(g3 q hq).trans (Nat.add_le_add_left htD _), Nat.le_add_right _ _⟩⟩

/-- The final check reads the prefix vectors on its own lanes only. -/
theorem finCheck_pre (n : ℕ) (pv : PV) (uh : ℕ) (sg : List ℕ) (topFg : Bool) (A : LA) :
    finCheck (mkVC n) pv uh sg topFg A =
      finCheck (mkVC n) (PV.mk (preL n pv.pos) (preL n pv.dl) (preL n pv.fg) (preL n pv.cs)) uh sg
        topFg A := by
  have hpoint : ∀ F, pre LW n (Nat.shiftLeft F 143) = pre LW n (Nat.shiftLeft (pre LW n F) 143) := by
    intro F
    have hpre : ∀ P, pre LW n P = P % (2 ^ (LW * n)) := by
      intro P
      unfold pre
      simp [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod]
    rw [hpre (Nat.shiftLeft (pre LW n F) 143), hpre (Nat.shiftLeft F 143)]
    simp [Nat.shiftLeft_eq]
    rw [hpre F]
    -- Goal: (F * 2^143) % M = ((F % M) * 2^143) % M
    calc
      (F * 2 ^ 143) % (2 ^ (LW * n)) = ((F % (2 ^ (LW * n)) + (2 ^ (LW * n)) * (F / (2 ^ (LW * n)))) * 2 ^ 143) % (2 ^ (LW * n)) := by rw [Nat.mod_add_div F (2 ^ (LW * n))]
      _ = ((F % (2 ^ (LW * n))) * 2 ^ 143 + ((2 ^ (LW * n)) * (F / (2 ^ (LW * n)))) * 2 ^ 143) % (2 ^ (LW * n)) := by rw [add_mul]
      _ = ((F % (2 ^ (LW * n))) * 2 ^ 143 + (2 ^ (LW * n)) * ((F / (2 ^ (LW * n))) * 2 ^ 143)) % (2 ^ (LW * n)) := by rw [mul_assoc]
      _ = ((F % (2 ^ (LW * n))) * 2 ^ 143) % (2 ^ (LW * n)) := by
        rw [Nat.add_mod]
        simp [Nat.mul_mod]
  have h_lmap_eq : lmap (fun F => pre LW n (Nat.shiftLeft F 143)) pv.fg =
                  lmap (fun F => pre LW n (Nat.shiftLeft F 143)) (preL n pv.fg) := by
    rw [preL]
    simp [lmap_eq]
    intro a _
    exact hpoint a
  unfold finCheck
  rw [mkVC_n n]
  rw [h_lmap_eq]

/-- The final check on all lanes is `checkVar1` on each lane. -/
theorem finCheck_sound (c : Ctx) (hc : ctxOK c = true) (lk : ℕ → SV) (a n : ℕ)
    (hn : a + n ≤ cnt (c.m - 1) c.recs.length) (pv : PV) (hpv : PVRep c a n pv) (uf : ℕ → ℕ)
    (sf : ℕ → ℕ → ℕ) (huf : ∀ l < n, uf l < 2 ^ 48) (hsf : ∀ f l, l < n → sf f l < 2 ^ 48)
    (top : SR) (A : LA) (As : ℕ → Acc) (af lf : ℕ → ℕ → ℕ) (hA : LARep c.m n A As af lf)
    (hB : LABound c.m n As af lf (2 ^ 142))
    (h : finCheck (mkVC n) pv (pack LW n uf) ((List.range c.m).map fun f => pack LW n (sf f))
      top.fg A = true) :
    ∀ l < n, checkVar.checkVar1 (uf l) ((List.range c.m).map fun f => sf f l)
      (mkPre c lk (prefS c (a + l))) top (As l) = true := by
  have hok := cok_of_ctxOK c hc
  have hm : 1 ≤ c.m := by have := hok.m2; omega
  have hFL := finCheck_lanes n c.m hm pv (fun q l => (rget (prefS c (a + l)) q).fg) top.fg hpv.fg uf sf
    huf hsf A (fun l => (As l).rp) (fun l => (As l).rn) af lf hA.rp hA.rn hA.ac hA.lm
    (fun l hl => ⟨(hB l hl).1, (hB l hl).2.1, fun q hq => (hB l hl).2.2 q hq⟩) h
  intro l hl
  obtain ⟨h1, h2⟩ := hFL l hl
  have hP := prefS_length c (a + l) (by omega)
  have hlen : (prefS c (a + l) ++ [top]).length = c.m := by
    rw [List.length_append, hP, List.length_singleton]; omega
  have hmu : muOK (prefS c (a + l) ++ [top]) ((List.range c.m).map fun f => sf f l)
      (∑ q ∈ Finset.range (prefS c (a + l) ++ [top]).length, af q l * F128 ^ q)
      (∑ q ∈ Finset.range (prefS c (a + l) ++ [top]).length, lf q l * F128 ^ q) = true := by
    refine muOK_of (prefS c (a + l) ++ [top]) ((List.range c.m).map fun f => sf f l) (fun q => af q l)
      (fun q => lf q l) (by rw [hlen, List.length_map, List.length_range])
      (fun q hq => (h2 q (hlen ▸ hq)).1) (fun q hq => (h2 q (hlen ▸ hq)).2.1) fun q hq => ?_
    have hq' : q < c.m := hlen ▸ hq
    have e1 : ((List.range c.m).map fun f => sf f l).getD q 0 = sf q l := by
      rw [List.getD_eq_getElem _ _ (by simpa using hq'), List.getElem_map, List.getElem_range]
    rw [e1]
    have h3 := (h2 q hq').2.2
    have e2 : (prefS c (a + l) ++ [top])[q].fg = (if q < c.m - 1 then (rget (prefS c (a + l)) q).fg else top.fg) := by
      split_ifs with hq1
      · rw [List.getElem_append_left (by omega), rget_of_lt _ _ (by omega)]
      · rw [List.getElem_append_right (by omega)]
        simp
    rw [e2]
    exact h3
  rw [hlen] at hmu
  show bsel (Nat.ble (Nat.add (Nat.mul (Nat.mul 2 DS2) (uf l)) (As l).rn) (As l).rp)
    (muOK (lapp (prefS c (a + l)) [top]) ((List.range c.m).map fun f => sf f l) (As l).ac (As l).lm)
    false = true
  have hle : Nat.ble (Nat.add (Nat.mul (Nat.mul 2 DS2) (uf l)) (As l).rn) (As l).rp = true :=
    Nat.ble_eq.mpr h1
  rw [lapp_eq, hA.acS l hl, hA.lmS l hl, hmu, hle]
  rfl

/-! ## The accumulators of one top -/

theorem mkPre_pd_length (c : Ctx) (lk : ℕ → SV) (rs : List SR) :
    (mkPre c lk rs).pd.length = c.cells.length :=
  pdLoop_length _ _ _ _ _ _ _ _

theorem pdAt_getElem (c : Ctx) (lk : ℕ → SV) (l k : ℕ) (hk : k < (mkPre c lk (prefS c l)).pd.length) :
    (mkPre c lk (prefS c l)).pd[k] = pdAt c lk l (k + 1) := by
  unfold pdAt
  rw [Nat.add_sub_cancel, List.headD_eq_head?_getD, List.head?_drop, List.getElem?_eq_getElem hk]
  rfl

theorem pdAt_from (c : Ctx) (hc : ctxOK c = true) (lk : ℕ → SV) (l i : ℕ) (hi1 : 1 ≤ i)
    (hi : i ≤ c.cells.length) : (pdAt c lk l i).from' = c.cells.drop (i - 1) := by
  have h := pdLoop_get c.a1 lk (prefS c l) c.cells (prefS_sorted c hc l) i hi1 hi
  unfold pdAt
  rw [List.headD_eq_head?_getD, List.head?_drop]
  show ((pdLoop c.a1 lk (prefS c l) c.cells 1 0 (lmap SR.pos (prefS c l)) (rankCs (prefS c l)))[i - 1]?.getD
    _).from' = _
  rw [h]
  rfl

theorem topCellV_ok (v : VC) (a1 : ℕ) (tp : TV) (cv : CV) (isTop : Bool) (A : LA)
    (h : (topCellV v a1 tp cv isTop A).ok = true) : A.ok = true := by
  unfold topCellV topCellV.topCellV1 topCellV.topCellV2 topCellV.topCellV3 topCellV.topCellV4
    topCellV.topCellV5 topCellV.topCellV6 at h
  dsimp only at h
  rw [bsel_false, Bool.and_eq_true] at h
  exact h.2

/-- The zero accumulators of `m` fields. -/
noncomputable def LA0 (m : ℕ) : LA :=
  LA.mk 0 0 (lmap (fun _ => 0) (List.range m)) (lmap (fun _ => 0) (List.range m)) true

/-- The lanes accumulators of a top after its cells `1 .. k`. -/
noncomputable def accV (c : Ctx) (n : ℕ) (tp : TV) (cvs : List CV) : ℕ → LA
  | 0 => LA0 c.m
  | k + 1 => topCellV (mkVC n) c.a1 tp (preCV n (cget cvs k)) (Nat.beq (k + 1) tp.im) (accV c n tp cvs k)

/-- The scalar accumulators of the prefix `l` and the top after the cells `1 .. k`. -/
noncomputable def accS (c : Ctx) (lk : ℕ → SV) (top : SR) (l : ℕ) : ℕ → Acc
  | 0 => Acc.mk 0 0 0 0
  | k + 1 => topCell c.a1 (tpOf c top) (pdAt c lk l (k + 1)) (Nat.beq (k + 1) top.pos)
      (Nat.add (pdAt c lk l (k + 1)).bet (tpOf c top).DEm) (accS c lk top l k)

theorem topLoopV_acc (c : Ctx) (n : ℕ) (tp : TV) (cvs : List CV) (htp : tp.im ≤ cvs.length) :
    ∀ d k, k + d = tp.im →
      topLoopV (mkVC n) c.a1 tp (cvs.drop k) (k + 1) (accV c n tp cvs k) = accV c n tp cvs tp.im := by
  intro d
  induction d with
  | zero =>
    intro k hk
    simp only [Nat.add_zero] at hk
    subst hk
    rcases h : cvs.drop tp.im with _ | ⟨cv, rest⟩
    · rfl
    · show bsel (Nat.ble (tp.im + 1) tp.im) _ _ = _
      have : Nat.ble (tp.im + 1) tp.im = false := Bool.eq_false_iff.2 fun h => by rw [Nat.ble_eq] at h; omega
      rw [this]
      rfl
  | succ d ih =>
    intro k hk
    have hk' : k < cvs.length := by omega
    rw [List.drop_eq_getElem_cons hk']
    show bsel (Nat.ble (k + 1) tp.im) (topLoopV (mkVC n) c.a1 tp (cvs.drop (k + 1)) (k + 1 + 1)
      (topCellV (mkVC n) c.a1 tp (preCV (mkVC n).n cvs[k]) (Nat.beq (k + 1) tp.im) (accV c n tp cvs k)))
      (accV c n tp cvs k) = _
    have hb : Nat.ble (k + 1) tp.im = true := by simp; omega
    rw [hb]
    have := ih (k + 1) (by omega)
    rw [← this]
    show topLoopV (mkVC n) c.a1 tp (cvs.drop (k + 1)) (k + 1 + 1) _ = topLoopV (mkVC n) c.a1 tp
      (cvs.drop (k + 1)) (k + 1 + 1) (topCellV (mkVC n) c.a1 tp (preCV n (cget cvs k)) (Nat.beq (k + 1) tp.im)
        (accV c n tp cvs k))
    rw [cget_of_lt _ _ hk']
    rfl

theorem topLoop_acc (c : Ctx) (lk : ℕ → SV) (top : SR) (l : ℕ) (hc : ctxOK c = true)
    (htp : top.pos ≤ c.cells.length) :
    ∀ d k, k + d = top.pos →
      topLoop c lk (mkPre c lk (prefS c l)) top (tpOf c top) ((mkPre c lk (prefS c l)).pd.drop k) (k + 1)
        (accS c lk top l k) =
      if top.pos < c.cells.length ∧ top.fg = false then
        tailPart c lk (mkPre c lk (prefS c l)) top (c.cells.drop top.pos) (accS c lk top l top.pos)
      else accS c lk top l top.pos := by
  have hlen := mkPre_pd_length c lk (prefS c l)
  intro d
  induction d with
  | zero =>
    intro k hk
    simp only [Nat.add_zero] at hk
    subst hk
    rcases lt_or_eq_of_le htp with hlt | heq
    · have hk' : top.pos < (mkPre c lk (prefS c l)).pd.length := by omega
      rw [List.drop_eq_getElem_cons hk', pdAt_getElem]
      show bsel (Nat.ble (top.pos + 1) (tpOf c top).im) _ (bsel top.fg _ (tailPart c lk _ top (pdAt c lk l (top.pos + 1)).from' _)) = _
      have : Nat.ble (top.pos + 1) (tpOf c top).im = false :=
        Bool.eq_false_iff.2 fun h => by rw [Nat.ble_eq] at h; simp [tpOf] at h
      rw [this, pdAt_from c hc lk l (top.pos + 1) (by omega) (by omega), Nat.add_sub_cancel]
      cases hf : top.fg
      · simp [hlt, bsel]
      · simp [bsel]
    · have : (mkPre c lk (prefS c l)).pd.drop top.pos = [] := by
        rw [List.drop_eq_nil_iff]; omega
      rw [this]
      simp [heq]
      rfl
  | succ d ih =>
    intro k hk
    have hk' : k < (mkPre c lk (prefS c l)).pd.length := by omega
    rw [List.drop_eq_getElem_cons hk', pdAt_getElem]
    show bsel (Nat.ble (k + 1) (tpOf c top).im) (topLoop c lk _ top (tpOf c top) _ (k + 1 + 1)
      (topCell c.a1 (tpOf c top) (pdAt c lk l (k + 1)) (Nat.beq (k + 1) (tpOf c top).im)
        (Nat.add (pdAt c lk l (k + 1)).bet (tpOf c top).DEm) (accS c lk top l k))) _ = _
    have hb : Nat.ble (k + 1) (tpOf c top).im = true := by simp [tpOf]; omega
    rw [hb]
    exact ih (k + 1) (by omega)

theorem LABound_mono {m n : ℕ} {As : ℕ → Acc} {af lf : ℕ → ℕ → ℕ} {B B' : ℕ}
    (h : LABound m n As af lf B) (hB : B ≤ B') : LABound m n As af lf B' := by
  intro l hl
  obtain ⟨h1, h2, h3⟩ := h l hl
  exact ⟨by omega, by omega, fun q hq => ⟨by have := (h3 q hq).1; omega, by have := (h3 q hq).2; omega⟩⟩

theorem LABound_grow {m n : ℕ} {As As' : ℕ → Acc} {af lf af' lf' : ℕ → ℕ → ℕ} {B δ : ℕ}
    (h : LABound m n As af lf B) (hg : LAGrow m n As af lf As' af' lf' δ) :
    LABound m n As' af' lf' (B + δ) := by
  intro l hl
  obtain ⟨h1, h2, h3⟩ := h l hl
  obtain ⟨g1, g2, g3⟩ := hg l hl
  refine ⟨by omega, by omega, fun q hq => ⟨?_, ?_⟩⟩
  · have := (h3 q hq).1; have := (g3 q hq).1; omega
  · have := (h3 q hq).2; have := (g3 q hq).2; omega

theorem accV_ok (c : Ctx) (n : ℕ) (tp : TV) (cvs : List CV) (k : ℕ) :
    ∀ d, (accV c n tp cvs (k + d)).ok = true → (accV c n tp cvs k).ok = true := by
  intro d
  induction d with
  | zero => exact id
  | succ d ih =>
    intro h
    exact ih (topCellV_ok _ _ _ _ _ _ h)

theorem LARep_zero (m n : ℕ) :
    LARep m n (LA0 m) (fun _ => Acc.mk 0 0 0 0) (fun _ _ => 0) (fun _ _ => 0) := by
  refine ⟨by rw [pack_zeros]; rfl, by rw [pack_zeros]; rfl, ?_, ?_, fun l _ => by simp, fun l _ => by simp⟩
  · show lmap (fun _ => 0) (List.range m) = _
    rw [lmap_eq]
    exact List.map_congr_left fun q _ => (pack_zeros n).symm
  · show lmap (fun _ => 0) (List.range m) = _
    rw [lmap_eq]
    exact List.map_congr_left fun q _ => (pack_zeros n).symm

theorem acc_inv (c : Ctx) (hc : ctxOK c = true) (hx : CtxX c) (lk : ℕ → SV)
    (hlk : ∀ idx, (lk idx).V < 2 ^ 48 ∧ ∀ f, lget (lk idx).sl f < 2 ^ 48) (top : SR) (htop : top ∈ c.recs)
    (hpos : top.pos ≤ c.cells.length) (a np n : ℕ) (hnnp : n ≤ np)
    (hnpR : a + np ≤ cnt (c.m - 1) c.recs.length)
    (cvs : List CV) (hcv : ∀ i, 1 ≤ i → i ≤ top.pos → CVRep c lk a np i (cget cvs (i - 1)))
    (hokF : (accV c n (tvOf top) cvs top.pos).ok = true) :
    ∀ k ≤ top.pos, ∃ af lf : ℕ → ℕ → ℕ, LARep c.m n (accV c n (tvOf top) cvs k)
      (fun l => accS c lk top (a + l) k) af lf ∧
      LABound c.m n (fun l => accS c lk top (a + l) k) af lf ((k + 1) * 2 ^ 126) := by
  have hok := cok_of_ctxOK c hc
  have hL : c.cells.length ≤ 4096 := by rw [hok.len]; exact hok.len4096
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun _ _ => 0, fun _ _ => 0, LARep_zero c.m n, fun l _ => ?_⟩
    exact ⟨by show 0 < _; positivity, by show 0 < _; positivity, fun q _ => ⟨by positivity, by positivity⟩⟩
  | succ k ih =>
    intro hk
    obtain ⟨af, lf, hA, hB⟩ := ih (by omega)
    have hok' := accV_ok c n (tvOf top) cvs (k + 1) (top.pos - (k + 1))
      (by rw [show k + 1 + (top.pos - (k + 1)) = top.pos by omega]; exact hokF)
    have hcv' := preCV_rep c hc hx lk hlk a np n (k + 1) hnnp hnpR (by omega) (by omega) _
      (hcv (k + 1) (by omega) hk)
    rw [Nat.add_sub_cancel] at hcv'
    obtain ⟨af', lf', hA', hG⟩ := topCellV_rep c hc hx lk hlk a n (k + 1) (by omega) (by omega)
      (by omega) _ hcv' top htop hk (accV c n (tvOf top) cvs k) (fun l => accS c lk top (a + l) k) af lf hA
      (LABound_mono hB (by
        have : (k + 1) * 2 ^ 126 ≤ 4097 * 2 ^ 126 := Nat.mul_le_mul_right _ (by omega)
        exact le_trans this (by norm_num))) hok'
    refine ⟨af', lf', hA', ?_⟩
    have := LABound_grow hB hG
    exact LABound_mono this (by ring_nf; omega)

theorem lfoldr_add_map (k : ℕ) (G : ℕ → ℕ) :
    lfoldr Nat.add 0 ((List.range k).map G) = ∑ q ∈ Finset.range k, G q := by
  rw [lfoldr_eq]
  have e : ∀ L : List ℕ, List.foldr Nat.add 0 L = L.sum := by
    intro L
    induction L with
    | nil => rfl
    | cons a L ih => rw [List.foldr_cons, ih, List.sum_cons]; rfl
  rw [e]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem zipWith_range (f : ℕ → ℕ → ℕ) (G H : ℕ → ℕ) (a b : ℕ) :
    List.zipWith f ((List.range a).map G) ((List.range b).map H) =
      (List.range (min a b)).map fun q => f (G q) (H q) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem llast_map_range (m : ℕ) (hm : 1 ≤ m) (G : ℕ → ℕ) :
    llast 0 ((List.range m).map G) = G (m - 1) := by
  rw [llast_eq, List.getLastD_eq_getLast?, List.getLast?_map]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [List.range_succ, List.getLast?_append]
  simp

theorem Cpre_eq (c : Ctx) (lk : ℕ → SV) (rs : List SR) :
    (mkPre c lk rs).Cpre = lget (rankCs rs) rs.length := by
  show llast 0 (rankCs rs) = _
  rw [llast_eq, lget_eq, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, rankCs_length,
    Nat.add_sub_cancel, List.getD_eq_getElem?_getD]

theorem dot_zero (xs ys : List ℕ) (h : ∀ x ∈ xs, x = 0) : dot xs ys = 0 := by
  unfold dot
  rw [lfoldr_eq, lzipWith_eq]
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    cases ys with
    | nil => simp
    | cons b ys =>
      simp only [List.zipWith_cons_cons, List.foldr_cons]
      rw [ih ys fun x hx => h x (List.mem_cons_of_mem _ hx), h a (List.mem_cons_self ..)]
      show 0 * b + 0 = 0
      simp

theorem dot_eq (xs ys : List ℕ) (h : xs.length = ys.length) :
    dot xs ys = ∑ q ∈ Finset.range xs.length, xs.getD q 0 * ys.getD q 0 := by
  unfold dot
  rw [lfoldr_eq, lzipWith_eq]
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      simp only [List.zipWith_cons_cons, List.foldr_cons, List.length_cons, Finset.sum_range_succ']
      rw [ih ys (by simpa using h)]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      show a * b + _ = _
      ring

theorem packF_range (sl : List ℕ) : packF sl = packF ((List.range sl.length).map (lget sl)) := by
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, lget_eq]
    rw [List.getD_eq_getElem _ _ h1]

theorem finCheck_ok (v : VC) (pv : PV) (uh : ℕ) (sg : List ℕ) (fg : Bool) (A : LA)
    (h : finCheck v pv uh sg fg A = true) : A.ok = true := by
  unfold finCheck at h
  rw [bsel_eq] at h
  split_ifs at h with h0
  exact h0

theorem lt_LW (x : ℕ) (h : x < 2 ^ 48) : x < 2 ^ LW :=
  lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by decide))

theorem small_LW (x : ℕ) (h : x ≤ 32 * B32) : x < 2 ^ LW :=
  lt_of_le_of_lt h (by unfold B32 LW; norm_num)

theorem mul_pow_lt (a j : ℕ) (ha : a < 2 ^ 48) (hj : j < 37) : a * 2 ^ j < 2 ^ 144 := by
  calc a * 2 ^ j < 2 ^ 48 * 2 ^ j := Nat.mul_lt_mul_of_pos_right ha (by positivity)
    _ ≤ 2 ^ 48 * 2 ^ 37 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hj.le)
    _ ≤ 2 ^ 144 := by norm_num

/-- The check of the top `j` on `n` lanes from the prefix `a` (`topCheck1`): every state of those
lanes passes `checkVar` against its claimed state, read from the fields `UV`, `US` from the lane
`off` on. -/
theorem topCheck1_sound (c : Ctx) (hc : ctxOK c = true) (hx : CtxX c) (lk : ℕ → SV)
    (hlk : ∀ idx, (lk idx).V < 2 ^ 48 ∧ ∀ f, lget (lk idx).sl f < 2 ^ 48)
    (hlkl : ∀ idx, (lk idx).sl.length = c.m) (hi : ℕ)
    (hhi : hi ≤ c.recs.length) (a np n : ℕ) (hnnp : n ≤ np)
    (hnpR : a + np ≤ cnt (c.m - 1) c.recs.length) (pv : PV)
    (hpv : PVRep c a np pv) (cvs : List CV) (hcvs : cvs.length = hi)
    (hcv : ∀ i, 1 ≤ i → i ≤ hi → CVRep c lk a np i (cget cvs (i - 1)))
    (nU : ℕ) (hnUB : nU ≤ B32) (uf : ℕ → ℕ) (sf : ℕ → ℕ → ℕ) (huf : ∀ s < nU, uf s < 2 ^ 48)
    (hsf : ∀ f s, s < nU → sf f s < 2 ^ 48) (off j : ℕ) (hj : j < hi) (hoffn : off + n ≤ nU)
    (h : topCheck.topCheck1 c pv cvs (pack LW nU uf) ((List.range c.m).map fun f => pack LW nU (sf f))
      (rget c.recs j) n off = true) :
    ∀ l < n,
      checkVar c lk (uf (off + l))
        ((List.range c.m).map fun f => sf f (off + l)) (mkPre c lk (prefS c (a + l)))
        (rget c.recs j) = true := by
  have hok := cok_of_ctxOK c hc
  have hjR : j < c.recs.length := by omega
  set top := rget c.recs j with htopdef
  have htop : top ∈ c.recs := by rw [htopdef, rget_of_lt _ _ hjR]; exact List.getElem_mem hjR
  have hpos : top.pos = j + 1 := by rw [htopdef, rget_of_lt _ _ hjR]; exact hok.pos j hjR
  have hL : c.cells.length = c.recs.length := hok.len
  have h4096 : top.pos ≤ 4096 := by have := hok.len4096; omega
  have hm1 : 2 ≤ c.m := hok.m2
  have hnB : n ≤ B32 := by omega
  have hnR : a + n ≤ cnt (c.m - 1) c.recs.length := by omega
  have hpL : top.pos ≤ c.cells.length := by omega
  -- the claimed fields on the lanes of the top
  have euh : pre LW n (drp LW off (pack LW nU uf)) = pack LW n fun l => uf (off + l) := by
    rw [drp_pack LW nU off uf (fun l hl => lt_LW _ (huf l hl)),
      pre_pack LW (nU - off) n _ (fun l hl => lt_LW _ (huf _ (by omega))) (by omega)]
    exact pack_congr _ _ _ _ fun l _ => by rw [Nat.add_comm]
  have esg : preL n (lmap (drp LW off) ((List.range c.m).map fun f => pack LW nU (sf f))) =
      (List.range c.m).map fun f => pack LW n fun l => sf f (off + l) := by
    unfold preL
    rw [lmap_eq, lmap_eq, List.map_map, List.map_map]
    refine List.map_congr_left fun f _ => ?_
    simp only [Function.comp]
    rw [drp_pack LW nU off _ (fun l hl => lt_LW _ (hsf f l hl)),
      pre_pack LW (nU - off) n _ (fun l hl => lt_LW _ (hsf f _ (by omega))) (by omega)]
    exact pack_congr _ _ _ _ fun l _ => by rw [Nat.add_comm]
  have e' : topLoopV (mkVC n) c.a1 (tvOf top) cvs 1 (LA.mk 0 0 (lmap (fun _ => 0) (List.range c.m))
      (lmap (fun _ => 0) (List.range c.m)) true) = accV c n (tvOf top) cvs top.pos := by
    have e := topLoopV_acc c n (tvOf top) cvs (by show top.pos ≤ cvs.length; omega) top.pos 0
      (Nat.zero_add _)
    rw [List.drop_zero] at e
    exact e
  have h3 : topCheck.topCheck3 c pv (pack LW n fun l => uf (off + l))
      ((List.range c.m).map fun f => pack LW n fun l => sf f (off + l)) top (mkVC n)
      (preCV n (cget cvs (top.pos - 1))) (accV c n (tvOf top) cvs top.pos)
      (bsel (Nat.ble c.cells.length top.pos) true top.fg) = true := by
    rw [← e', ← euh, ← esg]
    exact h
  have hpv' := PVRep_pre c hc a np n hnnp hnpR pv hpv
  have hBnd : (top.pos + 1) * 2 ^ 126 ≤ 4097 * 2 ^ 126 := Nat.mul_le_mul_right _ (by omega)
  intro l hl
  have hlR : a + l < cnt (c.m - 1) c.recs.length := by omega
  have eS := topLoop_acc c lk top (a + l) hc hpL top.pos 0 (Nat.zero_add _)
  rw [List.drop_zero] at eS
  by_cases hT : top.pos < c.cells.length ∧ top.fg = false
  · obtain ⟨hTp, hTf⟩ := hT
    simp only [hTp, hTf, and_self, ↓reduceIte] at eS
    have eCV : checkVar c lk (uf (off + l)) ((List.range c.m).map fun f => sf f (off + l))
        (mkPre c lk (prefS c (a + l))) top = checkVar.checkVar1 (uf (off + l))
        ((List.range c.m).map fun f => sf f (off + l)) (mkPre c lk (prefS c (a + l))) top
        (tailPart c lk (mkPre c lk (prefS c (a + l))) top (c.cells.drop top.pos) (accS c lk top (a + l) top.pos)) := by
      rw [← eS]; rfl
    have hNT : bsel (Nat.ble c.cells.length top.pos) true top.fg = false := by
      rw [hTf, show Nat.ble c.cells.length top.pos = false from
        Bool.eq_false_iff.2 fun h => by rw [Nat.ble_eq] at h; omega]
      rfl
    unfold topCheck.topCheck3 at h3
    rw [hNT, bsel_ff, bsel_eq] at h3
    split_ifs at h3 with hidx
    rw [finCheck_pre] at h3
    have hci : CVRep c lk a n top.pos (preCV n (cget cvs (top.pos - 1))) :=
      preCV_rep c hc hx lk hlk a np n top.pos hnnp hnpR (by omega) hpL _
        (hcv top.pos (by omega) (by omega))
    have hB32 : B32 = 4294967296 := rfl
    have hm32 : c.m ≤ 32 := hok.m32
    -- the lookup of the tail
    have hrk : ∀ l < np, lget (rankCs (prefS c (a + l))) (c.m - 1) ≤ (c.m - 1) * B32 := by
      intro l hl
      have := rankCs_le (prefS c (a + l))
        (fun r hr b hb => (hok.rcs r (prefS_mem c (a + l) r hr)).2.2.2.2.2.2.2 b hb) (c.m - 1)
      rwa [prefS_length c (a + l) (by omega)] at this
    have hrkL : ∀ l < np, lget (rankCs (prefS c (a + l))) (c.m - 1) < 2 ^ LW := fun l hl =>
      small_LW _ (le_trans (hrk l hl) (Nat.mul_le_mul_right _ (by omega)))
    have hidx' : ∀ l < n, idxS c (a + l) top.pos = lget (rankCs (prefS c (a + l))) (c.m - 1) + top.bsl := by
      rw [Nat.beq_eq, hci.idx, hpv.cs, llast_map_range c.m (by omega),
        show (mkVC n).n = n from rfl,
        pre_pack LW np n _ hrkL hnnp,
        bc_eq, Nat.add_eq, pack_add] at hidx
      refine (pack_inj LW n _ _ (fun l hl => small_LW _ ?_) (fun l hl => small_LW _ ?_)).1 hidx
      · have := idxS_le c hc (a + l) top.pos (by omega) hpL
        rw [prefS_length c (a + l) (by omega)] at this
        rw [hB32] at this ⊢
        omega
      · have := hrk l (by omega)
        have := (hok.rcs top htop).2.2.2.2.2.2.1
        rw [hB32] at *
        omega
    -- the tail on the lanes
    set Uf : ℕ → ℕ := fun l => DS * (lk (idxS c (a + l) top.pos)).V with hUf
    set gf : ℕ → ℕ → ℕ := fun f l => lget (lk (idxS c (a + l) top.pos)).sl f with hgf
    set Sf : ℕ → ℕ := fun l => ∑ q ∈ Finset.range (c.m - 1), gf q l * (rget (prefS c (a + l)) q).dl +
      top.dl * gf (c.m - 1) l with hSf
    have hDS : DS = 2 ^ 36 := rfl
    have eU : Nat.mul DS (preCV n (cget cvs (top.pos - 1))).gv = pack LW n Uf := by
      rw [hci.gv, Nat.mul_eq, pack_const_mul]
    have eSm : Nat.add (lfoldr Nat.add 0 (lzipWith (fun g w => mulv (mkVC n) 37 g w)
          (preCV n (cget cvs (top.pos - 1))).gs (preL (mkVC n).n pv.dl)))
        (Nat.mul top.dl (llast 0 (preCV n (cget cvs (top.pos - 1))).gs)) = pack LW n Sf := by
      have edl : preL n pv.dl = (List.range (c.m - 1)).map fun q =>
          pack LW n fun l => (rget (prefS c (a + l)) q).dl := hpv'.dl
      have e1 : lzipWith (fun g w => mulv (mkVC n) 37 g w) (preCV n (cget cvs (top.pos - 1))).gs
          (preL n pv.dl) = (List.range (c.m - 1)).map fun q =>
            pack LW n fun l => gf q l * (rget (prefS c (a + l)) q).dl := by
        rw [edl, hci.gs, lzipWith_eq, zipWith_range, min_eq_right (Nat.sub_le _ _)]
        refine List.map_congr_left fun q hq => ?_
        rw [mulv_eq n 37 _ _ (by norm_num) (fun l hl j hj => mul_pow_lt _ _ ((hlk _).2 _) hj)
          (fun l hl => lt_of_le_of_lt (rget_prefS_dl c hc (a + l) q) (by rw [hDS]; norm_num))]
        refine pack_congr _ _ _ _ fun l hl => ?_
        rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (rget_prefS_dl c hc (a + l) q) (by rw [hDS]; norm_num))]
      rw [show (mkVC n).n = n from rfl, e1, hci.gs, llast_map_range c.m (by omega), lfoldr_add_map,
        pack_sum, Nat.mul_eq, pack_const_mul, Nat.add_eq, pack_add]
    have eACT : (pack LW n fun l => if (fun _ : ℕ => true) l = true then 2 ^ 143 else 0) =
        pack LW n fun _ => 2 ^ 143 := pack_congr _ _ _ _ fun l _ => by simp
    rw [eU, eSm, hci.gs, show (mkVC n).G = pack LW n fun _ => 2 ^ 143 from mkVC_G n] at h3
    have hokT := finCheck_ok _ _ _ _ _ _ h3
    have hokF := tailV_ok _ _ _ _ _ _ _ _ _ _ _ _ _ hokT
    obtain ⟨af, lf, hA, hB⟩ := acc_inv c hc hx lk hlk top htop hpL a np n hnnp hnpR cvs
      (fun i hi1 hi2 => hcv i hi1 (by omega)) hokF top.pos le_rfl
    have hrt := hok.rcs top htop
    obtain ⟨af', lf', hA', hG'⟩ := tailV_rep c hc hx n hnB Uf Sf gf
      (fun l hl => by
        show DS * _ < _
        have := (hlk (idxS c (a + l) top.pos)).1
        rw [hDS]
        calc 2 ^ 36 * (lk (idxS c (a + l) top.pos)).V < 2 ^ 36 * 2 ^ 48 := Nat.mul_lt_mul_of_pos_left this (by positivity)
          _ ≤ 2 ^ 85 := by norm_num)
      (fun l hl => by
        show _ + _ < _
        have hq : ∀ q, gf q l * (rget (prefS c (a + l)) q).dl ≤ 2 ^ 48 * 2 ^ 36 := fun q =>
          Nat.mul_le_mul ((hlk _).2 q).le (by rw [← hDS]; exact rget_prefS_dl c hc (a + l) q)
        have h1 : ∑ q ∈ Finset.range (c.m - 1), gf q l * (rget (prefS c (a + l)) q).dl ≤
            (c.m - 1) * (2 ^ 48 * 2 ^ 36) := by
          calc _ ≤ ∑ q ∈ Finset.range (c.m - 1), 2 ^ 48 * 2 ^ 36 := Finset.sum_le_sum fun q _ => hq q
            _ = _ := by simp
        have h2 : top.dl * gf (c.m - 1) l ≤ 2 ^ 36 * 2 ^ 48 :=
          Nat.mul_le_mul (by rw [← hDS]; exact hrt.2.1) ((hlk _).2 _).le
        have h3 : (c.m - 1) * (2 ^ 48 * 2 ^ 36) ≤ 31 * (2 ^ 48 * 2 ^ 36) :=
          Nat.mul_le_mul_right _ (by omega)
        have : 31 * (2 ^ 48 * 2 ^ 36) + 2 ^ 36 * 2 ^ 48 < 2 ^ 91 := by norm_num
        omega)
      (fun f l _ => (hlk _).2 f) top.pos top.val top.em top.etm hrt.2.2.2.2.1 hrt.2.2.1 hrt.2.2.2.1
      (fun _ => true) _ _ af lf hA (LABound_mono hB (le_trans hBnd (by norm_num)))
      (by rw [eACT]; exact hokT)
    have := finCheck_sound c hc lk a n hnR _ hpv' (fun l => uf (off + l)) (fun f l => sf f (off + l))
      (fun l hl => huf _ (by omega)) (fun f l hl => hsf f _ (by omega)) top _ _ af' lf' hA'
      (LABound_mono (LABound_grow hB hG') (by
        have : (top.pos + 1) * 2 ^ 126 + 2 ^ 139 ≤ 4097 * 2 ^ 126 + 2 ^ 139 := Nat.add_le_add_right hBnd _
        exact le_trans this (by norm_num)))
      (by rw [eACT]; exact h3) l hl
    -- the scalar tail
    have eidx : Nat.add (mkPre c lk (prefS c (a + l))).Cpre top.bsl = idxS c (a + l) top.pos := by
      rw [hidx' l hl, Cpre_eq, prefS_length c (a + l) hlR]; rfl
    have hpl := prefS_length c (a + l) hlR
    have eT : tailPart c lk (mkPre c lk (prefS c (a + l))) top (c.cells.drop top.pos)
        (accS c lk top (a + l) top.pos) = tailCells c.r c.a1 (Nat.mul (Nat.succ c.m) DS2) (Uf l) (Sf l)
          (packF ((List.range c.m).map fun f => gf f l)) (ldrop top.pos c.cells) top.val top.em
          top.etm (accS c lk top (a + l) top.pos) := by
      show tailPart.tailPart1 c (mkPre c lk (prefS c (a + l))) top (c.cells.drop top.pos)
        (accS c lk top (a + l) top.pos) (lk (Nat.add (mkPre c lk (prefS c (a + l))).Cpre top.bsl)) = _
      rw [eidx, ldrop_eq]
      unfold tailPart.tailPart1
      congr 1
      · have hz : dot (lapp (mkPre c lk (prefS c (a + l))).evs [top.ev]) (lk (idxS c (a + l) top.pos)).sl = 0 := by
          apply dot_zero
          intro x hx
          change x ∈ lapp (lmap SR.ev (prefS c (a + l))) [top.ev] at hx
          rw [lapp_eq, lmap_eq, List.mem_append, List.mem_map, List.mem_singleton] at hx
          rcases hx with ⟨r, hr, rfl⟩ | rfl
          · exact (hok.rcs r (prefS_mem c (a + l) r hr)).1
          · exact hrt.1
        rw [hz]; rfl
      · change dot (lapp (lmap SR.dl (prefS c (a + l))) [top.dl]) (lk (idxS c (a + l) top.pos)).sl = _
        have hlen : (lapp (lmap SR.dl (prefS c (a + l))) [top.dl]).length = c.m - 1 + 1 := by
          rw [lapp_eq, lmap_eq, List.length_append, List.length_map, hpl]; rfl
        rw [dot_eq _ _ (by rw [hlen, hlkl]; omega), hlen, Finset.sum_range_succ]
        show _ = ∑ q ∈ Finset.range (c.m - 1), lget (lk (idxS c (a + l) top.pos)).sl q * (rget (prefS c (a + l)) q).dl +
          top.dl * lget (lk (idxS c (a + l) top.pos)).sl (c.m - 1)
        congr 1
        · refine Finset.sum_congr rfl fun q hq => ?_
          rw [Finset.mem_range] at hq
          have hq' : q < (prefS c (a + l)).length := by omega
          rw [lapp_eq, lmap_eq, List.getD_append _ _ _ _ (by simp; omega),
            List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, rget_of_lt _ _ hq', lget_eq,
            mul_comm]
        · rw [lapp_eq, lmap_eq, List.getD_append_right _ _ _ _ (by simp; omega), lget_eq]
          simp [hpl]
      · rw [packF_range, hlkl]
    rw [eCV, eT]
    exact this
  · simp only [hT, ↓reduceIte] at eS
    have eCV : checkVar c lk (uf (off + l)) ((List.range c.m).map fun f => sf f (off + l))
        (mkPre c lk (prefS c (a + l))) top = checkVar.checkVar1 (uf (off + l))
        ((List.range c.m).map fun f => sf f (off + l)) (mkPre c lk (prefS c (a + l))) top
        (accS c lk top (a + l) top.pos) := by
      rw [← eS]; rfl
    have hNT : bsel (Nat.ble c.cells.length top.pos) true top.fg = true := by
      rcases Nat.lt_or_ge top.pos c.cells.length with hp | hp
      · have hf : top.fg = true := by
          cases hf : top.fg
          · exact absurd ⟨hp, hf⟩ hT
          · rfl
        rw [hf]; cases Nat.ble c.cells.length top.pos <;> rfl
      · rw [show Nat.ble c.cells.length top.pos = true by rw [Nat.ble_eq]; exact hp]; rfl
    unfold topCheck.topCheck3 at h3
    rw [hNT, bsel_tt, finCheck_pre] at h3
    have hokF : (accV c n (tvOf top) cvs top.pos).ok = true := finCheck_ok _ _ _ _ _ _ h3
    obtain ⟨af, lf, hA, hB⟩ := acc_inv c hc hx lk hlk top htop hpL a np n hnnp hnpR cvs
      (fun i hi1 hi2 => hcv i hi1 (by omega)) hokF top.pos le_rfl
    have := finCheck_sound c hc lk a n hnR _ hpv' (fun l => uf (off + l)) (fun f l => sf f (off + l))
      (fun l hl => huf _ (by omega)) (fun f l hl => hsf f _ (by omega)) top _ _ af lf hA
      (LABound_mono hB (le_trans hBnd (by norm_num))) h3 l hl
    rw [eCV]
    exact this

/-- The check of the top `j`: every state of the top passes `checkVar` against its claimed
state, read from the fields `UV`, `US` of the claimed table of time `t` from the state `base` on. -/
theorem topCheck_sound (c : Ctx) (hc : ctxOK c = true) (hx : CtxX c) (lk : ℕ → SV)
    (hlk : ∀ idx, (lk idx).V < 2 ^ 48 ∧ ∀ f, lget (lk idx).sl f < 2 ^ 48)
    (hlkl : ∀ idx, (lk idx).sl.length = c.m) (hi : ℕ)
    (hhi : hi ≤ c.recs.length) (np : ℕ) (hnp : np = cnt (Nat.sub c.m 1) hi) (pv : PV)
    (hpv : PVRep c 0 np pv) (cvs : List CV) (hcvs : cvs.length = hi)
    (hcv : ∀ i, 1 ≤ i → i ≤ hi → CVRep c lk 0 np i (cget cvs (i - 1)))
    (nU : ℕ) (hnUB : nU ≤ B32) (uf : ℕ → ℕ) (sf : ℕ → ℕ → ℕ) (huf : ∀ s < nU, uf s < 2 ^ 48)
    (hsf : ∀ f s, s < nU → sf f s < 2 ^ 48) (base j : ℕ) (hj : j < hi) (hbase : base ≤ cnt c.m j)
    (hnU : cnt c.m (j + 1) - base ≤ nU)
    (h : topCheck c pv cvs (pack LW nU uf) ((List.range c.m).map fun f => pack LW nU (sf f)) base j
      (rget c.recs j) = true) :
    ∀ l < cnt (c.m - 1) (j + 1),
      checkVar c lk (uf (cnt c.m j - base + l))
        ((List.range c.m).map fun f => sf f (cnt c.m j - base + l)) (mkPre c lk (prefS c l))
        (rget c.recs j) = true := by
  have hok := cok_of_ctxOK c hc
  obtain ⟨m', hm'⟩ : ∃ m', c.m = m' + 1 := ⟨c.m - 1, by have := hok.m2; omega⟩
  have hsucc : cnt c.m (j + 1) = cnt c.m j + cnt (c.m - 1) (j + 1) := by
    rw [hm', cnt_succ]; rfl
  have hnnp : cnt (c.m - 1) (j + 1) ≤ np := by rw [hnp]; exact cnt_mono _ (by omega)
  have hnpR : 0 + np ≤ cnt (c.m - 1) c.recs.length := by
    rw [Nat.zero_add, hnp]; exact cnt_mono _ hhi
  intro l hl
  have := topCheck1_sound c hc hx lk hlk hlkl hi hhi 0 np (cnt (c.m - 1) (j + 1)) hnnp hnpR pv hpv
    cvs hcvs hcv nU hnUB uf sf huf hsf (cnt c.m j - base) j hj (by omega) h l hl
  rwa [Nat.zero_add] at this

/-! ## A range of tops, a step -/

/-- A passed range: the global facts of the step, and every state of the tops `lo .. hi - 1`
passes. -/
theorem lanesRange_StOK (g : Grid) (t : ℕ) (Nn Nt : List ℕ) (lo hi : ℕ)
    (h : lanesRange g t Nn Nt lo hi = true) :
    2 ≤ g.m ∧ litsOK (Wm g.m) Nt = true ∧ (decS g.m Nt).length = (stsS g t Nn).length ∧
      ∀ k, cnt g.m lo ≤ k → k < cnt g.m (min hi (mkCtx g t).recs.length) → StOK g t Nn Nt k := by
  have hx : CtxX (mkCtx g t) := mkCtx_X g t
  unfold lanesRange lanesRange.lanesRange1 at h
  rw [bsel_false, bsel_false, bsel_false, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨hc, hNn, hNt, h⟩ := h
  have hok := cok_of_ctxOK _ hc
  have hm2 : 2 ≤ g.m := hok.m2
  have hW : 0 < Wm g.m := by show 0 < 48 * (g.m + 1); positivity
  change lanesRange.lanesRange2 (mkCtx g t) (litCat (Wm g.m) Nn) (litCat (Wm g.m) Nt) (Wm g.m) lo
    (min hi (mkCtx g t).recs.length) (mkCtx g t).recs.length = true at h
  rw [litCat_spec _ hW Nn hNn, litCat_spec _ hW Nt hNt] at h
  have eNn : lfoldr (decLit (Wm g.m) (2 ^ Wm g.m - 1)) [] Nn = decS g.m Nn := rfl
  have eNt : lfoldr (decLit (Wm g.m) (2 ^ Wm g.m - 1)) [] Nt = decS g.m Nt := rfl
  rw [eNn, eNt] at h
  set c := mkCtx g t with hcdef
  have hcm : c.m = g.m := rfl
  set R := c.recs.length with hR
  set H := min hi R with hH
  have hHR : H ≤ R := min_le_right _ _
  set sn : ℕ → ℕ := fun k => (decS g.m Nn).getD k 0 with hsn
  set st : ℕ → ℕ := fun k => (decS g.m Nt).getD k 0 with hst
  have hsnb : ∀ k, sn k < 2 ^ Wm g.m := fun k => decAll_getD_lt _ hW Nn k
  have hstb : ∀ k, st k < 2 ^ Wm g.m := fun k => decAll_getD_lt _ hW Nt k
  unfold lanesRange.lanesRange2 at h
  dsimp only at h
  rw [bsel_false, bsel_false, bsel_false, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Nat.beq_eq, Nat.ble_eq, Nat.ble_eq] at h
  obtain ⟨⟨hTt, hTtB⟩, hNS, h⟩ := h
  have hlenS : (stsS g t Nn).length = cnt g.m R := stsS_length g t Nn hm2
  refine ⟨hm2, hNt, by rw [hlenS, hTt]; rfl, fun k hk1 hk2 => ?_⟩
  obtain ⟨m', hm'⟩ : ∃ m', g.m = m' + 1 := ⟨g.m - 1, by omega⟩
  have hcnt0 : cnt g.m 0 = 0 := by rw [hm', cnt_succ_zero]
  have hHn : cnt c.m H ≤ cnt c.m R := cnt_mono _ hHR
  have hH1 : 1 ≤ H := by
    by_contra h0
    have : H = 0 := by omega
    rw [this, hcnt0] at hk2
    omega
  -- the tables as packs
  have ePn : preS (Wm c.m) (cnt c.m H) (pack (Wm c.m) (decS g.m Nn).length sn) =
      pack (Wm c.m) (cnt c.m H) sn :=
    pre_pack _ _ _ sn (fun l _ => hsnb l) hNS
  have ePt : preS (Wm c.m) (Nat.sub (cnt c.m H) (cnt c.m lo))
      (Nat.shiftRight (pack (Wm c.m) (decS g.m Nt).length st) (Nat.mul (Wm c.m) (cnt c.m lo))) =
      pack (Wm c.m) (Nat.sub (cnt c.m H) (cnt c.m lo)) (fun l => st (l + cnt c.m lo)) := by
    show pre _ _ (drp (Wm c.m) (cnt c.m lo) (pack _ _ st)) = _
    rw [drp_pack (Wm c.m) _ _ st (fun l _ => hstb l)]
    exact pre_pack (Wm c.m) _ _ _ (fun l _ => hstb _) (by rw [hTt]; show cnt c.m H - cnt c.m lo ≤ _; omega)
  rw [show Wm g.m = Wm c.m from rfl, ePn, ePt] at h
  unfold lanesRange.lanesRange3 at h
  rw [bsel_false, bsel_false, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨hFn, hFt, h⟩ := h
  have hmc : c.m ≤ 32 := hok.m32
  have hNSB : cnt c.m H ≤ B32 := le_trans hHn (by rw [← hTt]; exact hTtB)
  set NS := cnt c.m H with hNSdef
  set nU := Nat.sub NS (cnt c.m lo) with hnUdef
  have hnUB : nU ≤ B32 := le_trans (Nat.sub_le _ _) hNSB
  obtain ⟨eFn1, eFn2⟩ := fields_spec c.m NS hNSB hmc sn (fun s _ => hsnb s) hFn
  obtain ⟨eFt1, eFt2⟩ := fields_spec c.m nU hnUB hmc (fun l => st (l + cnt c.m lo))
    (fun s _ => hstb _) hFt
  set Fn := fields c.m (pack (Wm c.m) NS sn) NS with hFndef
  set Ft := fields c.m (pack (Wm c.m) nU fun l => st (l + cnt c.m lo)) nU with hFtdef
  set np := cnt (Nat.sub c.m 1) H with hnpdef
  set pv := PV.mk (preL np (mkPV c.recs (Nat.sub c.m 1)).pos) (preL np (mkPV c.recs (Nat.sub c.m 1)).dl)
    (preL np (mkPV c.recs (Nat.sub c.m 1)).fg) (preL np (mkPV c.recs (Nat.sub c.m 1)).cs) with hpvdef
  have hpv : PVRep c 0 np pv := mkPV_rep c hc np (cnt_mono _ hHR)
  unfold lanesRange.lanesRange4 lanesRange.lanesRange5 at h
  rw [bsel_false, Bool.and_eq_true, lall_iff, lall_iff] at h
  obtain ⟨hcvs, htops⟩ := h
  set cvs := lmapIdx (fun i cl => mkCV (mkVC np) pv NS c.a1 Fn.1 Fn.2.1 (Nat.succ i) cl) 0
    (ltake H c.cells) with hcvsdef
  set lk := lkS g Nn with hlkdef
  have hcellsH : H ≤ c.cells.length := by rw [hok.len]; exact hHR
  have hcvslen : cvs.length = H := by
    rw [hcvsdef, lmapIdx_length, ltake_eq, List.length_take]
    omega
  -- the lookups
  have hFV : Fn.1 = pack LW NS fun s => (lk s).V := by
    rw [eFn1]
    refine pack_congr _ _ _ _ fun s hs => ?_
    rw [hlkdef, lkS_eq g Nn hNn s (by omega)]
  have hFS : Fn.2.1 = (List.range c.m).map fun f => pack LW NS fun s => lget (lk s).sl f := by
    rw [eFn2]
    refine List.map_congr_left fun f hf => pack_congr _ _ _ _ fun s hs => ?_
    rw [hlkdef, lkS_eq g Nn hNn s (by omega), lget_eq]
    have hf' : f < g.m := List.mem_range.1 hf
    rw [List.getD_eq_getElem _ _ (by simpa using hf')]
    simp only [List.getElem_map, List.getElem_range]
    rfl
  have hcv : ∀ i, 1 ≤ i → i ≤ H → CVRep c lk 0 np i (cget cvs (i - 1)) := by
    intro i hi1 hiH
    have hi' : i - 1 < cvs.length := by omega
    have e0 := lmapIdx_getElem (fun i cl => mkCV (mkVC np) pv NS c.a1 Fn.1 Fn.2.1 (Nat.succ i) cl) 0
      (ltake H c.cells) (i - 1) hi'
    rw [cget_of_lt _ _ hi', show cvs[i - 1] = _ from e0]
    have hcell : (ltake H c.cells)[i - 1]'(by rw [ltake_eq, List.length_take]; omega) = cellS c i := by
      unfold cellS
      simp only [ltake_eq, List.getElem_take]
      rw [List.headD_eq_head?_getD, List.head?_drop, List.getElem?_eq_getElem (by omega)]
      rfl
    have e1 : Nat.succ (0 + (i - 1)) = i := by omega
    simp only [e1, hcell]
    refine mkCV_rep c hc hx lk H hHR 0 np (Nat.zero_add _).le pv hpv NS hNSB (fun s _ => ⟨(lkS_bound g Nn s).1,
      fun f _ => (lkS_bound g Nn s).2 f⟩) Fn.1 hFV Fn.2.1 hFS i hi1 hiH ?_
    have hmem := hcvs (cvs[i - 1]'hi') (List.getElem_mem hi')
    rw [show cvs[i - 1] = _ from e0] at hmem
    simpa only [e1, hcell] using hmem
  -- the top `j` of the state `k`
  have hex : ∃ j, k < cnt g.m (j + 1) := ⟨H - 1, by rw [show H - 1 + 1 = H by omega]; exact hk2⟩
  set j := Nat.find hex with hjdef
  have hj1 : k < cnt g.m (j + 1) := Nat.find_spec hex
  have hjH : j < H := by
    have := Nat.find_min' hex (show k < cnt g.m (H - 1 + 1) by rw [show H - 1 + 1 = H by omega]; exact hk2)
    omega
  have hj0 : cnt g.m j ≤ k := by
    rcases Nat.eq_zero_or_pos j with e | e
    · rw [e, hcnt0]; omega
    · have := Nat.find_min hex (show j - 1 < j by omega)
      rw [show j - 1 + 1 = j by omega] at this
      omega
  have hloj : lo ≤ j := by
    by_contra hc'
    have : cnt g.m (j + 1) ≤ cnt g.m lo := cnt_mono _ (by omega)
    omega
  have hjR : j < R := lt_of_lt_of_le hjH hHR
  set l := k - cnt g.m j with hldef
  have hsucc : cnt g.m (j + 1) = cnt g.m j + cnt (g.m - 1) (j + 1) := by
    rw [hm', cnt_succ]
    rfl
  have hl : l < cnt (g.m - 1) (j + 1) := by omega
  have hkl : k = cnt g.m j + l := by omega
  intro hk
  have hget := stsS_get g t Nn hm2 j l hjR hl
  rw [← hkl, List.getElem?_eq_getElem hk, Option.some_inj] at hget
  rw [hget, checkState_eq c hok.newp]
  dsimp only
  -- the top check of `j`
  have htop : topCheck c pv cvs (pack LW nU fun s => st (s + cnt c.m lo) % 2 ^ 48)
      ((List.range c.m).map fun f => pack LW nU fun s => st (s + cnt c.m lo) / 2 ^ (48 * (f + 1)) % 2 ^ 48)
      (cnt c.m lo) j (rget c.recs j) = true := by
    have hlen' : j - lo < (lmapIdx (fun j r => (j, r)) lo (ltake (Nat.sub H lo) (ldrop lo c.recs))).length := by
      rw [lmapIdx_length, ltake_eq, ldrop_eq, List.length_take, List.length_drop]
      show j - lo < min (H - lo) _
      omega
    have := htops _ (List.getElem_mem hlen')
    rw [lmapIdx_getElem] at this
    simp only [ltake_eq, ldrop_eq, List.getElem_take, List.getElem_drop] at this
    have e3 : lo + (j - lo) = j := by omega
    simp only [e3] at this
    rw [← eFt1, ← eFt2, rget_of_lt _ _ hjR]
    exact this
  have := topCheck_sound c hc hx lk (fun idx => lkS_bound g Nn idx) (fun idx => lkS_length g Nn idx)
    H hHR np rfl pv hpv cvs hcvslen hcv nU hnUB (fun s => st (s + cnt c.m lo) % 2 ^ 48)
    (fun f s => st (s + cnt c.m lo) / 2 ^ (48 * (f + 1)) % 2 ^ 48)
    (fun s _ => Nat.mod_lt _ (by norm_num)) (fun f s _ => Nat.mod_lt _ (by norm_num))
    (cnt c.m lo) j hjH (cnt_mono _ hloj) (by show cnt c.m (j + 1) - cnt c.m lo ≤ NS - cnt c.m lo
                                             have := cnt_mono c.m (show j + 1 ≤ H by omega); omega)
    htop l hl
  have e2 : cnt c.m j - cnt c.m lo + l + cnt c.m lo = k := by
    have : cnt g.m lo ≤ cnt g.m j := cnt_mono _ hloj
    show cnt g.m j - cnt g.m lo + l + cnt g.m lo = k
    omega
  simp only [e2] at this
  exact this

/-- Ranges of top records from `0` to at least the number of records, each passed by
`lanesRange`, give the scalar check of the step. -/
theorem checkStep_of_lanesRanges (g : Grid) (t : ℕ) (Nn Nt : List ℕ) (cs : List ℕ)
    (h0 : cs.head? = some 0) (hR : (mkCtx g t).recs.length ≤ cs.getLast?.getD 0)
    (h : ∀ i, i + 1 < cs.length → lanesRange g t Nn Nt (cs.getD i 0) (cs.getD (i + 1) 0) = true) :
    checkStep g t Nn Nt = true := by
  set R := (mkCtx g t).recs.length with hRdef
  have hR1 : 1 ≤ R := mkCtx_recs_pos g t
  have hlen : 2 ≤ cs.length := by
    rcases cs with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at h0
    · simp at h0 hR
      omega
    · simp
  obtain ⟨hm, hlits, hdl, -⟩ := lanesRange_StOK g t Nn Nt _ _ (h 0 (by omega))
  refine checkStep_of_StOK g t Nn Nt hlits hdl fun k hk => ?_
  have hkR : k < cnt g.m R := by rw [← stsS_length g t Nn hm]; exact hk
  have hcnt0 : cnt g.m 0 = 0 := by
    obtain ⟨m', hm'⟩ : ∃ m', g.m = m' + 1 := ⟨g.m - 1, by omega⟩
    rw [hm', cnt_succ_zero]
  set f : ℕ → ℕ := fun i => cnt g.m (min (cs.getD i 0) R) with hf
  have hf0 : f 0 = 0 := by
    have : cs.getD 0 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, h0]
      rfl
    simp only [hf, this, Nat.zero_min, hcnt0]
  have hflast : f (cs.length - 1) = cnt g.m R := by
    have : R ≤ cs.getD (cs.length - 1) 0 := by
      rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?]
      exact hR
    simp only [hf, min_eq_right this]
  have hex : ∃ j, k < f j := ⟨cs.length - 1, by rw [hflast]; exact hkR⟩
  have hj : k < f (Nat.find hex) := Nat.find_spec hex
  have hj0 : Nat.find hex ≠ 0 := fun e => by rw [e, hf0] at hj; omega
  have hjle : Nat.find hex ≤ cs.length - 1 := Nat.find_min' hex (by rw [hflast]; exact hkR)
  have hfi : f (Nat.find hex - 1) ≤ k := not_lt.1 (Nat.find_min hex (by omega))
  have hcsi : cs.getD (Nat.find hex - 1) 0 ≤ R := by
    by_contra hc
    have : f (Nat.find hex - 1) = cnt g.m R := by
      simp only [hf, min_eq_right (le_of_lt (not_le.1 hc))]
    omega
  obtain ⟨-, -, -, hst⟩ := lanesRange_StOK g t Nn Nt _ _ (h (Nat.find hex - 1) (by omega))
  have e1 : Nat.find hex - 1 + 1 = Nat.find hex := by omega
  rw [e1] at hst
  refine hst k ?_ ?_ hk
  · have : f (Nat.find hex - 1) = cnt g.m (cs.getD (Nat.find hex - 1) 0) := by
      simp only [hf, min_eq_left hcsi]
    omega
  · exact hj

/-- The lanes check of a whole step gives the scalar check. -/
theorem checkStep_of_lanesStep (g : Grid) (t : ℕ) (Nn Nt : List ℕ)
    (h : lanesStep g t Nn Nt = true) : checkStep g t Nn Nt = true := by
  refine checkStep_of_lanesRanges g t Nn Nt [0, (mkCtx g t).recs.length] rfl (by simp) fun i hi => ?_
  have hi0 : i = 0 := by simp at hi; omega
  subst hi0
  exact h

end Robbins.Cert.SO.L
