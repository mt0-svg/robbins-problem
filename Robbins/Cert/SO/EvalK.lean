import Robbins.Cert.EvalK

/-!
# The second-order step in kernel form

The specification of Robbins/Cert/SO/Spec.lean, sections 3 to 6, written for the Lean kernel as Robbins/Cert/EvalK.lean
is: in the per-state code every loop is a recursor, every branch a `Bool.rec` on `Nat.ble` or
`Nat.beq`, every operation a direct `Nat` operation. The per-step data (cells, records, penalty
lists) is built once per step with ordinary list functions.

Signs. The specification works over the integers. Here the sum `R` of section 5 is carried as a
pair `(rp, rn)` with `R = rp - rn` (the continuation integral `IB` has a negative part), and the
positive parts of the specification (`M`, the numerator of the chord) are truncated differences;
every other quantity is a natural number by its definition. So every value below is the integer
of the specification, with no condition on the data.

The check of one step. For a claimed table of time `t + 1` (`Nn`) and of time `t` (`Nt`), for
every state `k` of `Y_t` and every record list of section 6 built from `k` (all of them, not only
the minimizing one), with `(rp, rn, mu)` the output of section 5 on the list:
`2 D^2 uh_t (k) + rn ≤ rp` (that is `uh_t (k) ≤ T0`) and `sg_t (k)_l ≤ mu_l` for every `l`. The
evaluator of the specification produces equality (the program soq); the inequalities are what the
soundness of section 8.7 uses.

Sharing. The quantities of a cell `i ≤ im` that do not involve the last record (the lookup of
`H_i`, `sigma`, `beta` less `D Em`, `S` and the coefficients less the last one) depend on the
first `m - 1` records only; they are computed once per such prefix (`Pre`, `PD`) and used for
every last record. The accumulators `acc` and `lam` are packed, the coordinate `l` in the bits
`[128 l, 128 (l + 1))` (`F = 2 ^ 128`), so that `acc += Q coef` is one product and one sum.

Kernel cost. The kernel instantiates the body of a definition or a `let` at each use, so the
code that runs per state and per cell is written as small definitions that pass their values as
arguments.

Tables. A table is a list of literals; a literal holds up to 16 states, the state `s` in the bits
`[W s, W (s + 1))`, `W = 48 (m + 1)`, under a leading `1` bit; a state holds `uh` in the bits
`[0, 48)` and `sg_l` in the bits `[48 (l + 1), 48 (l + 2))`. The lookups into the table of time
`t + 1` go through a complete binary tree over its literals, built once per step, and each index
is forced to a literal before the descent (`lkF`), so that a repeated lookup is one hit of the
kernel's cache. Every loop over many items (states, literals) is a loop over the literals, so that
the kernel's recursion depth stays of the order of their number.

`D = 2 ^ 36` (`DS`).
-/

namespace Robbins.Cert.SO.K

open Robbins.Cert Robbins.Cert.K

/-- `D = 2 ^ 36`. -/
def DS : Nat := 68719476736

/-- `D ^ 2 = 2 ^ 72`. -/
def DS2 : Nat := 4722366482869645213696

/-- `2 ^ 48 - 1`. -/
def M48 : Nat := 281474976710655

/-- `F = 2 ^ 128`, the field of the packed accumulators. -/
def F128 : Nat := 340282366920938463463374607431768211456

/-- `F - 1`. -/
def M128 : Nat := 340282366920938463463374607431768211455

/-! ## Per-step data -/

/-- A record of section 5.0, with the quantities of section 5 that depend on it alone. -/
structure SR where
  /-- `pos`: the cell of the record. -/
  pos : Nat
  /-- `val = gpt[gi]`. -/
  val : Nat
  /-- `map`: the local index of `ceil_{t+1} (gi)` in `G_{t+1}`. -/
  cm : Nat
  /-- `w`: the box width (`0` for the point `1` and the new points). -/
  dl : Nat
  /-- `forg`. -/
  fg : Bool
  /-- `ev = gpt[global_{t+1} (map)] - val` (`0` if `forg`). -/
  ev : Nat
  /-- `E_t[gi]`. -/
  em : Nat
  /-- `r E_{t+1}[gi]`. -/
  pm : Nat
  /-- `E_{t-1}[gi]`. -/
  etm : Nat
  /-- `C (map + j, j + 1)`, `j = 0 .. m - 1`. -/
  bs : List Nat
  /-- `C (map + m - 1, m)`, the last of `bs`. -/
  bsl : Nat

/-- A cell `i` of `P_t`, with the constants of section 5 that depend on the cell alone. -/
structure SC where
  /-- `p_{i-1}`. -/
  pa : Nat
  /-- `p_i`. -/
  pb : Nat
  /-- `P'_i = gpt[global_{t+1} (nxt_i)]`. -/
  pn : Nat
  /-- `C (nxt_i + b, b + 1)`, `b = 0 .. m - 1`. -/
  cb : List Nat
  /-- `E_t[pts[i]]`. -/
  et : Nat
  /-- `E_{t+1}[pts[i]]`. -/
  e1 : Nat
  /-- `E_{t-1}[pts[i]]`. -/
  etm : Nat
  /-- `h = p_i - p_{i-1}`. -/
  h : Nat
  /-- `2 h`. -/
  h2 : Nat
  /-- `p_i ^ 2 - p_{i-1} ^ 2`. -/
  sqd : Nat
  /-- `a1 (p_i ^ 2 - p_{i-1} ^ 2)`, `a1 = r D`. -/
  a1sq : Nat

/-- The data of one step. -/
structure Ctx where
  /-- `m`. -/
  m : Nat
  /-- `r = n - t`. -/
  r : Nat
  /-- `a1 = r D`. -/
  a1 : Nat
  /-- `F ^ (m - 1)`, the field of the last record. -/
  FT : Nat
  /-- The cells `1 .. L`. -/
  cells : List SC
  /-- The records of the local points `0 .. cnt_t` of `G_t`. -/
  recs : List SR
  /-- The records of the new points. -/
  newp : List SR

/-- `C (x + j, j + 1)` for `j = i .. i + k - 1`, from `b = C (x + i, i + 1)`. -/
def binomsAux (x : Nat) : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | k + 1, i, b => b :: binomsAux x k (i + 1) (b * (x + i + 1) / (i + 2))

/-- `C (x + j, j + 1)`, `j = 0 .. m - 1`: the terms of the rank of a sorted tuple (section 2 of the
format). -/
def binoms (m x : Nat) : List Nat := binomsAux x m 0 x

/-- Section 3: `E_t` from `E_{t+1}`. -/
noncomputable def nextE (gptD E : List Nat) : List Nat :=
  lzipWith (fun p e => Nat.div (Nat.mul e (Nat.sub DS p)) DS) gptD E

/-- `E_{n-q}` on the global points `0 .. J`. -/
noncomputable def Eback (gptD : List Nat) (q : Nat) : List Nat :=
  @Nat.rec (fun _ => List Nat) (lmap (fun _ => DS) gptD) (fun _ ih => nextE gptD ih) q

/-- The window of time `t`. -/
def winAt (g : Grid) (t : Nat) : Win := g.win (g.start.getD (t - 1) 0)

/-- `global` of a local index. -/
def glob (J : Nat) (w : Win) (k : Nat) : Nat := if k < w.cnt then w.s + k else J

/-- The record of the global index `gi` (section 5.0). -/
def mkRec (m J r : Nat) (w1 : Win) (gptD Et E1 Etm pts : List Nat) (gi dl : Nat) (fg : Bool) :
    SR :=
  let cm := ceilLocal J w1 gi
  let val := gptD.getD gi 0
  { pos := pts.idxOf gi + 1, val := val, cm := cm, dl := dl, fg := fg,
    ev := if fg then 0 else gptD.getD (glob J w1 cm) 0 - val,
    em := Et.getD gi 0, pm := r * E1.getD gi 0, etm := Etm.getD gi 0, bs := binoms m cm,
    bsl := (binoms m cm).getLastD 0 }

/-- The data of the step `t` (`1 ≤ t < n`). -/
noncomputable def mkCtx (g : Grid) (t : Nat) : Ctx :=
  let J := g.gpt.length
  let gptD := g.gpt ++ [DS]
  let r := g.n - t
  let a1 := r * DS
  let E1 := Eback gptD (r - 1)
  let Et := nextE gptD E1
  let Etm := nextE gptD Et
  let w0 := winAt g t
  let w1 := winAt g (t + 1)
  let inW (w : Win) (j : Nat) : Bool := w.s ≤ j && j < w.s + w.cnt
  let pts := (List.range J).filter (fun j => inW w0 j || inW w1 j) ++ [J]
  let pv := pts.map (fun j => gptD.getD j 0)
  let cells := (List.zip pts (List.zip (0 :: pv) pv)).map fun (j, pa, pb) =>
    let nx := ceilLocal J w1 j
    ({ pa := pa, pb := pb, pn := gptD.getD (glob J w1 nx) 0, cb := binoms g.m nx,
       et := Et.getD j 0, e1 := E1.getD j 0, etm := Etm.getD j 0, h := pb - pa,
       h2 := 2 * (pb - pa), sqd := pb * pb - pa * pa, a1sq := a1 * (pb * pb - pa * pa) } : SC)
  let loc := (List.range w0.cnt).map fun k =>
    let gi := w0.s + k
    mkRec g.m J r w1 gptD Et E1 Etm pts gi
      (gptD.getD gi 0 - (if k = 0 then 0 else gptD.getD (gi - 1) 0)) false
  let recs := loc ++ [mkRec g.m J r w1 gptD Et E1 Etm pts J 0 true]
  let newp := ((List.range w1.cnt).map (w1.s + ·)).filter (fun j => w0.s + w0.cnt ≤ j) |>.map
    fun j => mkRec g.m J r w1 gptD Et E1 Etm pts j 0 false
  ⟨g.m, r, a1, F128 ^ (g.m - 1), cells, recs, newp⟩

/-! ## Lookups into the table of time `t + 1` -/

/-- A complete binary tree over the literals of a table. -/
inductive BT where
  /-- A literal. -/
  | lf (x : Nat)
  /-- A node. -/
  | nd (l r : BT)

/-- Adjacent pairs of a list of trees, `[nd t0 t1, nd t2 t3, ...]`, a last odd tree paired with
`lf 0`. -/
noncomputable def pairUp (l : List BT) : List BT :=
  @List.rec BT (fun _ => Option BT → List BT)
    (fun p => @Option.rec BT (fun _ => List BT) [] (fun a => [BT.nd a (BT.lf 0)]) p)
    (fun x _ ih p => @Option.rec BT (fun _ => List BT) (ih (some x)) (fun a => BT.nd a x :: ih none) p)
    l none

/-- The tree of depth `d` over the literals of `L` (built bottom-up, so that the kernel's
recursion depth stays of the order of `d`; a missing subtree is `lf 0`). -/
noncomputable def bld (d : Nat) (L : List Nat) : BT :=
  @List.rec BT (fun _ => BT) (BT.lf 0) (fun a _ _ => a)
    (@Nat.rec (fun _ => List BT) (lmap BT.lf L) (fun _ ih => pairUp ih) d)

/-- The literal `li` of a tree of depth `d`. -/
noncomputable def bget (T : BT) (d li : Nat) : Nat :=
  @BT.rec (fun _ => Nat → Nat) (fun x _ => x)
    (fun _ _ rl rr d => bget2 li rl rr (Nat.sub d 1)) T d
where
  /-- One level of the descent. -/
  bget2 (li : Nat) (rl rr : Nat → Nat) (d' : Nat) : Nat :=
    bsel (Nat.beq (Nat.land (Nat.shiftRight li d') 1) 1) (rr d') (rl d')

/-- A state of the table of time `t + 1`: `uh` and the slopes. -/
structure SV where
  /-- `uh_{t+1}`. -/
  V : Nat
  /-- `sg_{t+1}`. -/
  sl : List Nat

/-- The `m` slopes of a packed state. -/
noncomputable def slopes (m st : Nat) : List Nat :=
  @Nat.rec (fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih x => slopes2 ih (Nat.shiftRight x 48)) m st
where
  /-- One slope. -/
  slopes2 (ih : Nat → List Nat) (x' : Nat) : List Nat := Nat.land x' M48 :: ih x'

/-- The packed state of rank `idx` (`W = 48 (m + 1)`, `MW = 2 ^ W - 1`). -/
noncomputable def lkSt (T : BT) (d W MW idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight (bget T d (Nat.shiftRight idx 4)) (Nat.mul W (Nat.land idx 15))) MW

/-- The state of rank `idx`. -/
noncomputable def lk0 (T : BT) (d m W MW idx : Nat) : SV :=
  lk1 m (lkSt T d W MW idx)
where
  /-- Decode. -/
  lk1 (m st : Nat) : SV := SV.mk (Nat.land st M48) (slopes m st)

/-- `f idx`, with `idx` reduced to a literal first. -/
noncomputable def lkF (f : Nat → SV) (idx : Nat) : SV :=
  @Nat.rec (fun _ => SV) (f 0) (fun j _ => f (Nat.succ j)) idx

/-! ## Section 5, generic pieces -/

/-- `l[i]`, `0` past the end. -/
noncomputable def lget (l : List Nat) (i : Nat) : Nat := hd (ldrop i l)

/-- `min a b`. -/
noncomputable def nmin2 (a b : Nat) : Nat := bsel (Nat.ble a b) a b

/-- The pair `(rp, rn)`. -/
structure PN where
  /-- The positive part. -/
  p : Nat
  /-- The negative part. -/
  n : Nat

/-- Section 5.1, `cell2 = P - N` added to `(rp, rn)`. -/
noncomputable def cell2 (pa pb a0 a1 b0 b1 rp rn : Nat) : PN :=
  cell2a pa pb a0 a1 b0 b1 rp rn (Nat.add a1 b1)
where
  /-- With `kk = a1 + b1`. -/
  cell2a (pa pb a0 a1 b0 b1 rp rn kk : Nat) : PN :=
    cell2b pa pb a0 a1 b0 b1 rp rn kk (Nat.add a0 (Nat.mul kk pa)) (Nat.add a0 (Nat.mul kk pb))
  /-- With `A0 = a0 + kk pa`, `A1 = a0 + kk pb`. -/
  cell2b (pa pb a0 a1 b0 b1 rp rn kk A0 A1 : Nat) : PN :=
    bsel (Nat.ble A1 b0)
      (PN.mk (Nat.add rp (Nat.mul (Nat.sub pb pa) (Nat.add (Nat.mul 2 a0) (Nat.mul a1 (Nat.add pb pa)))))
        rn)
      (bsel (Nat.ble b0 A0)
        (PN.mk (Nat.add rp (Nat.mul (Nat.mul 2 b0) (Nat.sub pb pa)))
          (Nat.add rn (Nat.mul b1 (Nat.sub (Nat.mul pb pb) (Nat.mul pa pa)))))
        (cell2z pa pb a0 a1 b0 b1 rp rn kk (Nat.add pa (Nat.div (Nat.sub b0 A0) kk))))
  /-- The crossing case, `z = pa + floor ((b0 - A0) / kk)`. -/
  cell2z (pa pb a0 a1 b0 b1 rp rn kk z : Nat) : PN :=
    PN.mk (Nat.add rp (Nat.add
        (Nat.mul (Nat.sub z pa) (Nat.add (Nat.mul 2 a0) (Nat.mul a1 (Nat.add z pa))))
        (Nat.mul (Nat.mul 2 b0) (Nat.sub pb z))))
      (Nat.add rn (Nat.add (Nat.mul b1 (Nat.sub (Nat.mul pb pb) (Nat.mul z z))) (Nat.mul 2 kk)))

/-- Section 5.2, the chord (for `S > 0`). -/
noncomputable def chord (pa pb a0 a1 b0 b1 S : Nat) : Nat :=
  chord1 pa pb b0 S (Nat.add a1 b1) (Nat.add a0 (Nat.mul (Nat.add a1 b1) pa))
    (Nat.add a0 (Nat.mul (Nat.add a1 b1) pb))
where
  /-- With `kk`, `A0`, `A1`. -/
  chord1 (pa pb b0 S kk A0 A1 : Nat) : Nat :=
    bsel (Nat.ble A1 b0) 0
      (bsel (Nat.ble (Nat.add b0 S) A0) (Nat.sub pb pa)
        (chord2 pa pb b0 S kk A0 A1
          (bsel (Nat.ble b0 A0) (Nat.mul (Nat.add (Nat.sub A0 b0) (Nat.sub A1 b0)) (Nat.sub pb pa))
            (chordLo pa pb kk (Nat.sub b0 A0) (Nat.sub A1 b0)))))
  /-- The lower component of `pos2 (0)` when `da < 0 < db`. -/
  chordLo (pa pb kk nda db : Nat) : Nat :=
    Nat.mul (Nat.add (Nat.sub kk (Nat.mod nda kk)) db)
      (Nat.sub (Nat.sub pb (Nat.add pa (Nat.div nda kk))) 1)
  /-- With `lo`, the lower component of `pos2 (0)`. -/
  chord2 (pa pb b0 S kk A0 A1 lo : Nat) : Nat :=
    bsel (Nat.ble A1 (Nat.add b0 S)) (Nat.div lo (Nat.mul 2 S))
      (chord3 pb S kk A1 (Nat.add b0 S) lo (Nat.sub (Nat.add b0 S) A0)
        (Nat.sub pb (Nat.add pa (Nat.div (Nat.sub (Nat.add b0 S) A0) kk))))
  /-- With `nac = b0 + S - A0` and `hz = pb - z`. -/
  chord3 (_pb S kk A1 b0S lo nac hz : Nat) : Nat :=
    Nat.div (Nat.sub (Nat.add lo (Nat.mul (Nat.mod nac kk) hz))
      (Nat.add (Nat.mul (Nat.sub A1 b0S) hz) (Nat.mul 2 kk))) (Nat.mul 2 S)

/-! ## The prefix data: one record list's first `m - 1` records -/

/-- The quantities of the prefix records in one cell: `Σ sl_slot ev`, `S'`, the packed
coefficients, and the fields `F ^ l` of the records with their own cell here. -/
structure PS where
  /-- `Σ_{l ≤ m - 2} sl_slot(l) ev_l`. -/
  es : Nat
  /-- `S' = Σ_{l ≤ m - 2} coef_l w_l`. -/
  sp : Nat
  /-- `Σ_{l ≤ m - 2} coef_l F ^ l`. -/
  cp : Nat
  /-- `F ^ l` for the records `l ≤ m - 2` with `pos_l = i`, not forgotten, increasing `l`. -/
  own : List Nat

/-- One prefix record of a cell. -/
noncomputable def passStep3 (r : SR) (Fl s : Nat) (isOwn zero : Bool) (rec : PS) : PS :=
  PS.mk (Nat.add (Nat.mul s r.ev) rec.es)
    (bsel zero rec.sp (Nat.add (Nat.mul s r.dl) rec.sp))
    (bsel zero rec.cp (Nat.add (Nat.mul s Fl) rec.cp))
    (bsel isOwn (Fl :: rec.own) rec.own)

/-- The prefix records of the cell `i` with `below_i = b` against the slopes of `H_i`: the record
`l` takes the slope of its slot (`l` below `b`, `l + 1` from `b` on). -/
noncomputable def pass (i b : Nat) (rs : List SR) : Nat → Nat → List Nat → PS :=
  @List.rec SR (fun _ => Nat → Nat → List Nat → PS)
    (fun _ _ _ => PS.mk 0 0 0 [])
    (fun r _ ih l Fl sl => pass1 i r Fl (bsel (Nat.beq l b) (tl sl) sl) (ih (Nat.succ l) (Nat.mul Fl F128)))
    rs
where
  /-- With the slopes from the slot of `l` on. -/
  pass1 (i : Nat) (r : SR) (Fl : Nat) (sl' : List Nat) (ih' : List Nat → PS) : PS :=
    passStep3 r Fl (hd sl') (bsel r.fg false (Nat.beq r.pos i)) (bsel r.fg true (Nat.beq r.pos i))
      (ih' (tl sl'))

/-- The data of a prefix in the cell `i ≤ im` (section 5.3), for every last record. -/
structure PD where
  /-- `p_{i-1}`. -/
  pa : Nat
  /-- `p_i`. -/
  pb : Nat
  /-- `h = p_i - p_{i-1}`. -/
  h : Nat
  /-- `2 h`. -/
  h2 : Nat
  /-- `a0 = (1 + below_i) D ^ 2`. -/
  a0 : Nat
  /-- `sigma`. -/
  sig : Nat
  /-- `beta - D Em`. -/
  bet : Nat
  /-- `S` less the term of the last record. -/
  sp : Nat
  /-- The packed coefficients less the last one. -/
  cp : Nat
  /-- `A0 = a0 + (a1 + sigma) p_{i-1}`. -/
  A0 : Nat
  /-- `A1 = a0 + (a1 + sigma) p_i`. -/
  A1 : Nat
  /-- `IA (p_{i-1}, p_i)`. -/
  IA : Nat
  /-- `sigma (p_i ^ 2 - p_{i-1} ^ 2)`. -/
  ssq : Nat
  /-- The fields of the prefix records with their own cell here. -/
  own : List Nat
  /-- `own` is not empty. -/
  hasOwn : Bool
  /-- The cells `i, i + 1, .., L`. -/
  from' : List SC

/-- `PD` from the cell, `a0`, `sigma`, `beta - D Em`, and the prefix pass. -/
noncomputable def mkPD (a1 : Nat) (cl : SC) (from' : List SC) (a0 sig bet : Nat) (ps : PS) : PD :=
  mkPD1 cl from' a0 sig bet ps (Nat.add a1 sig)
where
  /-- With `kk = a1 + sigma`. -/
  mkPD1 (cl : SC) (from' : List SC) (a0 sig bet : Nat) (ps : PS) (kk : Nat) : PD :=
    PD.mk cl.pa cl.pb cl.h cl.h2 a0 sig bet ps.sp ps.cp (Nat.add a0 (Nat.mul kk cl.pa))
      (Nat.add a0 (Nat.mul kk cl.pb)) (Nat.add (Nat.mul cl.h2 a0) cl.a1sq) (Nat.mul sig cl.sqd)
      ps.own (@List.rec Nat (fun _ => Bool) false (fun _ _ _ => true) ps.own) from'

/-- The cell `i` of a prefix, `below_i = b`, `Cb` the rank of `H_i` less the term of `nxt_i`. -/
noncomputable def pdCell (a1 : Nat) (lk : Nat → SV) (rs : List SR) (cl : SC) (from' : List SC)
    (i b Cb : Nat) : PD :=
  pdCell1 a1 rs cl from' i b (lk (Nat.add Cb (lget cl.cb b)))
where
  /-- With the state `H_i`. -/
  pdCell1 (a1 : Nat) (rs : List SR) (cl : SC) (from' : List SC) (i b : Nat) (sv : SV) : PD :=
    pdCell2 a1 cl from' b sv (lget sv.sl b) (pass i b rs 0 1 sv.sl)
  /-- With `sigma` and the pass. -/
  pdCell2 (a1 : Nat) (cl : SC) (from' : List SC) (b : Nat) (sv : SV) (sig : Nat) (ps : PS) : PD :=
    mkPD a1 cl from' (Nat.mul (Nat.succ b) DS2) sig
      (Nat.add (Nat.add (Nat.mul DS sv.V) (Nat.mul sig cl.pn)) ps.es) ps

/-- Pop the cuts `pos_l < i`, counting `below`. -/
noncomputable def adv {β : Type} (i : Nat) (cuts Cs : List Nat) (b : Nat)
    (k : Nat → List Nat → List Nat → β) : β :=
  @List.rec Nat (fun _ => Nat → List Nat → β)
    (fun b Cs => k b [] Cs)
    (fun p ps ih b Cs => bsel (Nat.ble i p) (k b (p :: ps) Cs) (ih (Nat.succ b) (tl Cs)))
    cuts b Cs

/-- The prefix data of all cells. -/
noncomputable def pdLoop (a1 : Nat) (lk : Nat → SV) (rs : List SR) (cells : List SC) :
    Nat → Nat → List Nat → List Nat → List PD :=
  @List.rec SC (fun _ => Nat → Nat → List Nat → List Nat → List PD)
    (fun _ _ _ _ => [])
    (fun cl rest ih i b cuts Cs => adv i cuts Cs b fun b cuts Cs =>
      pdCell a1 lk rs cl (cl :: rest) i b (hd Cs) :: ih (Nat.succ i) b cuts Cs)
    cells

/-- `C_b = Σ_{l<b} bs_l[l] + Σ_{b ≤ l ≤ m-2} bs_l[l+1]` for `b = 0 .. m - 1`, from the
`u_l = bs_l[l]` and `v_l = bs_l[l+1]` of `rs`, and `C_0 = Σ v_l`. -/
noncomputable def rankCs (rs : List SR) : List Nat :=
  rankCs1 (lmapIdx (fun l r => (lget r.bs l, lget r.bs (Nat.succ l))) 0 rs)
where
  /-- From the pairs `(u_l, v_l)`. -/
  rankCs1 (uv : List (Nat × Nat)) : List Nat :=
    rankCs2 uv (lfoldr (fun p a => Nat.add p.2 a) 0 uv)
  /-- From `C_0`. -/
  rankCs2 (uv : List (Nat × Nat)) (C0 : Nat) : List Nat :=
    C0 :: @List.rec (Nat × Nat) (fun _ => Nat → List Nat) (fun _ => [])
      (fun p _ ih C => rankCs3 ih (Nat.add (Nat.sub C p.2) p.1)) uv C0
  /-- One step. -/
  rankCs3 (ih : Nat → List Nat) (C' : Nat) : List Nat := C' :: ih C'

/-- A prefix: its records, the data of its cells, the rank of the tail state less the last term,
and the `ev` and `w` of its records. -/
structure Pre where
  /-- `c_0 .. c_{m-2}`. -/
  rs : List SR
  /-- The data of the cells `1 .. L`. -/
  pd : List PD
  /-- `Σ_{l ≤ m-2} C (map_l + l, l + 1)`. -/
  Cpre : Nat
  /-- `ev_l`, `l ≤ m - 2`. -/
  evs : List Nat
  /-- `w_l`, `l ≤ m - 2`. -/
  dls : List Nat

/-- The prefix data of the records `rs`. -/
noncomputable def mkPre (c : Ctx) (lk : Nat → SV) (rs : List SR) : Pre :=
  mkPre1 c lk rs (rankCs rs)
where
  /-- With the rank sums. -/
  mkPre1 (c : Ctx) (lk : Nat → SV) (rs : List SR) (Cs : List Nat) : Pre :=
    Pre.mk rs (pdLoop c.a1 lk rs c.cells 1 0 (lmap SR.pos rs) Cs) (llast 0 Cs) (lmap SR.ev rs)
      (lmap SR.dl rs)

/-! ## The last record -/

/-- The accumulators: `R = rp - rn`, packed `acc` and `lam`. -/
structure Acc where
  /-- The positive part of `R` (units `1 / (2 D ^ 3)`). -/
  rp : Nat
  /-- The negative part of `R`. -/
  rn : Nat
  /-- `Σ_l acc_l F ^ l` (units `1 / D ^ 2`). -/
  ac : Nat
  /-- `Σ_l lam_l F ^ l` (units `1 / D`). -/
  lm : Nat

/-- `min ((q + 1) D, M) - min (q D, M)`. -/
noncomputable def dq (q M : Nat) : Nat :=
  Nat.sub (nmin2 (Nat.mul (Nat.succ q) DS) M) (nmin2 (Nat.mul q DS) M)

/-- The own-cell credits `Σ_q dq q M F ^ (l_q)` of the prefix records `own`, then `dq q M topF`
for the last record (`topF = 0` when it gets none). -/
noncomputable def ownLam (M : Nat) (own : List Nat) (topF : Nat) : Nat :=
  @List.rec Nat (fun _ => Nat → Nat) (fun q => Nat.mul (dq q M) topF)
    (fun s _ ih q => Nat.add (Nat.mul (dq q M) s) (ih (Nat.succ q))) own 0

/-- The constants of the last record: `D Em`, `Pm w` and `Pm F ^ (m - 1)` (`0` if forgotten),
`im`, its field, `tf`. -/
structure Tp where
  /-- `D Em`. -/
  DEm : Nat
  /-- `Pm w_{m-1}`, `0` if `tf`. -/
  PmW : Nat
  /-- `Pm F ^ (m - 1)`, `0` if `tf`. -/
  PmF : Nat
  /-- `im`. -/
  im : Nat
  /-- `F ^ (m - 1)`, `0` if `tf` (the own-cell credit of the last record). -/
  topF : Nat

/-- A cell `i ≤ im` of the last record (section 5.3), the case `A1 ≤ beta`: the stop cost is
below the continuation on the cell, `cell2 = IA`, the chord is `0`, and the own-cell credits with
`M = floor ((beta - A1) / D)`. -/
noncomputable def tcStop (tp : Tp) (pd : PD) (isTop : Bool) (beta : Nat) (A : Acc) :
    Acc :=
  Acc.mk (Nat.add A.rp pd.IA) A.rn A.ac
    (bsel (bsel isTop true pd.hasOwn)
      (Nat.add A.lm (ownLam (Nat.div (Nat.sub beta pd.A1) DS) pd.own (bsel isTop tp.topF 0)))
      A.lm)

/-- The chord of the cases `beta > A1`, `S > 0`: `h` when `beta + S ≤ A0`, else section 5.2. -/
noncomputable def qCont (a1 : Nat) (pd : PD) (beta S : Nat) : Nat :=
  bsel (Nat.ble (Nat.add beta S) pd.A0) pd.h (chord pd.pa pd.pb pd.a0 a1 beta pd.sig S)

/-- `acc += Q (cp + last coefficient)` when `S > 0`. -/
noncomputable def accAdd (a1 : Nat) (pd : PD) (beta S cP ac : Nat) : Nat :=
  bsel (Nat.beq S 0) ac (Nat.add ac (Nat.mul (qCont a1 pd beta S) cP))

/-- A cell `i ≤ im` of the last record, `beta = bet + D Em`. -/
noncomputable def topCell (a1 : Nat) (tp : Tp) (pd : PD) (isTop : Bool) (beta : Nat) (A : Acc) :
    Acc :=
  bsel (Nat.ble pd.A1 beta) (tcStop tp pd isTop beta A)
    (tcRest a1 pd beta (bsel isTop pd.sp (Nat.add pd.sp tp.PmW))
      (bsel isTop pd.cp (Nat.add pd.cp tp.PmF)) A)
where
  /-- The cases `beta > A1`: no own-cell credit (`gap ≤ 0`). -/
  tcRest (a1 : Nat) (pd : PD) (beta S cP : Nat) (A : Acc) : Acc :=
    bsel (Nat.ble beta pd.A0)
      (Acc.mk (Nat.add A.rp (Nat.mul pd.h2 beta)) (Nat.add A.rn pd.ssq) (accAdd a1 pd beta S cP A.ac)
        A.lm)
      (tcCross pd beta (cell2 pd.pa pd.pb pd.a0 a1 beta pd.sig A.rp A.rn)
        (accAdd a1 pd beta S cP A.ac) A.lm)
  /-- The crossing case. -/
  tcCross (_pd : PD) (_beta : Nat) (pn : PN) (ac lm : Nat) : Acc := Acc.mk pn.p pn.n ac lm

/-- Section 5.4, the tail cells from the boundary `j` (`pj = p_j`, `etj = E_t[pts[j]]`,
`etmj = E_{t-1}[pts[j]]`), `slcF` the packed slopes of `Hc`. -/
noncomputable def tailCells (r a1 a0 U S slcF : Nat) (cells : List SC) :
    Nat → Nat → Nat → Acc → Acc :=
  @List.rec SC (fun _ => Nat → Nat → Nat → Acc → Acc)
    (fun _ _ _ A => A)
    (fun cl _ ih pj etj etmj A =>
      bsel (Nat.ble (Nat.add (Nat.add (Nat.mul DS (Nat.add etj r)) U) S) (Nat.add a0 (Nat.mul a1 pj)))
        (tailEnd r U slcF pj etmj A)
        (tailCell r a1 a0 U S slcF cl (ih cl.pb cl.et cl.etm) (Nat.mul r cl.e1) A))
    cells
where
  /-- The exact tail from `p_jT`. -/
  tailEnd (r U slcF pj etmj : Nat) (A : Acc) : Acc :=
    bsel (Nat.ble DS pj) A
      (Acc.mk (Nat.add A.rp (Nat.add (Nat.div (Nat.mul (Nat.mul 2 DS2) etmj) (Nat.succ r))
          (Nat.mul (Nat.mul 2 (Nat.sub DS pj)) U)))
        A.rn (Nat.add A.ac (Nat.mul (Nat.sub DS pj) slcF)) A.lm)
  /-- A tail cell, `sigma = r E_{t+1}[pts[i]]`. -/
  tailCell (_r a1 a0 U S slcF : Nat) (cl : SC) (k : Acc → Acc) (sig : Nat) (A : Acc) : Acc :=
    tailCell1 a1 a0 S slcF cl k sig (Nat.add (Nat.add (Nat.mul DS cl.et) U) (Nat.mul sig cl.pb)) A
  /-- With `beta`. -/
  tailCell1 (a1 a0 S slcF : Nat) (cl : SC) (k : Acc → Acc) (sig beta : Nat) (A : Acc) : Acc :=
    tailCell2 k (cell2 cl.pa cl.pb a0 a1 beta sig A.rp A.rn)
      (bsel (Nat.beq S 0) A.ac
        (Nat.add A.ac (Nat.mul (chord cl.pa cl.pb a0 a1 beta sig S) slcF))) A.lm
  /-- With the new accumulators. -/
  tailCell2 (k : Acc → Acc) (pn : PN) (ac lm : Nat) : Acc := k (Acc.mk pn.p pn.n ac lm)

/-- `Σ x_l y_l`. -/
noncomputable def dot (xs ys : List Nat) : Nat :=
  lfoldr Nat.add 0 (lzipWith Nat.mul xs ys)

/-- `Σ_l x_l F ^ l`. -/
noncomputable def packF (xs : List Nat) : Nat :=
  lfoldr (fun x a => Nat.add x (Nat.mul a F128)) 0 xs

/-- Section 5.4 (the last record not forgotten): the tail from `p_im`. -/
noncomputable def tailPart (c : Ctx) (lk : Nat → SV) (p : Pre) (top : SR) (cells : List SC)
    (A : Acc) : Acc :=
  tailPart1 c p top cells A (lk (Nat.add p.Cpre top.bsl))
where
  /-- With the state `Hc`. -/
  tailPart1 (c : Ctx) (p : Pre) (top : SR) (cells : List SC) (A : Acc) (sv : SV) : Acc :=
    tailCells c.r c.a1 (Nat.mul (Nat.succ c.m) DS2)
      (Nat.add (Nat.mul DS sv.V) (dot (lapp p.evs [top.ev]) sv.sl))
      (dot (lapp p.dls [top.dl]) sv.sl) (packF sv.sl) cells top.val top.em top.etm A

/-- The cell loop of the last record over the prefix data, then the tail. -/
noncomputable def topLoop (c : Ctx) (lk : Nat → SV) (p : Pre) (top : SR) (tp : Tp) :
    List PD → Nat → Acc → Acc :=
  @List.rec PD (fun _ => Nat → Acc → Acc)
    (fun _ A => A)
    (fun pd _ ih i A =>
      bsel (Nat.ble i tp.im)
        (ih (Nat.succ i) (topCell c.a1 tp pd (Nat.beq i tp.im) (Nat.add pd.bet tp.DEm) A))
        (bsel top.fg A (tailPart c lk p top pd.from' A)))

/-- Section 5 on the record list `p.rs ++ [top]`: the accumulators. -/
noncomputable def evalTop (c : Ctx) (lk : Nat → SV) (p : Pre) (top : SR) : Acc :=
  topLoop c lk p top
    (Tp.mk (Nat.mul DS top.em) (bsel top.fg 0 (Nat.mul top.pm top.dl))
      (bsel top.fg 0 (Nat.mul top.pm c.FT)) top.pos (bsel top.fg 0 c.FT))
    p.pd 1 (Acc.mk 0 0 0 0)

/-! ## The check of a state -/

/-- `sg_l ≤ mu_l = lam_l + floor (acc_l / D)` (`0` if forgotten), the fields of `ac` and `lm` read
from the bottom, and the same length. -/
noncomputable def muOK (cs : List SR) (sg : List Nat) (ac lm : Nat) : Bool :=
  @List.rec SR (fun _ => List Nat → Nat → Nat → Bool)
    (fun sg _ _ => @List.rec Nat (fun _ => Bool) true (fun _ _ _ => false) sg)
    (fun r _ ih sg ac lm => @List.rec Nat (fun _ => Bool) false
      (fun s sg' _ => bsel
        (Nat.ble s (bsel r.fg 0 (Nat.add (Nat.land lm M128) (Nat.div (Nat.land ac M128) DS))))
        (ih sg' (Nat.shiftRight ac 128) (Nat.shiftRight lm 128)) false) sg)
    cs sg ac lm

/-- The check of a claimed state `(uh, sg)` against one record list `p.rs ++ [top]`:
`2 D^2 uh + rn ≤ rp` and `sg_l ≤ mu_l`. -/
noncomputable def checkVar (c : Ctx) (lk : Nat → SV) (uh : Nat) (sg : List Nat) (p : Pre)
    (top : SR) : Bool :=
  checkVar1 uh sg p top (evalTop c lk p top)
where
  /-- With the accumulators. -/
  checkVar1 (uh : Nat) (sg : List Nat) (p : Pre) (top : SR) (A : Acc) : Bool :=
    bsel (Nat.ble (Nat.add (Nat.mul (Nat.mul 2 DS2) uh) A.rn) A.rp)
      (muOK (lapp p.rs [top]) sg A.ac A.lm) false

/-- The nondecreasing `k`-tuples over `xs`, reversed (largest first), in colex order. -/
noncomputable def tupR {α : Type} (k : Nat) (xs : List α) : List (List α) :=
  @Nat.rec (fun _ => List α → List (List α)) (fun _ => [[]])
    (fun _ ih xs =>
      @List.rec α (fun _ => List α → List (List α)) (fun _ => [])
        (fun x _ r pre => tupR1 x (ih (lapp pre [x])) (r (lapp pre [x])))
        xs [])
    k xs
where
  /-- One group. -/
  tupR1 {α : Type} (x : α) (inner rest : List (List α)) : List (List α) :=
    lapp (lmap (fun t => x :: t) inner) rest

/-- The nondecreasing `(k + 1)`-tuples over `xs`, reversed, grouped by their largest entry
`xs[j]`, `j = 0, 1, ...`. -/
noncomputable def tupG {α : Type} (k : Nat) (xs : List α) : List (List (List α)) :=
  @List.rec α (fun _ => List α → List (List (List α))) (fun _ => [])
    (fun x _ r pre => lmap (fun t => x :: t) (tupR k (lapp pre [x])) :: r (lapp pre [x]))
    xs []

/-- The number of forgotten records. -/
noncomputable def nfg (cs : List SR) : Nat :=
  lfoldr (fun r a => bsel r.fg (Nat.succ a) a) 0 cs

/-- The record lists of section 6 built from the state `p.rs ++ [top]`, as prefixes and last
records: the state itself when it has no forgotten record or there is no new point, else every
nondecreasing choice among the new points and the point `1` (the prefix data of a modified
prefix is computed afresh). -/
noncomputable def variants (c : Ctx) (lk : Nat → SV) (p : Pre) (top : SR) : List (Pre × SR) :=
  bsel (bsel top.fg (@List.rec SR (fun _ => Bool) true (fun _ _ _ => false) c.newp) true)
    [(p, top)]
    (variants1 c lk (lapp p.rs [top]) (nfg (lapp p.rs [top])))
where
  /-- With the list and `f`. -/
  variants1 (c : Ctx) (lk : Nat → SV) (cs : List SR) (f : Nat) : List (Pre × SR) :=
    lmap (fun t => variants2 c lk (lapp (ltake (Nat.sub c.m f) cs) (lrevOnto t [])))
      (tupR f (lapp c.newp [llast (SR.mk 0 0 0 0 true 0 0 0 0 [] 0) cs]))
  /-- The prefix and the last record of a list. -/
  variants2 (c : Ctx) (lk : Nat → SV) (cs' : List SR) : Pre × SR :=
    (mkPre c lk (ltake (Nat.sub c.m 1) cs'), llast (SR.mk 0 0 0 0 true 0 0 0 0 [] 0) cs')

/-- All of `l`. -/
noncomputable def lall {α : Type} (p : α → Bool) (l : List α) : Bool :=
  @List.rec α (fun _ => Bool) true (fun a _ r => bsel (p a) r false) l

/-- The check of one state `(p, top)` against the claimed packed state `x`. -/
noncomputable def checkState (c : Ctx) (lk : Nat → SV) (st : Pre × SR) (x : Nat) : Bool :=
  lall (fun v => checkVar c lk (Nat.land x M48) (slopes c.m x) v.1 v.2) (variants c lk st.1 st.2)

/-- The states of a literal (`W` bits each, under a leading `1`), prepended to `rest`. -/
noncomputable def decLit (W MW x : Nat) (rest : List Nat) : List Nat :=
  @Nat.rec (fun _ => Nat → List Nat) (fun _ => rest)
    (fun _ ih x => bsel (Nat.ble x 1) rest (Nat.land x MW :: ih (Nat.shiftRight x W))) 16 x

/-- `f` on the pairs, and the same length. -/
noncomputable def lall2 {α : Type} (f : α → Nat → Bool) (l1 : List α) (l2 : List Nat) : Bool :=
  @List.rec α (fun _ => List Nat → Bool)
    (fun l2 => @List.rec Nat (fun _ => Bool) true (fun _ _ _ => false) l2)
    (fun a _ r l2 => @List.rec Nat (fun _ => Bool) false
      (fun b t2 _ => bsel (f a b) (r t2) false) l2) l1 l2

/-- The least `d` with `2 ^ d ≥ len`, for `len ≥ 1`. -/
def depth (len : Nat) : Nat := Nat.log2 (2 * len - 1)

/-- The check of the states `sts` (rank order) against the literals `lits` of the claimed table,
16 states per literal, with nothing left over on either side. The loop runs over the literals. -/
noncomputable def chunkCheck {α : Type} (f : α → Nat → Bool) (W MW : Nat) (lits : List Nat) :
    List α → Bool :=
  @List.rec Nat (fun _ => List α → Bool)
    (fun sts => @List.rec α (fun _ => Bool) true (fun _ _ _ => false) sts)
    (fun x _ ih sts => bsel (lall2 f (ltake 16 sts) (decLit W MW x [])) (ih (ldrop 16 sts)) false)
    lits

/-- The states of `Y_t` in rank order, as (prefix, last record): for the last record `recs[j]`,
the prefixes with entries among `recs[0 .. j]`, which are the first groups of `PG`. -/
noncomputable def states (recs : List SR) (PG : List (List Pre)) : List (Pre × SR) :=
  lflat (lmapIdx (fun j r => lmap (fun p => (p, r)) (lflat (ltake (Nat.succ j) PG))) 0 recs)

/-- The check of the step `t` of a grid: the claimed table `Nt` of time `t` against the claimed
table `Nn` of time `t + 1` (sections 5 and 6), for `m ≥ 2`. -/
noncomputable def checkStep (g : Grid) (t : Nat) (Nn Nt : List Nat) : Bool :=
  checkStep1 (mkCtx g t) (Nat.mul 48 (Nat.succ g.m)) (depth Nn.length) Nn Nt
where
  /-- With the step data, `W` and the depth of the tree. -/
  checkStep1 (c : Ctx) (W d : Nat) (Nn Nt : List Nat) : Bool :=
    checkStep2 c W (Nat.sub (Nat.shiftLeft 1 W) 1) Nt
      (lkF (lk0 (bld d Nn) d c.m W (Nat.sub (Nat.shiftLeft 1 W) 1)))
  /-- With the lookup. -/
  checkStep2 (c : Ctx) (W MW : Nat) (Nt : List Nat) (lk : Nat → SV) : Bool :=
    chunkCheck (checkState c lk) W MW Nt
      (states c.recs (lmap (lmap (fun t => mkPre c lk (lrevOnto t []))) (tupG (Nat.sub c.m 2) c.recs)))

/-! ## A step in several kernel checks -/

/-- `chunkCheck` restricted to the literals `lo .. hi - 1` (index `j` from `0`): every literal is
decoded and aligned with its 16 states and nothing is left over on either side, as in `chunkCheck`,
but `f` runs on the states of those literals only. -/
noncomputable def rangeLoop {α : Type} (f : α → Nat → Bool) (W MW lo hi : Nat) (lits : List Nat) :
    List α → Nat → Bool :=
  @List.rec Nat (fun _ => List α → Nat → Bool)
    (fun sts _ => @List.rec α (fun _ => Bool) true (fun _ _ _ => false) sts)
    (fun x _ ih sts j =>
      bsel (bsel (Nat.ble lo j) (Nat.blt j hi) false)
        (bsel (lall2 f (ltake 16 sts) (decLit W MW x [])) (ih (ldrop 16 sts) (Nat.succ j)) false)
        (bsel (lall2 (fun _ _ => true) (ltake 16 sts) (decLit W MW x [])) (ih (ldrop 16 sts) (Nat.succ j))
          false))
    lits

/-- `checkStep` on the literals `lo .. hi - 1` of `Nt`: a step is checked by several kernel checks
whose ranges cover the literals of `Nt`. -/
noncomputable def checkRange (g : Grid) (t : Nat) (Nn Nt : List Nat) (lo hi : Nat) : Bool :=
  checkRange1 (mkCtx g t) (Nat.mul 48 (Nat.succ g.m)) (depth Nn.length) Nn Nt lo hi
where
  /-- With the step data, `W` and the depth of the tree. -/
  checkRange1 (c : Ctx) (W d : Nat) (Nn Nt : List Nat) (lo hi : Nat) : Bool :=
    checkRange2 c W (Nat.sub (Nat.shiftLeft 1 W) 1) Nt lo hi
      (lkF (lk0 (bld d Nn) d c.m W (Nat.sub (Nat.shiftLeft 1 W) 1)))
  /-- With the lookup. -/
  checkRange2 (c : Ctx) (W MW : Nat) (Nt : List Nat) (lo hi : Nat) (lk : Nat → SV) : Bool :=
    rangeLoop (checkState c lk) W MW lo hi Nt
      (states c.recs (lmap (lmap (fun t => mkPre c lk (lrevOnto t []))) (tupG (Nat.sub c.m 2) c.recs))) 0

/-! ## Time n (section 4) -/

/-- The local points `0 .. cnt_n` of `G_n`: the value (`D` for the point `1`) and whether it is
the point `1`. -/
noncomputable def lastPts (g : Grid) : List (Nat × Bool) :=
  lastPts1 g.gpt (winAt g g.n)
where
  /-- With the window. -/
  lastPts1 (gpt : List Nat) (w : Win) : List (Nat × Bool) :=
    lapp (lmap (fun k => (lget gpt (Nat.add w.s k), false)) (List.range w.cnt)) [(DS, true)]

/-- `sg_l ≤ D` (`≤ 0` at the point `1`), and the same length. -/
noncomputable def lastSg (tup : List (Nat × Bool)) (sg : List Nat) : Bool :=
  lall2 (fun p s => Nat.ble s (bsel p.2 0 DS)) tup sg

/-- The check of a claimed state of time `n` against the sorted tuple `tup` (reversed, largest
first): `uh + sum of the values ≤ (m + 1) D` and the slopes. -/
noncomputable def lastOK (m : Nat) (tup : List (Nat × Bool)) (x : Nat) : Bool :=
  bsel (Nat.ble (Nat.add (Nat.land x M48) (lfoldr (fun p a => Nat.add p.1 a) 0 tup))
      (Nat.mul (Nat.succ m) DS))
    (lastSg (lrevOnto tup []) (slopes m x)) false

/-- The check of the claimed table `Nn` of time `n` (section 4, as upper bounds): every state of
`G_n`, in rank order, against its literal, with nothing left over on either side. -/
noncomputable def checkLast (g : Grid) (Nn : List Nat) : Bool :=
  chunkCheck (lastOK g.m) (Nat.mul 48 (Nat.succ g.m))
    (Nat.sub (Nat.shiftLeft 1 (Nat.mul 48 (Nat.succ g.m))) 1) Nn (tupR g.m (lastPts g))

end Robbins.Cert.SO.K
