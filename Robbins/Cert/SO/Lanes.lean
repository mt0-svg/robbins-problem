import Robbins.Cert.SO.EvalK
import Robbins.Lanes.Ops

/-!
# The second-order step in packed lanes (fixed-window steps)

The check `checkStep` of Robbins/Cert/SO/EvalK.lean for a step whose windows at `t` and `t + 1`
agree (no new point, every `ev = 0`, one record list per state), computed on packed lanes of
`LW = 144` bits (Robbins/Lanes/Ops.lean): one lane per prefix (the `m - 1` smallest records of a
state), one pack per top record, the per-cell quantities of a prefix computed once per step over
all prefixes.

Layout. The prefixes are the `(m - 1)`-tuples of records in the order of `tupR (m - 1)`; those of
the states with top record `j` are its first `C (j + m - 1, m - 1)`, and those states are the block
of the claimed table of time `t` at `C (j + m - 1, m)`. The slot vectors of the prefixes are built
by concatenations that follow the recursion of `tupR` (`tupV`).

Tables. The literals of a claimed table are concatenated (`litCat`, a balanced merge) into one
natural with a state every `288` bits, which is two lanes of `144` bits; a field is masked in place
and the even lanes are compacted (`route`). The lookups of the states `H_i` of time `t + 1` are
compactions too: for the cell of the point `x`, the prefixes `p` map to the states `p ∪ {x}` in
increasing rank. A compaction is a network of stages that move masked lanes down by `2 ^ k` lanes
(`cnet`), with masks computed by the inverse network (`expand`); the network is not trusted: the
check `mkRt` runs it on the ones and on `l ↦ l + 1`, and requires every destination lane to receive
exactly one source lane, the expected one. Each lane of every network stage is a sum of source
lanes, so the two tests identify the source of every destination lane.

Arithmetic. Every quantity of section 5 is a lane of a pack; the branches of the scalar code are
lanewise masks (`sel`), the divisions restoring divisions on all lanes (`divQR`, 37 quotient bits),
the products of two lanes bit-serial products (`mulBS`). A division whose quotient saturates where
it is used fails the check. Bounds: the step data are checked against `D = 2 ^ 36` and the fields
of the tables have 48 bits, so every lane stays below `2 ^ 143`.

Kernel form as in Robbins/Cert/SO/EvalK.lean: recursors, `Bool.rec` branches, raw `Nat`
operations, values passed as arguments of small definitions.
-/

namespace Robbins.Cert.SO.L

open Robbins.Cert Robbins.Cert.K Robbins.Cert.SO.K Robbins.Lanes

/-- The lane width. -/
def LW : Nat := 144

/-- `2 ^ 144 - 1`. -/
def FM : Nat := 22300745198530623141535718272648361505980415

/-- `2 ^ 108 - 1`, the lane mask of a shift by `36`. -/
def M108 : Nat := 324518553658426726783156020576255

/-- `2 ^ 128 - 1`, the fields of the scalar accumulators. -/
def M128' : Nat := 340282366920938463463374607431768211455

/-- `2 ^ 37 - 2`, the largest unsaturated quotient. -/
def QMX : Nat := 137438953470

/-! ## Vectors of `n` lanes -/

/-- The constants of `n` lanes: guard bits, ones. -/
structure VC where
  /-- The number of lanes. -/
  n : Nat
  /-- `2 ^ 143` in every lane. -/
  G : Nat
  /-- `1` in every lane. -/
  O : Nat

/-- The constants of `n` lanes. -/
noncomputable def mkVC (n : Nat) : VC := VC.mk n (guard LW n) (ones LW n)

/-- `c` in every lane. -/
noncomputable def bc (v : VC) (c : Nat) : Nat := Nat.mul c v.O

/-- The guard mask of `b ≤ a`. -/
noncomputable def ge (v : VC) (A B : Nat) : Nat := geMask v.G A B

/-- `A` where the guard mask `M` is set, else `B`. -/
noncomputable def sl (M A B : Nat) : Nat := sel (full LW M) A B

/-- `A` where the guard mask `M` is set, else `0`. -/
noncomputable def msk (M A : Nat) : Nat := Nat.land A (full LW M)

/-- The complement of a guard mask. -/
noncomputable def notM (v : VC) (M : Nat) : Nat := Nat.sub v.G M

/-- The truncated difference `a - b` in every lane. -/
noncomputable def tsub (v : VC) (A B : Nat) : Nat := Nat.sub A (lmin LW v.G A B)

/-- The lanewise product of `A` by the `Q`-bit multipliers `B`. -/
noncomputable def mulv (v : VC) (Q A B : Nat) : Nat := mulBS LW Q v.O A B

/-- The lanewise `a / 2 ^ 36`. -/
noncomputable def shr36 (A : Nat) (v : VC) : Nat := shrL (bc v M108) 36 A

/-- The guard mask of `a ≠ 0`. -/
noncomputable def nz (v : VC) (A : Nat) : Nat := Nat.sub v.G (ge v (bc v 0) A)

/-- The first `n` lanes of each vector of a list. -/
noncomputable def preL (n : Nat) (l : List Nat) : List Nat := lmap (pre LW n) l

/-! ## Tables -/

/-- The number of `Ws`-bit states of a literal under its leading `1`: the `k`, `1 ≤ k ≤ 16`, with
`x / 2 ^ (k Ws) = 1` (`0` if there is none). -/
noncomputable def lcount (Ws x : Nat) : Nat :=
  @Nat.rec (fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih k => bsel (Nat.beq (Nat.shiftRight x (Nat.mul k Ws)) 1) k (ih (Nat.succ k))) 16 1

/-- The body of a literal (its states, without the leading `1`) and its number of states. -/
noncomputable def litBC (Ws x : Nat) : Nat × Nat :=
  litBC1 Ws x (lcount Ws x)
where
  /-- With the number of states. -/
  litBC1 (Ws x k : Nat) : Nat × Nat := (Nat.sub x (Nat.shiftLeft 1 (Nat.mul k Ws)), k)

/-- Every literal holds `16` states of `Ws` bits under its leading `1`, the last one `1` to `16`. -/
noncomputable def litsOK (Ws : Nat) (lits : List Nat) : Bool :=
  @List.rec Nat (fun _ => Bool) true
    (fun x t ih => bsel (@List.rec Nat (fun _ => Bool) true (fun _ _ _ => false) t)
      (Nat.blt 0 (lcount Ws x)) (bsel (Nat.beq (Nat.shiftRight x (Nat.mul 16 Ws)) 1) ih false))
    lits

/-- Two runs of states, concatenated. -/
noncomputable def catR (Ws : Nat) (a b : Nat × Nat) : Nat × Nat :=
  (Nat.add a.1 (Nat.shiftLeft b.1 (Nat.mul Ws a.2)), Nat.add a.2 b.2)

/-- Adjacent runs merged, a last odd run kept. -/
noncomputable def mergeP (Ws : Nat) (l : List (Nat × Nat)) : List (Nat × Nat) :=
  @List.rec (Nat × Nat) (fun _ => Option (Nat × Nat) → List (Nat × Nat))
    (fun p => @Option.rec (Nat × Nat) (fun _ => List (Nat × Nat)) [] (fun a => [a]) p)
    (fun x _ ih p => @Option.rec (Nat × Nat) (fun _ => List (Nat × Nat)) (ih (some x))
      (fun a => catR Ws a x :: ih none) p)
    l none

/-- The states of the literals concatenated (`Ws` bits each) and their number. -/
noncomputable def litCat (Ws : Nat) (lits : List Nat) : Nat × Nat :=
  litCat1 (@Nat.rec (fun _ => List (Nat × Nat)) (lmap (litBC Ws) lits) (fun _ ih => mergeP Ws ih)
    (depth lits.length))
where
  /-- The single run left. -/
  litCat1 (l : List (Nat × Nat)) : Nat × Nat :=
    @List.rec (Nat × Nat) (fun _ => Nat × Nat) (0, 0) (fun a _ _ => a) l

/-! ## Compaction networks -/

/-- A stage: the lanes under the full-lane mask `M` move down by `s` bits. -/
noncomputable def cst (s M V : Nat) : Nat := cst1 s V (Nat.land V M)
where
  /-- With the moving lanes. -/
  cst1 (s V Vm : Nat) : Nat := Nat.add (Nat.sub V Vm) (Nat.shiftRight Vm s)

/-- The network: stage `k` moves by `2 ^ k` lanes. -/
noncomputable def cnet (Ms : List Nat) (V : Nat) : Nat :=
  @List.rec Nat (fun _ => Nat → Nat → Nat) (fun _ V => V)
    (fun M _ ih s V => frc2 (cst s M V) 1 (fun V' _ => ih (Nat.add s s) V')) Ms LW V

/-- A stage of the inverse network, bit `k`: the lanes with bit `k` set move up by `2 ^ k` lanes,
and the mask of their new positions is the mask of stage `k` of `cnet`. -/
noncomputable def exp1 (G k X : Nat) (κ : Nat → Nat → Nat × List Nat) : Nat × List Nat :=
  exp2 (Nat.shiftLeft LW k) X (full LW (Nat.land (Nat.shiftLeft X (Nat.sub 143 k)) G)) κ
where
  /-- With the shift and the moving lanes' mask. -/
  exp2 (sh X B : Nat) (κ : Nat → Nat → Nat × List Nat) : Nat × List Nat :=
    exp3 sh X (Nat.land X B) B κ
  /-- With the moving lanes. -/
  exp3 (sh X Xm B : Nat) (κ : Nat → Nat → Nat × List Nat) : Nat × List Nat :=
    frc2 (Nat.add (Nat.sub X Xm) (Nat.shiftLeft Xm sh)) (Nat.shiftLeft B sh) κ

/-- The inverse network over the bits `K - 1` down to `0`: the final word and the masks of
`cnet`, bit `0` first. -/
noncomputable def expand (G K X : Nat) : Nat × List Nat :=
  @Nat.rec (fun _ => Nat → List Nat → Nat × List Nat) (fun X acc => (X, acc))
    (fun k ih X acc => exp1 G k X (fun X' M => ih X' (M :: acc))) K X []

/-- `l ↦ l + 1` on `n` lanes. -/
noncomputable def iota1 (n : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.mul n (Nat.shiftLeft 1 (Nat.mul LW n))) (ones LW n)) FM

/-- A compaction: the masks, the selection of the source lanes, the number of destination lanes,
and the result of its two tests. -/
structure Rt where
  /-- The masks of `cnet`. -/
  Ms : List Nat
  /-- The full lanes of the source lanes. -/
  sel : Nat
  /-- The number of destination lanes. -/
  nd : Nat
  /-- Both tests pass. -/
  ok : Bool

/-- The compaction of `V`. -/
noncomputable def route (rt : Rt) (V : Nat) : Nat := pre LW rt.nd (cnet rt.Ms (Nat.land V rt.sel))

/-- The compaction from `NS` source lanes to `ND` destination lanes, destination lane `j` from the
source lane `I_j` (`I` increasing, `I_j ≥ j`), tested on the ones and on `l ↦ l + 1`. -/
noncomputable def mkRt (NS ND I : Nat) : Rt :=
  mkRt1 NS ND I (expand (guard LW NS) (Nat.succ (Nat.log2 NS))
    (Nat.add (Nat.sub I (Nat.sub (iota1 ND) (ones LW ND))) (guard LW ND)))
where
  /-- With the inverse network. -/
  mkRt1 (NS ND I : Nat) (E : Nat × List Nat) : Rt :=
    mkRt2 NS ND I E.2 (full LW (Nat.land E.1 (guard LW NS)))
  /-- With the masks and the selection. -/
  mkRt2 (NS ND I : Nat) (Ms : List Nat) (S : Nat) : Rt :=
    Rt.mk Ms S ND
      (bsel (Nat.beq (pre LW ND (cnet Ms (Nat.land (ones LW NS) S))) (ones LW ND))
        (Nat.beq (pre LW ND (cnet Ms (Nat.land (iota1 NS) S))) (Nat.add I (ones LW ND))) false)

/-- The fields of a table: `(uh, [sg_0, ..., sg_{m-1}])` on one lane per state, from the
concatenated states `T` (`n` states of `48 (m + 1)` bits, which is `ls = (m + 1) / 3` lanes), and
the result of the test of the compaction of the lanes `ls s`. -/
noncomputable def fields (m T n : Nat) : Nat × List Nat × Bool :=
  fields1 m T (Nat.div (Nat.succ m) 3) (mkRt (Nat.mul (Nat.div (Nat.succ m) 3) n) n
      (Nat.mul (Nat.div (Nat.succ m) 3) (Nat.sub (iota1 n) (ones LW n))))
    (Nat.mul 281474976710655 (ones (Nat.mul 48 (Nat.succ m)) n))
where
  /-- With `ls`, the compaction and the mask of the low `48` bits of the lanes `ls s`. -/
  fields1 (m T ls : Nat) (rt : Rt) (EV : Nat) : Nat × List Nat × Bool :=
    (route rt (Nat.land T EV),
      lmap (fun f => route rt (Nat.land (Nat.shiftRight T (Nat.add (Nat.mul 144 (Nat.div f 3))
        (Nat.mul 48 (Nat.mod f 3)))) EV)) (List.range' 1 m),
      bsel (Nat.beq (Nat.mul 3 ls) (Nat.succ m)) rt.ok false)

/-! ## Prefixes -/

/-- `C (a, b)` by the product formula (`0` for `a < b`). -/
noncomputable def binK (a b : Nat) : Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih j acc => ih (Nat.succ j) (Nat.div (Nat.mul acc (Nat.sub a j)) (Nat.succ j))) b 0 1

/-- The number of nondecreasing `k`-tuples over `n` values, `C (n + k - 1, k)` (`1` for `k = 0`). -/
noncomputable def cnt (k n : Nat) : Nat := binK (Nat.sub (Nat.add n k) 1) k

/-- `g 0, g 1, ..., g (R - 1)` concatenated, `g v` of `cnt k (v + 1)` lanes. -/
noncomputable def catV (R k : Nat) (g : Nat → Nat) : Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ ih v o acc =>
      frc2 (Nat.add acc (Nat.shiftLeft (g v) (Nat.mul LW o))) (Nat.add o (cnt k (Nat.succ v)))
        (fun acc' o' => ih (Nat.succ v) o' acc'))
    R 0 0 0

/-- The slot vectors of `f` over the tuples `tupR k (range R)`, slot `0` the largest entry: level
`k + 1` is, for each largest entry `v`, `v` before the tuples of level `k` over `range (v + 1)`,
which are the first `cnt k (v + 1)` of level `k`. -/
noncomputable def tupV (f : Nat → Nat) (R : Nat) : Nat → List Nat :=
  @Nat.rec (fun _ => List Nat) []
    (fun k ih => catV R k (fun v => Nat.mul (f v) (ones LW (cnt k (Nat.succ v)))) ::
      lmap (fun P => catV R k (fun v => pre LW (cnt k (Nat.succ v)) P)) ih)

/-- The record `k` of a list (a dummy past the end). -/
noncomputable def rget (l : List SR) (k : Nat) : SR :=
  @List.rec SR (fun _ => SR) (SR.mk 0 0 0 0 true 0 0 0 0 [] 0) (fun a _ _ => a) (ldrop k l)

/-- The prefix vectors of a step: the slots in increasing order (`q = 0` the smallest record). -/
structure PV where
  /-- `pos` of the record of slot `q`. -/
  pos : List Nat
  /-- `w` of the record of slot `q`. -/
  dl : List Nat
  /-- `1` if the record of slot `q` is forgotten. -/
  fg : List Nat
  /-- `C_b`, `b = 0 .. m - 1` (`rankCs`). -/
  cs : List Nat

/-- The slot `q` (increasing) of the slot vectors of `f` (largest first, `d` slots). -/
noncomputable def slotInc (d : Nat) (f : Nat → Nat) (R : Nat) : List Nat :=
  lrevOnto (tupV f R d) []

/-- `C_0 = Σ v_q`, `C_{b+1} = C_b - v_b + u_b`. -/
noncomputable def rankV (us vs : List Nat) : List Nat :=
  rankV1 us vs (lfoldr Nat.add 0 vs)
where
  /-- From `C_0`. -/
  rankV1 (us vs : List Nat) (C0 : Nat) : List Nat :=
    C0 :: @List.rec Nat (fun _ => List Nat → Nat → List Nat) (fun _ _ => [])
      (fun u _ ih vs C => rankV2 ih (tl vs) (Nat.add (Nat.sub C (hd vs)) u)) us vs C0
  /-- One step. -/
  rankV2 (ih : List Nat → Nat → List Nat) (vs : List Nat) (C' : Nat) : List Nat := C' :: ih vs C'

/-- The prefix vectors of the records `recs` (`d = m - 1` slots). -/
noncomputable def mkPV (recs : List SR) (d : Nat) : PV :=
  mkPV1 recs d (List.length recs)
where
  /-- With the number of records. -/
  mkPV1 (recs : List SR) (d R : Nat) : PV :=
    PV.mk (slotInc d (fun k => (rget recs k).pos) R) (slotInc d (fun k => (rget recs k).dl) R)
      (slotInc d (fun k => bsel (rget recs k).fg 1 0) R)
      (rankV (lmap (fun q => lget (slotInc d (fun k => lget (rget recs k).bs q) R) q) (List.range d))
        (lmap (fun q => lget (slotInc d (fun k => lget (rget recs k).bs (Nat.succ q)) R) q)
          (List.range d)))

/-! ## The cells -/

/-- The quantities of a cell `i` over all prefixes (section 5.3, `PD`), the lookup of `H_i`, and
the result of its compaction tests. -/
structure CV where
  /-- `p_{i-1}`. -/
  pa : Nat
  /-- `p_i`. -/
  pb : Nat
  /-- `h`. -/
  h : Nat
  /-- `2 h`. -/
  h2 : Nat
  /-- `p_i ^ 2`. -/
  pb2 : Nat
  /-- `below_i`. -/
  B : Nat
  /-- `sigma`. -/
  sig : Nat
  /-- `beta - D Em`. -/
  bet : Nat
  /-- `S` less the last record. -/
  sp : Nat
  /-- The coefficients of the prefix slots. -/
  co : List Nat
  /-- The guard masks of the prefix slots with their own cell here. -/
  own : List Nat
  /-- `a0`. -/
  a0 : Nat
  /-- `a1 + sigma`. -/
  kk : Nat
  /-- `A0`. -/
  A0 : Nat
  /-- `A1`. -/
  A1 : Nat
  /-- `IA`. -/
  IA : Nat
  /-- `ssq`. -/
  ssq : Nat
  /-- The rank of `H_i`. -/
  idx : Nat
  /-- `uh_{t+1} (H_i)`. -/
  gv : Nat
  /-- `sg_{t+1} (H_i)`. -/
  gs : List Nat
  /-- The compaction tests. -/
  ok : Bool

/-- `xs[b]` where `B = b` (`B ≤ d`, `xs` of `d + 1` vectors): the last `xs[b]` with `B ≥ b`. -/
noncomputable def pickB (v : VC) (B : Nat) (xs : List Nat) : Nat :=
  @List.rec Nat (fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun x _ ih b acc => ih (Nat.succ b) (sl (ge v B (bc v b)) x acc)) (tl xs) 1 (hd xs)

/-- The slot slopes of the prefix records: slot `q` takes `gs[q]` if `q < B`, else `gs[q + 1]`. -/
noncomputable def slotS (v : VC) (B : Nat) (gs : List Nat) : List Nat :=
  lmapIdx (fun q p => sl (ge v B (bc v (Nat.succ q))) p.1 p.2) 0 (lzipWith Prod.mk gs (tl gs))

/-- The guard masks of `pos_q = i`. -/
noncomputable def eqM (v : VC) (i P : Nat) : Nat := Nat.land (ge v (bc v i) P) (ge v P (bc v i))

/-- A cell `i` (`cl`) over the `n` prefixes (`v`), from the prefix vectors, the fields of the table
of time `t + 1` (`NS` states), `a1 = r D`. -/
noncomputable def mkCV (v : VC) (pv : PV) (NS a1 : Nat) (FV : Nat) (FS : List Nat) (i : Nat)
    (cl : SC) : CV :=
  mkCV1 v pv NS a1 FV FS i cl
    (lfoldr Nat.add 0 (lmap (fun P => ind LW (ge v (bc v i) (Nat.add P v.O))) pv.pos))
where
  /-- With `below_i`. -/
  mkCV1 (v : VC) (pv : PV) (NS a1 FV : Nat) (FS : List Nat) (i : Nat) (cl : SC) (B : Nat) : CV :=
    mkCV2 v pv a1 i cl B
      (pickB v B (lzipWith (fun C c => Nat.add C (bc v c)) pv.cs cl.cb))
      NS FV FS
  /-- With the ranks of `H_i`. -/
  mkCV2 (v : VC) (pv : PV) (a1 i : Nat) (cl : SC) (B I NS FV : Nat) (FS : List Nat) : CV :=
    mkCV3 v pv a1 i cl B I (mkRt NS v.n I) FV FS
  /-- With the compaction. -/
  mkCV3 (v : VC) (pv : PV) (a1 i : Nat) (cl : SC) (B I : Nat) (rt : Rt) (FV : Nat)
      (FS : List Nat) : CV :=
    mkCV4 v pv a1 i cl B I rt.ok (route rt FV) (lmap (route rt) FS)
  /-- With the lookups. -/
  mkCV4 (v : VC) (pv : PV) (a1 i : Nat) (cl : SC) (B I : Nat) (ok : Bool) (gv : Nat)
      (gs : List Nat) : CV :=
    mkCV5 v pv a1 i cl B I ok gv gs (pickB v B gs)
      (lzipWith (fun E F => Nat.lor E (Nat.shiftLeft F 143))
        (lmap (eqM v i) pv.pos) pv.fg)
      (lzipWith (fun E F => Nat.sub E (Nat.land E (Nat.shiftLeft F 143)))
        (lmap (eqM v i) pv.pos) pv.fg)
  /-- With `sigma`, the masks `zero` and `isOwn` of the slots. -/
  mkCV5 (v : VC) (pv : PV) (a1 _i : Nat) (cl : SC) (B I : Nat) (ok : Bool) (gv : Nat)
      (gs : List Nat) (sig : Nat) (zero own : List Nat) : CV :=
    mkCV6 v pv a1 cl B I ok gv gs sig own
      (lzipWith (fun Z s => sl Z 0 s) zero (slotS v B gs))
      (Nat.mul DS2 (Nat.add B v.O)) (Nat.add (bc v a1) sig)
  /-- With the coefficients, `a0` and `kk`. -/
  mkCV6 (v : VC) (pv : PV) (_a1 : Nat) (cl : SC) (B I : Nat) (ok : Bool) (gv : Nat)
      (gs : List Nat) (sig : Nat) (own co : List Nat) (a0 kk : Nat) : CV :=
    CV.mk cl.pa cl.pb cl.h cl.h2 (Nat.mul cl.pb cl.pb) B sig
      (Nat.add (Nat.mul DS gv) (Nat.mul cl.pn sig))
      (lfoldr Nat.add 0 (lzipWith (fun c w => mulv v 37 c w) co pv.dl)) co own a0 kk
      (Nat.add a0 (Nat.mul cl.pa kk)) (Nat.add a0 (Nat.mul cl.pb kk))
      (Nat.add (Nat.mul cl.h2 a0) (bc v cl.a1sq)) (Nat.mul cl.sqd sig) I gv gs ok

/-- A cell restricted to its first `n` lanes. -/
noncomputable def preCV (n : Nat) (c : CV) : CV :=
  CV.mk c.pa c.pb c.h c.h2 c.pb2 (pre LW n c.B) (pre LW n c.sig) (pre LW n c.bet) (pre LW n c.sp)
    (preL n c.co) (preL n c.own) (pre LW n c.a0) (pre LW n c.kk) (pre LW n c.A0) (pre LW n c.A1)
    (pre LW n c.IA) (pre LW n c.ssq) (pre LW n c.idx) (pre LW n c.gv) (preL n c.gs) c.ok

/-! ## The accumulators and the cells `i ≤ im` -/

/-- The accumulators of the states of one top: `rp`, `rn`, `acc_l`, `lam_l` (`l < m`), and the
checks of saturated quotients. -/
structure LA where
  /-- The positive part of `R`. -/
  rp : Nat
  /-- The negative part of `R`. -/
  rn : Nat
  /-- `acc_l`. -/
  ac : List Nat
  /-- `lam_l`. -/
  lm : List Nat
  /-- No saturated quotient where one is used. -/
  ok : Bool

/-- `xs` plus `ys`, elementwise. -/
noncomputable def addL (xs ys : List Nat) : List Nat := lzipWith Nat.add xs ys

/-- The chord (section 5.2) on the lanes of `use`, `0` elsewhere, with `b0 = beta`, `b1 = sigma`
(`kk`, `A0`, `A1` given), the quotient `q1 = (b0 - A0) / kk` and its remainder `r1` where
`b0 > A0`; the second component checks that the last quotient does not saturate on `use`. -/
noncomputable def chordV (v : VC) (h : Nat) (beta S kk A0 A1 q1 r1 use : Nat) : Nat × Bool :=
  chordV1 v h beta S kk A0 A1 use
    (sl (ge v A0 beta) (Nat.mul h (Nat.add (tsub v A0 beta) (tsub v A1 beta)))
      (mulv v 37 (Nat.add (tsub v kk r1) (tsub v A1 beta)) (tsub v (tsub v (bc v h) q1) v.O)))
    (Nat.add beta S)
where
  /-- With `lo` and `b0 + S`. -/
  chordV1 (v : VC) (h _beta S kk A0 A1 use lo bS : Nat) : Nat × Bool :=
    chordV2 v h S kk A1 use lo bS (divQR LW 37 v.G (tsub v bS A0) kk)
  /-- With `(q2, r2)` of `(b0 + S - A0) / kk`. -/
  chordV2 (v : VC) (h S kk A1 use lo bS : Nat) (qr : Nat × Nat) : Nat × Bool :=
    chordV3 v S use (sl (ge v bS A1) lo
      (tsub v (Nat.add lo (mulv v 37 qr.2 (tsub v (bc v h) qr.1)))
        (Nat.add (mulv v 37 (tsub v A1 bS) (tsub v (bc v h) qr.1)) (Nat.add kk kk))))
  /-- With the numerator. -/
  chordV3 (v : VC) (S use N : Nat) : Nat × Bool :=
    chordV4 v use (divQR LW 37 v.G N (Nat.add S S)).1
  /-- With the quotient. -/
  chordV4 (v : VC) (use q : Nat) : Nat × Bool :=
    (msk use q, allGe v.G (bc v QMX) (msk use q))

/-- `dq q M = min ((q + 1) D, M) - min (q D, M)` in every lane (`Q` the lanes of `q`). -/
noncomputable def dqV (v : VC) (Q M : Nat) : Nat :=
  Nat.sub (lmin LW v.G (Nat.mul DS (Nat.add Q v.O)) M) (lmin LW v.G (Nat.mul DS Q) M)

/-- The own-cell credits of the prefix slots (`own` the guard masks, in slot order) and of the top
(`topOn`), `M` the lanes of `floor ((beta - A1) / D)`: `(credits of the slots, credit of the top)`. -/
noncomputable def creditV (v : VC) (M : Nat) (own : List Nat) (topOn : Bool) : List Nat × Nat :=
  @List.rec Nat (fun _ => Nat → List Nat × Nat)
    (fun Q => ([], bsel topOn (dqV v Q M) 0))
    (fun o _ ih Q => creditV1 (msk o (dqV v Q M)) (ih (Nat.add Q (ind LW o))))
    own 0
where
  /-- One slot. -/
  creditV1 (c : Nat) (r : List Nat × Nat) : List Nat × Nat := (c :: r.1, r.2)

/-- The constants of the top record (section 5.3, `Tp`): `D Em`, `Pm w`, `Pm` (`0` if forgotten),
`im`, whether it gets its own-cell credit. -/
structure TV where
  /-- `D Em`. -/
  DEm : Nat
  /-- `Pm w`, `0` if forgotten. -/
  PmW : Nat
  /-- `Pm`, `0` if forgotten. -/
  Pm : Nat
  /-- `im`. -/
  im : Nat
  /-- Not forgotten. -/
  topOn : Bool

/-- The crossing terms of `cell2` (`z = p_{i-1} + q1`): the additions to `rp` and to `rn`. -/
noncomputable def crossV (v : VC) (a1 : Nat) (c : CV) (beta q1 : Nat) : Nat × Nat :=
  (Nat.add
      (mulv v 37 (Nat.add (Nat.add c.a0 c.a0) (Nat.mul a1 (Nat.add (bc v (Nat.add c.pa c.pa)) q1))) q1)
      (Nat.mul 2 (mulv v 37 beta (tsub v (bc v c.h) q1))),
    Nat.add (mulv v 48 (tsub v (bc v c.pb2) (mulv v 37 (Nat.add (bc v c.pa) q1) (Nat.add (bc v c.pa) q1)))
      c.sig) (Nat.add c.kk c.kk))

/-- A cell `i ≤ im` of the last record on all lanes (`topCell`): the stop case, the case
`beta ≤ A0` and the crossing case, by masks. -/
noncomputable def topCellV (v : VC) (a1 : Nat) (tp : TV) (c : CV) (isTop : Bool) (A : LA) : LA :=
  topCellV1 v a1 tp c isTop A (Nat.add c.bet (bc v tp.DEm))
where
  /-- With `beta`. -/
  topCellV1 (v : VC) (a1 : Nat) (tp : TV) (c : CV) (isTop : Bool) (A : LA) (beta : Nat) : LA :=
    topCellV2 v a1 tp c isTop A beta (ge v beta c.A1) (ge v c.A0 beta)
      (bsel isTop c.sp (Nat.add c.sp (bc v tp.PmW)))
  /-- With the masks `STOP` (`A1 ≤ beta`) and `LOW` (`beta ≤ A0`), and `S`. -/
  topCellV2 (v : VC) (a1 : Nat) (tp : TV) (c : CV) (isTop : Bool) (A : LA) (beta STOP LOW S : Nat) :
      LA :=
    topCellV3 v a1 tp c isTop A beta STOP LOW S
      (Nat.land (notM v STOP) (notM v LOW))
      (Nat.land (notM v STOP) (Nat.land (nz v S) (notM v (ge v c.A0 (Nat.add beta S)))))
  /-- With the masks `CROSS` and `CHORD` (not stop, `S ≠ 0`, `beta + S > A0`). -/
  topCellV3 (v : VC) (a1 : Nat) (tp : TV) (c : CV) (isTop : Bool) (A : LA)
      (beta STOP LOW S CROSS CH : Nat) : LA :=
    topCellV4 v a1 tp c isTop A beta STOP LOW S CROSS CH
      (bsel (Nat.beq (Nat.lor CROSS CH) 0) (0, 0) (divQR LW 37 v.G (tsub v beta c.A0) c.kk))
  /-- With `(q1, r1)` of `(beta - A0) / kk`. -/
  topCellV4 (v : VC) (a1 : Nat) (tp : TV) (c : CV) (isTop : Bool) (A : LA)
      (beta STOP LOW S CROSS CH : Nat) (qr : Nat × Nat) : LA :=
    topCellV5 v tp c isTop A beta STOP LOW S
      (bsel (Nat.beq CROSS 0) (0, 0) (crossV v a1 c beta qr.1))
      (bsel (Nat.beq CH 0) (0, true) (chordV v c.h beta S c.kk c.A0 c.A1 qr.1 qr.2 CH))
      (Nat.land (notM v STOP) (nz v S))
  /-- With the crossing terms, the chord, and the mask of `acc += Q coef`. -/
  topCellV5 (v : VC) (tp : TV) (c : CV) (isTop : Bool) (A : LA) (beta STOP LOW S : Nat)
      (cr : Nat × Nat) (ch : Nat × Bool) (USE : Nat) : LA :=
    topCellV6 v tp c isTop A STOP USE (sl (ge v c.A0 (Nat.add beta S)) (bc v c.h) ch.1) ch.2
      (Nat.add A.rp (sl STOP c.IA (sl LOW (Nat.mul c.h2 beta) cr.1)))
      (Nat.add A.rn (sl STOP 0 (sl LOW c.ssq cr.2)))
      (creditV v (shr36 (tsub v beta c.A1) v) c.own (bsel isTop tp.topOn false))
  /-- With `Q`, the new `rp`, `rn` and the credits. -/
  topCellV6 (v : VC) (tp : TV) (c : CV) (isTop : Bool) (A : LA) (STOP USE Q : Nat) (qok : Bool)
      (rp rn : Nat) (cr : List Nat × Nat) : LA :=
    LA.mk rp rn
      (addL A.ac (lapp (lmap (fun co => msk USE (mulv v 37 co Q)) c.co)
        [msk USE (Nat.mul (bsel isTop 0 tp.Pm) Q)]))
      (addL A.lm (lapp (lmap (msk STOP) cr.1) [msk STOP cr.2]))
      (bsel qok A.ok false)

/-! ## The tail (section 5.4) -/

/-- The crossing terms of `cell2` in a tail cell (scalar `sigma`, `kk`). -/
noncomputable def crossT (v : VC) (a1 a0 sig kk : Nat) (cl : SC) (beta q1 : Nat) : Nat × Nat :=
  (Nat.add
      (mulv v 37 (Nat.add (bc v (Nat.add a0 a0)) (Nat.mul a1 (Nat.add (bc v (Nat.add cl.pa cl.pa)) q1))) q1)
      (Nat.mul 2 (mulv v 37 beta (tsub v (bc v cl.h) q1))),
    Nat.add (Nat.mul sig (tsub v (bc v (Nat.mul cl.pb cl.pb))
      (mulv v 37 (Nat.add (bc v cl.pa) q1) (Nat.add (bc v cl.pa) q1)))) (bc v (Nat.add kk kk)))

/-- A tail cell `cl` on the lanes of `CONT` (`tailCell`): `cell2` with the scalars `a0`, `sigma =
r E_{t+1}`, `kk`, `A0`, `A1`, and `acc += chord sg (Hc)` where `S ≠ 0`. -/
noncomputable def tailCellV (v : VC) (r a1 a0 U S : Nat) (gs : List Nat) (cl : SC) (CONT : Nat)
    (A : LA) : LA :=
  tailCellV1 v a1 a0 S gs cl CONT A (Nat.mul r cl.e1)
    (Nat.add U (bc v (Nat.add (Nat.mul DS cl.et) (Nat.mul (Nat.mul r cl.e1) cl.pb))))
where
  /-- With `sigma` and `beta`. -/
  tailCellV1 (v : VC) (a1 a0 S : Nat) (gs : List Nat) (cl : SC) (CONT : Nat) (A : LA)
      (sig beta : Nat) : LA :=
    tailCellV2 v a1 a0 S gs cl CONT A sig beta (Nat.add a1 sig)
      (Nat.add a0 (Nat.mul (Nat.add a1 sig) cl.pa)) (Nat.add a0 (Nat.mul (Nat.add a1 sig) cl.pb))
  /-- With `kk`, `A0`, `A1`. -/
  tailCellV2 (v : VC) (a1 a0 S : Nat) (gs : List Nat) (cl : SC) (CONT : Nat) (A : LA)
      (sig beta kk A0 A1 : Nat) : LA :=
    tailCellV3 v a1 a0 S gs cl CONT A sig beta kk A0 A1 (ge v beta (bc v A1)) (ge v (bc v A0) beta)
  /-- With the masks `HI` (`A1 ≤ beta`) and `LOW` (`beta ≤ A0`). -/
  tailCellV3 (v : VC) (a1 a0 S : Nat) (gs : List Nat) (cl : SC) (CONT : Nat) (A : LA)
      (sig beta kk A0 A1 HI LOW : Nat) : LA :=
    tailCellV4 v a1 a0 S gs cl CONT A sig beta kk A0 A1 HI LOW
      (Nat.land CONT (Nat.land (notM v HI) (notM v LOW)))
      (Nat.land CONT (Nat.land (nz v S) (Nat.land (notM v HI)
        (notM v (ge v (bc v A0) (Nat.add beta S))))))
  /-- With the masks `CROSS` and `CHORD`. -/
  tailCellV4 (v : VC) (a1 a0 S : Nat) (gs : List Nat) (cl : SC) (CONT : Nat) (A : LA)
      (sig beta kk A0 A1 HI LOW CROSS CH : Nat) : LA :=
    tailCellV5 v a1 a0 S gs cl CONT A sig beta kk A0 A1 HI LOW CROSS CH
      (bsel (Nat.beq (Nat.lor CROSS CH) 0) (0, 0)
        (divQR LW 37 v.G (tsub v beta (bc v A0)) (bc v kk)))
  /-- With `(q1, r1)`. -/
  tailCellV5 (v : VC) (a1 a0 S : Nat) (gs : List Nat) (cl : SC) (CONT : Nat) (A : LA)
      (sig beta kk A0 A1 HI LOW CROSS CH : Nat) (qr : Nat × Nat) : LA :=
    tailCellV6 v S gs CONT A HI LOW
      (bsel (Nat.beq CROSS 0) (0, 0) (crossT v a1 a0 sig kk cl beta qr.1))
      (bsel (Nat.beq CH 0) (0, true)
        (chordV v cl.h beta S (bc v kk) (bc v A0) (bc v A1) qr.1 qr.2 CH))
      (Nat.mul cl.h (Nat.add (Nat.add a0 a0) (Nat.mul a1 (Nat.add cl.pb cl.pa))))
      (Nat.mul (Nat.add cl.h cl.h) beta) (Nat.mul sig (Nat.sub (Nat.mul cl.pb cl.pb) (Nat.mul cl.pa cl.pa)))
      (Nat.land CONT (Nat.land (nz v S) (notM v HI)))
      (sl (ge v (bc v A0) (Nat.add beta S)) (bc v cl.h) 0)
  /-- With the crossing terms, the chord, the terms of the two other cases, the mask of
  `acc += chord sg` (`HI` gives the chord `0`) and the chord `h` where `beta + S ≤ A0`. -/
  tailCellV6 (v : VC) (_S : Nat) (gs : List Nat) (CONT : Nat) (A : LA) (HI LOW : Nat)
      (cr : Nat × Nat) (ch : Nat × Bool) (rpHI rpLOW rnLOW USE QH : Nat) : LA :=
    tailCellV7 gs A
      (msk CONT (sl HI (bc v rpHI) (sl LOW rpLOW cr.1)))
      (msk CONT (sl HI 0 (sl LOW (bc v rnLOW) cr.2)))
      (msk USE (Nat.add QH ch.1)) ch.2 v
  /-- With the additions to `rp`, `rn` and the chord. -/
  tailCellV7 (gs : List Nat) (A : LA) (drp drn Q : Nat) (qok : Bool) (v : VC) : LA :=
    LA.mk (Nat.add A.rp drp) (Nat.add A.rn drn) (addL A.ac (lmap (fun g => mulv v 37 g Q) gs)) A.lm
      (bsel qok A.ok false)

/-- The tail cells from the boundary `(pj, etj, etmj)` on the lanes of `ACT` (`tailCells`): a lane
stops at the first boundary with `D (etj + r) + U + S ≤ a0 + a1 pj` and takes the exact tail from
there, else the cell. -/
noncomputable def tailV (v : VC) (r a1 a0 U S : Nat) (gs : List Nat) :
    List SC → Nat → Nat → Nat → Nat → LA → LA :=
  @List.rec SC (fun _ => Nat → Nat → Nat → Nat → LA → LA)
    (fun _ _ _ _ A => A)
    (fun cl _ ih pj etj etmj ACT A =>
      tailV1 v r U gs cl ih pj etmj ACT A (Nat.land ACT (ge v (bc v (Nat.add a0 (Nat.mul a1 pj)))
        (Nat.add (Nat.add U S) (bc v (Nat.mul DS (Nat.add etj r)))))) a1 a0 S)
where
  /-- With the mask `END` of the lanes that stop here. -/
  tailV1 (v : VC) (r U : Nat) (gs : List Nat) (cl : SC)
      (ih : Nat → Nat → Nat → Nat → LA → LA) (pj etmj ACT : Nat) (A : LA) (END a1 a0 S : Nat) : LA :=
    tailV2 v r U gs cl ih (Nat.sub ACT END)
      (bsel (Nat.ble DS pj) A
        (LA.mk (Nat.add A.rp (msk END (Nat.add (bc v (Nat.div (Nat.mul (Nat.mul 2 DS2) etmj) (Nat.succ r)))
            (Nat.mul (Nat.mul 2 (Nat.sub DS pj)) U)))) A.rn
          (addL A.ac (lmap (fun g => msk END (Nat.mul (Nat.sub DS pj) g)) gs)) A.lm A.ok))
      a1 a0 S
  /-- With the lanes that go on and the accumulators after the stops. -/
  tailV2 (v : VC) (r U : Nat) (gs : List Nat) (cl : SC) (ih : Nat → Nat → Nat → Nat → LA → LA)
      (CONT : Nat) (A : LA) (a1 a0 S : Nat) : LA :=
    bsel (Nat.beq CONT 0) A
      (ih cl.pb cl.et cl.etm CONT (tailCellV v r a1 a0 U S gs cl CONT A))

/-! ## The states of one top record -/

/-- The cells `i ≤ im` of the top record (`topLoop`, before the tail). -/
noncomputable def topLoopV (v : VC) (a1 : Nat) (tp : TV) : List CV → Nat → LA → LA :=
  @List.rec CV (fun _ => Nat → LA → LA) (fun _ A => A)
    (fun cv _ ih i A =>
      bsel (Nat.ble i tp.im) (ih (Nat.succ i) (topCellV v a1 tp (preCV v.n cv) (Nat.beq i tp.im) A)) A)

/-- The record list of a state as `rget`: `rget l k` of the cells. -/
noncomputable def cget (l : List CV) (k : Nat) : CV :=
  @List.rec CV (fun _ => CV) (CV.mk 0 0 0 0 0 0 0 0 0 [] [] 0 0 0 0 0 0 0 0 [] false) (fun a _ _ => a)
    (ldrop k l)

/-- The final checks of the states of one top: `2 D^2 uh + rn ≤ rp`, `sg_l ≤ mu_l` (`mu_l = 0` for a
forgotten record), `acc_l`, `lam_l < 2 ^ 128`, no saturated quotient. -/
noncomputable def finCheck (v : VC) (pv : PV) (uh : Nat) (sg : List Nat) (topFg : Bool) (A : LA) :
    Bool :=
  bsel A.ok
    (bsel (allGe v.G A.rp (Nat.add (Nat.mul (Nat.mul 2 DS2) uh) A.rn))
      (lall (fun p => bsel (allGe v.G (bc v M128') p.1) (bsel (allGe v.G (bc v M128') p.2.1)
          (allGe v.G p.2.2.1 p.2.2.2) false) false)
        (lzipWith (fun fgm x => (x.1, x.2.1,
            msk (notM v fgm) (Nat.add x.2.1 (shr36 x.1 v)), x.2.2))
          (lapp (lmap (fun F => pre LW v.n (Nat.shiftLeft F 143)) pv.fg) [bsel topFg v.G 0])
          (lzipWith (fun a y => (a, y)) A.ac (lzipWith (fun l s => (l, s)) A.lm sg))))
      false)
    false

/-- The check of the states of top record `j` (`top`, `n` lanes, offset `off` in the claimed fields
that start at the state `base` of the table of time `t`): the accumulators of section 5 on all lanes, then `2 D^2 uh + rn ≤ rp`, `sg_l ≤ mu_l`,
the fields of `acc` and `lam` below `2 ^ 128`, and the tail lookup `Hc = H_im`. -/
noncomputable def topCheck (c : Ctx) (pv : PV) (cvs : List CV) (UV : Nat) (US : List Nat) (base j : Nat)
    (top : SR) : Bool :=
  topCheck1 c pv cvs UV US top (cnt (Nat.sub c.m 1) (Nat.succ j)) (Nat.sub (cnt c.m j) base)
where
  /-- With the number of lanes `n` and the offset `off`. -/
  topCheck1 (c : Ctx) (pv : PV) (cvs : List CV) (UV : Nat) (US : List Nat) (top : SR)
      (n off : Nat) : Bool :=
    topCheck2 c pv cvs (pre LW n (drp LW off UV)) (preL n (lmap (drp LW off) US)) top (mkVC n)
      (TV.mk (Nat.mul DS top.em) (bsel top.fg 0 (Nat.mul top.pm top.dl)) (bsel top.fg 0 top.pm)
        top.pos (bsel top.fg false true))
  /-- With the claimed fields of the states, the lanes and the constants of the top. -/
  topCheck2 (c : Ctx) (pv : PV) (cvs : List CV) (uh : Nat) (sg : List Nat) (top : SR) (v : VC)
      (tp : TV) : Bool :=
    topCheck3 c pv uh sg top v (preCV v.n (cget cvs (Nat.sub top.pos 1)))
      (topLoopV v c.a1 tp cvs 1 (LA.mk 0 0 (lmap (fun _ => 0) (List.range c.m))
        (lmap (fun _ => 0) (List.range c.m)) true))
      (bsel (Nat.ble (List.length c.cells) top.pos) true top.fg)
  /-- With the cell `im` (its lookup is `Hc`), the accumulators of the cells `i ≤ im`, and
  whether there is no tail. -/
  topCheck3 (c : Ctx) (pv : PV) (uh : Nat) (sg : List Nat) (top : SR) (v : VC) (ci : CV) (A : LA)
      (noTail : Bool) : Bool :=
    bsel noTail (finCheck v pv uh sg top.fg A)
      (bsel (Nat.beq ci.idx (Nat.add (pre LW v.n (llast 0 pv.cs)) (bc v top.bsl)))
        (finCheck v pv uh sg top.fg
          (tailV v c.r c.a1 (Nat.mul (Nat.succ c.m) DS2) (Nat.mul DS ci.gv)
            (Nat.add (lfoldr Nat.add 0 (lzipWith (fun g w => mulv v 37 g w) ci.gs (preL v.n pv.dl)))
              (Nat.mul top.dl (llast 0 ci.gs)))
            ci.gs (ldrop top.pos c.cells) top.val top.em top.etm v.G A))
        false)

/-! ## The step -/

/-- `2 ^ 32`, the bound of the ranks. -/
def B32 : Nat := 4294967296

/-- The scalar conditions of a fixed-window step: `2 ≤ m ≤ 32`, no new point, the record `k` in
the cell `k + 1` and as many cells as records (at most `4096`), every `ev = 0`, and the step data
bounded (by `D`, `D ^ 2`, `1024 D ^ 3` and, for the binomials of the ranks, `2 ^ 32`), so that every
lane of the lanes check stays below `2 ^ 143`. -/
noncomputable def ctxOK (c : Ctx) : Bool :=
  bsel (bsel (Nat.ble 2 c.m) (Nat.ble c.m 32) false)
    (bsel (@List.rec SR (fun _ => Bool) true (fun _ _ _ => false) c.newp)
      (bsel (lall (fun r => bsel (Nat.beq r.ev 0) (bsel (Nat.ble r.dl DS) (bsel (Nat.ble r.em DS)
          (bsel (Nat.ble r.etm DS) (bsel (Nat.ble r.val DS) (bsel (Nat.ble r.pm (Nat.mul 1024 DS))
            (bsel (Nat.ble r.bsl B32) (lall (fun b => Nat.ble b B32) r.bs) false) false) false)
            false) false) false) false) c.recs)
        (bsel (posEq c.recs 0)
          (bsel (bsel (Nat.ble c.r 1023) (bsel (Nat.beq (List.length c.cells) (List.length c.recs))
              (Nat.ble (List.length c.recs) 4096) false) false)
            (lall (fun cl => bsel (Nat.ble cl.pa cl.pb) (bsel (Nat.ble cl.pb DS)
              (bsel (Nat.ble cl.et DS) (bsel (Nat.ble cl.e1 DS) (bsel (Nat.ble cl.etm DS)
                (bsel (Nat.ble cl.pn DS) (cellOK cl) false) false) false) false) false) false) c.cells)
            false)
          false)
        false)
      false)
    false
where
  /-- The record `k` sits in the cell `k + 1`, from `k = p`. -/
  posEq (l : List SR) (p : Nat) : Bool :=
    @List.rec SR (fun _ => Nat → Bool) (fun _ => true)
      (fun r _ ih p => bsel (Nat.beq r.pos (Nat.succ p)) (ih (Nat.succ p)) false) l p
  /-- The derived constants of a cell bounded: `h ≤ D`, `2 h ≤ 2 D`, `p_i ^ 2 - p_{i-1} ^ 2 ≤ D ^ 2`,
  `a1 (p_i ^ 2 - p_{i-1} ^ 2) ≤ 1024 D ^ 3`, the binomials of the rank at most `2 ^ 32`. -/
  cellOK (cl : SC) : Bool :=
    bsel (Nat.ble cl.h DS) (bsel (Nat.ble cl.h2 (Nat.add DS DS)) (bsel (Nat.ble cl.sqd DS2)
      (bsel (Nat.ble cl.a1sq (Nat.mul 1024 (Nat.mul DS DS2))) (lall (fun b => Nat.ble b B32) cl.cb)
        false) false) false) false

/-- The first `n` states of a concatenation of `Ws`-bit states. -/
noncomputable def preS (Ws n T : Nat) : Nat := Nat.land T (Nat.sub (Nat.shiftLeft 1 (Nat.mul Ws n)) 1)

/-- The lanes check of the states of the top records `lo .. hi - 1` of the step `t` of a
fixed-window step: the claimed table `Nt` of time `t` against the claimed table `Nn` of time
`t + 1`. Only the cells `1 .. hi`, the prefixes of those tops, the states of `Nn` of top below `hi`
and the states of `Nt` of those tops are unpacked. -/
noncomputable def lanesRange (g : Grid) (t : Nat) (Nn Nt : List Nat) (lo hi : Nat) : Bool :=
  lanesRange1 (mkCtx g t) Nn Nt (Nat.mul 48 (Nat.succ g.m)) lo hi
where
  /-- With the step data and the state width. -/
  lanesRange1 (c : Ctx) (Nn Nt : List Nat) (Ws lo hi : Nat) : Bool :=
    bsel (ctxOK c) (bsel (litsOK Ws Nn) (bsel (litsOK Ws Nt)
      (lanesRange2 c (litCat Ws Nn) (litCat Ws Nt) Ws lo (Nat.min hi (List.length c.recs))
        (List.length c.recs)) false) false) false
  /-- With the concatenated tables, `hi ≤ R` and the number of records `R`. -/
  lanesRange2 (c : Ctx) (Tn Tt : Nat × Nat) (Ws lo hi R : Nat) : Bool :=
    bsel (bsel (Nat.beq Tt.2 (cnt c.m R)) (Nat.ble Tt.2 B32) false) (bsel (Nat.ble (cnt c.m hi) Tn.2)
      (lanesRange3 c (fields c.m (preS Ws (cnt c.m hi) Tn.1) (cnt c.m hi))
        (fields c.m (preS Ws (Nat.sub (cnt c.m hi) (cnt c.m lo)) (Nat.shiftRight Tt.1 (Nat.mul Ws (cnt c.m lo))))
          (Nat.sub (cnt c.m hi) (cnt c.m lo)))
        lo hi (cnt (Nat.sub c.m 1) hi) (mkPV c.recs (Nat.sub c.m 1)))
      false) false
  /-- With the fields, the number of prefixes `np` and the prefix vectors. -/
  lanesRange3 (c : Ctx) (Fn Ft : Nat × List Nat × Bool) (lo hi np : Nat) (pv : PV) : Bool :=
    bsel Fn.2.2 (bsel Ft.2.2
      (lanesRange4 c Ft lo hi (PV.mk (preL np pv.pos) (preL np pv.dl) (preL np pv.fg) (preL np pv.cs))
        (mkVC np) (cnt c.m hi) Fn) false) false
  /-- With the prefix vectors and the constants of the `np` lanes. -/
  lanesRange4 (c : Ctx) (Ft : Nat × List Nat × Bool) (lo hi : Nat) (pv : PV) (v : VC) (NS : Nat)
      (Fn : Nat × List Nat × Bool) : Bool :=
    lanesRange5 c Ft lo hi pv
      (lmapIdx (fun i cl => mkCV v pv NS c.a1 Fn.1 Fn.2.1 (Nat.succ i) cl) 0 (ltake hi c.cells))
  /-- With the cells. -/
  lanesRange5 (c : Ctx) (Ft : Nat × List Nat × Bool) (lo hi : Nat) (pv : PV) (cvs : List CV) :
      Bool :=
    bsel (lall (fun cv => cv.ok) cvs)
      (lall (fun jr => topCheck c pv cvs Ft.1 Ft.2.1 (cnt c.m lo) jr.1 jr.2)
        (lmapIdx (fun j r => (j, r)) lo (ltake (Nat.sub hi lo) (ldrop lo c.recs))))
      false

/-- The lanes check of the step `t` of a fixed-window step, all top records at once. -/
noncomputable def lanesStep (g : Grid) (t : Nat) (Nn Nt : List Nat) : Bool :=
  lanesStep1 (mkCtx g t) Nn Nt (Nat.mul 48 (Nat.succ g.m))
where
  /-- With the step data and the state width. -/
  lanesStep1 (c : Ctx) (Nn Nt : List Nat) (Ws : Nat) : Bool :=
    lanesRange.lanesRange1 c Nn Nt Ws 0 (List.length c.recs)

end Robbins.Cert.SO.L
