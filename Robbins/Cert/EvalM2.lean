import Robbins.Cert.EvalK

/-!
# The kernel evaluator for memory size `m = 2`

The computation of Robbins/Cert/EvalK.lean for `m = 2`, with the tables as triangles of lists and
the crossing found by an untrusted search, then checked.

A table `uhat_t` is kept head-major: `H [a] = [uhat (a, a), uhat (a, a + 1), ..., uhat (a, cnt)]`.
One step builds the top-major triangle `T [b] = [N (0, b), ..., N (b, b)]` of the input `N`, the
lines `line [x] = [N (sort (x, y)) : y = 0, ..., cnt']` as `T [x] ++ tail H [x]`, and for each
head `h` of time `t` (with the line of `map h`) the cells of the head and the values of the
states `(h, k)`, `k = h, ..., cnt`. For each state the search returns a zipper `(pre, suf)` of the
head cells; the crossing `c = |pre| + 1` is checked (`Pos` fails at the head of `pre` and holds at
the head of `suf`), and the value is `R (c) / 2 ^ 41`, or `0` when the check fails (sound, and
never the case on tables that agree bit for bit with the specification). The min-closure is fused with the
heads: `C_h = runMin (min (O_h, tail C_{h-1}))`.
-/

namespace Robbins.Cert.M2

open Robbins.Cert Robbins.Cert.K

/-- `min` by `Nat.ble`. -/
noncomputable def nmin (a b : Nat) : Nat := bsel (Nat.ble a b) a b

/-- The top-major triangle `T [b] = [H [a] [b - a] : a ≤ b]` of a head-major triangle `H`. -/
noncomputable def skewT (H : List (List Nat)) : List (List Nat) :=
  lfoldr (fun row acc => [hd row] :: lzipWith List.cons (tl row) acc) [] H

/-- The lines `T [x] ++ tail H [x]`. -/
noncomputable def lines (H : List (List Nat)) : List (List Nat) :=
  lzipWith (fun tx hx => lapp tx (tl hx)) (skewT H) H

/-- Running minimum. -/
noncomputable def runMin2 (l : List Nat) : List Nat :=
  @List.rec Nat (fun _ => Nat → List Nat) (fun _ => [])
    (fun a _ r p => let c := nmin a p; c :: r c) l (hd l)

/-- The min-closure of head-major rows: `C_0 = runMin O_0`,
`C_h = runMin (min (O_h, tail C_{h-1}))`. -/
noncomputable def closeRows (rows : List (List Nat)) : List (List Nat) :=
  @List.rec (List Nat) (fun _ => Option (List Nat) → List (List Nat)) (fun _ => [])
    (fun o _ r p =>
      let c := runMin2 (@Option.rec (List Nat) (fun _ => List Nat) o
        (fun p => lzipWith nmin o (tl p)) p)
      c :: r (some c)) rows none

/-- The head cells of head `h` (`hlt`: `h < cnt_t`), walking the cells and the line. -/
noncomputable def headCells (cells : List KCell) (line : List Nat) (h : Nat) (hlt : Bool) :
    List KH :=
  @List.rec KCell (fun _ => List Nat → Nat → Nat → List KH)
    (fun _ _ _ => [])
    (fun c _ rec line q sp =>
      let line' := ldrop c.dn line
      let rw := hd line'
      let q' := Nat.add q (Nat.mul c.h2 rw)
      let two := bsel hlt (Nat.ble (Nat.add h 2) c.i) false
      let aD := bsel two 2199023255552 1099511627776
      let sA := Nat.add (bsel two (Nat.add c.hD2 c.hD2) c.hD2) c.sq
      KH.mk c rw q' sp (Nat.add aD c.rb) (Nat.add aD c.ra) sA ::
        rec line' q' (Nat.add sp sA))
    cells line 0 0

/-- The tail at the cell `x` for `U`. -/
noncomputable def tailM (r U : Nat) (x : KCell) : Nat :=
  bsel x.lt1 (bsel (Nat.ble (Nat.add (Nat.add U x.ep) r) x.mDrp)
    (Nat.add x.tT1 (Nat.mul x.tX2 U)) 0) 0

/-- `R` for the top cell `top` and the zipper suffix at the crossing. -/
noncomputable def stateR (r spL : Nat) (top : KH) (suf : List KH) : Nat :=
  let U := top.row
  @List.rec KH (fun _ => Nat)
    (Nat.add spL (Nat.sub 2417851639229258349412352 top.c.pb2D))
    (fun hc rest _ =>
      bsel (Nat.ble hc.c.i top.c.i)
        (let C := Nat.add top.c.ep hc.row
         Nat.add (Nat.add (Nat.add (Nat.add hc.spa (jK r C hc.aDrp hc.aDra hc.sA hc.c.h2))
           (Nat.mul (Nat.mul 2 top.c.ep) (Nat.sub top.c.pb hc.c.pb)))
           (Nat.sub top.qb hc.qb)) (tailM r U top.c))
        (let C := Nat.add hc.c.ep U
         let base := Nat.add (Nat.add hc.spa (Nat.sub hc.c.pa2D top.c.pb2D))
           (jK r C hc.c.mDrp hc.c.mDra hc.c.mS hc.c.h2)
         bsel (bsel hc.c.lt1 (Nat.ble (Nat.add (Nat.add U hc.c.ep) r) hc.c.mDrp) true)
           (Nat.add base (tailM r U hc.c))
           (@List.rec KH (fun _ => Nat) base
             (fun nx _ _ => Nat.add (Nat.add base (Nat.mul nx.c.h2 (Nat.add nx.c.ep U)))
               (tailM r U nx.c)) rest)))
    suf

/-- The check of the crossing at the zipper `(pre, suf)`: `Pos` fails at the head of `pre` and
holds at the head of `suf`. -/
noncomputable def crossChk (im Em U : Nat) (pre suf : List KH) : Bool :=
  bsel (@List.rec KH (fun _ => Bool) true (fun q _ _ => bsel (posK im Em U q) false true) pre)
    (@List.rec KH (fun _ => Bool) true (fun x _ _ => posK im Em U x) suf) false

/-- The values of the states with top cells `tops`. -/
noncomputable def headStates (r spL : Nat) (tops pre suf : List KH) : List Nat :=
  @List.rec KH (fun _ => List KH → List KH → List Nat) (fun _ _ => [])
    (fun top _ rec pre suf =>
      searchK top.c.i top.c.ep top.row pre suf
        (fun pre' suf' =>
          bsel (crossChk top.c.i top.c.ep top.row pre' suf')
            (Nat.shiftRight (stateR r spL top suf') 41) 0 :: rec pre' suf'))
    tops pre suf

/-- The raw values `[V (h, k) : k = h, ..., cnt]` of the head `h`. -/
noncomputable def headRow (sd : KStep) (h : Nat) (line : List Nat) : List Nat :=
  let hlt := Nat.blt h sd.cnt
  let hcs := headCells sd.cells line h hlt
  let last := llast KH.dflt hcs
  let suf := ldrop h hcs
  let tops := bsel hlt (lapp (ltake (Nat.sub sd.cnt h) suf) [last]) [last]
  headStates sd.r (Nat.add last.spa last.sA) tops (lrevOnto (ltake h hcs) []) suf

/-- One step: `uhat_t` (head-major) from `N = uhat_{t+1}` (head-major). -/
noncomputable def step (J r : Nat) (w w1 : Win) (gptD Et Etm1 : List Nat)
    (H : List (List Nat)) : List (List Nat) :=
  let sd := stepDataK 2 J r w w1 gptD Et Etm1
  closeRows (lmapIdx (fun h line => headRow sd h line) 0 (lselect [] sd.mp (lines H)))

/-- Run the steps from `t0` along the windows `[w_{t0}, ..., w_{t1}]`, from `H = uhat_{t0}`,
`E = E_{t0}`, `E1 = E_{t0-1}`. -/
noncomputable def run (n J : Nat) (gptD : List Nat) (ws : List Win) :
    Nat → List (List Nat) → List Nat → List Nat → List (List Nat) × List Nat :=
  @List.rec Win (fun _ => Win → Nat → List (List Nat) → List Nat → List Nat →
      List (List Nat) × List Nat)
    (fun _ _ H E _ => (H, E))
    (fun w _ r w1 t0 H _ E1 =>
      let E2 := nextEK gptD E1
      r w (Nat.sub t0 1) (step J (Nat.sub n (Nat.sub t0 1)) w w1 gptD E1 E2 H) E1 E2)
    (tl ws) (ws.headD ⟨0, 0⟩)

/-- The head-major triangle of a flat rank-order (top-major) table over `0, ..., a - 1`. -/
noncomputable def ofFlatH (a : Nat) (l : List Nat) : List (List Nat) :=
  triColsK (ofFlat 2 a l)

/-- The flat rank-order list of a head-major triangle. -/
noncomputable def toFlat (H : List (List Nat)) : List Nat :=
  lflat (skewT H)

/-- A block between checkpoints (flat rank-order tables). -/
noncomputable def block (g : Grid) (t0 t1 : Nat) (U0 E0 : List Nat) : List Nat × List Nat :=
  let gptD := g.gpt ++ [D]
  let ws := g.winsDown t0 t1
  let H0 := ofFlatH (Nat.succ (ws.headD ⟨0, 0⟩).cnt) U0
  let res := run g.n g.gpt.length gptD ws t0 H0 E0 (nextEK gptD E0)
  (toFlat res.1, res.2)

/-- The check of a block against the next checkpoint. -/
noncomputable def checkBlock (g : Grid) (t0 t1 : Nat) (U0 E0 U1 E1 : List Nat) : Bool :=
  let res := block g t0 t1 U0 E0
  bsel (lbeq res.1 U1) (lbeq res.2 E1) false

end Robbins.Cert.M2

namespace Robbins.Cert.M2

open Robbins.Cert Robbins.Cert.K

/-! ## Packed tables

A row is a list of literals of up to 16 values of 48 bits each, the first value in the lowest bits,
under a leading `1` bit. -/

/-- The values of one literal, prepended to `rest`. -/
noncomputable def decChunk (x : Nat) (rest : List Nat) : List Nat :=
  @Nat.rec (fun _ => Nat → List Nat) (fun _ => rest)
    (fun _ ih x => bsel (Nat.ble x 1) rest
      (Nat.land x 281474976710655 :: ih (Nat.shiftRight x 48))) 16 x

/-- The values of a packed row. -/
noncomputable def decRow (l : List Nat) : List Nat :=
  lfoldr decChunk [] l

/-- Equality of triangles. -/
noncomputable def lbeq2 (l1 l2 : List (List Nat)) : Bool :=
  @List.rec (List Nat) (fun _ => List (List Nat) → Bool)
    (fun l2 => @List.rec (List Nat) (fun _ => Bool) true (fun _ _ _ => false) l2)
    (fun a _ r l2 => @List.rec (List Nat) (fun _ => Bool) false
      (fun b t2 _ => bsel (lbeq a b) (r t2) false) l2) l1 l2

/-- The window of time `t`. -/
def wAt (g : Grid) (t : Nat) : Win := g.win (g.start.getD (t - 1) 0)

/-- The check of step `t`: `E_t = nextE E_{t+1}` and `uhat_t = step (uhat_{t+1})`, all four
tables packed (head-major for `uhat`). -/
noncomputable def checkStep (g : Grid) (t : Nat) (Hn : List (List Nat)) (En : List Nat)
    (Ht : List (List Nat)) (Et : List Nat) : Bool :=
  let gptD := g.gpt ++ [D]
  let Et' := decRow Et
  bsel (lbeq (nextEK gptD (decRow En)) Et')
    (lbeq2 (step g.gpt.length (Nat.sub g.n t) (wAt g t) (wAt g (Nat.succ t)) gptD Et'
      (nextEK gptD Et') (lmap decRow Hn)) (lmap decRow Ht)) false

/-! ## The tables of time `n` -/

/-- Head-major rows `[3 D - g_a - g_b : b = a, ..., cnt]` from the point values
`P = [g_0, ..., g_cnt]` (`3 D = 3298534883328`). -/
noncomputable def lastRows (P : List Nat) : List (List Nat) :=
  @List.rec Nat (fun _ => List (List Nat)) []
    (fun p ps r => lmap (fun y => Nat.sub (Nat.sub 3298534883328 p) y) (p :: ps) :: r) P

/-- The point values `g_0, ..., g_cnt` of `G_n`. -/
noncomputable def ptsLast (g : Grid) : List Nat :=
  lapp (ltake (wAt g g.n).cnt (ldrop (wAt g g.n).s g.gpt)) [D]

/-- The check of time `n`: `uhat_n` is `3 D - g_a - g_b` and `E_n` is `D` on `0, ..., J`. -/
noncomputable def checkLast (g : Grid) (Hn : List (List Nat)) (En : List Nat) : Bool :=
  bsel (lbeq2 (lmap decRow Hn) (lastRows (ptsLast g)))
    (lbeq (decRow En) (lmap (fun _ => D) (lapp g.gpt [D]))) false

end Robbins.Cert.M2
