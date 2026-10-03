import Robbins.Cert.Eval

/-!
# The evaluator in kernel form

The computation of Robbins/Cert/Eval.lean written for the Lean kernel: every loop over a list is
a `List.rec` (no `brecOn`), every branch a `Bool.rec` on `Nat.ble` or `Nat.beq`, every arithmetic
operation a direct `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div` (no type classes), results passed
to continuations rather than in pairs, and the per-state arithmetic of section 4.3 of the format reduced
to about twenty operations by per-cell and per-head constants. These definitions are not compiled
(the code generator does not take recursors); they are run by `decide +kernel`.
-/

namespace Robbins.Cert.K

open Robbins.Cert

/-! ## Combinators -/

/-- `List.foldr` as a recursor. -/
noncomputable def lfoldr {α β : Type} (f : α → β → β) (b : β) (l : List α) : β :=
  @List.rec α (fun _ => β) b (fun a _ r => f a r) l

/-- `List.map` as a recursor. -/
noncomputable def lmap {α β : Type} (f : α → β) (l : List α) : List β :=
  @List.rec α (fun _ => List β) [] (fun a _ r => f a :: r) l

/-- `if b then x else y`. -/
noncomputable def bsel {α : Type} (b : Bool) (x y : α) : α :=
  @Bool.rec (fun _ => α) y x b

/-- `List.headD l 0`. -/
noncomputable def hd (l : List Nat) : Nat :=
  @List.rec Nat (fun _ => Nat) 0 (fun a _ _ => a) l

/-- `List.tail`. -/
noncomputable def tl {α : Type} (l : List α) : List α :=
  @List.rec α (fun _ => List α) [] (fun _ t _ => t) l

/-- `List.drop`. -/
noncomputable def ldrop {α : Type} (k : Nat) (l : List α) : List α :=
  @Nat.rec (fun _ => List α → List α) (fun l => l) (fun _ ih l => ih (tl l)) k l

/-- `List.take`. -/
noncomputable def ltake {α : Type} (k : Nat) (l : List α) : List α :=
  @Nat.rec (fun _ => List α → List α) (fun _ => [])
    (fun _ ih l => @List.rec α (fun _ => List α) [] (fun a t _ => a :: ih t) l) k l

/-- `List.append`. -/
noncomputable def lapp {α : Type} (l1 l2 : List α) : List α :=
  @List.rec α (fun _ => List α) l2 (fun a _ r => a :: r) l1

/-- `List.reverse` onto an accumulator. -/
noncomputable def lrevOnto {α : Type} (l acc : List α) : List α :=
  @List.rec α (fun _ => List α → List α) (fun acc => acc) (fun a _ r acc => r (a :: acc)) l acc

/-- The last element, `dflt` for the empty list. -/
noncomputable def llast {α : Type} (dflt : α) (l : List α) : α :=
  @List.rec α (fun _ => α → α) (fun x => x) (fun a _ r _ => r a) l dflt

/-- `List.zipWith`. -/
noncomputable def lzipWith {α β γ : Type} (f : α → β → γ) (l1 : List α) (l2 : List β) : List γ :=
  @List.rec α (fun _ => List β → List γ) (fun _ => [])
    (fun a _ r l2 => @List.rec β (fun _ => List γ) [] (fun b t2 _ => f a b :: r t2) l2) l1 l2

/-- `zipLong`: `f` on the common prefix, then the rest of the first list. -/
noncomputable def lzipLong {α β : Type} (f : α → β → α) (l1 : List α) (l2 : List β) : List α :=
  @List.rec α (fun _ => List β → List α) (fun _ => [])
    (fun a t r l2 => @List.rec β (fun _ => List α) (a :: t) (fun b t2 _ => f a b :: r t2) l2) l1 l2

/-- `List.flatten`. -/
noncomputable def lflat {α : Type} (l : List (List α)) : List α :=
  @List.rec (List α) (fun _ => List α) [] (fun a _ r => lapp a r) l

/-- `mapIdxFrom`. -/
noncomputable def lmapIdx {α β : Type} (f : Nat → α → β) (k : Nat) (l : List α) : List β :=
  @List.rec α (fun _ => Nat → List β) (fun _ => []) (fun a _ r k => f k a :: r (Nat.succ k)) l k

/-- Running minimum. -/
noncomputable def runMin (l : List Nat) : List Nat :=
  @List.rec Nat (fun _ => Nat → List Nat) (fun _ => [])
    (fun a _ r p => let c := Nat.min a p; c :: r c) l (hd l)

/-- `select`: the entries of `l` at the nondecreasing indices `idx`. -/
noncomputable def lselect {α : Type} (dflt : α) (idx : List Nat) (l : List α) : List α :=
  @List.rec Nat (fun _ => Nat → List α → List α) (fun _ _ => [])
    (fun i _ r pos l =>
      let l' := ldrop (Nat.sub i pos) l
      (@List.rec α (fun _ => α) dflt (fun a _ _ => a) l') :: r i l') idx 0 l

/-- The `List.beq` of two lists of naturals. -/
noncomputable def lbeq (l1 l2 : List Nat) : Bool :=
  @List.rec Nat (fun _ => List Nat → Bool)
    (fun l2 => @List.rec Nat (fun _ => Bool) true (fun _ _ _ => false) l2)
    (fun a _ r l2 => @List.rec Nat (fun _ => Bool) false
      (fun b t2 _ => bsel (Nat.beq a b) (r t2) false) l2) l1 l2

/-! ## Tables -/

/-- Entrywise map. -/
noncomputable def tmap {α β : Type} (f : α → β) : (d : Nat) → Tab α d → Tab β d
  | 0, x => f x
  | d + 1, l => lmap (tmap f d) (l : List (Tab α d))

/-- Entrywise zip. -/
noncomputable def tzip {α β γ : Type} (f : α → β → γ) : (d : Nat) → Tab α d → Tab β d → Tab γ d
  | 0, x, y => f x y
  | d + 1, xs, ys => lzipWith (tzip f d) (xs : List (Tab α d)) (ys : List (Tab β d))

/-- Flatten in rank order. -/
noncomputable def tflat : (d : Nat) → Tab Nat d → List Nat
  | 0, x => [x]
  | 1, l => (l : List Nat)
  | d + 2, l => lflat (lmap (tflat (d + 1)) (l : List (Tab Nat (d + 1))))

/-- Read the slices of sizes given by `j + 1, j + 2, ...` (`k` of them) with the reader `f`,
continuation style. -/
noncomputable def unflatLoop {β γ : Type} (f : Nat → List Nat → (β → List Nat → γ) → γ) :
    Nat → Nat → List Nat → (List β → List Nat → γ) → γ :=
  fun k => @Nat.rec (fun _ => Nat → List Nat → (List β → List Nat → γ) → γ)
    (fun _ l c => c [] l)
    (fun _ ih j l c => f (Nat.succ j) l (fun x rest => ih (Nat.succ j) rest (fun xs r => c (x :: xs) r))) k

/-- Read a table over `0, ..., a - 1` from a flat rank-order list, continuation style. -/
noncomputable def tunflat {γ : Type} : (d : Nat) → Nat → List Nat → (Tab Nat d → List Nat → γ) → γ
  | 0, _, l, c => c (hd l) (tl l)
  | 1, a, l, c => c (ltake a l) (ldrop a l)
  | d + 2, a, l, c => unflatLoop (fun k l c => tunflat (d + 1) k l c) a 0 l c

/-- The table read from a flat list. -/
noncomputable def ofFlat (d a : Nat) (l : List Nat) : Tab Nat d :=
  tunflat d a l (fun x _ => x)

/-! ## The closure -/

/-- Entrywise min. -/
noncomputable def tmin : (d : Nat) → Tab Nat d → Tab Nat d → Tab Nat d
  | 0, x, y => Nat.min x y
  | 1, xs, ys => lzipWith Nat.min (xs : List Nat) (ys : List Nat)
  | d + 2, xs, ys => lzipWith (tmin (d + 1)) (xs : List (Tab Nat (d + 1)))
      (ys : List (Tab Nat (d + 1)))

/-- The combination of the slice `T_j` with the closed slice `C_{j-1}`. -/
noncomputable def tcomb : (d : Nat) → Tab Nat d → Tab Nat d → Tab Nat d
  | 0, x, y => Nat.min x y
  | d + 1, xs, ys => lzipLong (tmin d) (xs : List (Tab Nat d)) (ys : List (Tab Nat d))

/-- The min-closure. -/
noncomputable def tclose : (d : Nat) → Tab Nat d → Tab Nat d
  | 0, x => x
  | 1, l => runMin (l : List Nat)
  | d + 2, l =>
    @List.rec (Tab Nat (d + 1)) (fun _ => Option (Tab Nat (d + 1)) → List (Tab Nat (d + 1)))
      (fun _ => [])
      (fun t _ r p =>
        let c := tclose (d + 1) (Option.rec t (fun p => tcomb (d + 1) t p) p)
        c :: r (some c))
      (l : List (Tab Nat (d + 1))) none

/-! ## Lines, selection, head-major to rank order -/

/-- Prepend the entries of `row` to the first lists of `acc`. -/
noncomputable def zipPre {α : Type} (row : List α) (acc : List (List α)) : List (List α) :=
  @List.rec α (fun _ => List (List α) → List (List α)) (fun acc => acc)
    (fun x _ r acc => @List.rec (List α) (fun _ => List (List α)) ([x] :: r [])
      (fun c cs _ => (x :: c) :: r cs) acc) row acc

/-- Columns of a triangle. -/
noncomputable def triColsK {α : Type} (l : List (List α)) : List (List α) :=
  lfoldr zipPre [] l

/-- Collect a list of tables of one shape into a table of lists (`tmpl` gives the shape). -/
noncomputable def collectK {α : Type} (d : Nat) (tmpl : Tab α d) (ts : List (Tab α d)) :
    Tab (List α) d :=
  lfoldr (fun x acc => tzip List.cons d x acc) (tmap (fun _ => []) d tmpl) ts

/-- Lines of a table of `(d + 1)`-tuples. -/
noncomputable def linesK : (d : Nat) → Tab Nat (d + 1) → Tab (List Nat) d
  | 0, t => (t : List Nat)
  | d + 1, t =>
    lzipWith
      (fun (tj : Tab Nat (d + 1)) (col : List (Tab Nat d)) =>
        @List.rec (Tab Nat d) (fun _ => Tab (List Nat) d) (tmap (fun _ => []) d (linesK d tj))
          (fun diag above _ => tzip lapp d (linesK d tj) (collectK d diag above)) col)
      (t : List (Tab Nat (d + 1))) (triColsK (t : List (List (Tab Nat d))))

/-- The table `T (f k_1, ..., f k_d)` for a nondecreasing `f` given by its values. -/
noncomputable def selectK {α : Type} (dflt : α) : (d : Nat) → List Nat → Tab α d → Tab α d
  | 0, _, x => x
  | 1, f, l => lselect dflt f (l : List α)
  | d + 2, f, l =>
    lmapIdx (fun j (r : Tab α (d + 1)) => selectK dflt (d + 1) (ltake (Nat.succ j) f) r) 0
      (lselect (tmap (fun _ => dflt) (d + 1) ([] : List (Tab α d))) f (l : List (Tab α (d + 1))))

/-- Entrywise map with the tuple (ascending) of the entry. -/
noncomputable def mapTupK {α β : Type} : (d : Nat) → (List Nat → α → β) → Tab α d → Tab β d
  | 0, f, x => f [] x
  | d + 1, f, l =>
    lmapIdx (fun j (tj : Tab α d) => mapTupK d (fun κ x => f (lapp κ [j]) x) tj) 0
      (l : List (Tab α d))

/-- Head-major lists to rank order. -/
noncomputable def headToTopK : (d : Nat) → Tab (List Nat) d → Tab Nat (d + 1)
  | 0, h => (h : List Nat)
  | d + 1, h =>
    @List.rec (Tab (List Nat) d) (fun _ => List (Tab (List Nat) d) → List (List (Tab Nat d)))
      (fun _ => [])
      (fun x _ r act =>
        let act' := lapp act [x]
        lmap (tmap hd d) act' :: r (lmap (tmap tl d) act'))
      (h : List (Tab (List Nat) d)) []

/-! ## One step -/

/-- The constants of a cell `(p_{i-1}, p_i]` at time `t` (`r = n - t`, `m` the memory size). -/
structure KCell where
  /-- `i`. -/
  i : Nat
  /-- `nxt_i - nxt_{i-1}` (`nxt_0 = 0`). -/
  dn : Nat
  /-- `p_{i-1}`. -/
  pa : Nat
  /-- `p_i`. -/
  pb : Nat
  /-- `E_t (p_i)`. -/
  ep : Nat
  /-- `E_{t-1} (p_i)`. -/
  e1p : Nat
  /-- `2 (p_i - p_{i-1})`. -/
  h2 : Nat
  /-- `2 D (p_i - p_{i-1})`. -/
  hD2 : Nat
  /-- `r (p_i ^ 2 - p_{i-1} ^ 2)`. -/
  sq : Nat
  /-- `r p_i`. -/
  rb : Nat
  /-- `r p_{i-1}`. -/
  ra : Nat
  /-- `2 D p_{i-1}`. -/
  pa2D : Nat
  /-- `2 D p_i`. -/
  pb2D : Nat
  /-- `p_i < D`. -/
  lt1 : Bool
  /-- `(1 + m) D + r p_i`. -/
  mDrp : Nat
  /-- `(1 + m) D + r p_{i-1}`. -/
  mDra : Nat
  /-- `(1 + m) 2 D (p_i - p_{i-1}) + r (p_i ^ 2 - p_{i-1} ^ 2)`. -/
  mS : Nat
  /-- `floor (2 D E_{t-1} (p_i) / (r + 1))`. -/
  tT1 : Nat
  /-- `2 (D - p_i)`. -/
  tX2 : Nat

/-- A cell with the data of one head. -/
structure KH where
  /-- The cell. -/
  c : KCell
  /-- `row (h, i)`. -/
  row : Nat
  /-- `Q (h, i)`. -/
  qb : Nat
  /-- `Sint_head (p_{i-1})`. -/
  spa : Nat
  /-- `alpha_i D + r p_i`. -/
  aDrp : Nat
  /-- `alpha_i D + r p_{i-1}`. -/
  aDra : Nat
  /-- `alpha_i 2 D (p_i - p_{i-1}) + r (p_i ^ 2 - p_{i-1} ^ 2)`. -/
  sA : Nat

/-- The cell integral from the constants: `S` if `aDrp ≤ C`, `h2 C` if `C ≤ aDra`, else
`S - ceil ((aDrp - C) ^ 2 / r)`. -/
noncomputable def jK (r C aDrp aDra S h2 : Nat) : Nat :=
  bsel (Nat.ble aDrp C) S
    (bsel (Nat.ble C aDra) (Nat.mul h2 C)
      (let F := Nat.sub aDrp C
       Nat.sub S (Nat.div (Nat.add (Nat.mul F F) (Nat.sub r 1)) r)))

/-- The tail at the cell `x` (its endpoint `X = p_i`), for `U`. -/
noncomputable def tailK (r U : Nat) (x : KCell) : Nat :=
  bsel (x.lt1 && Nat.ble (Nat.add (Nat.add U x.ep) r) x.mDrp)
    (Nat.add x.tT1 (Nat.mul x.tX2 U)) 0

/-- The test `Pos_i`. -/
noncomputable def posK (im Em U : Nat) (hc : KH) : Bool :=
  bsel (Nat.ble hc.c.i im) (Nat.ble (Nat.add Em hc.row) hc.aDrp)
    (Nat.ble (Nat.add hc.c.ep U) hc.c.mDrp)

/-- `R` for the top cell `top` and the zipper suffix at the crossing. -/
noncomputable def stateRK (r spL : Nat) (top : KH) (suf : List KH) : Nat :=
  let U := top.row
  @List.rec KH (fun _ => Nat)
    (Nat.add spL (Nat.sub 2417851639229258349412352 top.c.pb2D))
    (fun hc rest _ =>
      bsel (Nat.ble hc.c.i top.c.i)
        (let C := Nat.add top.c.ep hc.row
         Nat.add (Nat.add (Nat.add (Nat.add hc.spa (jK r C hc.aDrp hc.aDra hc.sA hc.c.h2))
           (Nat.mul (Nat.mul 2 top.c.ep) (Nat.sub top.c.pb hc.c.pb)))
           (Nat.sub top.qb hc.qb)) (tailK r U top.c))
        (let C := Nat.add hc.c.ep U
         let base := Nat.add (Nat.add hc.spa (Nat.sub hc.c.pa2D top.c.pb2D))
           (jK r C hc.c.mDrp hc.c.mDra hc.c.mS hc.c.h2)
         bsel (!hc.c.lt1 || Nat.ble (Nat.add (Nat.add U hc.c.ep) r) hc.c.mDrp)
           (Nat.add base (tailK r U hc.c))
           (@List.rec KH (fun _ => Nat) base
             (fun nx _ _ => Nat.add (Nat.add base (Nat.mul nx.c.h2 (Nat.add nx.c.ep U)))
               (tailK r U nx.c)) rest)))
    suf

/-- Move the zipper left while the cell before it passes the test. -/
noncomputable def goLeftK {β : Type} (im Em U : Nat) (pre suf : List KH)
    (k : List KH → List KH → β) : β :=
  @List.rec KH (fun _ => List KH → β) (fun suf => k [] suf)
    (fun q qs r suf => bsel (posK im Em U q) (r (q :: suf)) (k (q :: qs) suf)) pre suf

/-- Move the zipper right while the cell under it fails the test. -/
noncomputable def goRightK {β : Type} (im Em U : Nat) (pre suf : List KH)
    (k : List KH → List KH → β) : β :=
  @List.rec KH (fun _ => List KH → β) (fun pre => k pre [])
    (fun x xs r pre => bsel (posK im Em U x) (k pre (x :: xs)) (r (x :: pre))) suf pre

/-- The crossing search, continuation style. -/
noncomputable def searchK {β : Type} (im Em U : Nat) (pre suf : List KH)
    (k : List KH → List KH → β) : β :=
  @List.rec KH (fun _ => β) (goLeftK im Em U pre suf k)
    (fun x _ _ => bsel (posK im Em U x) (goLeftK im Em U pre suf k) (goRightK im Em U pre suf k))
    suf

/-- The values `Btilde` of the states with top cells `tops`. -/
noncomputable def headStatesK (r spL : Nat) (tops pre suf : List KH) : List Nat :=
  @List.rec KH (fun _ => List KH → List KH → List Nat) (fun _ _ => [])
    (fun top _ rec pre suf =>
      searchK top.c.i top.c.ep top.row pre suf
        (fun pre' suf' => Nat.shiftRight (stateRK r spL top suf') 41 :: rec pre' suf'))
    tops pre suf

/-- Pop the head points `k` with `k + 2 ≤ i` (`κ` ascending), counting them into `al`. -/
noncomputable def popK {β : Type} (i : Nat) (κ : List Nat) (al : Nat)
    (k : List Nat → Nat → β) : β :=
  @List.rec Nat (fun _ => Nat → β) (fun al => k [] al)
    (fun x xs r al => bsel (Nat.ble (Nat.add x 2) i) (r (Nat.succ al)) (k (x :: xs) al)) κ al

/-- The head cells: walks the cells and the line of the head together. -/
noncomputable def headCellsK (cells : List KCell) (line κ : List Nat) : List KH :=
  @List.rec KCell (fun _ => List Nat → List Nat → Nat → Nat → Nat → List KH)
    (fun _ _ _ _ _ => [])
    (fun c _ rec line κ al q sp =>
      popK c.i κ al (fun κ' al' =>
        let line' := ldrop c.dn line
        let rw := hd line'
        let q' := Nat.add q (Nat.mul c.h2 rw)
        let aD := Nat.mul al' D
        let sA := Nat.add (Nat.mul al' c.hD2) c.sq
        KH.mk c rw q' sp (Nat.add aD c.rb) (Nat.add aD c.ra) sA ::
          rec line' κ' al' q' (Nat.add sp sA)))
    cells line κ 1 0 0

/-- A placeholder head cell. -/
def KH.dflt : KH :=
  ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, false, 0, 0, 0, 0, 0⟩, 0, 0, 0, 0, 0, 0⟩

/-- The per-step data. -/
structure KStep where
  /-- `r`. -/
  r : Nat
  /-- The cells. -/
  cells : List KCell
  /-- `map`. -/
  mp : List Nat
  /-- `cnt_t`. -/
  cnt : Nat

/-- One head: its cells and its states. -/
noncomputable def headRowK (sd : KStep) (κ : List Nat) (line : List Nat) : List Nat :=
  let top := llast 0 κ
  let hcs := headCellsK sd.cells line (κ.filter (fun k => Nat.blt k sd.cnt))
  let last := llast KH.dflt hcs
  let suf := ldrop top hcs
  let tops := bsel (Nat.blt top sd.cnt) (lapp (ltake (Nat.sub sd.cnt top) suf) [last]) [last]
  headStatesK sd.r (Nat.add last.spa last.sA) tops (lrevOnto (ltake top hcs) []) suf

/-- The step data at time `t` (`r = n - t`), windows `w` (time `t`) and `w1` (time `t + 1`). -/
def stepDataK (m J r : Nat) (w w1 : Win) (gptD Et Etm1 : List Nat) : KStep :=
  let pts := unionWin w w1 ++ [J]
  let pv := select 0 pts gptD
  let ep := select 0 pts Et
  let e1p := select 0 pts Etm1
  let nxt := pts.map (ceilLocal J w1)
  let dns := List.zipWith (fun a b => b - a) (0 :: nxt) nxt
  let mk := fun (i : Nat) (x : (Nat × Nat) × (Nat × Nat) × Nat) =>
    let pa := x.1.1
    let pb := x.1.2
    let e := x.2.1.1
    let e1 := x.2.1.2
    let hD2 := 2 * D * (pb - pa)
    let sq := r * (pb * pb - pa * pa)
    (⟨i, x.2.2, pa, pb, e, e1, 2 * (pb - pa), hD2, sq, r * pb, r * pa, 2 * D * pa, 2 * D * pb,
      decide (pb < D), (1 + m) * D + r * pb, (1 + m) * D + r * pa, (1 + m) * hD2 + sq,
      2 * D * e1 / (r + 1), 2 * (D - pb)⟩ : KCell)
  let cells := mapIdxFrom mk 1 (List.zip (List.zip (0 :: pv) pv) (List.zip (List.zip ep e1p) dns))
  let mp := (List.range' w.s w.cnt).map (ceilLocal J w1) ++ [ceilLocal J w1 J]
  ⟨r, cells, mp, w.cnt⟩

/-- One step for `m = d + 1`. -/
noncomputable def stepK (d J r : Nat) (w w1 : Win) (gptD Et Etm1 : List Nat)
    (N : Tab Nat (d + 1)) : Tab Nat (d + 1) :=
  let sd := stepDataK (d + 1) J r w w1 gptD Et Etm1
  tclose (d + 1) (headToTopK d (mapTupK d (fun κ line => headRowK sd κ line)
    (selectK [] d sd.mp (linesK d N))))

/-- `E_{t-1}` from `E_t`. -/
noncomputable def nextEK (gptD Et : List Nat) : List Nat :=
  lzipWith (fun e p => Nat.div (Nat.mul e (Nat.sub D p)) D) Et gptD

/-- Run the steps from `t0` along the windows `[w_{t0}, ..., w_{t1}]`, from `N = uhat_{t0}`,
`E = E_{t0}`, `E1 = E_{t0-1}`; the continuation gets `uhat_{t1}` and `E_{t1}`. -/
noncomputable def runK (d n J : Nat) (gptD : List Nat) (ws : List Win) :
    Nat → Tab Nat (d + 1) → List Nat → List Nat → Tab Nat (d + 1) × List Nat :=
  @List.rec Win (fun _ => Win → Nat → Tab Nat (d + 1) → List Nat → List Nat →
      Tab Nat (d + 1) × List Nat)
    (fun _ _ N E _ => (N, E))
    (fun w _ r w1 t0 N _ E1 =>
      let E2 := nextEK gptD E1
      r w (Nat.sub t0 1) (stepK d J (Nat.sub n (Nat.sub t0 1)) w w1 gptD E1 E2 N) E1 E2)
    (tl ws) (ws.headD ⟨0, 0⟩)

/-- A block between checkpoints: `uhat_{t1}` (flat) from `uhat_{t0}` (flat) and `E_{t0}`. -/
noncomputable def blockK (g : Grid) (d t0 t1 : Nat) (U0 E0 : List Nat) : List Nat × List Nat :=
  let gptD := g.gpt ++ [D]
  let ws := g.winsDown t0 t1
  let N0 := ofFlat (d + 1) (Nat.succ (ws.headD ⟨0, 0⟩).cnt) U0
  let res := runK d g.n g.gpt.length gptD ws t0 N0 E0 (nextEK gptD E0)
  (tflat (d + 1) res.1, res.2)

/-- The check of a block against the next checkpoint. -/
noncomputable def checkBlock (g : Grid) (d t0 t1 : Nat) (U0 E0 U1 E1 : List Nat) : Bool :=
  let res := blockK g d t0 t1 U0 E0
  lbeq res.1 U1 && lbeq res.2 E1

end Robbins.Cert.K
