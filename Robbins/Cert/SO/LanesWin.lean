import Robbins.Cert.SO.Lanes

/-!
# Windows of lanes

The lanes check of a fixed-window step cut finer than whole top records, so that every kernel
declaration of a run stays small enough for nanoda at 4 threads under 16 GB.

`lanesWin g t Nn Nt j a w` checks the lanes `[a, a + w)` of the top record `j` alone, that is the
states `[cnt m j + a, cnt m j + a + w)` of the claimed table of time `t`: the same scalar checks,
tables and lookups as `lanesRange g t Nn Nt j (j + 1)`, with the prefix vectors and the cells on the
`w` lanes of the window (`drp` then `pre`), the claimed fields from the state `cnt m j + a`, and
the lookups of the cells from the first rank of the window on (`mkCVw`).

`LPart` is one declaration of a step, a range of tops or a window; `lpCover` checks that the
states of the parts of a step cover the whole table, from the state `0` on.
-/

namespace Robbins.Cert.SO.L

open Robbins.Cert Robbins.Cert.K Robbins.Cert.SO.K Robbins.Lanes

/-- A cell on the `n` lanes of a window (`mkCV`), with the lookups of `H_i` from the source lane
`s0` on, `s0` the rank on the first lane: every rank at least `s0` is checked, and the compaction
and the routes run on the `NS - s0` source lanes from `s0`, so that their cost follows the ranks of
the window and not the whole table. -/
noncomputable def mkCVw (v : VC) (pv : PV) (NS a1 : Nat) (FV : Nat) (FS : List Nat) (i : Nat)
    (cl : SC) : CV :=
  mkCVw1 v pv NS a1 FV FS i cl
    (lfoldr Nat.add 0 (lmap (fun P => ind LW (ge v (bc v i) (Nat.add P v.O))) pv.pos))
where
  /-- With `below_i`. -/
  mkCVw1 (v : VC) (pv : PV) (NS a1 FV : Nat) (FS : List Nat) (i : Nat) (cl : SC) (B : Nat) : CV :=
    mkCVw2 v pv a1 i cl B (pickB v B (lzipWith (fun C c => Nat.add C (bc v c)) pv.cs cl.cb)) NS FV
      FS
  /-- With the ranks of `H_i`. -/
  mkCVw2 (v : VC) (pv : PV) (a1 i : Nat) (cl : SC) (B I NS FV : Nat) (FS : List Nat) : CV :=
    mkCVw3 v pv a1 i cl B I (pre LW 1 I) NS FV FS
  /-- With the first rank `s0`. -/
  mkCVw3 (v : VC) (pv : PV) (a1 i : Nat) (cl : SC) (B I s0 NS FV : Nat) (FS : List Nat) : CV :=
    mkCVw4 v pv a1 i cl B I (allGe v.G I (bc v s0))
      (mkRt (Nat.sub NS s0) v.n (Nat.sub I (bc v s0))) (drp LW s0 FV) (lmap (drp LW s0) FS)
  /-- With the compaction from `s0`. -/
  mkCVw4 (v : VC) (pv : PV) (a1 i : Nat) (cl : SC) (B I : Nat) (g : Bool) (rt : Rt) (FV : Nat)
      (FS : List Nat) : CV :=
    mkCV.mkCV4 v pv a1 i cl B I (bsel g rt.ok false) (route rt FV) (lmap (route rt) FS)

/-- The `w` lanes from the lane `a` of each vector of a list. -/
noncomputable def winL (a w : Nat) (l : List Nat) : List Nat := preL w (lmap (drp LW a) l)

/-- The lanes check of the lanes `[a, a + w)` of the top record `j` of the fixed-window step `t`:
the claimed table `Nt` of time `t` against the claimed table `Nn` of time `t + 1`, with
`j < R` and `a + w ≤ cnt (m - 1) (j + 1)` checked. -/
noncomputable def lanesWin (g : Grid) (t : Nat) (Nn Nt : List Nat) (j a w : Nat) : Bool :=
  lanesWin1 (mkCtx g t) Nn Nt (Nat.mul 48 (Nat.succ g.m)) j a w
where
  /-- With the step data and the state width. -/
  lanesWin1 (c : Ctx) (Nn Nt : List Nat) (Ws j a w : Nat) : Bool :=
    bsel (ctxOK c) (bsel (litsOK Ws Nn) (bsel (litsOK Ws Nt)
      (lanesWin2 c (litCat Ws Nn) (litCat Ws Nt) Ws j a w (List.length c.recs)) false) false) false
  /-- With the concatenated tables and the number of records `R`. -/
  lanesWin2 (c : Ctx) (Tn Tt : Nat × Nat) (Ws j a w R : Nat) : Bool :=
    bsel (bsel (Nat.beq Tt.2 (cnt c.m R)) (Nat.ble Tt.2 B32) false)
      (bsel (bsel (Nat.ble (Nat.succ j) R)
          (Nat.ble (Nat.add a w) (cnt (Nat.sub c.m 1) (Nat.succ j)))
          false)
        (bsel (Nat.ble (cnt c.m (Nat.succ j)) Tn.2)
          (lanesWin3 c (fields c.m (preS Ws (cnt c.m (Nat.succ j)) Tn.1) (cnt c.m (Nat.succ j)))
            (fields c.m (preS Ws w (Nat.shiftRight Tt.1 (Nat.mul Ws (Nat.add (cnt c.m j) a)))) w)
            j a w (mkPV c.recs (Nat.sub c.m 1)))
          false)
        false)
      false
  /-- With the fields of the states of top below `j + 1` and of the window, and the prefix
  vectors of all the prefixes. -/
  lanesWin3 (c : Ctx) (Fn Ft : Nat × List Nat × Bool) (j a w : Nat) (pv : PV) : Bool :=
    bsel Fn.2.2 (bsel Ft.2.2
      (lanesWin4 c Ft j w
        (PV.mk (winL a w pv.pos) (winL a w pv.dl) (winL a w pv.fg) (winL a w pv.cs))
        (mkVC w) (cnt c.m (Nat.succ j)) Fn) false) false
  /-- With the prefix vectors and the constants of the `w` lanes. -/
  lanesWin4 (c : Ctx) (Ft : Nat × List Nat × Bool) (j w : Nat) (pv : PV) (v : VC) (NS : Nat)
      (Fn : Nat × List Nat × Bool) : Bool :=
    lanesWin5 c Ft j w pv
      (lmapIdx (fun i cl => mkCVw v pv NS c.a1 Fn.1 Fn.2.1 (Nat.succ i) cl) 0
        (ltake (Nat.succ j) c.cells))
  /-- With the cells `1 .. j + 1`. -/
  lanesWin5 (c : Ctx) (Ft : Nat × List Nat × Bool) (j w : Nat) (pv : PV) (cvs : List CV) : Bool :=
    bsel (lall (fun cv => cv.ok) cvs)
      (topCheck.topCheck1 c pv cvs Ft.1 Ft.2.1 (rget c.recs j) w 0) false

/-- One declaration of the lanes check of a step: the top records `[lo, hi)` (`lanesRange`) or the
lanes `[a, a + w)` of the top record `j` (`lanesWin`). -/
inductive LPart where
  | rng (lo hi : Nat)
  | win (j a w : Nat)

/-- The check of a part. -/
noncomputable def LPart.check (g : Grid) (t : Nat) (Nn Nt : List Nat) : LPart → Bool
  | .rng lo hi => lanesRange g t Nn Nt lo hi
  | .win j a w => lanesWin g t Nn Nt j a w

/-- The first state of a part (`m` the memory length). -/
noncomputable def LPart.first (m : Nat) : LPart → Nat
  | .rng lo _ => cnt m lo
  | .win j a _ => Nat.add (cnt m j) a

/-- One past the last state of a part, for `R` records. -/
noncomputable def LPart.last (m R : Nat) : LPart → Nat
  | .rng _ hi => cnt m (Nat.min hi R)
  | .win j a w => Nat.add (Nat.add (cnt m j) a) w

/-- The states of the parts cover `[s, cnt m R)`: each part starts at or before the end of the
states covered so far. -/
noncomputable def lpCover (m R : Nat) : Nat → List LPart → Bool
  | s, [] => Nat.ble (cnt m R) s
  | s, p :: ps => bsel (Nat.ble (p.first m) s) (lpCover m R (Nat.max s (p.last m R)) ps) false

end Robbins.Cert.SO.L
