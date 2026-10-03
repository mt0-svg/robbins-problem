/-!
# Packed lanes: the kernel operations

Natural numbers in lanes of `W` bits, packed in one natural number (lane `l` at bits
`W l .. W l + W - 1`); evaluated by `decide +kernel` at `W = 128`. The specification of every
operation is the pack of the lanewise operation (Robbins/Lanes/Pack.lean defines `pack` and
proves the lanewise lemmas, Robbins/Lanes/OpsSound.lean the specifications).

Written for the kernel: raw `Nat` operations (no type classes), branches by `Bool.rec`, loops
by `Nat.rec` or `List.rec`, no well-founded recursion. Mathlib-free.

Sources: `lamportMul` (L. Lamport, "Multiple byte processing with full-word instructions",
CACM 18(8), 1975) and `lamD`; `frc2`, the bit-serial product `mulBS`, the restoring division
`divBS` and the quotient check `chkP`, generic in `W`.
-/

namespace Robbins.Lanes

/-- `if b then x else y`, by the recursor. -/
noncomputable def cnd {α : Type} (b : Bool) (x y : α) : α :=
  @Bool.rec (fun _ => α) y x b

/-- Force `a` and `b` (a test against `0` each), then continue with them. -/
noncomputable def frc2 {α : Type} (a b : Nat) (k : Nat → Nat → α) : α :=
  cnd (Nat.beq a 0) (cnd (Nat.beq b 0) (k 0 0) (k 0 b)) (cnd (Nat.beq b 0) (k a 0) (k a b))

/-! ## Constants -/

/-- `2 ^ W - 1`, the mask of one lane. -/
def lmask (W : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 W) 1

/-- `1` in each of the `L` lanes: `(2 ^ (W L) - 1) / (2 ^ W - 1)`. -/
def ones (W L : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul W L)) 1) (Nat.sub (Nat.shiftLeft 1 W) 1)

/-- The guard bits: `2 ^ (W - 1)` in each of the `L` lanes. -/
def guard (W L : Nat) : Nat := Nat.shiftLeft (ones W L) (Nat.sub W 1)

/-- `c` in each of the `L` lanes. -/
def bcast (W L c : Nat) : Nat := Nat.mul c (ones W L)

/-! ## Lanes, prefixes, concatenation -/

/-- Lane `l` of `P`: `P / 2 ^ (W l) % 2 ^ W`. -/
def lane (W P l : Nat) : Nat := Nat.land (Nat.shiftRight P (Nat.mul W l)) (lmask W)

/-- The first `n` lanes of `P`. -/
def pre (W n P : Nat) : Nat := Nat.land P (Nat.sub (Nat.shiftLeft 1 (Nat.mul W n)) 1)

/-- `P` without its first `a` lanes. -/
def drp (W a P : Nat) : Nat := Nat.shiftRight P (Nat.mul W a)

/-- The `a` lanes of `P` followed by the lanes of `Q`. -/
def app (W a P Q : Nat) : Nat := Nat.add P (Nat.shiftLeft Q (Nat.mul W a))

/-- The gather: lane `j` of the result is lane `idx[j]` of `src`. -/
noncomputable def gath (W src : Nat) (idx : List Nat) : Nat :=
  @List.rec Nat (fun _ => Nat) 0
    (fun i _ r => Nat.add (lane W src i) (Nat.shiftLeft r W)) idx

/-! ## Compare, masks, select -/

/-- The guard-bit compare (`G` the guard bits): lane `l` is `2 ^ (W - 1)` if `b_l ≤ a_l`, else
`0` (lanes below `2 ^ (W - 1)`). -/
def geMask (G A B : Nat) : Nat := Nat.land (Nat.sub (Nat.add A G) B) G

/-- `b_l ≤ a_l` in every lane. -/
def allGe (G A B : Nat) : Bool := Nat.beq (geMask G A B) G

/-- Guard bits to lane units: `2 ^ (W - 1)` to `1`. -/
def ind (W P : Nat) : Nat := Nat.shiftRight P (Nat.sub W 1)

/-- Guard bits to full lanes: `2 ^ (W - 1)` to `2 ^ W - 1`. -/
def full (W P : Nat) : Nat := Nat.sub (Nat.add P P) (Nat.shiftRight P (Nat.sub W 1))

/-- The select: lanes of `A` where the full-lane mask `M` is set, lanes of `B` elsewhere. -/
def sel (M A B : Nat) : Nat := Nat.xor B (Nat.land (Nat.xor A B) M)

/-- The lanewise minimum. -/
def lmin (W G A B : Nat) : Nat := sel (full W (geMask G A B)) B A

/-- The lanewise maximum. -/
def lmax (W G A B : Nat) : Nat := sel (full W (geMask G A B)) A B

/-- The lanewise zero test: lane `l` is `0` if `t_l = 0`, else `2 ^ (W - 1)` (lanes below
`2 ^ (W - 1)`; `G` the guard bits, `O` the ones). -/
def nzMask (G O T : Nat) : Nat := Nat.land (Nat.add T (Nat.sub G O)) G

/-- The lanewise shift right by `s ≤ W`: `Ms` holds `2 ^ (W - s) - 1` in every lane. -/
def shrL (Ms s A : Nat) : Nat := Nat.land (Nat.shiftRight A s) Ms

/-! ## Products -/

/-- The lanewise product of `A` by the `k`-bit multipliers `B` (Lamport's shift and add): step `j`
adds `(A 2 ^ j) &&& (bit j of B, spread to full lanes)`; `O` the ones, `F = 2 ^ W - 1`. -/
noncomputable def lamportMul (k : Nat) (A B O F : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat × Nat) (0, 0)
    (fun _ p => (Nat.add p.1 (Nat.land (Nat.shiftLeft A p.2)
      (Nat.mul (Nat.land (Nat.shiftRight B p.2) O) F)), Nat.add p.2 1)) k).1

/-- The same by doublings: at step `j` the state is `(sum, A 2 ^ j, O 2 ^ j, 2 ^ (W - j) - 1)`
and the term `(A 2 ^ j) &&& ((B &&& O 2 ^ j) (2 ^ (W - j) - 1))`. -/
noncomputable def lamD (K : Nat) (O A B F : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat × Nat × Nat × Nat) (0, A, O, F)
    (fun _ p => (Nat.add p.1 (Nat.land p.2.1 (Nat.mul (Nat.land B p.2.2.1) p.2.2.2)),
      Nat.add p.2.1 p.2.1, Nat.add p.2.2.1 p.2.2.1, Nat.shiftRight p.2.2.2 1)) K).1

/-- One bit of the bit-serial product `b q`: the lanes with bit `k` of `q` set get `b 2 ^ k`. -/
noncomputable def mulBit (W L1 B Qd k P : Nat) (ih : Nat → Nat) : Nat :=
  mulBit2 W B k P ih (Nat.land (Nat.shiftRight Qd k) L1)
where
  /-- With the bit `k` of every lane. -/
  mulBit2 (W B k P : Nat) (ih : Nat → Nat) (bt : Nat) : Nat :=
    frc2 (Nat.add P (Nat.land (Nat.shiftLeft B k) (Nat.sub (Nat.shiftLeft bt W) bt))) 1
      (fun P _ => ih P)

/-- The lanewise product of `B` by the `Q`-bit multipliers `Qd`, bits `Q - 1` down to `0`. -/
noncomputable def mulBS (W Q L1 B Qd : Nat) : Nat :=
  @Nat.rec (fun _ => Nat → Nat) (fun P => P) (fun k ih P => mulBit W L1 B Qd k P ih) Q 0

/-! ## Divisions -/

/-- One bit of the restoring division: `T = b 2 ^ k`, the lanes with `R ≥ T` lose `T` and get
the bit `k` of the quotient. -/
noncomputable def divBit {α : Type} (W G B k R Qa : Nat) (ih : Nat → Nat → α) : α :=
  divBit2 W k R Qa ih (Nat.shiftLeft B k) G
where
  /-- With `T`. -/
  divBit2 {α : Type} (W k R Qa : Nat) (ih : Nat → Nat → α) (T G : Nat) : α :=
    divBit3 W k R Qa ih T (Nat.land (Nat.sub (Nat.add R G) T) G)
  /-- With the guard bits of `R ≥ T`. -/
  divBit3 {α : Type} (W k R Qa : Nat) (ih : Nat → Nat → α) (T ge : Nat) : α :=
    frc2 (Nat.sub R (Nat.land T (full W ge)))
      (Nat.add Qa (Nat.shiftRight ge (Nat.sub (Nat.sub W 1) k))) ih

/-- The quotient lanes `a / b` of `Q` bits, by restoring division, bits `Q - 1` down to `0`. -/
noncomputable def divBS (W Q G A B : Nat) : Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat) (fun _ Qa => Qa) (fun k ih R Qa => divBit W G B k R Qa ih)
    Q A 0

/-- The restoring division with its final remainder: `(quotient, remainder)` lanes. -/
noncomputable def divQR (W Q G A B : Nat) : Nat × Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat × Nat) (fun R Qa => (Qa, R))
    (fun k ih R Qa => divBit W G B k R Qa ih) Q A 0

/-- `p ≤ a < p + b` in every lane (`P = b q` for a quotient witness `q`): `G` the guard bits,
`L1` the ones. -/
noncomputable def chkP (G L1 A B P : Nat) : Bool :=
  cnd (Nat.beq (Nat.land (Nat.sub (Nat.add A G) P) G) G)
    (Nat.beq (Nat.land (Nat.sub (Nat.add (Nat.add P B) G) (Nat.add A L1)) G) G) false

/-- The quotient witness check: the `k`-bit lanes `Qd` are `a / b` lane by lane, checked as
`b q ≤ a < b q + b` with the product `b q` by the bit-serial `mulBS` (faster in the kernel than
`lamportMul`). -/
noncomputable def chkQ (W k G L1 A B Qd : Nat) : Bool :=
  chkP G L1 A B (mulBS W k L1 B Qd)

/-- The multiply and shift division by a constant `d` (Granlund and Montgomery):
`(x ((2 ^ s + d - 1) / d)) >>> s` in every lane, `Ms` the lane mask of `shrL`. -/
def divC (Ms s M A : Nat) : Nat := shrL Ms s (Nat.mul M A)

/-! ## Fields of the claimed tables -/

/-- The fields of the states of one literal (states of `Ws` bits under a leading `1`, at most
16, as `decLit` of Robbins/Cert/SO/EvalK.lean reads them): `(Σ_i fld (s_i) 2 ^ (W i), count)`,
with `fld s = s / 2 ^ fo % 2 ^ F` (`MWs = 2 ^ Ws - 1`, `MF = 2 ^ F - 1`). -/
noncomputable def litChunk (W Ws MWs fo MF x : Nat) : Nat × Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat → Nat × Nat) (fun _ c i => (c, i))
    (fun _ ih x c i => cnd (Nat.ble x 1) (c, i)
      (ih (Nat.shiftRight x Ws)
        (Nat.add c (Nat.shiftLeft (Nat.land (Nat.shiftRight (Nat.land x MWs) fo) MF) (Nat.mul W i)))
        (Nat.succ i)))
    16 x 0 0

/-- The fields of all states of the literals, one lane each, and their count. -/
noncomputable def fieldPackP (W Ws MWs fo MF : Nat) (lits : List Nat) : Nat × Nat :=
  @List.rec Nat (fun _ => Nat × Nat) (0, 0)
    (fun x _ r => fieldCons W (litChunk W Ws MWs fo MF x) r) lits
where
  /-- A chunk before the rest. -/
  fieldCons (W : Nat) (c r : Nat × Nat) : Nat × Nat :=
    (Nat.add c.1 (Nat.shiftLeft r.1 (Nat.mul W c.2)), Nat.add c.2 r.2)

/-- One `W`-bit lane per state of the literals `lits`: the `F`-bit field at bit `fo` of the
state. -/
noncomputable def fieldPack (W Ws fo F : Nat) (lits : List Nat) : Nat :=
  (fieldPackP W Ws (lmask Ws) fo (lmask F) lits).1

end Robbins.Lanes
