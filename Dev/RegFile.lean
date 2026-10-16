import PrimeFactorLean.ECMFast

/-! Prototype: the ECM ladder on a register file (a `FloatArray` of 28-bit limbs,
exact as doubles) with one shared non-inlined function per operation, against
the fused generated ladder. -/

open PrimeFactorLean PrimeFactorLean.Mont

namespace PrimeFactorLean.RegFile

@[inline] def ld (rf : FloatArray) (r : Nat) : N10 :=
  let b := 10 * r
  ⟨(rf.get! (b + 0)).toUInt64, (rf.get! (b + 1)).toUInt64, (rf.get! (b + 2)).toUInt64, (rf.get! (b + 3)).toUInt64, (rf.get! (b + 4)).toUInt64, (rf.get! (b + 5)).toUInt64, (rf.get! (b + 6)).toUInt64, (rf.get! (b + 7)).toUInt64, (rf.get! (b + 8)).toUInt64, (rf.get! (b + 9)).toUInt64⟩

@[inline] def st (rf : FloatArray) (r : Nat) (x : N10) : FloatArray :=
  let b := 10 * r
  let rf := rf.set! (b + 0) x.l0.toFloat
  let rf := rf.set! (b + 1) x.l1.toFloat
  let rf := rf.set! (b + 2) x.l2.toFloat
  let rf := rf.set! (b + 3) x.l3.toFloat
  let rf := rf.set! (b + 4) x.l4.toFloat
  let rf := rf.set! (b + 5) x.l5.toFloat
  let rf := rf.set! (b + 6) x.l6.toFloat
  let rf := rf.set! (b + 7) x.l7.toFloat
  let rf := rf.set! (b + 8) x.l8.toFloat
  let rf := rf.set! (b + 9) x.l9.toFloat
  rf

@[noinline] def mulR (m : Mod10) (rf : FloatArray) (d a b : Nat) : FloatArray :=
  st rf d (N10.mul m (ld rf a) (ld rf b))

@[noinline] def addR (m : Mod10) (rf : FloatArray) (d a b : Nat) : FloatArray :=
  st rf d (N10.add m (ld rf a) (ld rf b))

@[noinline] def subR (m : Mod10) (rf : FloatArray) (d a b : Nat) : FloatArray :=
  st rf d (N10.sub m (ld rf a) (ld rf b))

@[noinline] def sqrR (m : Mod10) (rf : FloatArray) (d a : Nat) : FloatArray :=
  st rf d (N10.sqr m (ld rf a))

/-- One ladder step: pairs `(0, 1)` and `(2, 3)`; the pair `bit` is doubled, the
sum goes into the other pair (the differential addition is symmetric in its two
inputs). `a24` in register 4, `xP` in 5, temporaries 6-11. -/
def stepR (m : Mod10) (rf : FloatArray) (bit : Bool) : FloatArray :=
  let dx := if bit then 2 else 0
  let ox := 2 - dx
  let rf := subR m rf 6 2 3
  let rf := addR m rf 7 0 1
  let rf := mulR m rf 8 6 7
  let rf := addR m rf 6 2 3
  let rf := subR m rf 7 0 1
  let rf := mulR m rf 9 6 7
  let rf := addR m rf 6 dx (dx + 1)
  let rf := sqrR m rf 6 6
  let rf := subR m rf 7 dx (dx + 1)
  let rf := sqrR m rf 7 7
  let rf := subR m rf 10 6 7
  let rf := mulR m rf dx 6 7
  let rf := mulR m rf 11 4 10
  let rf := addR m rf 11 7 11
  let rf := mulR m rf (dx + 1) 10 11
  let rf := addR m rf 6 8 9
  let rf := sqrR m rf ox 6
  let rf := subR m rf 7 8 9
  let rf := sqrR m rf 7 7
  mulR m rf (ox + 1) 5 7

/-- The ladder over `bits[i-1], …, bits[0]`. -/
def ladderR (m : Mod10) (bits : ByteArray) : Nat → FloatArray → FloatArray
  | 0, rf => rf
  | i + 1, rf => ladderR m bits i (stepR m rf (bits.get! i == 1))

/-- Stage 1 per bit at 80 digits: register-file ladder against the fused one. -/
def regBench (b1 : Nat) : IO Unit := do
  let n := 17100104831195064426243855290661269581152208979016832912601645679249190067150771
  let m := Mod10.ofNat n
  let fast := ECMF.mkFast b1 b1
  let bits := fast.bits
  let a24 : N10 := Arith.toMont m 12345
  let x0 : N10 := Arith.toMont m 7
  let one : N10 := Arith.toMont m 1
  let P : ECMF.Pt N10 := ⟨x0, one⟩
  let D := ECMF.dbl m a24 P
  let t0 ← IO.monoNanosNow
  let r1 ← IO.lazyPure fun _ => let r := ECMF.ladderLoop m a24 x0 bits P D (bits.size - 1); (r.x, r.z)
  let t1 ← IO.monoNanosNow
  let rf0 : FloatArray := ⟨Array.replicate 120 0.0⟩
  let rf0 := st rf0 0 P.x
  let rf0 := st rf0 1 P.z
  let rf0 := st rf0 2 D.x
  let rf0 := st rf0 3 D.z
  let rf0 := st rf0 4 a24
  let rf0 := st rf0 5 x0
  let t2 ← IO.monoNanosNow
  let rf ← IO.lazyPure fun _ => ladderR m bits (bits.size - 1) rf0
  let t3 ← IO.monoNanosNow
  let X := ld rf 0
  let Z := ld rf 1
  let same := Arith.fromMont m (Arith.mul m r1.1 Z) == Arith.fromMont m (Arith.mul m X r1.2)
  IO.println s!"{bits.size} bits: fused {(t1 - t0).toFloat / bits.size.toFloat} ns/bit, register file {(t3 - t2).toFloat / bits.size.toFloat} ns/bit, same point {same}"

end PrimeFactorLean.RegFile

namespace PrimeFactorLean.RegFile

/-- `N10` arithmetic with multiplication and squaring as shared (non-inlined)
functions: small code, one result object per operation. -/
structure NI where
  v : N10
  deriving Inhabited

@[noinline] def mulNI (m : Mod10) (a b : NI) : NI := ⟨N10.mul m a.v b.v⟩
@[noinline] def sqrNI (m : Mod10) (a : NI) : NI := ⟨N10.sqr m a.v⟩
@[noinline] def addNI (m : Mod10) (a b : NI) : NI := ⟨N10.add m a.v b.v⟩
@[noinline] def subNI (m : Mod10) (a b : NI) : NI := ⟨N10.sub m a.v b.v⟩

instance : Arith NI Mod10 where
  mul := mulNI
  sqr := sqrNI
  add := addNI
  sub := subNI
  modulus := Mod10.n
  ofLimbs _ x := ⟨N10.ofLimbs x⟩
  limbNat a := N10.limbNat a.v
  isZero a := N10.isZero a.v
  limbs := 10

def niBench (b1 : Nat) : IO Unit := do
  let n := 17100104831195064426243855290661269581152208979016832912601645679249190067150771
  let m := Mod10.ofNat n
  let fast := ECMF.mkFast b1 b1
  let bits := fast.bits
  let a24 : NI := Arith.toMont m 12345
  let x0 : NI := Arith.toMont m 7
  let one : NI := Arith.toMont m 1
  let P : ECMF.Pt NI := ⟨x0, one⟩
  let D := ECMF.dbl m a24 P
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => ECMF.ladderLoop m a24 x0 bits P D (bits.size - 1)
  let t1 ← IO.monoNanosNow
  IO.println s!"{bits.size} bits: non-inlined ops {(t1 - t0).toFloat / bits.size.toFloat} ns/bit ({r.x.v.l0})"

end PrimeFactorLean.RegFile

namespace PrimeFactorLean.RegFile

/-- Multiplication and squaring shared (non-inlined), addition and subtraction inlined. -/
@[noinline] def mulN (m : Mod10) (a b : N10) : N10 := N10.mul m a b
@[noinline] def sqrN (m : Mod10) (a : N10) : N10 := N10.sqr m a

structure N2I where
  v : N10
  deriving Inhabited

instance : Arith N2I Mod10 where
  mul m a b := ⟨mulN m a.v b.v⟩
  sqr m a := ⟨sqrN m a.v⟩
  add m a b := ⟨N10.add m a.v b.v⟩
  sub m a b := ⟨N10.sub m a.v b.v⟩
  modulus := Mod10.n
  ofLimbs _ x := ⟨N10.ofLimbs x⟩
  limbNat a := N10.limbNat a.v
  isZero a := N10.isZero a.v
  limbs := 10

def ni2Bench (b1 : Nat) : IO Unit := do
  let n := 17100104831195064426243855290661269581152208979016832912601645679249190067150771
  let m := Mod10.ofNat n
  let fast := ECMF.mkFast b1 b1
  let bits := fast.bits
  let a24 : N2I := Arith.toMont m 12345
  let x0 : N2I := Arith.toMont m 7
  let one : N2I := Arith.toMont m 1
  let P : ECMF.Pt N2I := ⟨x0, one⟩
  let D := ECMF.dbl m a24 P
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => ECMF.ladderLoop m a24 x0 bits P D (bits.size - 1)
  let t1 ← IO.monoNanosNow
  IO.println s!"{bits.size} bits: shared mul/sqr, inline add/sub {(t1 - t0).toFloat / bits.size.toFloat} ns/bit ({r.x.v.l0})"

end PrimeFactorLean.RegFile
