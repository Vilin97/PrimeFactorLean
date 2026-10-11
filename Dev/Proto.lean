import PrimeFactorLean.SIQS

namespace PrimeFactorLean.Proto
open SIQS

/-- Eight Montgomery ladders in lockstep (prototype). -/
def ladder8 (m : UInt64) (mf : Float) (bits : ByteArray) (a0 a1 a2 a3 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) :
    Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, X0_0, Z0_0, X1_0, Z1_0, X0_1, Z0_1, X1_1, Z1_1, X0_2, Z0_2, X1_2, Z1_2, X0_3, Z0_3, X1_3, Z1_3, X0_4, Z0_4, X1_4, Z1_4, X0_5, Z0_5, X1_5, Z1_5, X0_6, Z0_6, X1_6, Z1_6, X0_7, Z0_7, X1_7, Z1_7 =>
    Z0_0 ^^^ Z0_1 ^^^ Z0_2 ^^^ Z0_3 ^^^ Z0_4 ^^^ Z0_5 ^^^ Z0_6 ^^^ Z0_7
  | j + 1, X0_0, Z0_0, X1_0, Z1_0, X0_1, Z0_1, X1_1, Z1_1, X0_2, Z0_2, X1_2, Z1_2, X0_3, Z0_3, X1_3, Z1_3, X0_4, Z0_4, X1_4, Z1_4, X0_5, Z0_5, X1_5, Z1_5, X0_6, Z0_6, X1_6, Z1_6, X0_7, Z0_7, X1_7, Z1_7 =>
    let sel := -(bits.get! j).toUInt64
    let Ax0 := X0_0 ^^^ ((X0_0 ^^^ X1_0) &&& sel)
    let Az0 := Z0_0 ^^^ ((Z0_0 ^^^ Z1_0) &&& sel)
    let p0 := addM Ax0 Az0 m
    let q0 := subM Ax0 Az0 m
    let Ax1 := X0_1 ^^^ ((X0_1 ^^^ X1_1) &&& sel)
    let Az1 := Z0_1 ^^^ ((Z0_1 ^^^ Z1_1) &&& sel)
    let p1 := addM Ax1 Az1 m
    let q1 := subM Ax1 Az1 m
    let Ax2 := X0_2 ^^^ ((X0_2 ^^^ X1_2) &&& sel)
    let Az2 := Z0_2 ^^^ ((Z0_2 ^^^ Z1_2) &&& sel)
    let p2 := addM Ax2 Az2 m
    let q2 := subM Ax2 Az2 m
    let Ax3 := X0_3 ^^^ ((X0_3 ^^^ X1_3) &&& sel)
    let Az3 := Z0_3 ^^^ ((Z0_3 ^^^ Z1_3) &&& sel)
    let p3 := addM Ax3 Az3 m
    let q3 := subM Ax3 Az3 m
    let Ax4 := X0_4 ^^^ ((X0_4 ^^^ X1_4) &&& sel)
    let Az4 := Z0_4 ^^^ ((Z0_4 ^^^ Z1_4) &&& sel)
    let p4 := addM Ax4 Az4 m
    let q4 := subM Ax4 Az4 m
    let Ax5 := X0_5 ^^^ ((X0_5 ^^^ X1_5) &&& sel)
    let Az5 := Z0_5 ^^^ ((Z0_5 ^^^ Z1_5) &&& sel)
    let p5 := addM Ax5 Az5 m
    let q5 := subM Ax5 Az5 m
    let Ax6 := X0_6 ^^^ ((X0_6 ^^^ X1_6) &&& sel)
    let Az6 := Z0_6 ^^^ ((Z0_6 ^^^ Z1_6) &&& sel)
    let p6 := addM Ax6 Az6 m
    let q6 := subM Ax6 Az6 m
    let Ax7 := X0_7 ^^^ ((X0_7 ^^^ X1_7) &&& sel)
    let Az7 := Z0_7 ^^^ ((Z0_7 ^^^ Z1_7) &&& sel)
    let p7 := addM Ax7 Az7 m
    let q7 := subM Ax7 Az7 m
    let sp0 := mulmod50 p0 p0 m mf
    let sp1 := mulmod50 p1 p1 m mf
    let sp2 := mulmod50 p2 p2 m mf
    let sp3 := mulmod50 p3 p3 m mf
    let sp4 := mulmod50 p4 p4 m mf
    let sp5 := mulmod50 p5 p5 m mf
    let sp6 := mulmod50 p6 p6 m mf
    let sp7 := mulmod50 p7 p7 m mf
    let sq0 := mulmod50 q0 q0 m mf
    let sq1 := mulmod50 q1 q1 m mf
    let sq2 := mulmod50 q2 q2 m mf
    let sq3 := mulmod50 q3 q3 m mf
    let sq4 := mulmod50 q4 q4 m mf
    let sq5 := mulmod50 q5 q5 m mf
    let sq6 := mulmod50 q6 q6 m mf
    let sq7 := mulmod50 q7 q7 m mf
    let t0 := subM sp0 sq0 m
    let t1 := subM sp1 sq1 m
    let t2 := subM sp2 sq2 m
    let t3 := subM sp3 sq3 m
    let t4 := subM sp4 sq4 m
    let t5 := subM sp5 sq5 m
    let t6 := subM sp6 sq6 m
    let t7 := subM sp7 sq7 m
    let DX0 := mulmod50 sp0 sq0 m mf
    let DX1 := mulmod50 sp1 sq1 m mf
    let DX2 := mulmod50 sp2 sq2 m mf
    let DX3 := mulmod50 sp3 sq3 m mf
    let DX4 := mulmod50 sp4 sq4 m mf
    let DX5 := mulmod50 sp5 sq5 m mf
    let DX6 := mulmod50 sp6 sq6 m mf
    let DX7 := mulmod50 sp7 sq7 m mf
    let at0 := mulmod50 a0 t0 m mf
    let at1 := mulmod50 a1 t1 m mf
    let at2 := mulmod50 a2 t2 m mf
    let at3 := mulmod50 a3 t3 m mf
    let at4 := mulmod50 a4 t4 m mf
    let at5 := mulmod50 a5 t5 m mf
    let at6 := mulmod50 a6 t6 m mf
    let at7 := mulmod50 a7 t7 m mf
    let DZ0 := mulmod50 t0 (addM sq0 at0 m) m mf
    let DZ1 := mulmod50 t1 (addM sq1 at1 m) m mf
    let DZ2 := mulmod50 t2 (addM sq2 at2 m) m mf
    let DZ3 := mulmod50 t3 (addM sq3 at3 m) m mf
    let DZ4 := mulmod50 t4 (addM sq4 at4 m) m mf
    let DZ5 := mulmod50 t5 (addM sq5 at5 m) m mf
    let DZ6 := mulmod50 t6 (addM sq6 at6 m) m mf
    let DZ7 := mulmod50 t7 (addM sq7 at7 m) m mf
    let u0 := mulmod50 (subM X1_0 Z1_0 m) (addM X0_0 Z0_0 m) m mf
    let u1 := mulmod50 (subM X1_1 Z1_1 m) (addM X0_1 Z0_1 m) m mf
    let u2 := mulmod50 (subM X1_2 Z1_2 m) (addM X0_2 Z0_2 m) m mf
    let u3 := mulmod50 (subM X1_3 Z1_3 m) (addM X0_3 Z0_3 m) m mf
    let u4 := mulmod50 (subM X1_4 Z1_4 m) (addM X0_4 Z0_4 m) m mf
    let u5 := mulmod50 (subM X1_5 Z1_5 m) (addM X0_5 Z0_5 m) m mf
    let u6 := mulmod50 (subM X1_6 Z1_6 m) (addM X0_6 Z0_6 m) m mf
    let u7 := mulmod50 (subM X1_7 Z1_7 m) (addM X0_7 Z0_7 m) m mf
    let v0 := mulmod50 (addM X1_0 Z1_0 m) (subM X0_0 Z0_0 m) m mf
    let v1 := mulmod50 (addM X1_1 Z1_1 m) (subM X0_1 Z0_1 m) m mf
    let v2 := mulmod50 (addM X1_2 Z1_2 m) (subM X0_2 Z0_2 m) m mf
    let v3 := mulmod50 (addM X1_3 Z1_3 m) (subM X0_3 Z0_3 m) m mf
    let v4 := mulmod50 (addM X1_4 Z1_4 m) (subM X0_4 Z0_4 m) m mf
    let v5 := mulmod50 (addM X1_5 Z1_5 m) (subM X0_5 Z0_5 m) m mf
    let v6 := mulmod50 (addM X1_6 Z1_6 m) (subM X0_6 Z0_6 m) m mf
    let v7 := mulmod50 (addM X1_7 Z1_7 m) (subM X0_7 Z0_7 m) m mf
    let e0 := addM u0 v0 m
    let f0 := subM u0 v0 m
    let e1 := addM u1 v1 m
    let f1 := subM u1 v1 m
    let e2 := addM u2 v2 m
    let f2 := subM u2 v2 m
    let e3 := addM u3 v3 m
    let f3 := subM u3 v3 m
    let e4 := addM u4 v4 m
    let f4 := subM u4 v4 m
    let e5 := addM u5 v5 m
    let f5 := subM u5 v5 m
    let e6 := addM u6 v6 m
    let f6 := subM u6 v6 m
    let e7 := addM u7 v7 m
    let f7 := subM u7 v7 m
    let SX0 := mulmod50 e0 e0 m mf
    let SX1 := mulmod50 e1 e1 m mf
    let SX2 := mulmod50 e2 e2 m mf
    let SX3 := mulmod50 e3 e3 m mf
    let SX4 := mulmod50 e4 e4 m mf
    let SX5 := mulmod50 e5 e5 m mf
    let SX6 := mulmod50 e6 e6 m mf
    let SX7 := mulmod50 e7 e7 m mf
    let ff0 := mulmod50 f0 f0 m mf
    let ff1 := mulmod50 f1 f1 m mf
    let ff2 := mulmod50 f2 f2 m mf
    let ff3 := mulmod50 f3 f3 m mf
    let ff4 := mulmod50 f4 f4 m mf
    let ff5 := mulmod50 f5 f5 m mf
    let ff6 := mulmod50 f6 f6 m mf
    let ff7 := mulmod50 f7 f7 m mf
    let SZ0 := mulmod50 x0 ff0 m mf
    let SZ1 := mulmod50 x1 ff1 m mf
    let SZ2 := mulmod50 x2 ff2 m mf
    let SZ3 := mulmod50 x3 ff3 m mf
    let SZ4 := mulmod50 x4 ff4 m mf
    let SZ5 := mulmod50 x5 ff5 m mf
    let SZ6 := mulmod50 x6 ff6 m mf
    let SZ7 := mulmod50 x7 ff7 m mf
    ladder8 m mf bits a0 a1 a2 a3 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 x6 x7 j
      (DX0 ^^^ ((DX0 ^^^ SX0) &&& sel)) (DZ0 ^^^ ((DZ0 ^^^ SZ0) &&& sel)) (SX0 ^^^ ((SX0 ^^^ DX0) &&& sel)) (SZ0 ^^^ ((SZ0 ^^^ DZ0) &&& sel))
      (DX1 ^^^ ((DX1 ^^^ SX1) &&& sel)) (DZ1 ^^^ ((DZ1 ^^^ SZ1) &&& sel)) (SX1 ^^^ ((SX1 ^^^ DX1) &&& sel)) (SZ1 ^^^ ((SZ1 ^^^ DZ1) &&& sel))
      (DX2 ^^^ ((DX2 ^^^ SX2) &&& sel)) (DZ2 ^^^ ((DZ2 ^^^ SZ2) &&& sel)) (SX2 ^^^ ((SX2 ^^^ DX2) &&& sel)) (SZ2 ^^^ ((SZ2 ^^^ DZ2) &&& sel))
      (DX3 ^^^ ((DX3 ^^^ SX3) &&& sel)) (DZ3 ^^^ ((DZ3 ^^^ SZ3) &&& sel)) (SX3 ^^^ ((SX3 ^^^ DX3) &&& sel)) (SZ3 ^^^ ((SZ3 ^^^ DZ3) &&& sel))
      (DX4 ^^^ ((DX4 ^^^ SX4) &&& sel)) (DZ4 ^^^ ((DZ4 ^^^ SZ4) &&& sel)) (SX4 ^^^ ((SX4 ^^^ DX4) &&& sel)) (SZ4 ^^^ ((SZ4 ^^^ DZ4) &&& sel))
      (DX5 ^^^ ((DX5 ^^^ SX5) &&& sel)) (DZ5 ^^^ ((DZ5 ^^^ SZ5) &&& sel)) (SX5 ^^^ ((SX5 ^^^ DX5) &&& sel)) (SZ5 ^^^ ((SZ5 ^^^ DZ5) &&& sel))
      (DX6 ^^^ ((DX6 ^^^ SX6) &&& sel)) (DZ6 ^^^ ((DZ6 ^^^ SZ6) &&& sel)) (SX6 ^^^ ((SX6 ^^^ DX6) &&& sel)) (SZ6 ^^^ ((SZ6 ^^^ DZ6) &&& sel))
      (DX7 ^^^ ((DX7 ^^^ SX7) &&& sel)) (DZ7 ^^^ ((DZ7 ^^^ SZ7) &&& sel)) (SX7 ^^^ ((SX7 ^^^ DX7) &&& sel)) (SZ7 ^^^ ((SZ7 ^^^ DZ7) &&& sel))

/-- Time 8-lane ladders against 8 single ladders on the uecm stage-1 bits. -/
def bench (reps : Nat) : IO Unit := do
  let m : UInt64 := 1125899906842597 -- a prime below 2^50 (the arithmetic does not care)
  let mf := 1.0 / m.toFloat
  let bits := (uecmPlan.get).1
  let n := bits.size - 1
  let a : Array UInt64 := #[12345, 23456, 34567, 45678, 56789, 67890, 78901, 89012]
  let x : Array UInt64 := #[1111, 2222, 3333, 4444, 5555, 6666, 7777, 8888]
  let t0 ← IO.monoNanosNow
  let mut acc : UInt64 := 0
  for r in [0:reps] do
    let s := r.toUInt64
    acc := acc ^^^ ladder8 m mf bits a[0]! a[1]! a[2]! a[3]! a[4]! a[5]! a[6]! a[7]!
      x[0]! x[1]! x[2]! x[3]! x[4]! x[5]! x[6]! x[7]! n
      (x[0]! + s) 1 5 7 (x[1]! + s) 1 5 7 (x[2]! + s) 1 5 7 (x[3]! + s) 1 5 7
      (x[4]! + s) 1 5 7 (x[5]! + s) 1 5 7 (x[6]! + s) 1 5 7 (x[7]! + s) 1 5 7
  let t1 ← IO.monoNanosNow
  for r in [0:reps] do
    let s := r.toUInt64
    for i in [0:8] do
      let (_, z) := uecmLadder m a[i]! x[i]! mf bits n (x[i]! + s) 1 5 7
      acc := acc ^^^ z
  let t2 ← IO.monoNanosNow
  IO.println s!"{n} bits: 8-lane ladder {(t1 - t0) / reps} ns per 8 curves; single ladders {(t2 - t1) / reps} ns per 8 curves (check {acc})"

end PrimeFactorLean.Proto
