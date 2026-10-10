import PrimeFactorLean.ECMFast

/-! Tests and timings for the fixed-width Montgomery arithmetic and the fast ECM. -/

open PrimeFactorLean PrimeFactorLean.Mont

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Random checks of mul/sqr/add/sub against `Nat` arithmetic. -/
def checkWidth {α μ : Type} [Arith α μ] (mk : Nat → μ) (bits : Nat) (trials : Nat) : Nat := Id.run do
  let mut s := bits * 7919 + 17
  let mut bad := 0
  for _ in [0:trials] do
    s := lcg s
    let mut n := 0
    for _ in [0:(bits + 63) / 64] do
      s := lcg s
      n := (n <<< 64) + s
    n := n % 2 ^ bits ||| 2 ^ (bits - 1) ||| 1
    let m := mk n
    s := lcg s
    let a := (s * 1234567 + s / 3 * 2 ^ 40 + s * s) % n
    s := lcg s
    let b := (s * 7654321 + s * s * s) % n
    let A : α := Arith.toMont m a
    let B : α := Arith.toMont m b
    if Arith.fromMont m (Arith.mul m A B) != a * b % n then bad := bad + 1
    if Arith.fromMont m (Arith.sqr m A) != a * a % n then bad := bad + 1
    if Arith.fromMont m (Arith.add m A B) != (a + b) % n then bad := bad + 1
    if Arith.fromMont m (Arith.sub m A B) != (a + n - b) % n then bad := bad + 1
    -- edge values
    let C : α := Arith.toMont m (n - 1)
    if Arith.fromMont m (Arith.mul m C C) != 1 % n then bad := bad + 1
    if Arith.fromMont m (Arith.add m C C) != (2 * (n - 1)) % n then bad := bad + 1
  return bad

def montTestMain : IO Unit := do
  let mut total := 0
  for (L, bad) in [
      (1, checkWidth (α := N1) Mod1.ofNat 27 200), (2, checkWidth (α := N2) Mod2.ofNat 55 200),
      (3, checkWidth (α := N3) Mod3.ofNat 84 200), (4, checkWidth (α := N4) Mod4.ofNat 112 200),
      (5, checkWidth (α := N5) Mod5.ofNat 139 200), (6, checkWidth (α := N6) Mod6.ofNat 168 200),
      (7, checkWidth (α := N7) Mod7.ofNat 190 200), (8, checkWidth (α := N8) Mod8.ofNat 224 200),
      (9, checkWidth (α := N9) Mod9.ofNat 250 200), (10, checkWidth (α := N10) Mod10.ofNat 280 200),
      (11, checkWidth (α := N11) Mod11.ofNat 300 200), (12, checkWidth (α := N12) Mod12.ofNat 336 200)] do
    IO.println s!"L={L}: {bad} mismatches"
    total := total + bad
  -- also the widths below their maximum
  let b2 := checkWidth (α := N3) Mod3.ofNat 60 200
  IO.println s!"L=3 with 60-bit moduli: {b2} mismatches"
  IO.println (if total + b2 == 0 then "MONT OK" else "MONT FAILED")

def ecmBench (n b1 curves threads : Nat) : IO Unit := do
  let fast := ECMF.mkFast b1 (100 * b1)
  let plan := fast.plan
  let t0 ← IO.monoNanosNow
  let r1 ← IO.lazyPure fun _ => (List.range curves).filterMap fun c =>
    (ECMF.runCurve n fast (11 + c)).map (·.val)
  let t1 ← IO.monoNanosNow
  let r2 ← IO.lazyPure fun _ => (List.range curves).filterMap fun c =>
    (ECMM.runCurve n plan (11 + c)).map (·.val)
  let t2 ← IO.monoNanosNow
  IO.println s!"B1={b1} curves={curves}: fast {(t1 - t0).toFloat / 1.0e6 / curves.toFloat} ms/curve found {r1}; nat {(t2 - t1).toFloat / 1.0e6 / curves.toFloat} ms/curve found {r2}"
  let t3 ← IO.monoNanosNow
  let r3 ← IO.lazyPure fun _ => (ECMF.split n { b1 := b1, curves := curves * 4, threads := threads }).map (·.val)
  let t4 ← IO.monoNanosNow
  IO.println s!"parallel split {curves * 4} curves: {(t4 - t3).toFloat / 1.0e6} ms -> {r3}"
