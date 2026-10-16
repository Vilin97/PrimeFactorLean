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

/-- `k` dependent Montgomery products `a ← a b`. -/
def mulChain (m : Mod10) (b : N10) : N10 → Nat → N10
  | a, 0 => a
  | a, k + 1 => mulChain m b (N10.mul m a b) k

/-- Two independent chains in one loop. -/
def mulChain2 (m : Mod10) (b : N10) : N10 → N10 → Nat → N10 × N10
  | a, c, 0 => (a, c)
  | a, c, k + 1 => mulChain2 m b (N10.mul m a b) (N10.mul m c b) k

/-- Timings (ns per product) of one and two interleaved product chains, and of
the stage-1 ladder per bit, at 80 digits on one thread. -/
def mulBench (k : Nat) : IO Unit := do
  let n := 10 ^ 79 + 5923
  let m := Mod10.ofNat n
  let a : N10 := Arith.toMont m 1234567891011
  let b : N10 := Arith.toMont m 98765432123456789
  let t0 ← IO.monoNanosNow
  let r1 ← IO.lazyPure fun _ => mulChain m b a k
  let t1 ← IO.monoNanosNow
  let r2 ← IO.lazyPure fun _ => mulChain2 m b a b k
  let t2 ← IO.monoNanosNow
  IO.println s!"one chain: {(t1 - t0).toFloat / k.toFloat} ns/product ({r1.l0}); two chains: {(t2 - t1).toFloat / (2 * k).toFloat} ns/product ({r2.1.l0 + r2.2.l0})"
  let bits := ECMF.natBits (3 ^ (k / 16))
  let a24 : N10 := Arith.toMont m 12345
  let x0 : N10 := Arith.toMont m 7
  let one : N10 := Arith.toMont m 1
  let P : ECMF.Pt N10 := ⟨x0, one⟩
  let t3 ← IO.monoNanosNow
  let Q ← IO.lazyPure fun _ => ECMF.ladderLoop m a24 x0 bits P (ECMF.dbl m a24 P) (bits.size - 1)
  let t4 ← IO.monoNanosNow
  IO.println s!"ladder: {bits.size} bits, {(t4 - t3).toFloat / bits.size.toFloat} ns/bit ({Q.x.l0})"

/-- Fast ECM, one thread: milliseconds per curve with stage 2 (`B2 = 100 B1`)
and with stage 1 only. -/
def ecmCurveBench (n b1 curves : Nat) : IO Unit := do
  let full := ECMF.mkFast b1 (100 * b1)
  let one := ECMF.mkFast b1 b1
  let _ ← IO.lazyPure fun _ => full.plan.isPrime.size + one.bits.size
  let t0 ← IO.monoNanosNow
  let r1 ← IO.lazyPure fun _ => (List.range curves).filterMap fun c =>
    (ECMF.runCurve n full (1000 + c)).map (·.val)
  let t1 ← IO.monoNanosNow
  let r2 ← IO.lazyPure fun _ => (List.range curves).filterMap fun c =>
    (ECMF.runCurve n one (1000 + c)).map (·.val)
  let t2 ← IO.monoNanosNow
  IO.println s!"B1={b1}: {(t1 - t0).toFloat / 1.0e6 / curves.toFloat} ms/curve (found {r1.length}), stage 1 only {(t2 - t1).toFloat / 1.0e6 / curves.toFloat} ms/curve (found {r2.length})"

/-- Stage 1 per bit at 80 digits: the fused generated ladder against the generic
`ladderLoop` (same curve, same bits). -/
def ladderCompare (b1 : Nat) : IO Unit := do
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
  let r2 ← IO.lazyPure fun _ => ECMF.ladderLoop m a24 x0 bits P D (bits.size - 1)
  let t1 ← IO.monoNanosNow
  IO.println s!"{bits.size} bits: ladder {(t1 - t0).toFloat / bits.size.toFloat} ns/bit ({r2.x.l0})"

/-- Wall time of `curves` curves on `threads` tasks (one batch per round), with
`B2 = b2` (`b2 = b1`: stage 1 only), in one process. -/
def ecmPar (n b1 b2 curves threads : Nat) : IO Unit := do
  let fast := ECMF.mkFast b1 b2
  let _ ← IO.lazyPure fun _ => fast.plan.isPrime.size + fast.bits.size + fast.sched.hits.size
  let t0 ← IO.monoNanosNow
  let mut found := 0
  let mut done := 0
  while done < curves do
    let tasks := (List.range threads).map fun t =>
      Task.spawn fun _ => ECMF.runCurve n fast (100 + done + t)
    for task in tasks do
      if (task.get).isSome then found := found + 1
    done := done + threads
  let t1 ← IO.monoNanosNow
  IO.println s!"B1={b1} B2={b2} {done} curves on {threads} threads: {(t1 - t0).toFloat / 1.0e6} ms, {(t1 - t0).toFloat / 1.0e6 / (done / threads).toFloat} ms per round ({found} found)"

/-- Time to build the stage data of `B1 = b1`, `B2 = 100 b1`. -/
def planTime (b1 : Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let plan ← IO.lazyPure fun _ => ECMM.mkPlan b1 (100 * b1)
  let t1 ← IO.monoNanosNow
  let sched ← IO.lazyPure fun _ => ECMF.schedule plan
  let t2 ← IO.monoNanosNow
  let bits ← IO.lazyPure fun _ => ECMF.natBits (plan.powers.foldl (· * ·) 1)
  let t3 ← IO.monoNanosNow
  IO.println s!"B1={b1}: mkPlan {(t1 - t0) / 1000000} ms ({plan.isPrime.size}), schedule {(t2 - t1) / 1000000} ms ({sched.hits.size}), bits {(t3 - t2) / 1000000} ms ({bits.size})"

/-- `k` dependent Montgomery squares. -/
def sqrChain (m : Mod10) : N10 → Nat → N10
  | a, 0 => a
  | a, k + 1 => sqrChain m (N10.sqr m a) k

/-- `k` dependent additions and subtractions. -/
def addChain (m : Mod10) (b : N10) : N10 → Nat → N10
  | a, 0 => a
  | a, k + 1 => addChain m b (N10.sub m (N10.add m a b) b |> fun x => N10.add m x b) k

/-- Per-operation costs at 80 digits (one thread): square, add+sub+add chain. -/
def opBench (k : Nat) : IO Unit := do
  let n := 17100104831195064426243855290661269581152208979016832912601645679249190067150771
  let m := Mod10.ofNat n
  let a : N10 := Arith.toMont m 1234567891011
  let b : N10 := Arith.toMont m 98765432123456789
  let t0 ← IO.monoNanosNow
  let r1 ← IO.lazyPure fun _ => mulChain m b a k
  let t1 ← IO.monoNanosNow
  let r2 ← IO.lazyPure fun _ => sqrChain m a k
  let t2 ← IO.monoNanosNow
  let r3 ← IO.lazyPure fun _ => addChain m b a k
  let t3 ← IO.monoNanosNow
  IO.println s!"mul {(t1 - t0).toFloat / k.toFloat} ns, sqr {(t2 - t1).toFloat / k.toFloat} ns, add/sub {(t3 - t2).toFloat / (3 * k).toFloat} ns ({r1.l0 + r2.l0 + r3.l0})"

/-- PRAC stage 1 against the binary ladder on the same curve (projective `x`
compared), the number of primes without a chain (opcode 14), and both times. -/
def pracCheck (b1 : Nat) : IO Unit := do
  let n := 17100104831195064426243855290661269581152208979016832912601645679249190067150771
  let m := Mod10.ofNat n
  let t0 ← IO.monoNanosNow
  let fast ← IO.lazyPure fun _ => ECMF.mkFast b1 b1
  let t1 ← IO.monoNanosNow
  let prog := fast.prac
  let fallbacks := (List.range prog.size).foldl (fun acc i => if prog.get! i == 14 then acc + 1 else acc) 0
  let mut bad := 0
  let mut tl := 0
  let mut tp := 0
  for c in [0:4] do
    let a24 : N10 := Arith.toMont m (12345 + 977 * c)
    let x0 : N10 := Arith.toMont m (7 + c)
    let one : N10 := Arith.toMont m 1
    let P : ECMF.Pt N10 := ⟨x0, one⟩
    let s0 ← IO.monoNanosNow
    let Q1 ← IO.lazyPure fun _ => ECMF.ladderLoop m a24 x0 fast.bits P (ECMF.dbl m a24 P) (fast.bits.size - 1)
    let s1 ← IO.monoNanosNow
    let Q2 ← IO.lazyPure fun _ => ECMF.pracRun m a24 prog (prog.size + 1) 0 P P P
    let s2 ← IO.monoNanosNow
    tl := tl + (s1 - s0)
    tp := tp + (s2 - s1)
    if Arith.fromMont m (Arith.mul m Q1.x Q2.z) != Arith.fromMont m (Arith.mul m Q2.x Q1.z) then bad := bad + 1
  IO.println s!"B1={b1}: program {prog.size} bytes ({(t1 - t0) / 1000000} ms), {fallbacks} primes without a chain; 4 curves: ladder {tl / 4000000} ms, PRAC {tp / 4000000} ms per curve, {bad} mismatches"
