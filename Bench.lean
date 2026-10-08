import PrimeFactorLean

/-!
Reproducible in-process optimization benchmark. Algorithms receive only each
input integer. Every returned divisor is independently validated before its
timing is accepted. Calls go through a non-inlined wrapper, consume runtime
loop-indexed inputs, and contribute to the reported checksum.
-/

open PrimeFactorLean Lean

namespace Benchmark

structure Row where
  suite : String
  algorithm : String
  inputs : Array Nat
  rounds : Nat
  returnedDivisors : Nat
  checksum : Nat
  roundNs : Array Nat
  outcomes : Array Lean.Json
  deriving Inhabited

private def Row.totalNs (row : Row) : Nat := row.roundNs.foldl (· + ·) 0

private def Row.medianRoundNs (row : Row) : Nat :=
  let sorted := row.roundNs.toList.mergeSort (· ≤ ·)
  sorted[row.rounds / 2]!

private def Row.json (row : Row) : Lean.Json := Lean.Json.mkObj [
  ("suite", toJson row.suite),
  ("algorithm", toJson row.algorithm),
  ("inputs", toJson (row.inputs.map toString)),
  ("rounds", toJson row.rounds),
  ("calls", toJson (row.rounds * row.inputs.size)),
  ("returnedDivisors", toJson row.returnedDivisors),
  ("allReturnedDivisorsValidated", toJson true),
  ("totalNs", toJson row.totalNs),
  ("medianRoundNs", toJson row.medianRoundNs),
  ("meanNsPerCall", toJson (row.totalNs / (row.rounds * row.inputs.size))),
  ("roundNs", toJson row.roundNs),
  ("checksum", toJson (toString row.checksum)),
  ("outcomes", Lean.Json.arr row.outcomes)]

private def Row.csv (row : Row) : String :=
  String.intercalate "," [row.suite, row.algorithm,
    toString (row.rounds * row.inputs.size), toString row.returnedDivisors,
    toString row.totalNs, toString row.medianRoundNs,
    toString (row.totalNs / (row.rounds * row.inputs.size)), toString row.checksum]

/-- Keep every benchmark iteration as an actual fresh search call. -/
@[noinline] private def invoke (search : Nat → Option Nat) (n : Nat) : IO (Option Nat) :=
  IO.lazyPure fun _ => search n

private def measure (suite algorithm : String) (inputs : Array Nat) (rounds : Nat)
    (search : Nat → Option Nat) (roundOffset : Nat := 0)
    (valid : Nat → Nat → Bool := Search.properFactor) : IO Row := do
  let mut returnedDivisors := 0
  let mut checksum := 0
  let mut roundNs := #[]
  let mut outcomes := #[]
  for r in [:rounds] do
    let started ← IO.monoNanosNow
    for i in [:inputs.size] do
      let n := inputs[(i + r + roundOffset) % inputs.size]!
      let result ← invoke search n
      match result with
      | none =>
          checksum := checksum + n
          if r + roundOffset == 0 then
            outcomes := outcomes.push (Lean.Json.mkObj [
              ("n", toJson (toString n)), ("divisor", Lean.Json.null)])
      | some d =>
          unless valid n d do
            throw (IO.userError ("Invalid divisor from " ++ algorithm ++
              " for " ++ toString n ++ ": " ++ toString d))
          returnedDivisors := returnedDivisors + 1
          checksum := checksum + d
          if r + roundOffset == 0 then
            outcomes := outcomes.push (Lean.Json.mkObj [
              ("n", toJson (toString n)), ("divisor", toJson (toString d))])
    let stopped ← IO.monoNanosNow
    roundNs := roundNs.push (stopped - started)
  let row : Row := ⟨suite, algorithm, inputs, rounds,
    returnedDivisors, checksum, roundNs, outcomes⟩
  return row

/-- Mixed close and unequal semiprimes, from roughly 40 through 60 bits. -/
private def semiprimes : Array Nat := #[
  1000036000099, 3000026000051, 1000070001221,
  100001880003211, 10000004400000259, 1000000016000000063]

/-- Prime inputs reveal the reference n-bound versus sqrt-bound difference. -/
private def trialPrimes : Array Nat := #[10007, 100003, 104729, 1000003, 1000033]

private def trialComposites : Array Nat := #[100160063, 10002200057, 1000036000099]

private def ecmInputs : Array Nat := #[10403, 100160063, 10002200057, 1000036000099]

/-- Cunningham numbers with 10- to 20-digit factors (2^101-1, 2^103-1, 2^109-1, 2^149-1). -/
private def ecmLarge : Array Nat := #[2 ^ 101 - 1, 2 ^ 103 - 1, 2 ^ 109 - 1, 2 ^ 149 - 1]

/-- Balanced semiprimes of 30, 34 and 38 digits from the dataset. -/
private def sieveInputs : Array Nat := #[
  423983770233695968509874612799, 2535301200456458802993406410751,
  7345020907083979076125850406521644466401]

/-- 45- and 50-digit balanced semiprimes for the parallel and number-field sieves. -/
private def bigInputs : Array Nat := #[
  42962805687576751187092496809409988591255346056409]

/-- Primes of 20 to 44 digits for certificate generation. -/
private def certPrimes : Array Nat := #[
  2 ^ 61 - 1, 2 ^ 89 - 1, 2 ^ 107 - 1, 2 ^ 127 - 1,
  79638304766856507377778616296087448490695649]

private structure Spec where
  suite : String
  algorithm : String
  inputs : Array Nat
  search : Nat → Option Nat
  /-- How a returned value is validated (a proper divisor, or the certified prime). -/
  valid : Nat → Nat → Bool := Search.properFactor
  deriving Inhabited

private def Spec.of (t : String × String × Array Nat × (Nat → Option Nat)) : Spec :=
  ⟨t.1, t.2.1, t.2.2.1, t.2.2.2, Search.properFactor⟩

private def specifications : Array Spec := Id.run do
  let mut specs := #[]
  let cfg : Search.Config := {rhoSteps := 200000, rhoRestarts := 4}
  for batch in [1, 8, 16, 32, 64, 128, 256] do
    specs := specs.push (Spec.of ("mixed-semiprimes", "brent-batch-" ++ toString batch,
      semiprimes, fun n => Search.brent n {cfg with brentBatch := batch}))
  specs := specs.push (Spec.of ("mixed-semiprimes", "rho-floyd", semiprimes,
    fun n => Search.rho n cfg))
  specs := specs.push (Spec.of ("mixed-semiprimes", "fermat-10000", semiprimes,
    fun n => Search.fermat n cfg))
  for (suite, inputs) in [("trial-primes", trialPrimes), ("trial-composites", trialComposites)] do
    specs := specs.push (Spec.of (suite, "trial-reference-n-bound", inputs, trialSearchReference))
    specs := specs.push (Spec.of (suite, "trial-sqrt", inputs, trialSearch))
    specs := specs.push (Spec.of (suite, "trial-wheel-6", inputs, trialWheelSearch))
  for bound in [100, 200] do
    specs := specs.push (Spec.of ("ecm-stage-one", "ecm-factorial-" ++ toString bound,
      ecmInputs, fun n => ECM.splitFactorial n bound 12))
    specs := specs.push (Spec.of ("ecm-stage-one", "ecm-prime-powers-" ++ toString bound,
      ecmInputs, fun n => ECM.split n bound 12))
  -- Affine Weierstrass ECM (inversions, stage 1) versus Montgomery x-only ECM with stage 2.
  specs := specs.push (Spec.of ("ecm-cunningham", "ecm-affine-B1-2000-x200", ecmLarge,
    fun n => ECM.split n 2000 200))
  specs := specs.push (Spec.of ("ecm-cunningham", "ecm-montgomery-B1-2000-x200-1thread", ecmLarge,
    fun n => (ECMM.split n { b1 := 2000, curves := 200, threads := 1 }).map (·.val)))
  specs := specs.push (Spec.of ("ecm-cunningham", "ecm-montgomery-B1-11000-x200-16threads", ecmLarge,
    fun n => (ECMM.split n { b1 := 11000, curves := 200, threads := 16 }).map (·.val)))
  -- Quadratic sieve family, single-threaded, then SIQS thread scaling.
  for (name, variant) in [("qs", QS.Variant.qs), ("mpqs", .mpqs), ("siqs", .siqs)] do
    specs := specs.push (Spec.of ("quadratic-sieves-30-40-digits", name ++ "-1thread", sieveInputs,
      fun n => (QS.split n { variant := variant, threads := 1 }).map (·.val)))
  for threads in [1, 4, 16] do
    specs := specs.push (Spec.of ("siqs-threads-50-digits", "siqs-" ++ toString threads ++ "threads",
      bigInputs, fun n => (QS.split n { threads := threads }).map (·.val)))
  -- Number field sieve: line sieving versus special-q lattice sieving (16 threads).
  let line : NFS.Params := { degree := 4, ratBound := 80000, algBound := 80000,
                             halfWidth := 262144, lpMult := 40, linesPerTask := 4 }
  let lattice : NFS.Params := { line with latticeI := 4096, latticeJ := 512, qPerTask := 2 }
  specs := specs.push (Spec.of ("gnfs-50-digits", "gnfs-line-sieve", bigInputs,
    fun n => (GNFS.split n { threads := 16, params := some line }).map (·.val)))
  specs := specs.push (Spec.of ("gnfs-50-digits", "gnfs-lattice-sieve", bigInputs,
    fun n => (GNFS.split n { threads := 16, params := some lattice }).map (·.val)))
  -- Primality certificates: Pratt (complete n-1 factorizations) versus Pocklington.
  let fullFactor : Nat → List Nat := fun m => (factor .auto m {}).getD []
  let split : Nat → Option Nat := fun m => rawSearch .auto {} m
  let certified : Nat → Nat → Bool := fun n v => n == v
  let pratt : Spec := ⟨"prime-certificates", "pratt", certPrimes,
    fun n => (generatePrimeCertificate fullFactor n).map (·.value), certified⟩
  let pocklington : Spec := ⟨"prime-certificates", "pocklington", certPrimes,
    fun n => (Pocklington.generate split n).map (·.n), certified⟩
  specs := specs.push pratt
  specs := specs.push pocklington
  return specs

private def merge (previous sample : Row) : Row :=
  {previous with
    rounds := previous.rounds + sample.rounds,
    returnedDivisors := previous.returnedDivisors + sample.returnedDivisors,
    checksum := previous.checksum + sample.checksum,
    roundNs := previous.roundNs ++ sample.roundNs,
    outcomes := if previous.outcomes.isEmpty then sample.outcomes else previous.outcomes}

def run (rounds : Nat) : IO (Array Row) := do
  let specs := specifications
  let mut rows := specs.map fun s =>
    Row.mk s.suite s.algorithm s.inputs 0 0 0 #[] #[]
  -- Interleave configurations, rotating their execution order each round.
  -- This balances process warmup, changing machine load, and thermal drift.
  for r in [:rounds] do
    for j in [:specs.size] do
      let index := (j + r) % specs.size
      let s := specs[index]!
      let sample ← measure s.suite s.algorithm s.inputs 1 s.search r s.valid
      rows := rows.set! index (merge rows[index]! sample)
  IO.println "suite,algorithm,calls,returned_divisors,total_ns,median_round_ns,mean_ns_per_call,checksum"
  for row in rows do IO.println row.csv
  return rows

end Benchmark

def main (args : List String) : IO UInt32 := do
  let output := args.head?.getD "results/optimization.json"
  let rounds := max 1 ((args[1]?).bind String.toNat?).getD 3
  try
    let rows ← Benchmark.run rounds
    let report := Lean.Json.mkObj [
      ("schemaVersion", toJson (1 : Nat)),
      ("methodology", toJson "Native Lean executable; in-process monotonic timing excludes startup and compilation. Configurations are interleaved and execution order is rotated each round to balance changing machine load. Every call reruns the search on a runtime-indexed integer through a noinline IO wrapper, preventing pure computation from floating outside the measured IO interval. Every returned divisor is independently checked. Bounded none results are retained; compare returnedDivisors and outcomes alongside timing."),
      ("configuration", Lean.Json.mkObj [
        ("rhoSteps", toJson (200000 : Nat)), ("rhoRestarts", toJson (4 : Nat)),
        ("fermatSteps", toJson (10000 : Nat)), ("ecmCurves", toJson (12 : Nat)),
        ("rounds", toJson rounds)]),
      ("rows", Lean.Json.arr (rows.map Benchmark.Row.json))]
    let path : System.FilePath := output
    if let some parent := path.parent then IO.FS.createDirAll parent
    IO.FS.writeFile path report.pretty
    IO.eprintln ("Saved optimization report: " ++ output)
    return 0
  catch e =>
    IO.eprintln e.toString
    return 1
