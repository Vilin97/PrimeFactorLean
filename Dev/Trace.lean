import PrimeFactorLean.Algorithms
import Dev.LasDebug

/-! The automatic portfolio (`autoSplitter` under `primeOracle`) stage by stage
with timings: which stage splits each composite, and how long each prime's
certificate takes. A development aid; it mirrors `Algorithms.autoSplitter`. -/

namespace PrimeFactorLean.Trace

/-- Run one stage, print its time and outcome. -/
def stage (depth : Nat) (label : String) (f : Unit → Option Nat) : IO (Option Nat) := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  let ms := (t1 - t0) / 1000000
  if r.isSome || ms ≥ 5 then
    IO.println s!"{"".pushn ' ' (2 * depth)}{label}: {ms} ms -> {r}"
  return r

/-- `autoSplitter` stage by stage. -/
def split (cfg : Config) (depth n : Nat) : IO (Option Nat) := do
  if n < 4 then return none
  let st (label : String) (f : Unit → Option Nat) := stage depth label f
  if let some d ← st "small" fun _ => (smallSplitter 4096 n).map (·.val) then return some d
  if let some d ← st "power" fun _ => (powerSplitter n).map (·.val) then return some d
  if let some d ← st "algebraic" fun _ => (algebraicSplitter n).map (·.val) then return some d
  if n < 2 ^ 62 then
    if let some d ← st "squfof" fun _ => (SQUFOF.split n).map (·.val) then return some d
  if let some d ← st "rho" fun _ => (RhoF.split n 8000 1).map (·.val) then return some d
  if n ≥ 10 ^ 44 then
    if let some d ← st "pm1" fun _ => (PM1F.split n 20000).map (·.val) then return some d
  let snfs := snfsCandidate n
  let pretest := match snfs with
    | some (_, _, _, D) => min (QS.decimalDigits n) ((38 * D + 4430) / 100)
    | none => QS.decimalDigits n
  let levels := ecmSchedule pretest
  for ((b1, curves), i) in levels.zip (List.range levels.length) do
    if let some d ← st s!"ecm B1={b1} curves={curves}" fun _ =>
        (ECMF.split n { b1 := b1, curves := curves, threads := cfg.threads,
                         sigma := 11 + 100003 * i }).map (·.val) then
      return some d
  match snfs with
  | some (b, k, plus, D) =>
    if let some d ← st s!"snfs {b}^{k}{if plus then "+" else "-"}1 (D={D})" fun _ =>
        (GNFS.splitSNFS n b k plus { threads := cfg.threads }).map (·.val) then
      return some d
    st "siqs" fun _ => (SIQS.split n { threads := cfg.threads }).map (·.val)
  | none => st "siqs" fun _ => (SIQS.split n { threads := cfg.threads }).map (·.val)

/-- `factorCoreWith (primeOracle cfg) (autoSplitter cfg)` with the stages traced. -/
def factor (cfg : Config) (depth : Nat) : Nat → Nat → IO (List Nat)
  | 0, n => return [n]
  | fuel + 1, n => do
    if n ≤ 1 then return []
    let pad := "".pushn ' ' (2 * depth)
    let t0 ← IO.monoNanosNow
    let prime ← IO.lazyPure fun _ => primeOracle cfg n
    let t1 ← IO.monoNanosNow
    let ms := (t1 - t0) / 1000000
    if prime then
      if ms ≥ 5 then IO.println s!"{pad}prime {QS.decimalDigits n}d certified: {ms} ms"
      return [n]
    IO.println s!"{pad}composite {QS.decimalDigits n}d (oracle {ms} ms)"
    match ← split cfg depth n with
    | some d =>
      let a ← factor cfg (depth + 1) fuel d
      let b ← factor cfg (depth + 1) fuel (n / d)
      return a ++ b
    | none =>
      let p := minFac n
      if p == n then return [n]
      return p :: (← factor cfg (depth + 1) fuel (n / p))

def main (n threads : Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let fs ← factor { threads } 0 64 n
  let t1 ← IO.monoNanosNow
  IO.println s!"factors {fs.mergeSort} in {(t1 - t0) / 1000000} ms"

end PrimeFactorLean.Trace


namespace PrimeFactorLean.Trace

/-- Per-update cost of `SIQS.sieveMed` on a buffer of `size` bytes, for every
other prime of `[lo, hi)` with random roots (`reps` passes). -/
def sieveBench (size lo hi reps : Nat) : IO Unit := do
  let ps := (Arith.primesUpTo hi).filter (· ≥ lo)
  let ps := (Array.range ((ps.size + 1) / 2)).map (ps[2 * ·]!)
  let prime := ps.map (·.toUInt32)
  let cnt := prime.map fun p => (size.toUInt32 + p - 1) / p
  let mut seed : UInt64 := 12345
  let mut roots : Array Nat := #[]
  for p in ps do
    seed := seed * 6364136223846793005 + 1442695040888963407
    let a := (seed >>> 33).toNat % p
    seed := seed * 6364136223846793005 + 1442695040888963407
    let b := (seed >>> 33).toNat % p
    roots := roots.push (SIQS.packRoots a.toUInt32 b.toUInt32)
  let logp := ByteArray.mk (ps.map fun p => (p.log2 + 1).toUInt8)
  let updates := ps.foldl (fun acc p => acc + 2 * ((size + p - 1) / p)) 0
  let mut buf := ByteArray.mk (Array.replicate (size + 1) 0)
  let len := size.toUSize
  let t0 ← IO.monoNanosNow
  for _ in [0:reps] do
    if h : len.toNat < buf.size ∧ ps.size ≤ prime.size ∧ ps.size ≤ cnt.size ∧ ps.size ≤ roots.size ∧
        ps.size ≤ logp.size then
      buf := SIQS.sieveMed prime cnt roots logp buf len h.1 0 ps.size h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  let t1 ← IO.monoNanosNow
  IO.println s!"size {size}, primes [{lo}, {hi}): {ps.size} primes, {updates} updates per pass: {(t1 - t0).toFloat / (updates * reps).toFloat} ns per update (check {buf.get! 7})"

end PrimeFactorLean.Trace

namespace PrimeFactorLean.Trace

/-- `sieveLargeCached` against `sieveLargePaired` on zeroed regions for the
special-`q` from `q0`: differing bytes and cached bases. -/
def pairCheck (path : String) (q0 count : Nat) : IO Unit := do
  let (n, sel) ← readCadoPoly path
  let params := NFS.chooseParams (GNFS.decimalDigits n)
  let ctx := NFS.mkCtx n sel params
  let lasParams : NFS.Las.LasParams :=
    { logI := params.lasLogI, lpbR := params.lpbR, lpbA := params.lpbA, mfbR := params.mfbR,
      mfbA := params.mfbA, fudge := params.lasFudge }
  let las := NFS.Las.mkLasCtx ctx lasParams
  for (q, ρ) in NFS.specialQs sel q0 count do
    let (u, v) := NFS.reduceLattice q ρ las.skew
    let Ra := NFS.Las.latticeRoots las.alg u.1 u.2 v.1 v.2
    let z := NFS.Las.zeroBytes (las.I * las.J + 1)
    let (b1, R1) := NFS.Las.sieveLargeCached las las.alg Ra z
    let (b2, R2) := NFS.Las.sieveLargePaired las las.alg Ra z
    let mut diff := 0
    let mut first := b1.size
    for i in [0:b1.size] do
      if b1.get! i != b2.get! i then
        diff := diff + 1
        if first == b1.size then first := i
    let rdiff := (List.range R1.size).filter (fun k => R1[k]! != R2[k]!) |>.length
    IO.println s!"q={q}: {diff} bytes differ (first at {first}: {b1.get! first} vs {b2.get! first}), {rdiff} bases differ"

end PrimeFactorLean.Trace

namespace PrimeFactorLean.Trace

/-- `fkSieve2U` against two `fkSieveU` walks on consecutive large ideals: the
first pair whose regions differ. -/
def pairCheck2 (path : String) (q0 : Nat) : IO Unit := do
  let (n, sel) ← readCadoPoly path
  let params := NFS.chooseParams (GNFS.decimalDigits n)
  let ctx := NFS.mkCtx n sel params
  let lasParams : NFS.Las.LasParams :=
    { logI := params.lasLogI, lpbR := params.lpbR, lpbA := params.lpbA, mfbR := params.mfbR,
      mfbA := params.mfbA, fudge := params.lasFudge }
  let las := NFS.Las.mkLasCtx ctx lasParams
  let (q, ρ) := (NFS.specialQs sel q0 1)[0]!
  let (u, v) := NFS.reduceLattice q ρ las.skew
  let side := las.alg
  let Ra := NFS.Las.latticeRoots side u.1 u.2 v.1 v.2
  let IU := las.I.toUInt64
  let len := (las.I * las.J).toUSize
  let z := NFS.Las.zeroBytes (las.I * las.J + 1)
  let decode (w : UInt64) : USize × USize × USize × USize :=
    let x := (w &&& 8191).toUSize
    let y := ((w >>> 13) &&& 8191).toUSize
    (x, y, (((w >>> 26) &&& 262143) * IU).toUSize - x, (((w >>> 44) &&& 262143) * IU).toUSize + y)
  let mut prev : Option (Nat × UInt64) := none
  let mut checked := 0
  for k in [side.largeStart:side.primes.size] do
    let p := side.primes[k]!
    let r := Ra[k]!
    if r ≥ p then continue
    let w := NFS.Las.fkBasis las.I.toUInt32 p.toUInt32 0 r.toUInt32 1 128
    if w ≤ 1 then continue
    match prev with
    | none => prev := some (k, w)
    | some (k0, w0) =>
      prev := none
      let p0 := side.primes[k0]!
      let (xa, ya, a0, a1) := decode w0
      let (xb, yb, b0, b1) := decode w
      if h : len.toNat < z.size then
        let fa := 2 * len / p0.toUSize + 4
        let fb := 2 * len / p.toUSize + 4
        let s1 := NFS.Las.fkSieveU z len h (IU - 1).toUSize xa ya a0 a1 1 (IU / 2).toUSize fa
        let s1 := if h1 : len.toNat < s1.size then
            NFS.Las.fkSieveU s1 len h1 (IU - 1).toUSize xb yb b0 b1 16 (IU / 2).toUSize fb else s1
        let s2 := NFS.Las.fkSieve2U z len h (IU - 1).toUSize xa ya a0 a1 1 (IU / 2).toUSize
          xb yb b0 b1 16 (IU / 2).toUSize (min fa fb) (fa - min fa fb) (fb - min fa fb)
        checked := checked + 1
        if s1 != s2 then
          let mut i := 0
          while i < s1.size && s1.get! i == s2.get! i do i := i + 1
          IO.println s!"pair {p0} {p}: first difference at {i} (row {i / las.I}, col {i % las.I}): single {s1.get! i} paired {s2.get! i}; bases {w0} {w}"
          return
  IO.println s!"{checked} pairs agree"

end PrimeFactorLean.Trace

namespace PrimeFactorLean.Trace

/-- Positions of one walk (`fkNext` from `pos` until `≥ len`, at most `fuel`). -/
def walkPositions (len mask x y d0 d1 : USize) : USize → Nat → Array Nat → Array Nat
  | _, 0, acc => acc
  | pos, fuel + 1, acc =>
    let pos := NFS.Las.fkNext mask x y d0 d1 pos
    if pos < len then walkPositions len mask x y d0 d1 pos fuel (acc.push pos.toNat) else acc

def pairCheck3 (len mask : USize) (I : UInt64) (w0 w : UInt64) (p0 p : Nat) : IO Unit := do
  let decode (w : UInt64) : USize × USize × USize × USize :=
    let x := (w &&& 8191).toUSize
    let y := ((w >>> 13) &&& 8191).toUSize
    (x, y, (((w >>> 26) &&& 262143) * I).toUSize - x, (((w >>> 44) &&& 262143) * I).toUSize + y)
  let (xb, yb, b0, b1) := decode w
  let (xa, ya, a0, a1) := decode w0
  let pb := walkPositions len mask xb yb b0 b1 (I / 2).toUSize 100000 #[]
  let pa := walkPositions len mask xa ya a0 a1 (I / 2).toUSize 100000 #[]
  IO.println s!"walk a ({p0}): {pa.size} hits, walk b ({p}): {pb.size} hits; fuel a {2 * len.toNat / p0 + 4}, b {2 * len.toNat / p + 4}"
  IO.println s!"b contains 695635: {pb.contains 695635}; a contains: {pa.contains 695635}"

end PrimeFactorLean.Trace

namespace PrimeFactorLean.Trace

/-- `SIQS.splitCore` step by step: relations collected, distinct `x`, the
dependencies and what each gives. -/
def siqsDiag (n threads : Nat) : IO Unit := do
  let params := SIQS.chooseParams (QS.decimalDigits n)
  match SIQS.mkCtx n params with
  | .inr p => IO.println s!"small factor {p}"
  | .inl ctx =>
    let needed := ctx.fb.size + 1 + params.extra
    let rels := SIQS.collect ctx needed threads 1000000
    let xs := (rels.map (·.x)).toList.eraseDups
    IO.println s!"fb {ctx.fb.size} k {ctx.k}, needed {needed}, collected {rels.size}, distinct x {xs.length}, large≠1 {(rels.filter (·.large != 1)).size}"
    let rows := rels.map Squares.parityColumns
    let deps := Lanczos.dependencies (ctx.fb.size + 1) rows 64 threads
    let gdeps := GF2.dependencies (ctx.fb.size + 1) rows 64
    IO.println s!"lanczos deps {deps.size}, gf2 deps {gdeps.size}"
    let mut shown := 0
    for (label, ds) in [("lanczos", deps), ("gf2", gdeps)] do
      let mut outcomes : Array String := #[]
      for dep in ds do
        if dep.isEmpty then outcomes := outcomes.push "empty"; continue
        let rs := dep.map fun i => rels[i]!
        match (Squares.Relation.prodTree rs 0 rs.size).toSquares with
        | none => outcomes := outcomes.push "notsq"
        | some sc =>
          match sc.factor with
          | some d => outcomes := outcomes.push s!"F{d.val}"
          | none => outcomes := outcomes.push "triv"
      let cnt (s : String) := (outcomes.filter (· == s)).size
      IO.println s!"{label}: empty {cnt "empty"}, not a square {cnt "notsq"}, trivial {cnt "triv"}, factor {outcomes.size - cnt "empty" - cnt "notsq" - cnt "triv"}"
      shown := shown + 1

end PrimeFactorLean.Trace
