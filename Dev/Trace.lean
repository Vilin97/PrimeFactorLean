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

namespace PrimeFactorLean.Trace

/-- Time `SIQS.cofactorFactor` (rho) against `SQUFOF.race` on the composites of a
file (one per line). -/
def splitBench (path : String) : IO Unit := do
  let ns := (← IO.FS.lines path).filterMap (·.trim.toNat?)
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure fun _ => ns.foldl (fun acc u => if SIQS.cofactorFactor u > 1 then acc + 1 else acc) 0
  let t1 ← IO.monoNanosNow
  let b ← IO.lazyPure fun _ => ns.foldl (fun acc u =>
    let g := SIQS.uecm u.toUInt64 40
    if g > 1 && g.toNat < u && u % g.toNat == 0 then acc + 1 else acc) 0
  let t2 ← IO.monoNanosNow
  IO.println s!"{ns.size} composites: rho {(t1 - t0) / 1000 / ns.size} us each ({a} split), uecm {(t2 - t1) / 1000 / ns.size} us each ({b} split)"
  -- one curve each: cost and success rate
  let t3 ← IO.monoNanosNow
  let c ← IO.lazyPure fun _ => ns.foldl (fun acc u =>
    let g := SIQS.uecmCurve u.toUInt64 6 (1.0 / u.toFloat)
    if g > 1 && g.toNat < u then acc + 1 else acc) 0
  let t4 ← IO.monoNanosNow
  IO.println s!"one curve: {(t4 - t3) / ns.size} ns each, {c} of {ns.size} split"
  let t8 ← IO.monoNanosNow
  let f ← IO.lazyPure fun _ => ns.foldl (fun acc u =>
    let g := SIQS.uecm2 u.toUInt64 16
    if g > 1 && g.toNat < u && u % g.toNat == 0 then acc + 1 else acc) 0
  let t9 ← IO.monoNanosNow
  IO.println s!"uecm2 (pairs): {(t9 - t8) / 1000 / ns.size} us per split ({f})"
  for (b1, k) in ([] : List (Nat × Nat)) do
    let plan := SIQS.uecmMkPlan b1 (k * b1)
    let t5 ← IO.monoNanosNow
    let d ← IO.lazyPure fun _ => ns.foldl (fun acc u =>
      let g := SIQS.uecmP plan u.toUInt64 40
      if g > 1 && g.toNat < u && u % g.toNat == 0 then acc + 1 else acc) 0
    let t6 ← IO.monoNanosNow
    let e ← IO.lazyPure fun _ => ns.foldl (fun acc u =>
      let g := SIQS.uecmCurveP plan u.toUInt64 6 (1.0 / u.toFloat)
      if g > 1 && g.toNat < u then acc + 1 else acc) 0
    let t7 ← IO.monoNanosNow
    IO.println s!"B1 {b1} B2 {k * b1}: {(t6 - t5) / 1000 / ns.size} us per split ({d}), one curve {(t7 - t6) / ns.size} ns, {e} of {ns.size}"

end PrimeFactorLean.Trace

namespace PrimeFactorLean.Trace
open Lanczos in
/-- `B x`, `Bᵀ y` and the inner products of a Lanczos step at several task
counts, on the matrix that `Lanczos.dependencies` would build. -/
def lanczosScale (numCols : Nat) (rows : Array (Array Nat)) (ts : List Nat) (reps : Nat) :
    IO Unit := do
  let kept := GF2.removeSingletons numCols rows
  let mut index : Array Nat := Array.replicate numCols numCols
  let mut active := 0
  for i in kept do
    for c in rows[i]! do
      if c < numCols && index[c]! == numCols then
        index := index.set! c active
        active := active + 1
  let take := min kept.size (active + 64)
  let mut cols : Array (Array Nat) := Array.mkEmpty take
  for k in [0:take] do
    cols := cols.push ((rows[kept[k]!]!.filter (· < numCols)).map fun c => index[c]!)
  let B := Sparse.mk' active cols
  let n := B.ncols
  let v := randomBlock n 5
  let bv := mulB B v 16
  IO.println s!"B: {B.nrows} x {n}"
  for t in ts do
    let t0 ← IO.monoNanosNow
    let mut acc : UInt64 := 0
    for _ in [0:reps] do
      let r ← IO.lazyPure fun _ => mulB B v t
      acc := acc ^^^ r.get 3
    let t1 ← IO.monoNanosNow
    for _ in [0:reps] do
      let r ← IO.lazyPure fun _ => mulBT B bv t
      acc := acc ^^^ r.get 3
    let t2 ← IO.monoNanosNow
    IO.println s!"tasks {t}: B x {(t1 - t0) / 1000 / reps} us, Bt y {(t2 - t1) / 1000 / reps} us ({acc})"

open Lanczos in
/-- `steps` iterations of the Lanczos recurrence (as `Lanczos.step`) with the time of
each phase summed: `A V`, the inner products, the column selection and small
products, the tables, the updates. -/
def lanczosSteps (numCols : Nat) (rows : Array (Array Nat)) (threads steps : Nat) : IO Unit := do
  let kept := GF2.removeSingletons numCols rows
  let mut index : Array Nat := Array.replicate numCols numCols
  let mut active := 0
  for i in kept do
    for c in rows[i]! do
      if c < numCols && index[c]! == numCols then
        index := index.set! c active
        active := active + 1
  let take := min kept.size (active + 64)
  let mut cols : Array (Array Nat) := Array.mkEmpty take
  for k in [0:take] do
    cols := cols.push ((rows[kept[k]!]!.filter (· < numCols)).map fun c => index[c]!)
  let B := Sparse.mk' active cols
  let n := B.ncols
  let y := randomBlock n 1
  let v0 := mulA B y threads
  let mut st : LState := ⟨v0, Block.zero n, Block.zero n, Block.zero n, Mat.zero, Mat.zero,
    Mat.zero, Mat.zero, Array.range 64, 0xFFFFFFFFFFFFFFFF⟩
  let mut tm : Array Nat := Array.replicate 8 0
  let tasks := threads
  let tStart ← IO.monoNanosNow
  let mut tPrev := tStart
  for _ in [0:steps] do
    let t0 ← IO.monoNanosNow
    tm := tm.modify 7 (· + (t0 - tPrev))
    let bv ← IO.lazyPure fun _ => mulB B st.v threads
    let t1 ← IO.monoNanosNow
    let stv := st.v
    let av ← IO.lazyPure fun _ => mulBT B bv threads
    let inner : Option (Mat × Mat × Mat) := none
    let t2 ← IO.monoNanosNow
    let ip : Mat × Mat × Mat ← IO.lazyPure fun _ =>
      if let some ms := inner then ms else
      let parts := (chunks n tasks).map fun (lo, hi) => Task.spawn fun _ =>
        let (vb, ab, zb) := (stv.data.b, av.data.b, v0.data.b)
        if h : 8 * hi ≤ vb.size ∧ 8 * hi ≤ ab.size ∧ 8 * hi ≤ zb.size ∧ vb.size < USize.size ∧
            ab.size < USize.size ∧ zb.size < USize.size then
          let a1 := innerGo vb ab hi h.1 h.2.1 ⟨h.2.2.2.1, h.2.2.2.2.1⟩ lo Tab.zero
          let a2 := innerGo ab ab hi h.2.1 h.2.1 ⟨h.2.2.2.2.1, h.2.2.2.2.1⟩ lo Tab.zero
          let a3 := innerGo vb zb hi h.1 h.2.2.1 ⟨h.2.2.2.1, h.2.2.2.2.2⟩ lo Tab.zero
          (tablesMat a1, tablesMat a2, tablesMat a3)
        else (Mat.zero, Mat.zero, Mat.zero)
      parts.foldl (fun (x1, x2, x3) tk =>
        let (y1, y2, y3) := tk.get
        (x1.xor y1, x2.xor y2, x3.xor y3)) (Mat.zero, Mat.zero, Mat.zero)
    let (vtav, vta2v, vtv0) := ip
    let t3 ← IO.monoNanosNow
    if vtav.isZero then break
    let some (winv, s, mask0) ← IO.lazyPure fun _ => selectColumns vtav st.s1 | break
    let d := (winv.mul ((vta2v.andMask mask0).xor vtav)).xor Mat.identity
    let e := st.winv1.mul (vtav.andMask mask0)
    let f := ((st.winv2.mul ((st.vtav1.mul st.winv1).xor Mat.identity)).mul
      (((st.vta2v1.andMask st.mask1).xor st.vtav1).andMask mask0))
    let wv := winv.mul vtv0
    let (d, e, f, wv) ← IO.lazyPure fun _ => (d, e, f, wv)
    let t4 ← IO.monoNanosNow
    let (tW, tD, tE, tF) ← IO.lazyPure fun _ =>
      ((tables wv).toB, (tables d).toB, (tables e).toB, (tables f).toB)
    let t5 ← IO.monoNanosNow
    let (nd, xd) ← IO.lazyPure fun _ =>
      let upd := (chunks n tasks).map fun (lo, hi) => Task.spawn fun _ =>
        (nextRange st.v st.v1 st.v2 av mask0 tD tE tF lo hi, xRange st.x st.v tW lo hi)
      upd.foldl (fun (a, b) tk =>
        let (c, e) := tk.get
        (a ++ c.b, b ++ e.b)) (ByteArray.emptyWithCapacity (8 * n), ByteArray.emptyWithCapacity (8 * n))
    let t6 ← IO.monoNanosNow
    st := ⟨⟨⟨nd⟩⟩, st.v, st.v1, ⟨⟨xd⟩⟩, winv, st.winv1, vtav, vta2v, s, mask0⟩
    let t7 ← IO.monoNanosNow
    tm := #[tm[0]! + (t1 - t0), tm[1]! + (t2 - t1), tm[2]! + (t3 - t2), tm[3]! + (t4 - t3),
      tm[4]! + (t5 - t4), tm[5]! + (t6 - t5), tm[6]! + (t7 - t6), tm[7]!]
    tPrev ← IO.monoNanosNow
    if (← IO.getEnv "LZMARK").isSome then IO.eprint "|"
  let tEnd ← IO.monoNanosNow
  let us (k : Nat) : Nat := tm[k]! / 1000 / steps
  IO.println s!"{steps} steps, {(tEnd - tStart) / 1000 / steps} us per step: B v {us 0}, Bt {us 1}, inner {us 2}, select+mats {us 3}, tables {us 4}, update {us 5}, state {us 6}, between steps {us 7}"

open Lanczos in
/-- The parts of a Lanczos step on the matrix that `Lanczos.dependencies` would
build from `(numCols, rows)`, timed over `reps` repetitions each. -/
def lanczosParts (numCols : Nat) (rows : Array (Array Nat)) (threads reps : Nat) : IO Unit := do
  let kept := GF2.removeSingletons numCols rows
  let mut index : Array Nat := Array.replicate numCols numCols
  let mut active := 0
  for i in kept do
    for c in rows[i]! do
      if c < numCols && index[c]! == numCols then
        index := index.set! c active
        active := active + 1
  let take := min kept.size (active + 64)
  let mut cols : Array (Array Nat) := Array.mkEmpty take
  for k in [0:take] do
    cols := cols.push ((rows[kept[k]!]!.filter (· < numCols)).map fun c => index[c]!)
  let B := Sparse.mk' active cols
  let n := B.ncols
  let v := randomBlock n 5
  let v0 := randomBlock n 6
  let nnz := cols.foldl (· + ·.size) 0
  IO.println s!"B: {B.nrows} x {n}, {nnz} entries ({nnz / max 1 n} per column), packed {B.packed}"
  let t0 ← IO.monoNanosNow
  let mut acc : UInt64 := 0
  for _ in [0:reps] do
    let r ← IO.lazyPure fun _ => mulB B v threads
    acc := acc ^^^ r.get 3
  let t1 ← IO.monoNanosNow
  let bv := mulB B v threads
  for _ in [0:reps] do
    let r ← IO.lazyPure fun _ => mulBT B bv threads
    acc := acc ^^^ r.get 3
  let t2 ← IO.monoNanosNow
  let av := mulA B v threads
  let tasks := threads
  for _ in [0:reps] do
    let parts ← IO.lazyPure fun _ => ((chunks n tasks).map fun (lo, hi) => Task.spawn fun _ =>
      let (vb, ab, zb) := (v.data.b, av.data.b, v0.data.b)
      if h : 8 * hi ≤ vb.size ∧ 8 * hi ≤ ab.size ∧ 8 * hi ≤ zb.size ∧ vb.size < USize.size ∧
          ab.size < USize.size ∧ zb.size < USize.size then
        let (a1, a2, a3) := innerAcc3 vb ab zb hi h.1 h.2.1 h.2.2.1
          ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩ lo Tab.zero Tab.zero Tab.zero
        (tablesMat a1).get 1 ^^^ (tablesMat a2).get 2 ^^^ (tablesMat a3).get 3
      else 0).foldl (fun a tk => a ^^^ tk.get) 0
    acc := acc ^^^ parts
  let t3 ← IO.monoNanosNow
  -- the same three products as three passes of `innerGo`
  for _ in [0:reps] do
    let parts ← IO.lazyPure fun _ => ((chunks n tasks).map fun (lo, hi) => Task.spawn fun _ =>
      let (vb, ab, zb) := (v.data.b, av.data.b, v0.data.b)
      if h : 8 * hi ≤ vb.size ∧ 8 * hi ≤ ab.size ∧ 8 * hi ≤ zb.size ∧ vb.size < USize.size ∧
          ab.size < USize.size ∧ zb.size < USize.size then
        let a1 := innerGo vb ab hi h.1 h.2.1 ⟨h.2.2.2.1, h.2.2.2.2.1⟩ lo Tab.zero
        let a2 := innerGo ab ab hi h.2.1 h.2.1 ⟨h.2.2.2.2.1, h.2.2.2.2.1⟩ lo Tab.zero
        let a3 := innerGo vb zb hi h.1 h.2.2.1 ⟨h.2.2.2.1, h.2.2.2.2.2⟩ lo Tab.zero
        (tablesMat a1).get 1 ^^^ (tablesMat a2).get 2 ^^^ (tablesMat a3).get 3
      else 0).foldl (fun a tk => a ^^^ tk.get) 0
    acc := acc ^^^ parts
  let t3b ← IO.monoNanosNow
  IO.println s!"inner products as three passes: {(t3b - t3) / 1000 / reps} us per call"
  let t3 ← IO.monoNanosNow
  let tD := (tables (Mat.ofFn fun i => (i * 7919 + 13).toUInt64 * 0x9E3779B97F4A7C15)).toB
  for _ in [0:reps] do
    let r ← IO.lazyPure fun _ => ((chunks n tasks).map fun (lo, hi) => Task.spawn fun _ =>
      (nextRange v v v av 0xFFFF0000FFFF0000 tD tD tD lo hi, xRange v v tD lo hi)).foldl
        (fun (a, b) tk => let (c, e) := tk.get; (a ++ c.b, b ++ e.b))
        (ByteArray.emptyWithCapacity (8 * n), ByteArray.emptyWithCapacity (8 * n))
    acc := acc ^^^ (r.1.size + r.2.size).toUInt64
  let t4 ← IO.monoNanosNow
  let us (a b : Nat) : Nat := (b - a) / 1000 / reps
  IO.println s!"per call (us): B x {us t0 t1}, Bt y {us t1 t2}, inner products {us t2 t3}, updates {us t3 t4} ({acc})"

end PrimeFactorLean.Trace

namespace PrimeFactorLean.Trace
open NFS.PolySelect in
/-- Our raw collision polynomials for the leading coefficients `[lo, hi)` (RSA-100
parameters), printed as `ad l m`. -/
def rawPolys (n lo hi : Nat) : IO Unit := do
  let rs := collisionRaw n 5 7000 15625 30 lo hi
  IO.println s!"{rs.size} raw polynomials"
  for (ad, l, m, _) in rs do IO.println s!"{ad} {l} {m}"

open Merge in
/-- `Merge.mergeLog2`'s passes, counted (a development aid): per pass the weight
cap, the fill bound, the candidate columns, those skipped by the fill cache, by
the star estimate and by the computed fill, the merges, the live rows and the
average weight. -/
def mergeStats (numCols dense : Nat) (rows0 : Array (Array Nat)) (density maxW : Nat)
    (mstMax : Nat := 6) (maxPasses : Nat := 1000) : Array (Array Nat) := Id.run do
  let mut stats : Array (Array Nat) := #[]
  let mut rows : Array (Array Nat) := Array.mkEmpty rows0.size
  let mut dmask : Array Nat := Array.mkEmpty rows0.size
  for r0 in rows0 do
    let r := normalize r0
    let mut mk := 0
    let mut sp : Array Nat := Array.mkEmpty r.size
    for c in r do
      if c < dense then mk := mk ^^^ (1 <<< c) else sp := sp.push c
    rows := rows.push sp
    dmask := dmask.push mk
  let mut colRows : Array (Array Nat) := Array.replicate numCols #[]
  let mut colWeight : Array Nat := Array.replicate numCols 0
  let mut weight := 0
  for i in [0:rows.size] do
    for c in rows[i]! do
      colRows := colRows.modify c (·.push i)
      colWeight := colWeight.set! c (colWeight[c]! + 1)
    weight := weight + rows[i]!.size
  let mut ops : Array Nat := #[]
  let mut alive : Array Bool := Array.replicate rows.size true
  let mut liveRows := rows.size
  let mut cwmax := 2
  let mut cbound := 0
  let mut idle := 0
  let mut done := false
  -- cached fills of rejected columns, and modification stamps of the rows
  let mut clock := 1
  let mut rowStamp : Array Nat := Array.replicate rows.size 0
  let mut colStamp : Array Nat := Array.replicate numCols 0
  let mut colFill : Array Int := Array.replicate numCols 0
  let mut colCw : Array Nat := Array.replicate numCols 0
  while !done && idle < 3 && stats.size < maxPasses do
    let mut merges := 0
    let mut cands := 0
    let mut cached := 0
    let mut fills := 0
    let mut stars := 0
    for c in [dense:numCols] do
      if done then break
      let cw := colWeight[c]!
      if cw == 0 || cw > cwmax then continue
      cands := cands + 1
      -- the live rows containing `c`
      let mut rs : Array Nat := #[]
      for r in colRows[c]! do
        if alive[r]! && containsSorted rows[r]! c && !rs.contains r then rs := rs.push r
      if rs.isEmpty then
        colRows := colRows.set! c #[]
        continue
      -- a minimum spanning tree of the rows (edge weight: the size of their
      -- sum): its edges are the new rows, the root is deleted
      let k := rs.size
      -- a fill computed earlier is still exact while neither the column's
      -- weight nor any of its rows changed: skip it without recomputation
      if k ≥ 3 && colStamp[c]! > 0 && colCw[c]! == k && colFill[c]! > (cbound : Int) &&
          rs.all (fun r => rowStamp[r]! ≤ colStamp[c]!) then
        colRows := colRows.set! c rs
        cached := cached + 1
        continue
      let mst := k ≥ 3 && k ≤ mstMax
      -- beyond `mstMax` rows: a star around the lightest row, fill estimated
      -- as `(k - 2) w` (pairwise sums cost `k (k - 1) / 2` merge walks)
      if k > mstMax then
        let mut pv := 0
        for v in [1:k] do
          if rows[rs[v]!]!.size < rows[rs[pv]!]!.size then pv := v
        if ((k - 2) * rows[rs[pv]!]!.size : Nat) > cbound then
          colRows := colRows.set! c rs
          stars := stars + 1
          continue
        -- reorder so that the pivot comes first (the star's root)
        let tmp := rs[0]!
        rs := (rs.set! 0 rs[pv]!).set! pv tmp
      let mut wt : Array Nat := Array.replicate (k * k) 0
      if mst then
        for i in [0:k] do
          for j in [i + 1:k] do
            let w := symmDiffSize rows[rs[i]!]! rows[rs[j]!]! 0 0 0
            wt := (wt.set! (i * k + j) w).set! (j * k + i) w
      let (parent, order) := if mst then primTree k wt
        else ((Array.range k).map fun v => if v == 0 then k else 0, Array.range k)
      if mst then
        let mut fill : Int := 0
        for v in [1:k] do fill := fill + wt[v * k + parent[v]!]!
        for v in [0:k] do fill := fill - rows[rs[v]!]!.size
        if fill > (cbound : Int) then
          fills := fills + 1
          colRows := colRows.set! c rs
          clock := clock + 1
          colStamp := colStamp.set! c clock
          colFill := colFill.set! c fill
          colCw := colCw.set! c k
          continue
      colRows := colRows.set! c #[]
      merges := merges + 1
      -- children before parents: each row gets its parent's original row
      for t in [0:k - 1] do
        let v := order[k - 1 - t]!
        let u := parent[v]!
        let r := rs[v]!
        let pr := rs[u]!
        let prow := rows[pr]!
        let old := rows[r]!
        let new := symmDiff old prow
        let mut i := 0
        for x in prow do
          while i < old.size && old[i]! < x do i := i + 1
          if i < old.size && old[i]! == x then
            colWeight := colWeight.set! x (colWeight[x]! - 1)
          else
            colWeight := colWeight.set! x (colWeight[x]! + 1)
            colRows := colRows.modify x (·.push r)
        weight := weight + new.size - old.size
        rows := rows.set! r new
        dmask := dmask.set! r (dmask[r]! ^^^ dmask[pr]!)
        ops := ops.push (r * 16777216 + pr)
        clock := clock + 1
        rowStamp := rowStamp.set! r clock
      -- delete the root
      let root := rs[order[0]!]!
      for x in rows[root]! do colWeight := colWeight.set! x (colWeight[x]! - 1)
      weight := weight - rows[root]!.size
      rows := rows.set! root #[]
      alive := alive.set! root false
      liveRows := liveRows - 1
      if weight ≥ density * liveRows then done := true
    stats := stats.push #[cwmax, cbound.toNat, cands, cached, stars, fills, merges, liveRows, weight / max 1 liveRows]
    -- raise the bound every pass, the weight cap when a pass merges little
    cbound := cbound + 8
    if merges * 100 < liveRows then
      if cwmax < maxW then cwmax := cwmax + 1
      else if merges == 0 then idle := idle + 1
  return stats

/-- `GF2.removeSingletons`, timed (a development aid). -/
def singletonParts (numCols : Nat) (rows : Array (Array Nat)) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let kept ← IO.lazyPure fun _ => GF2.removeSingletons numCols rows
  let t1 ← IO.monoNanosNow
  IO.println s!"removeSingletons {(t1 - t0) / 1000000} ms ({kept.size} rows)"

/-- `mergeStats` printed, with its time. -/
def mergeStatsIO (nc : Nat) (rows : Array (Array Nat)) : IO Unit := do
  for mst in [3, 4, 6, 8] do
    let a ← IO.monoNanosNow
    let (m, _, c) ← IO.lazyPure fun _ => Merge.mergeLog2 nc 0 rows 95 32 mst
    let b ← IO.monoNanosNow
    let w := m.foldl (fun acc r => acc + r.size) 0
    IO.println s!"  mstMax {mst}: mergeLog2 {(b - a) / 1000000} ms -> {m.size} x {c}, weight {w / max 1 m.size}"

open NFS.PolySelect in
/-- Our `logNorm` (and the golden-section search it replaces) against CADO-NFS's
lognorm and skewness on the size-optimized polynomials of a `polyselect` output. -/
def normCheck (path : String) (count : Nat) : IO Unit := do
  let lines ← IO.FS.lines path
  let mut polys : Array (Array Int × Float × Float) := #[]
  let mut inOpt := false
  let mut cur : Array Int := #[]
  for l in lines do
    if l.startsWith "# Size-optimized" then
      inOpt := true
      cur := #[]
    else if inOpt && l.startsWith "c" then
      match l.splitOn ": " with
      | [k, v] =>
        let i := (k.drop 1).toNat!
        while cur.size ≤ i do cur := cur.push 0
        cur := cur.set! i v.toInt!
      | _ => pure ()
    else if inOpt && l.startsWith "# exp_E" then
      -- `# exp_E 26.16, lognorm 31.21, skew 4587.02, 5 rroots`
      let parts := l.splitOn ", "
      let num (t : String) : Float := match (t.splitOn " ").getLast? with
        | some x => match x.splitOn "." with
          | [a, b] => a.toNat!.toFloat + b.toNat!.toFloat / Float.ofNat (10 ^ b.length)
          | _ => x.toNat!.toFloat
        | none => 0
      polys := polys.push (cur, num parts[1]!, num parts[2]!)
      inOpt := false
  let golden (cs : Array Int) : Float × Float := Id.run do
    let d := cs.size - 1
    let w := normPoly cs
    let dF := Arith.nf d
    let f (t : Float) : Float := hornerF w (Float.exp (2 * t)) * Float.exp (-dF * t)
    let mut lo : Float := 0.0
    let mut hi : Float := 80.0
    let phi : Float := 0.6180339887498949
    for _ in [0:45] do
      let a := hi - phi * (hi - lo)
      let b := lo + phi * (hi - lo)
      if f a < f b then hi := b else lo := a
    let t := (lo + hi) / 2.0
    return (0.5 * Float.log (f t), Float.exp t)
  let mut maxDn : Float := 0
  let mut maxDs : Float := 0
  let mut maxDg : Float := 0
  for (cs, ln, sk) in polys.extract 0 count do
    let (n1, s1) := logNorm cs
    let (n2, _) := golden cs
    maxDn := max maxDn (n1 - ln).abs
    maxDs := max maxDs ((s1 - sk) / sk).abs
    maxDg := max maxDg (n1 - n2).abs
  IO.println s!"{min count polys.size} polynomials: max |ours - CADO| lognorm {maxDn}, rel. skew {maxDs}; max |root - golden| {maxDg}"
  let t0 ← IO.monoNanosNow
  let mut acc : Float := 0
  for _ in [0:20] do
    for (cs, _, _) in polys do acc := acc + (logNorm cs).1
  let t1 ← IO.monoNanosNow
  for _ in [0:20] do
    for (cs, _, _) in polys do acc := acc + (golden cs).1
  let t2 ← IO.monoNanosNow
  IO.println s!"logNorm {(t1 - t0) / (20 * polys.size)} ns, golden {(t2 - t1) / (20 * polys.size)} ns ({acc})"
  let fs := polys.map fun (cs, _, _) => toFloats cs
  let t3 ← IO.monoNanosNow
  for _ in [0:20] do
    for (cs, _, _) in polys do acc := acc + (toFloats cs).get! 0
  let t4 ← IO.monoNanosNow
  for _ in [0:20] do
    for f in fs do acc := acc + (normPolyF f).get! 0
  let t5 ← IO.monoNanosNow
  for _ in [0:20] do
    for f in fs do acc := acc + (logNormF f).1
  let t6 ← IO.monoNanosNow
  for _ in [0:20] do
    for f in fs do acc := acc + (logNormFH f 5000).1
  let t7 ← IO.monoNanosNow
  let k := 20 * polys.size
  IO.println s!"toFloats {(t4 - t3) / k} ns, normPolyF {(t5 - t4) / k} ns, logNormF {(t6 - t5) / k} ns, logNormFH(5000) {(t7 - t6) / k} ns ({acc})"

open NFS.PolySelect in
/-- Our Murphy `E` (RSA-100 bounds) of the polynomial pairs of a CADO-NFS format
file (blocks separated by blank lines; `#` lines ignored). -/
def murphyFile (path : String) (lpbA lpbR logI qmin : Nat := 26) : IO Unit := do
  let txt ← IO.FS.readFile path
  let tbl := dickmanTable
  let (lpbR, logI, qmin) := if lpbA == 26 && lpbR == 26 then (25, 11, 180000) else (lpbR, logI, qmin)
  let area := Float.exp2 (2 * logI - 1).toFloat * qmin.toFloat
  let bf := Float.exp2 lpbA.toFloat
  let bg := Float.exp2 lpbR.toFloat
  for blk in txt.splitOn "\n\n" do
    let mut cs : Array Int := #[]
    let mut y0 : Int := 0
    let mut y1 : Int := 0
    for l in blk.splitOn "\n" do
      match l.splitOn ": " with
      | [k, v] =>
        if k == "Y0" then y0 := v.trim.toInt!
        else if k == "Y1" then y1 := v.trim.toInt!
        else if k.startsWith "c" && !k.startsWith "#" then
          let i := (k.drop 1).toNat!
          while cs.size ≤ i do cs := cs.push 0
          cs := cs.set! i v.trim.toInt!
      | _ => pure ()
    if cs.size < 2 || y1 == 0 then continue
    let (ln, sk) := logNorm cs
    let e := murphyE tbl cs y1 (-y0) sk bf bg area
    IO.println s!"Y1 {y1} c{cs.size - 1} {cs.back!}: E*1e7 {(e * 10000000).round} lognorm {ln} alpha {alphaExact cs 2000} skew {sk}"

open NFS.PolySelect in
/-- `sizeOpt` against `sizeOptF` (and `sizeOpt2` timing) on the raw collision
polynomials of the leading coefficients `[lo, hi)` (RSA-100 parameters). -/
def soptCheck (n lo hi : Nat) : IO Unit := do
  let raws := (collisionRaw n 5 7000 15625 30 lo hi).filter fun (_, _, _, cs) => cs[5]! * cs[3]! ≤ 0
  IO.println s!"{raws.size} raw polynomials"
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure fun _ => raws.map fun (_, l, m, cs) => sizeOpt cs l m
  let t1 ← IO.monoNanosNow
  let b ← IO.lazyPure fun _ => raws.map fun (_, l, m, cs) => sizeOptF cs l m
  let t2 ← IO.monoNanosNow
  let mut same := 0
  let mut better := 0
  let mut worse := 0
  let mut maxD : Float := 0
  for (x, y) in a.zip b do
    if x.1 == y.1 && x.2.1 == y.2.1 then same := same + 1
    else if y.2.2 < x.2.2 then better := better + 1 else worse := worse + 1
    maxD := max maxD (x.2.2 - y.2.2).abs
  IO.println s!"sizeOpt {(t1 - t0) / 1000000} ms, sizeOptF {(t2 - t1) / 1000000} ms: same {same}, F better {better}, F worse {worse}, max |dln| {maxD}"

open NFS.PolySelect in
/-- `collide` and `fromCollision` on one special-`q` root (RSA-100 parameters). -/
def collideTest (n ad Q rQ : Nat) : IO Unit := do
  let d := 5
  let P := 7000
  let ntilde := d ^ d * ad ^ (d - 1) * n
  let m0 := Arith.iroot ntilde d
  let primesP := (Arith.primesUpTo (2 * P)).filter (· ≥ P)
  let M := 4 * P * P
  let prs : Array (Nat × Array Nat) := primesP.filterMap fun p =>
    if (d * ad) % p == 0 || n % p == 0 then none
    else
      let rs := liftedRoots d ntilde m0 p
      if rs.isEmpty then none else some (p, rs)
  let QQ := Q * Q
  let invs := prs.map fun (p, _) => (invModW (QQ % (p * p)).toUInt64 (p * p).toUInt64).toNat
  let cols := collide prs invs rQ M
  IO.println s!"{cols.size} collisions: {cols}"
  for (i, p1, p2) in cols do
    let mt : Int := (m0 : Int) + (rQ : Int) + i * (QQ : Int)
    let l := p1 * p2 * Q
    IO.println s!"{i} {p1} {p2} l={l} -> {(fromCollision n d ad mt l).isSome}"

open NFS.PolySelect in
/-- The special-`q` primes (with root counts) and `k` of the collision search for
the leading coefficient `ad` (RSA-100 parameters). -/
def sqList (n ad : Nat) : IO Unit := do
  let d := 5
  let ntilde := d ^ d * ad ^ (d - 1) * n
  let m0 := Arith.iroot ntilde d
  let sq0 : Array (Nat × Array Nat) := specialQPrimes.toArray.filterMap fun q =>
    if (d * ad) % q == 0 || n % q == 0 then none
    else
      let rs := liftedRoots d ntilde m0 q
      if rs.isEmpty then none else some (q, rs)
  let p2 := (2 * 7000 : Nat).toFloat
  let (sq, k) := suitableQ sq0 d 15625 (m0.toFloat / (p2 * p2 * p2 * p2))
  IO.println s!"k {k} lq {sq.size}: {sq.map fun (q, rs) => (q, rs.size)}"
  let qs := specialQList sq k 15625
  IO.println s!"{qs.size} special-q, {qs.foldl (fun a (_, r, _) => a + r.size) 0} roots"
  for (Q, rs, _) in qs do IO.println s!"{Q} {rs.size} {rs}"
  for (q, rs) in sq0 do IO.println s!"root {q} {rs}"
  for p in (Arith.primesUpTo 14000).filter (· ≥ 7000) do
    if (d * ad) % p != 0 && n % p != 0 then
      IO.println s!"proot {p} {liftedRoots d ntilde m0 p}"

end PrimeFactorLean.Trace

namespace PrimeFactorLean.Trace

/-- The parts of one `uecm` curve on the composites of a file: the stage-1 ladder
alone, the whole curve, the final gcd and the curve setup's inversion. -/
def uecmParts (path : String) : IO Unit := do
  let ns := (← IO.FS.lines path).filterMap (·.trim.toNat?)
  let plan := SIQS.uecmPlan.get
  let bits := plan.1
  let reps := 5
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure fun _ => (List.range reps).foldl (fun acc r => ns.foldl (fun acc u =>
    let m : UInt64 := u.toUInt64
    let mf := 1.0 / m.toFloat
    let x0 := (7 + r.toUInt64) % m
    let (X, Z) := SIQS.uecmLadder m 12345 x0 mf bits (bits.size - 1) x0 1 (x0 + 1) 1
    acc ^^^ X ^^^ Z) acc) (0 : UInt64)
  let t1 ← IO.monoNanosNow
  let b ← IO.lazyPure fun _ => (List.range reps).foldl (fun acc r => ns.foldl (fun acc u =>
    let m : UInt64 := u.toUInt64
    acc ^^^ SIQS.uecmCurveP plan m (6 + r.toUInt64) (1.0 / m.toFloat)) acc) (0 : UInt64)
  let t2 ← IO.monoNanosNow
  let c ← IO.lazyPure fun _ => (List.range reps).foldl (fun acc r => ns.foldl (fun acc u =>
    let m : UInt64 := u.toUInt64
    acc ^^^ SIQS.gcd64 ((m >>> 3) * (2654435761 : UInt64) + r.toUInt64 + 1) m) acc) (0 : UInt64)
  let t3 ← IO.monoNanosNow
  let d ← IO.lazyPure fun _ => (List.range reps).foldl (fun acc r => ns.foldl (fun acc u =>
    let m : UInt64 := u.toUInt64
    acc ^^^ (SIQS.invLoop m ((m >>> 5) + r.toUInt64 + (3 : UInt64)) 0 1 100).toUInt64) acc) (0 : UInt64)
  let t4 ← IO.monoNanosNow
  let e ← IO.lazyPure fun _ => (List.range reps).foldl (fun acc r => ns.foldl (fun acc u =>
    let m : UInt64 := u.toUInt64
    let mf := 1.0 / m.toFloat
    let x0 := (7 + r.toUInt64) % m
    let y0 := (11 + r.toUInt64) % m
    let (X, Z, Y, W) := SIQS.uecmLadder2 m 12345 x0 54321 y0 mf bits (bits.size - 1) x0 1 (x0 + 1) 1
      y0 1 (y0 + 1) 1
    acc ^^^ X ^^^ Z ^^^ Y ^^^ W) acc) (0 : UInt64)
  let t5 ← IO.monoNanosNow
  let f ← IO.lazyPure fun _ => (List.range reps).foldl (fun acc r => ns.foldl (fun acc u =>
    let m : UInt64 := u.toUInt64
    acc ^^^ SIQS.uecmCurve2P plan m (6 + 2 * r.toUInt64) (1.0 / m.toFloat)) acc) (0 : UInt64)
  let t6 ← IO.monoNanosNow
  let k := ns.size * reps
  IO.println s!"per call: ladder {(t1 - t0) / k} ns, curve {(t2 - t1) / k} ns, gcd64 {(t3 - t2) / k} ns, invLoop {(t4 - t3) / k} ns, ladder2 {(t5 - t4) / k} ns, curve2 {(t6 - t5) / k} ns ({a ^^^ b ^^^ c ^^^ d ^^^ e ^^^ f})"

end PrimeFactorLean.Trace

namespace PrimeFactorLean.Trace

/-- `uecmP` with the plans `B1`, `k B1` of a grid on the composites of a file:
time per split and the splits found. -/
def uecmGrid (path : String) (grid : List (Nat × Nat)) : IO Unit := do
  let ns := (← IO.FS.lines path).filterMap (·.trim.toNat?)
  for (b1, k) in grid do
    let plan := SIQS.uecmMkPlan b1 (k * b1)
    let t0 ← IO.monoNanosNow
    let d ← IO.lazyPure fun _ => ns.foldl (fun acc u =>
      let g := SIQS.uecmP plan u.toUInt64 40
      if g > 1 && g.toNat < u && u % g.toNat == 0 then acc + 1 else acc) 0
    let t1 ← IO.monoNanosNow
    let e ← IO.lazyPure fun _ => ns.foldl (fun acc u =>
      let g := SIQS.uecmCurveP plan u.toUInt64 6 (1.0 / u.toFloat)
      if g > 1 && g.toNat < u then acc + 1 else acc) 0
    let t2 ← IO.monoNanosNow
    IO.println s!"B1 {b1} B2 {k * b1}: {(t1 - t0) / 1000 / ns.size} us per split ({d}), one curve {(t2 - t1) / ns.size} ns, {e} of {ns.size}"

end PrimeFactorLean.Trace

namespace PrimeFactorLean.Trace

/-- `Σ cᵢ 2^(S i)` of a list of naturals (slots `S` bits wide). -/
def packNat (cs : List Nat) (S : Nat) : Nat :=
  cs.foldr (fun c acc => c ||| (acc <<< S)) 0

/-- Kronecker substitution: `mulL xs ys` from one product of the packed lists
(balanced digits of `S` bits, `S` above twice the coefficients' bits). -/
def kronMul (xs ys : List Int) : List Int := Id.run do
  if xs.isEmpty || ys.isEmpty then return []
  let bits (zs : List Int) : Nat := zs.foldl (fun m c => max m (c.natAbs.log2 + 1)) 0
  let L := xs.length + ys.length - 1
  let S := bits xs + bits ys + (min xs.length ys.length).log2 + 3
  let pk (zs : List Int) : Int :=
    (packNat (zs.map fun c => if c ≥ 0 then c.toNat else 0) S : Int) -
      (packNat (zs.map fun c => if c < 0 then c.natAbs else 0) S : Int)
  let z := pk xs * pk ys
  let neg := z < 0
  let mut u := z.natAbs
  let half := 1 <<< (S - 1)
  let mask := (1 <<< S) - 1
  let mut out : Array Int := Array.mkEmpty L
  for _ in [0:L] do
    let low := u &&& mask
    u := u >>> S
    let carry := low ≥ half
    if carry then u := u + 1
    let d : Int := if carry then (low : Int) - ((1 <<< S : Nat) : Int) else (low : Int)
    out := out.push (if neg then -d else d)
  return out.toList

/-- `kronMul` against `NFS.mulLAuto` on polynomials with `bits`-bit coefficients
(built from powers, forced before the timings). -/
def kronBench (bits deg reps : Nat) : IO Unit := do
  let m3 := bits * 100 / 159
  let m7 := bits * 100 / 281
  let coef (seed k : Nat) : Int :=
    let v : Int := ((3 ^ m3 * (seed * 31 + k + 1) + 7 ^ m7 * (k + 2) : Nat) : Int)
    if k % 3 == 0 then -v else v
  let xs := (List.range (deg + 1)).map (coef 1)
  let ys := (List.range (deg + 1)).map (coef 2)
  let sz := xs.foldl (fun a c => a + c.natAbs.log2) 0 + ys.foldl (fun a c => a + c.natAbs.log2) 0
  IO.println s!"inputs: {sz} bits in all"
  let t0 ← IO.monoNanosNow
  let mut a := 0
  for _ in [0:reps] do
    let r ← IO.lazyPure fun _ => NFS.mulLAuto xs ys
    a := a + r.length
  let t1 ← IO.monoNanosNow
  let mut b := 0
  for _ in [0:reps] do
    let r ← IO.lazyPure fun _ => kronMul xs ys
    b := b + r.length
  let t2 ← IO.monoNanosNow
  let same := NFS.mulLAuto xs ys == kronMul xs ys
  IO.println s!"{bits} bits, degree {deg}: mulLAuto {(t1 - t0) / 1000000 / reps} ms, kronMul {(t2 - t1) / 1000000 / reps} ms, same {same} ({a} {b})"

end PrimeFactorLean.Trace

namespace PrimeFactorLean.Trace

/-- Time one product of two `bits`-bit integers (`Nat` and `Int`). -/
def mulBench (bits : Nat) : IO Unit := do
  let mk (seed : Nat) : Nat := Id.run do
    let mut x : Nat := seed
    let mut acc : Nat := 1
    for _ in [0:bits / 61 + 1] do
      x := (x * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
      acc := (acc <<< 61) ||| (x >>> 3)
    return acc
  let a := mk 1
  let b := mk 2
  let t0 ← IO.monoNanosNow
  let p ← IO.lazyPure fun _ => a * b
  let t1 ← IO.monoNanosNow
  let ai : Int := a
  let bi : Int := -(b : Int)
  let t2 ← IO.monoNanosNow
  let q ← IO.lazyPure fun _ => ai * bi
  let t3 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => (List.range 5).map fun k => Task.spawn fun _ => (a + k) * b
  let s := r.foldl (fun acc t => acc + t.get.log2) 0
  let t4 ← IO.monoNanosNow
  IO.println s!"{bits} bits: Nat mul {(t1 - t0) / 1000000} ms, Int mul {(t3 - t2) / 1000000} ms, 5 parallel Nat muls {(t4 - t3) / 1000000} ms ({p.log2} {q.natAbs.log2} {s})"

end PrimeFactorLean.Trace

namespace PrimeFactorLean.Trace

/-- The product `γ` of the square root on synthetic data shaped like an RSA-100
dependency (`count` pairs `(a, b)` of 30 and 20 bits, the RSA-100 polynomial):
`prodTreePar` at several depths, and the whole `sqrtFind`. -/
def gammaBench (count : Nat) (depths : List Nat) : IO Unit := do
  let cs : Array Int := #[-2225236004483188541369784, -93389187468837479525, 11905468723572312, -423328853227, -25528380, 900]
  let sel : NFS.Selection := { coeffs := cs, m := 25595796516068257174, y1 := 65995981247339 }
  let g := NFS.monicLower sel.coeffs
  let fp := NFS.derivative g
  let cd := sel.lead
  let mut S : Array (Int × Int) := Array.mkEmpty count
  let mut x : Nat := 12345
  for _ in [0:count] do
    x := (x * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
    let a : Int := ((x >>> 20) % 1073741824 : Nat)
    let b : Int := ((x >>> 4) % 1048576 + 1 : Nat)
    S := S.push (if x % 2 == 0 then -a else a, b)
  let xs := fp :: fp :: S.toList.map fun ab => [(cd : Int) * ab.1, -ab.2]
  IO.println s!"{xs.length} factors"
  for d in depths do
    let t0 ← IO.monoNanosNow
    let γ ← IO.lazyPure fun _ => NFS.prodTreePar g d xs
    let t1 ← IO.monoNanosNow
    IO.println s!"prodTreePar depth {d}: {(t1 - t0) / 1000000} ms ({NFS.maxBits γ} bits)"
  let γ := NFS.prodTreePar g 3 xs
  let some p := NFS.inertPrime g 1000003 | IO.println "no inert prime"
  let t2 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => (NFS.sqrtFind g γ p fun _ => true).map NFS.maxBits
  let t3 ← IO.monoNanosNow
  IO.println s!"sqrtFind (not a square: the lift alone): {(t3 - t2) / 1000000} ms ({r})"

end PrimeFactorLean.Trace

namespace PrimeFactorLean.Trace

/-- Whether a byte array captured by a task closure is copied on its first
write in the task (objects reachable from a task are marked multi-threaded,
and those are never exclusive), and what the allocations cost. -/
@[noinline] def mtWrite (b : ByteArray) (k : Nat) : Nat := (b.set! k 7).size + k

def mtCopyTest (mb : Nat) : IO Unit := do
  let n := mb * 1024 * 1024
  let t0 ← IO.monoNanosNow
  let z ← IO.lazyPure fun _ => NFS.Las.zeroBytes n
  let t1 ← IO.monoNanosNow
  IO.println s!"zeroBytes {mb} MB: {(t1 - t0) / 1000} us ({z.size})"
  let c ← IO.lazyPure fun _ => z.copySlice 0 (ByteArray.emptyWithCapacity n) 0 n
  let t2 ← IO.monoNanosNow
  IO.println s!"copySlice {mb} MB: {(t2 - t1) / 1000} us ({c.size})"
  -- in this thread: the array is exclusive, the write is in place
  let r1 ← IO.lazyPure fun _ => mtWrite c 5
  let t3 ← IO.monoNanosNow
  IO.println s!"write in place: {(t3 - t2) / 1000} us ({r1})"
  -- captured by a task: marked multi-threaded
  let r2 ← IO.lazyPure fun _ => (Task.spawn fun _ => mtWrite z 6).get
  let t4 ← IO.monoNanosNow
  IO.println s!"write in a task: {(t4 - t3) / 1000} us ({r2})"

end PrimeFactorLean.Trace

namespace PrimeFactorLean.Trace

open QS in
/-- `SIQS.collect` with the time of each round, the main thread's share and the
relations found (full and partial), to measure parallel efficiency. -/
def siqsRounds (n threads : Nat) : IO Unit := do
  let params := SIQS.chooseParams (QS.decimalDigits n)
  let .inl ctx := SIQS.mkCtx n params | IO.println "small factor"
  let needed := ctx.fb.size + 1 + params.extra
  let mut fulls := 0
  let mut edges : Array (Nat × Nat) := #[]
  let mut uf : UnionFind := {}
  let mut cycles := 0
  let mut seen : Std.HashSet Nat := {}
  let mut round := 0
  let mut nextSeed := 0
  let mut perTask := 1
  let mut processed := 0
  let mut raw := 0
  let t0 ← IO.monoNanosNow
  let mut tMain := 0
  while fulls + cycles < needed && round < 1000 do
    let a ← IO.monoNanosNow
    let base := nextSeed
    let k := perTask
    let tasks := (List.range threads).map fun t =>
      Task.spawn fun _ => SIQS.processAs ctx (base + t * k) k
    nextSeed := nextSeed + threads * k
    processed := processed + threads * k
    let res ← IO.lazyPure fun _ => tasks.map Task.get
    let b ← IO.monoNanosNow
    for batch in res do
      for f in batch do
        raw := raw + 1
        let key := min f.rel.x (ctx.n - f.rel.x)
        if seen.contains key then continue
        seen := seen.insert key
        if f.l1 == 1 && f.l2 == 1 then fulls := fulls + 1
        else
          edges := edges.push (f.l1, f.l2)
          let (uf', closed) := uf.union f.l1 f.l2
          uf := uf'
          if closed then cycles := cycles + 1
    round := round + 1
    let got := fulls + cycles
    if got > 0 && got < needed then
      let estA := (needed - got) * processed / got
      perTask := max 1 (min 32 (estA * 6 / 10 / threads))
    let c ← IO.monoNanosNow
    tMain := tMain + (c - b)
    IO.println s!"round {round}: {threads * k} A ({k}/task) {(b - a) / 1000000} ms + main {(c - b) / 1000000} ms; raw {raw}, fulls {fulls}, cycles {cycles} / {needed}"
  let t1 ← IO.monoNanosNow
  let cyc ← IO.lazyPure fun _ => graphCycles edges
  let t2 ← IO.monoNanosNow
  IO.println s!"{processed} A in {(t1 - t0) / 1000000} ms (main thread {tMain / 1000000} ms), graphCycles {(t2 - t1) / 1000000} ms ({cyc.size} cycles), raw relations {raw}"

end PrimeFactorLean.Trace
