import PrimeFactorLean.NFS.Las
import PrimeFactorLean.GNFS
import PrimeFactorLean.NFS.PolySelect
open PrimeFactorLean PrimeFactorLean.NFS

/-- Brute-force check of the Franke–Kleinjung walk: for random `p ≥ I` and `R`,
the positions visited from `(0, 0)` must be exactly the lattice points
`i ≡ j R (mod p)` with `-I/2 ≤ i < I/2`, `1 ≤ j < J`. -/
def fkUnit : IO Unit := do
  let I := 2048
  let J := 1024
  let len := I * J
  let mut seed := 12345
  let mut bad := 0
  let mut tested := 0
  for _ in [0:200] do
    seed := (seed * 1103515245 + 12345) % 2147483648
    let p := 2048 + seed % 3000000
    seed := (seed * 1103515245 + 12345) % 2147483648
    let R := seed % p
    match Las.fkReduce p R I with
    | none => continue
    | some (x, b0, y, b1) =>
      tested := tested + 1
      -- walk
      let mut pos := I / 2
      let mut walk : Array Nat := #[]
      let mut fuel := 2 * len / p + 10
      while fuel > 0 do
        fuel := fuel - 1
        let next := (Las.fkNext (I - 1).toUSize x.toUSize y.toUSize (b0 * I - x).toUSize (b1 * I + y).toUSize pos.toUSize).toNat
        if next ≥ len then break
        walk := walk.push next
        pos := next
      -- brute force
      let mut brute : Array Nat := #[]
      for j in [1:J] do
        -- i ≡ j R (mod p), i ∈ [-I/2, I/2): c = i + I/2
        let t := (j * R + I / 2) % p    -- c ≡ t (mod p)
        if t < I then brute := brute.push (j * I + t)
      if walk != brute then
        bad := bad + 1
        if bad ≤ 3 then IO.println s!"mismatch p={p} R={R} basis x={x} b0={b0} y={y} b1={b1}: walk {walk.size} brute {brute.size}; first walk {walk.extract 0 5} brute {brute.extract 0 5}"
  IO.println s!"fk tested {tested}, mismatches {bad}"

/-- Sieve a few special-`q` with the lattice siever, time it and check every relation. -/
def lasDebug (n : Nat) (count : Nat) (fudge : Nat := 4) (skewOverride : Nat := 0) (v3 : Bool := false)
    (v4 : Bool := false) (preSlack : Nat := 6) (qstart : Nat := 0) : IO Unit := do
  let params := chooseParams (GNFS.decimalDigits n)
  let params := { params with lpMult := 2 ^ (max params.lpbR params.lpbA) /
      (min params.ratBound params.algBound) + 1 }
  let some sel := (PolySelect.selectCollision n params.degree params.psP params.psNq params.psIncr
    params.psAdMax params.psKeep 16 100000 params.lpbR params.lpbA
    (Float.exp2 (2 * params.lasLogI - 1).toFloat * params.qmin.toFloat) 16).orElse fun _ =>
      selectPolynomial n params.degree params.polyTries params.halfWidth params.expectedLines
    | IO.println "no poly"
  IO.println s!"poly {sel.coeffs} m={sel.m} y1={sel.y1} skew={skewness sel}"
  let ctx := mkCtx n sel params
  let lasParams : Las.LasParams :=
    { logI := params.lasLogI, lpbR := params.lpbR, lpbA := params.lpbA, mfbR := params.mfbR,
      mfbA := params.mfbA, fudge := fudge, preSlack := preSlack }
  let las0 := Las.mkLasCtx ctx lasParams
  let las := if skewOverride > 0 then { las0 with skew := skewOverride } else las0
  IO.println s!"skew used {las.skew}; FB rat {las.rat.primes.size} (large from {las.rat.largeStart}) alg {las.alg.primes.size} (large from {las.alg.largeStart}); I={las.I} J={las.J}"
  let qs := specialQs sel (if qstart > 0 then qstart else params.qmin) count
  let mut total := 0
  let mut bad := 0
  let mut badIdeal := 0
  let t0 ← IO.monoNanosNow
  let mut sc := Las.Scratch.new las
  for (q, ρ) in qs do
    let (rels, sc') := if v4 then Las.processQ4 las q ρ sc else
      if v3 then Las.processQ3 las q ρ sc else Las.processQWith las q ρ sc
    sc := sc'
    total := total + rels.size
    for r in rels do
      let ratProd := r.rat.foldl (fun acc (p, e) => acc * p ^ e) 1
      let algProd := r.alg.foldl (fun acc (p, _, e) => acc * p ^ e) 1
      let nr := (sel.ratNorm r.a (r.b : Int)).natAbs
      let na := (homEval sel.coeffs r.a r.b).natAbs
      if ratProd != nr || algProd != na then bad := bad + 1
      for (p, root, _) in r.alg do
        let ok := if root == p then r.b % p == 0 else (r.a - (r.b : Int) * (root : Int)) % (p : Int) == 0
        if !ok then
          badIdeal := badIdeal + 1
          if badIdeal ≤ 5 then IO.println s!"bad ideal ({p}, {root}) for a={r.a} b={r.b}"
  let t1 ← IO.monoNanosNow
  IO.println s!"{qs.size} special-q: {total} relations ({bad} wrong, {badIdeal} bad ideals) in {(t1 - t0) / 1000000} ms ({(t1 - t0) / 1000 / max 1 qs.size} us per q)"

/-- The GNFS pipeline with the lattice siever, step by step. -/
def lasPipeline (n : Nat) (threads : Nat) (maxRounds : Nat) : IO Unit := do
  let params := chooseParams (GNFS.decimalDigits n)
  let params := { params with lpMult := 2 ^ (max params.lpbR params.lpbA) /
      (min params.ratBound params.algBound) + 1 }
  let some sel := selectPolynomial n params.degree params.polyTries params.halfWidth
    params.expectedLines | IO.println "no poly"
  let some st := GNFS.mkSetup n sel | IO.println "setup failed"
  let ctx := mkCtx n sel params
  let lasParams : Las.LasParams :=
    { logI := params.lasLogI, lpbR := params.lpbR, lpbA := params.lpbA, mfbR := params.mfbR,
      mfbA := params.mfbA }
  let las := Las.mkLasCtx ctx lasParams
  let some p := inertPrime st.g 1000003 | IO.println "no inert prime"
  IO.println s!"chars {ctx.fb.chars.size} (first {ctx.fb.chars[0]!}), lpR {ctx.lpR} lpA {ctx.lpA}"
  let t0 ← IO.monoNanosNow
  let mut coll : GNFS.Collection := {}
  let mut round := 0
  let mut ready := false
  while !ready && round < maxRounds do
    round := round + 1
    coll ← IO.lazyPure fun _ => GNFS.collectRoundLas las params threads 400 coll
    if round % 10 == 0 then
      let rels := coll.rels
      let (rows, numCols) := GNFS.buildRows ctx.fb rels
      let kept := PrimeFactorLean.GF2.removeSingletons numCols rows
      let active := GNFS.activeColumns numCols rows kept
      let t1 ← IO.monoNanosNow
      IO.println s!"round {round} q={coll.nextQ}: rels {rels.size} cols {numCols} kept {kept.size} active {active} ({(t1 - t0) / 1000000} ms)"
      (← IO.getStdout).flush
      ready := GNFS.matrixReady ctx params rels
  if !ready then
    IO.println "not ready"
    return
  let rels := coll.rels
  let (rows, numCols) := GNFS.buildRows ctx.fb rels
  let t1 ← IO.monoNanosNow
  let deps ← IO.lazyPure fun _ => PrimeFactorLean.Lanczos.dependencies numCols rows 64 threads
  let t2 ← IO.monoNanosNow
  IO.println s!"Lanczos: {deps.size} deps in {(t2 - t1) / 1000000} ms"
  let mut tried := 0
  for dep in deps do
    tried := tried + 1
    let rs := dep.toList.map fun i => rels[i]!
    -- even parity check
    let mut cnt : Std.HashMap Nat Nat := {}
    for i in dep do
      for c in rows[i]! do cnt := cnt.insert c (cnt.getD c 0 + 1)
    let even := cnt.fold (fun ok _ v => ok && v % 2 == 0) true
    let ry := GNFS.rationalRoot rs
    match GNFS.congruence st rs p with
    | none => IO.println s!"dep {tried}: {dep.size} rels, even {even}, rational root {ry.isSome}: congruence failed"
    | some sc =>
      match sc.factor with
      | some d => IO.println s!"dep {tried}: factor {d.val}"; return
      | none => IO.println s!"dep {tried}: trivial congruence"

/-- Survivor counts per stage (both initializations) on a few special-`q`. -/
def lasCounts (n : Nat) (count fudge pre : Nat) : IO Unit := do
  let params := chooseParams (GNFS.decimalDigits n)
  let params := { params with lpMult := 2 ^ (max params.lpbR params.lpbA) /
      (min params.ratBound params.algBound) + 1 }
  let some sel := PolySelect.selectCollision n params.degree params.psP params.psNq params.psIncr
    params.psAdMax params.psKeep 16 100000 params.lpbR params.lpbA
    (Float.exp2 (2 * params.lasLogI - 1).toFloat * params.qmin.toFloat) 16 | IO.println "no poly"
  let ctx := mkCtx n sel params
  let lasParams : Las.LasParams :=
    { logI := params.lasLogI, lpbR := params.lpbR, lpbA := params.lpbA, mfbR := params.mfbR,
      mfbA := params.mfbA, fudge := fudge, preSlack := pre }
  let las := Las.mkLasCtx ctx lasParams
  let qs := specialQs sel params.qmin count
  let len := las.I * las.J
  let mut tot : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0]
  for (q, ρ) in qs do
    let (u, v) := reduceLattice q ρ las.skew
    let (ua, ub, va, vb) := (u.1, u.2, v.1, v.2)
    let Rr := Las.latticeRoots las.rat ua ub va vb
    let Ra := Las.latticeRoots las.alg ua ub va vb
    let thrR := Las.rowThresholds las q ua ub va vb params.mfbR false
    let thrA := Las.rowThresholds las q ua ub va vb params.mfbA true
    let z := Las.zeroBytes (len + 1)
    let oR := Las.sieveSide las las.rat Rr (Las.fillRows las z thrR)
    let oA := Las.sieveSide las las.alg Ra (Las.fillRows las z thrA)
    let sR := Las.sieveSide las las.rat Rr (Las.fillSegments las z false q ua ub va vb params.mfbR)
    let sA := Las.sieveSide las las.alg Ra (Las.fillSegments las z true q ua ub va vb params.mfbA)
    let cnt (b : ByteArray) : Nat := Id.run do
      let mut c := 0
      for i in [0:len] do if b.get! i ≥ 128 then c := c + 1
      return c
    let o0 := Las.survivors oR oA len
    let s0 := Las.survivors sR sA len
    let o1 := Las.prefilterRows las q ua ub va vb thrR thrA oR oA o0
    let s1 := Las.prefilterSegs las q ua ub va vb sR sA s0
    let vals := #[cnt oR, cnt oA, o0.size, o1.size, cnt sR, cnt sA, s0.size, s1.size]
    tot := (Array.range 8).map fun i => tot[i]! + vals[i]!
  let k := max 1 qs.size
  IO.println s!"per q (rows):     R>=128 {tot[0]! / k}  A>=128 {tot[1]! / k}  both {tot[2]! / k}  prefiltered {tot[3]! / k}"
  IO.println s!"per q (segments): R>=128 {tot[4]! / k}  A>=128 {tot[5]! / k}  both {tot[6]! / k}  prefiltered {tot[7]! / k}"
