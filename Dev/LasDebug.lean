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
def lasDebug (n : Nat) (count : Nat) (fudge : Nat := 4) (skewOverride : Nat := 0)
    (preSlack : Nat := 6) (qstart : Nat := 0) (v5 : Bool := false) (v6 : Bool := false)
    (logI : Nat := 0) : IO Unit := do
  let params := chooseParams (GNFS.decimalDigits n)
  let params := if logI > 0 then { params with lasLogI := logI } else params
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
    let (rels, sc') := if v6 then Las.processQ6 las q ρ sc else
      if v5 then Las.processQ5 las q ρ sc else Las.processQWith las q ρ sc
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
    coll ← IO.lazyPure fun _ => (GNFS.collectRoundLas las params threads 400 coll []).1
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

/-- Siever throughput with `T` parallel tasks on disjoint special-`q` (each task
sieves `per` special-`q` with its own buffers). -/
def lasPar (n per : Nat) (ts : List Nat) : IO Unit := do
  let params := chooseParams (GNFS.decimalDigits n)
  let params := { params with lpMult := 2 ^ (max params.lpbR params.lpbA) /
      (min params.ratBound params.algBound) + 1 }
  let some sel := PolySelect.selectCollision n params.degree params.psP params.psNq params.psIncr
    params.psAdMax params.psKeep 16 100000 params.lpbR params.lpbA
    (Float.exp2 (2 * params.lasLogI - 1).toFloat * params.qmin.toFloat) 16 | IO.println "no poly"
  let ctx := mkCtx n sel params
  let lasParams : Las.LasParams :=
    { logI := params.lasLogI, lpbR := params.lpbR, lpbA := params.lpbA, mfbR := params.mfbR,
      mfbA := params.mfbA, fudge := params.lasFudge }
  let las := Las.mkLasCtx ctx lasParams
  let all := specialQs sel params.qmin (per * 32)
  for t in ts do
    let t0 ← IO.monoNanosNow
    let total ← IO.lazyPure fun _ => ((List.range t).map fun i => Task.spawn fun _ => Id.run do
      let mut sc := Las.Scratch.new las
      let mut c := 0
      for k in [0:per] do
        let (q, ρ) := all[i * per + k]!
        let (rels, sc') := Las.processQWith las q ρ sc
        sc := sc'
        c := c + rels.size
      return c).foldl (fun acc tk => acc + tk.get) 0
    let t1 ← IO.monoNanosNow
    let ms := (t1 - t0) / 1000000
    IO.println s!"tasks {t}: {t * per} special-q, {total} rels in {ms} ms: {ms * t * 1000 / (t * per)} us CPU per q"
