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
def lasPar (n per : Nat) (ts : List Nat) (jDiv : Nat := 2) : IO Unit := do
  let params := chooseParams (GNFS.decimalDigits n)
  let params := { params with lpMult := 2 ^ (max params.lpbR params.lpbA) /
      (min params.ratBound params.algBound) + 1 }
  let some sel := PolySelect.selectCollision n params.degree params.psP params.psNq params.psIncr
    params.psAdMax params.psKeep 16 100000 params.lpbR params.lpbA
    (Float.exp2 (2 * params.lasLogI - 1).toFloat * params.qmin.toFloat) 16 | IO.println "no poly"
  let ctx := mkCtx n sel params
  let lasParams : Las.LasParams :=
    { logI := params.lasLogI, lpbR := params.lpbR, lpbA := params.lpbA, mfbR := params.mfbR,
      mfbA := params.mfbA, fudge := params.lasFudge, jDiv := jDiv }
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

/-- Read a polynomial in CADO-NFS format (`n:`, `c0:` …, `Y0:`, `Y1:`). -/
def readCadoPoly (path : String) : IO (Nat × Selection) := do
  let lines ← IO.FS.lines path
  let mut n := 0
  let mut cs : Array Int := #[]
  let mut y0 : Int := 0
  let mut y1 : Nat := 1
  for l in lines do
    match l.splitOn ":" with
    | [k, v] =>
      let v := v.trim
      if k == "n" then n := v.toNat!
      else if k == "Y0" then y0 := v.toInt!
      else if k == "Y1" then y1 := v.toNat!
      else if k.startsWith "c" then
        let i := (k.drop 1).toNat!
        while cs.size ≤ i do cs := cs.push 0
        cs := cs.set! i v.toInt!
    | _ => pure ()
  return (n, { coeffs := cs, m := (-y0).toNat, y1 := y1 })

/-- Sieve `count` special-`q` from `q0` with a given polynomial (single thread) and
write the relations as `a,b` lines, for comparison with CADO-NFS's `las`. -/
def lasFile (path : String) (q0 count : Nat) (out : String) (kvs : List String) : IO Unit := do
  let (n, sel) ← readCadoPoly path
  let params := chooseParams (GNFS.decimalDigits n)
  let get (key : String) (d : Nat) : Nat := (kvs.findSome? fun kv => match kv.splitOn "=" with
    | [k, v] => if k == key then v.toNat? else none
    | _ => none).getD d
  let params := { params with lpMult := 2 ^ (max params.lpbR params.lpbA) /
      (min params.ratBound params.algBound) + 1 }
  let ctx := mkCtx n sel params
  let lasParams : Las.LasParams :=
    { logI := get "logI" params.lasLogI, lpbR := get "lpbR" params.lpbR, lpbA := get "lpbA" params.lpbA,
      mfbR := get "mfbR" params.mfbR, mfbA := get "mfbA" params.mfbA,
      fudge := get "fudge" params.lasFudge, jDiv := get "jDiv" 2,
      preSlack := get "pre" 6, sieveFrom := get "from" 30 }
  let v := get "v" 0
  let las := Las.mkLasCtx ctx lasParams
  IO.println s!"FB rat {las.rat.primes.size} alg {las.alg.primes.size} (powers {las.rat.pw.size}, {las.alg.pw.size}); I={las.I} J={las.J} skew {las.skew}"
  let qs := specialQs sel q0 count
  let h ← IO.FS.Handle.mk out .write
  let mut sc := Las.Scratch.new las
  let mut total := 0
  let t0 ← IO.monoNanosNow
  if v == 14 then
    let (rels, _) := Las.processQs14 las (get "slack" 2) qs sc
    for r in rels do
      h.putStrLn s!"{r.a},{r.b}"
    total := rels.size
  else
    for (q, ρ) in qs do
      let (rels, sc') := if v == 5 then Las.processQ5 las q ρ sc else
        if v == 6 then Las.processQ6 las q ρ sc else
        if v == 7 then Las.processQ7 las q ρ sc else
        if v == 8 then Las.processQ8 las (get "slack" 2) q ρ sc else
        if v == 9 then Las.processQ9 las (get "slack" 3) q ρ sc else
        if v == 10 then Las.processQ10 las (get "slack" 3) q ρ sc else
        if v == 11 then Las.processQ11 las q ρ sc else
        if v == 12 then Las.processQ12 las q ρ sc else
        if v == 13 then Las.processQ13 las (get "slack" 2) q ρ sc else Las.processQWith las q ρ sc
      sc := sc'
      total := total + rels.size
      for r in rels do
        h.putStrLn s!"{r.a},{r.b} {q} {ρ}"
  let t1 ← IO.monoNanosNow
  IO.println s!"{qs.size} special-q (last q {qs.back?.map (·.1)}): {total} relations in {(t1 - t0) / 1000000} ms ({(t1 - t0) / 1000 / max 1 qs.size} us per q)"

/-- The cheap checks of `Las.largePrimes` (no factoring): `0` fails, `1` needs no
split, `2` needs a split. -/
def lpClass (u lpb mfb lim : Nat) : Nat :=
  if u == 1 then 1
  else if u >>> mfb != 0 then 0
  else if u >>> lpb == 0 then 1
  else if u < lim * lim then 0
  else if u >>> 52 == 0 && u % 2 == 1 && SIQS.sprp2 u.toUInt64 then 0
  else 2

/-- Survivor statistics of one special-`q` (`processQ5` with counters): scan,
prefilter, cheap cofactor checks on each side, splits needed, relations. -/
def lasStats (path : String) (q0 count : Nat) (kvs : List String) : IO Unit := do
  let (n, sel) ← readCadoPoly path
  let params := chooseParams (GNFS.decimalDigits n)
  let get (key : String) (d : Nat) : Nat := (kvs.findSome? fun kv => match kv.splitOn "=" with
    | [k, v] => if k == key then v.toNat? else none
    | _ => none).getD d
  let params := { params with lpMult := 2 ^ (max params.lpbR params.lpbA) /
      (min params.ratBound params.algBound) + 1 }
  let ctx := mkCtx n sel params
  let lasParams : Las.LasParams :=
    { logI := get "logI" params.lasLogI, lpbR := params.lpbR, lpbA := params.lpbA,
      mfbR := params.mfbR, mfbA := params.mfbA, fudge := get "fudge" 4, jDiv := 2,
      preSlack := get "pre" 6, sieveFrom := get "from" 2 }
  let ctx := Las.mkLasCtx ctx lasParams
  let qs := specialQs sel q0 count
  let mut st : Array Nat := Array.replicate 14 0
  let mut hist : Array Nat := Array.replicate 41 0
  let mut histA : Array Nat := Array.replicate 41 0
  for (q, ρ) in qs do
    let (u, v) := reduceLattice q ρ ctx.skew
    let (ua, ub, va, vb) := (u.1, u.2, v.1, v.2)
    let len := ctx.I * ctx.J
    let sc := Las.Scratch.new ctx
    let Rr := Las.latticeRoots ctx.rat ua ub va vb
    let Ra := Las.latticeRoots ctx.alg ua ub va vb
    let Pr := Las.powerRoots ctx.rat ua ub va vb
    let Pa := Las.powerRoots ctx.alg ua ub va vb
    let exR := if get "ex" 1 == 1 then Las.rowExtras ctx ctx.rat Rr else #[]
    let exA := if get "ex" 1 == 1 then Las.rowExtras ctx ctx.alg Ra else #[]
    let (fR, biasR) := Las.fillSegments ctx sc.bufR false q ua ub va vb ctx.params.mfbR exR
    let (fA, biasA) := Las.fillSegments ctx sc.bufA true q ua ub va vb ctx.params.mfbA exA
    let bufR := Las.sieveSide ctx ctx.rat Rr fR
    let bufA := Las.sieveSide ctx ctx.alg Ra fA
    let bufR := if get "pw" 1 == 1 then Las.sievePowers ctx ctx.rat Pr bufR else bufR
    let bufA := if get "pw" 1 == 1 then Las.sievePowers ctx ctx.alg Pa bufA else bufA
    let surv0 := Las.dropSmallGcd ctx (Las.survivors bufR bufA len)
    let surv := if get "gap" 0 > 0 then
        Las.prefilterGap ctx q ua ub va vb bufR bufA biasR biasA (get "gap" 0 - 1) surv0
      else Las.prefilterExact ctx q ua ub va vb bufR bufA biasR biasA surv0
    st := st.modify 0 (· + surv0.size)
    st := st.modify 1 (· + surv.size)
    let (lab, rowStart) := Las.labelSurvivors ctx (Las.zeroRows ctx bufA) surv
    let bits := Las.markBits sc.bits surv true
    let listsR := Las.groupLabelled ctx surv lab rowStart (Las.resieveSideB ctx ctx.rat Rr bits #[])
    let listsA := Las.groupLabelled ctx surv lab rowStart (Las.resieveSideB ctx ctx.alg Ra bits #[])
    for k in [0:surv.size] do
      let pos := surv[k]!
      let I := ctx.I
      let j := pos / I
      let c := pos % I
      let i : Int := (c : Int) - (I / 2 : Nat)
      let a0 := i * ua + (j : Int) * va
      let b0 := i * ub + (j : Int) * vb
      let (a, b) := if b0 < 0 then (-a0, -b0) else (a0, b0)
      if b == 0 || Nat.gcd a.natAbs b.natAbs != 1 then
        st := st.modify 2 (· + 1); continue
      let mut u := (sel.ratNorm a b).natAbs
      for kk in Las.smallHits ctx.rat Rr c.toUInt64 j.toUInt64 I.toUInt64 0 ctx.rat.largeStart [] do
        u := (Las.stripNat u ctx.rat.primes[kk]!).1
      for kk in listsR[k]! do
        u := (Las.stripNat u ctx.rat.primes[kk]!).1
      let cr := lpClass u ctx.params.lpbR ctx.params.mfbR ctx.limR
      -- the estimate of the prefilter for this survivor
      let csF := Las.coeffsF ctx
      let seg := j * (I / 64) + c / 64
      let estR := Las.normBits false csF (csF.size - 1) (Arith.intF ua) (Arith.intF ub) (Arith.intF va)
        (Arith.intF vb) (Arith.nf sel.m) (Arith.nf sel.y1) (Arith.nf q) (Arith.nf c - Arith.nf (I / 2))
        (Arith.nf j) - ((bufR.get! pos).toUInt64.toFloat - (biasR.get! seg).toUInt64.toFloat)
      let actual := if u == 1 then 0 else u.log2 + 1
      let diff : Int := (estR.round.toUInt64.toNat : Int) - (actual : Int)
      if cr == 0 then
        if u >>> ctx.params.mfbR != 0 then st := st.modify 11 (· + 1)
        else if u < ctx.limR * ctx.limR then st := st.modify 12 (· + 1)
        else st := st.modify 13 (· + 1)
      let mut z := (Las.stripNat (homEval sel.coeffs a b).natAbs q).1
      for kk in Las.smallHits ctx.alg Ra c.toUInt64 j.toUInt64 I.toUInt64 0 ctx.alg.largeStart [] do
        z := (Las.stripNat z ctx.alg.primes[kk]!).1
      for kk in listsA[k]! do
        z := (Las.stripNat z ctx.alg.primes[kk]!).1
      let ca := lpClass z ctx.params.lpbA ctx.params.mfbA ctx.limA
      if cr == 0 then st := st.modify 3 (· + 1)
      if ca == 0 then st := st.modify 4 (· + 1)
      if cr != 0 && ca != 0 then
        st := st.modify 5 (· + 1)
        if cr == 2 then st := st.modify 6 (· + 1)
        if ca == 2 then st := st.modify 7 (· + 1)
        let okR := cr == 1 || (SIQS.splitCofactor u (2 ^ ctx.params.lpbR)).isSome
        let okA := ca == 1 || (SIQS.splitCofactor z (2 ^ ctx.params.lpbA)).isSome
        if okR && okA then
          st := st.modify 8 (· + 1)
          hist := hist.modify (min 40 (max 0 (diff + 20)).toNat) (· + 1)
          let estA := Las.normBits true csF (csF.size - 1) (Arith.intF ua) (Arith.intF ub) (Arith.intF va)
            (Arith.intF vb) (Arith.nf sel.m) (Arith.nf sel.y1) (Arith.nf q) (Arith.nf c - Arith.nf (I / 2))
            (Arith.nf j) - ((bufA.get! pos).toUInt64.toFloat - (biasA.get! seg).toUInt64.toFloat)
          let actualA := if z == 1 then 0 else z.log2 + 1
          let diffA : Int := (estA.round.toUInt64.toNat : Int) - (actualA : Int)
          histA := histA.modify (min 40 (max 0 (diffA + 20)).toNat) (· + 1)
        if cr == 2 && !okR then st := st.modify 9 (· + 1)
        if ca == 2 && !okA then st := st.modify 10 (· + 1)
  IO.println s!"{qs.size} q: scan {st[0]!}, prefilter {st[1]!}, coprime/b=0 fail {st[2]!}, rat check fail {st[3]!}, alg check fail {st[4]!}, both pass {st[5]!} (rat split {st[6]!}, alg split {st[7]!}), relations {st[8]!}, rat split fail {st[9]!}, alg split fail {st[10]!}; rat fails: too big {st[11]!}, dead zone {st[12]!}, prime {st[13]!}"
  IO.println s!"relations: estimate - actual (rational, bits, from -20): {hist}"
  IO.println s!"relations: estimate - actual (algebraic, bits, from -20): {histA}"

/-- Siever throughput with a given polynomial: `T` tasks on disjoint special-`q`
(each `per` of them), for each `T` in `ts`; `v=8` uses `processQ8`. -/
def lasParFile (path : String) (q0 per : Nat) (ts : List Nat) (kvs : List String) : IO Unit := do
  let (n, sel) ← readCadoPoly path
  let params := chooseParams (GNFS.decimalDigits n)
  let get (key : String) (d : Nat) : Nat := (kvs.findSome? fun kv => match kv.splitOn "=" with
    | [k, v] => if k == key then v.toNat? else none
    | _ => none).getD d
  let params := { params with lpMult := 2 ^ (max params.lpbR params.lpbA) /
      (min params.ratBound params.algBound) + 1 }
  let ctx := mkCtx n sel params
  let lasParams : Las.LasParams :=
    { logI := get "logI" params.lasLogI, lpbR := params.lpbR, lpbA := params.lpbA,
      mfbR := params.mfbR, mfbA := params.mfbA, fudge := get "fudge" params.lasFudge,
      jDiv := get "jDiv" 2, sieveFrom := get "from" 30 }
  let las := Las.mkLasCtx ctx lasParams
  let v := get "v" 0
  let slack := get "slack" 3
  let maxT := ts.foldl max 1
  let all := specialQs sel q0 (per * maxT)
  for t in ts do
    let t0 ← IO.monoNanosNow
    let total ← IO.lazyPure fun _ => ((List.range t).map fun i => Task.spawn fun _ => Id.run do
      let mut sc := Las.Scratch.new las
      let mut c := 0
      for k in [0:per] do
        let (q, ρ) := all[i * per + k]!
        let (rels, sc') := if v == 8 then Las.processQ8 las slack q ρ sc else
          if v == 9 then Las.processQ9 las slack q ρ sc else
          if v == 10 then Las.processQ10 las slack q ρ sc else
          if v == 11 then Las.processQ11 las q ρ sc else
          if v == 13 then Las.processQ13 las slack q ρ sc else
      if v == 12 then Las.processQ12 las q ρ sc else Las.processQWith las q ρ sc
        sc := sc'
        c := c + rels.size
      return c).foldl (fun acc tk => acc + tk.get) 0
    let t1 ← IO.monoNanosNow
    let ms := (t1 - t0) / 1000000
    IO.println s!"tasks {t}: {t * per} special-q, {total} rels in {ms} ms: {ms * t * 1000 / (t * per)} us CPU per q, {total * 1000 / max 1 ms} rels/s"

/-- A busy loop of `n` steps (machine words). -/
def busy (seed n : UInt64) : UInt64 := Id.run do
  let mut x := seed
  for _ in [0:n.toNat] do
    x := x * 6364136223846793005 + 1442695040888963407
  return x

/-- Wall time of `t` tasks each running `busy` (parallelism check). -/
def taskScaling (ts : List Nat) (n : Nat) : IO Unit := do
  for t in ts do
    let t0 ← IO.monoNanosNow
    let r ← IO.lazyPure fun _ => ((List.range t).map fun i =>
      Task.spawn fun _ => busy i.toUInt64 n.toUInt64).foldl (fun acc tk => acc ^^^ tk.get) 0
    let t1 ← IO.monoNanosNow
    IO.println s!"tasks {t}: {(t1 - t0) / 1000000} ms ({r})"


/-- Average wall time of a batch of `t` trivial tasks (spawn + get), `reps` times. -/
def taskOverhead (t reps : Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut acc : UInt64 := 0
  for r in [0:reps] do
    let x ← IO.lazyPure fun _ => ((List.range t).map fun i =>
      Task.spawn fun _ => busy (i + r).toUInt64 100).foldl (fun acc tk => acc ^^^ tk.get) 0
    acc := acc ^^^ x
  let t1 ← IO.monoNanosNow
  IO.println s!"{t} trivial tasks: {(t1 - t0) / reps / 1000} us per batch ({acc})"
