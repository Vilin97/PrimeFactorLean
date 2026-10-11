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
      let las := if get "copy" 1 == 1 then las.copy else las
      let mut sc := Las.Scratch.new las
      let mut c := 0
      if v == 14 then
        return (Las.processQs14 las slack (all.extract (i * per) (i * per + per)) sc).1.size
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

/-- The exact cofactors `(u, z)` of a survivor after dividing out every found
factor-base prime (as `factorSurvivor2`; `none` for trivial survivors). -/
def exactCofactors (ctx : Las.LasCtx) (q : Nat) (ua ub va vb : Int) (Rr Ra : Array Nat)
    (listR listA : List Nat) (pos : Nat) : Option (Nat × Nat) := Id.run do
  let I := ctx.I
  let j := pos / I
  let c := pos % I
  let i : Int := (c : Int) - (I / 2 : Nat)
  let a0 := i * ua + (j : Int) * va
  let b0 := i * ub + (j : Int) * vb
  let (a, b) := if b0 < 0 then (-a0, -b0) else (a0, b0)
  if b == 0 || Nat.gcd a.natAbs b.natAbs != 1 then return none
  let bn := b.natAbs
  let sel := ctx.base.sel
  let mut u := (sel.ratNorm a b).natAbs
  let side := ctx.rat
  for k in Las.smallHits side Rr c.toUInt64 j.toUInt64 I.toUInt64 0 side.largeStart [] do
    u := (Las.stripNat u side.primes[k]!).1
  for k in listR do
    u := (Las.stripNat u side.primes[k]!).1
  let (z0, _) := Las.stripNat (homEval sel.coeffs a b).natAbs q
  let mut z := z0
  let sideA := ctx.alg
  for k in Las.smallHits sideA Ra c.toUInt64 j.toUInt64 I.toUInt64 0 sideA.largeStart [] do
    let p := sideA.primes[k]!
    let r := sideA.roots[k]!
    let ok := Ra[k]! < p || (if r == p then bn % p == 0 else (a - b * (r : Int)) % (p : Int) == 0)
    if ok then z := (Las.stripNat z p).1
  for k in listA do
    z := (Las.stripNat z sideA.primes[k]!).1
  return some (u, z)

/-- Where a survivor ends in `factorSurvivor2`: `0` trivial or `gcd(a, b) ≠ 1`,
`1` rational cofactor rejected by the cheap checks, `2` algebraic, `3` algebraic
split failed, `4` rational split failed, `5` relation; with the number of splits
attempted. -/
def fs2Class (ctx : Las.LasCtx) (q : Nat) (ua ub va vb : Int) (Rr Ra : Array Nat)
    (listR listA : List Nat) (pos : Nat) : Nat × Nat := Id.run do
  let I := ctx.I
  let j := pos / I
  let c := pos % I
  let i : Int := (c : Int) - (I / 2 : Nat)
  let a0 := i * ua + (j : Int) * va
  let b0 := i * ub + (j : Int) * vb
  let (a, b) := if b0 < 0 then (-a0, -b0) else (a0, b0)
  if b == 0 then return (0, 0)
  if Nat.gcd a.natAbs b.natAbs != 1 then return (0, 0)
  let bn := b.natAbs
  let sel := ctx.base.sel
  let nr : Int := sel.ratNorm a b
  if nr == 0 then return (0, 0)
  let mut u := nr.natAbs
  let side := ctx.rat
  for k in Las.smallHits side Rr c.toUInt64 j.toUInt64 I.toUInt64 0 side.largeStart [] do
    u := (Las.stripNat u side.primes[k]!).1
  for k in listR do
    u := (Las.stripNat u side.primes[k]!).1
  let cr := Las.cofactorClass u ctx.params.lpbR ctx.params.mfbR ctx.limR
  if cr == 0 then return (1, 0)
  let na := homEval sel.coeffs a b
  if na == 0 then return (0, 0)
  let (z0, eq) := Las.stripNat na.natAbs q
  if eq == 0 then return (0, 0)
  let mut z := z0
  let sideA := ctx.alg
  for k in Las.smallHits sideA Ra c.toUInt64 j.toUInt64 I.toUInt64 0 sideA.largeStart [] do
    let p := sideA.primes[k]!
    let r := sideA.roots[k]!
    let ok := Ra[k]! < p || (if r == p then bn % p == 0 else (a - b * (r : Int)) % (p : Int) == 0)
    if ok then z := (Las.stripNat z p).1
  for k in listA do
    z := (Las.stripNat z sideA.primes[k]!).1
  let ca := Las.cofactorClass z ctx.params.lpbA ctx.params.mfbA ctx.limA
  if ca == 0 then return (2, 0)
  let splits := (if ca == 2 then 1 else 0)
  let some _ := Las.largePrimesOf ca z ctx.params.lpbA | return (3, splits)
  let splits := splits + (if cr == 2 then 1 else 0)
  let some _ := Las.largePrimesOf cr u ctx.params.lpbR | return (4, splits)
  return (5, splits)

/-- `processQs14` phase by phase on one thread: times and survivor counts. -/
def lasPhases (path : String) (q0 count : Nat) (kvs : List String) : IO Unit := do
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
      fudge := get "fudge" params.lasFudge, jDiv := get "jDiv" 2, sieveFrom := get "from" 30,
      fudgeA := get "fudgeA" 0, powMin := get "powMin" 0 }
  let slack := get "slack" 3
  let pair := get "pair" 1 == 1
  let fs := get "fs" 2
  let fs3 := fs == 3
  let las := Las.mkLasCtx ctx lasParams
  let las := { las with skew := get "skew" las.skew }
  let qs := specialQs sel q0 count
  let mut sc := Las.Scratch.new las
  let mut tm : Array Nat := Array.replicate 12 0
  let mut cnt : Array Nat := Array.replicate 12 0
  let mut tmX := 0
  let mut passR := 0
  let mut gates : Array Nat := Array.replicate 8 0
  let mut passB := 0
  let mut tmP : Array Nat := Array.replicate 4 0
  let mut gateMismatch := 0
  let mut tmG := 0
  let mut i := 0
  let len := las.I * las.J
  while i < qs.size do
    let grp := qs.extract i (i + 4)
    let t0 ← IO.monoNanosNow
    let bases ← IO.lazyPure fun _ => grp.map fun (q, ρ) =>
      let (u, v) := reduceLattice q ρ las.skew
      (u.1, u.2, v.1, v.2)
    let Rrs ← IO.lazyPure fun _ => Las.latticeRoots4 las.rat bases
    let Ras ← IO.lazyPure fun _ => Las.latticeRoots4 las.alg bases
    let t1 ← IO.monoNanosNow
    tm := tm.modify 0 (· + (t1 - t0))
    for jx in [0:grp.size] do
      let (q, ρ) := grp[jx]!
      let (ua, ub, va, vb) := bases[jx]!
      let Rr := Rrs[jx]!
      let Ra := Ras[jx]!
      let ⟨b1, b2, bits⟩ := sc
      let a0 ← IO.monoNanosNow
      let Pr ← IO.lazyPure fun _ => Las.powerRoots las.rat ua ub va vb
      let Pa ← IO.lazyPure fun _ => Las.powerRoots las.alg ua ub va vb
      let exR ← IO.lazyPure fun _ => Las.rowExtras las las.rat Rr
      let exA ← IO.lazyPure fun _ => Las.rowExtras las las.alg Ra
      let a1 ← IO.monoNanosNow
      let (fR, biasR) ← IO.lazyPure fun _ => Las.fillSegments las b1 false q ua ub va vb las.params.mfbR exR
      let (fA, biasA) ← IO.lazyPure fun _ => Las.fillSegments las b2 true q ua ub va vb las.params.mfbA exA
      let a2 ← IO.monoNanosNow
      let lR ← IO.lazyPure fun _ => Las.lineSieveSide las las.rat Rr fR
      let lA ← IO.lazyPure fun _ => Las.lineSieveSide las las.alg Ra fA
      let a3 ← IO.monoNanosNow
      let pR ← IO.lazyPure fun _ => Las.sievePowers las las.rat Pr lR
      let pA ← IO.lazyPure fun _ => Las.sievePowers las las.alg Pa lA
      let a4 ← IO.monoNanosNow
      let (bufR, RrB) ← IO.lazyPure fun _ => if pair then Las.sieveLargePaired las las.rat Rr pR
        else Las.sieveLargeCached las las.rat Rr pR
      let (bufA, RaB) ← IO.lazyPure fun _ => if pair then Las.sieveLargePaired las las.alg Ra pA
        else Las.sieveLargeCached las las.alg Ra pA
      let a5 ← IO.monoNanosNow
      let s0 ← IO.lazyPure fun _ => Las.survivors bufR bufA len
      let s1 ← IO.lazyPure fun _ => Las.dropSmallGcd las s0
      let a6 ← IO.monoNanosNow
      let surv ← IO.lazyPure fun _ => Las.prefilterGap4 las q ua ub va vb bufR bufA biasR biasA
        (Las.tinyPrimes las las.rat RrB) (Las.tinyPrimes las las.alg RaB) slack s1
      let a7 ← IO.monoNanosNow
      cnt := cnt.modify 0 (· + s0.size)
      cnt := cnt.modify 1 (· + s1.size)
      cnt := cnt.modify 2 (· + surv.size)
      tm := tm.modify 1 (· + (a1 - a0))
      tm := tm.modify 2 (· + (a2 - a1))
      tm := tm.modify 3 (· + (a3 - a2))
      tm := tm.modify 4 (· + (a4 - a3))
      tm := tm.modify 5 (· + (a5 - a4))
      tm := tm.modify 6 (· + (a6 - a5))
      tm := tm.modify 7 (· + (a7 - a6))
      if surv.isEmpty then
        sc := ⟨bufR, bufA, bits⟩
        continue
      let (lab, rowStart) ← IO.lazyPure fun _ => Las.labelSurvivors las (Las.zeroRows las bufA) surv
      let bits ← IO.lazyPure fun _ => Las.markBits bits surv true
      let a8 ← IO.monoNanosNow
      let listsR ← IO.lazyPure fun _ => Las.groupLabelled las surv lab rowStart
        (if pair then Las.resievePaired las las.rat RrB bits #[] else Las.resieveCached las las.rat RrB bits #[])
      let listsA ← IO.lazyPure fun _ => Las.groupLabelled las surv lab rowStart
        (if pair then Las.resievePaired las las.alg RaB bits #[] else Las.resieveCached las las.alg RaB bits #[])
      let bits ← IO.lazyPure fun _ => Las.markBits bits surv false
      let a9 ← IO.monoNanosNow
      let mut rels := 0
      let bd ← IO.lazyPure fun _ => Las.mkBounds las q ua ub va vb RrB RaB
      if fs == 5 then
        let tg0 ← IO.monoNanosNow
        let pass ← IO.lazyPure fun _ => Las.gateAll las bd surv listsR listsA
        let tg1 ← IO.monoNanosNow
        tmG := tmG + (tg1 - tg0)
        for k in pass do
          if (Las.factorSurvivor2 las q ρ ua ub va vb RrB RaB listsR[k]! listsA[k]! surv[k]!).isSome then
            rels := rels + 1
      else
        for k in [0:surv.size] do
          let r := if fs3 then Las.factorSurvivor3 las bd q ρ ua ub va vb RrB RaB listsR[k]! listsA[k]! surv[k]!
            else if fs == 4 then Las.factorSurvivor4 las bd q ρ ua ub va vb RrB RaB listsR[k]! listsA[k]! surv[k]!
            else Las.factorSurvivor2 las q ρ ua ub va vb RrB RaB listsR[k]! listsA[k]! surv[k]!
          if r.isSome then rels := rels + 1
      let a10 ← IO.monoNanosNow
      -- the bounds alone (both sides, every survivor) and the exact path alone
      let nb ← IO.lazyPure fun _ => Id.run do
        let mut n := 0
        for k in [0:surv.size] do
          let eR := Las.cofactorBound las bd true listsR[k]! surv[k]!
          let eA := Las.cofactorBound las bd false listsA[k]! surv[k]!
          if !Las.hopeless eR bd.hiR bd.loR bd.gapR then
            n := n + 1000000
            if !Las.hopeless eA bd.hiA bd.loA bd.gapA then n := n + 1
        return n
      passR := passR + nb / 1000000
      passB := passB + nb % 1000000
      let a11 ← IO.monoNanosNow
      let nx ← IO.lazyPure fun _ => Id.run do
        let mut n := 0
        for k in [0:surv.size] do
          if (exactCofactors las q ua ub va vb RrB RaB listsR[k]! listsA[k]! surv[k]!).isSome then n := n + 1
        return n
      let a12 ← IO.monoNanosNow
      let mut passOld : Array Nat := #[]
      for k in [0:surv.size] do
        let g := Las.survivorGate las bd listsR[k]! listsA[k]! surv[k]!
        gates := gates.modify g (· + 1)
        if g ≥ 4 then passOld := passOld.push k
      if passOld != Las.gateAll las bd surv listsR listsA then gateMismatch := gateMismatch + 1
      let I := las.I
      let s1 ← IO.lazyPure fun _ => Id.run do
        let mut acc : Float := 0
        for k in [0:surv.size] do
          let pos := surv[k]!
          acc := acc + Las.smallLogsP bd.tabR las.rat.pinvLim las.rat.lg2 las.rat.sieveStart
            ((pos % I).toUInt64 - (I / 2).toUInt64) (pos / I).toUInt64 I.toUInt64 0 0
        return acc
      let a13 ← IO.monoNanosNow
      let s2 ← IO.lazyPure fun _ => Id.run do
        let mut acc : Float := 0
        for k in [0:surv.size] do
          let pos := surv[k]!
          acc := acc + Las.tinyRatU bd.tq (pos % I).toUInt64 (pos / I).toUInt64 (I / 2).toUInt64 0 0
        return acc
      let a14 ← IO.monoNanosNow
      let s3 ← IO.lazyPure fun _ => Id.run do
        let mut acc : Float := 0
        for k in [0:surv.size] do
          let pos := surv[k]!
          acc := acc + Las.tinyAlgU bd.tq (pos % I).toUInt64 (pos / I).toUInt64 (I / 2).toUInt64 0 0
        return acc
      let a15 ← IO.monoNanosNow
      let s4 ← IO.lazyPure fun _ => Id.run do
        let mut acc := 0
        for k in [0:surv.size] do
          let pos := surv[k]!
          acc := acc + (Las.smallHits las.rat RrB (pos % I).toUInt64 (pos / I).toUInt64 I.toUInt64 0 las.rat.largeStart []).length
        return acc
      let a16 ← IO.monoNanosNow
      if s1 + s2 + s3 < 0 then IO.println "never"
      cnt := cnt.modify 11 (· + s4)
      tmP := tmP.modify 0 (· + (a13 - a12))
      tmP := tmP.modify 1 (· + (a14 - a13))
      tmP := tmP.modify 2 (· + (a15 - a14))
      tmP := tmP.modify 3 (· + (a16 - a15))
      cnt := cnt.modify 11 (· + nx)
      tm := tm.modify 11 (· + (a11 - a10))
      tm := tm.modify 0 (· + 0)
      tmX := tmX + (a12 - a11)
      for k in [0:surv.size] do
        let (cl, sp) := fs2Class las q ua ub va vb RrB RaB listsR[k]! listsA[k]! surv[k]!
        cnt := cnt.modify (4 + cl) (· + 1)
        cnt := cnt.modify 10 (· + sp)
      cnt := cnt.modify 3 (· + rels)
      tm := tm.modify 8 (· + (a8 - a7))
      tm := tm.modify 9 (· + (a9 - a8))
      tm := tm.modify 10 (· + (a10 - a9))
      sc := ⟨bufR, lab, bits⟩
    i := i + 4
  let nq := max 1 qs.size
  let us (k : Nat) : String := s!"{tm[k]! / 1000 / nq}"
  IO.println s!"{qs.size} special-q from {q0}: us/q roots {us 0}, powroots+extras {us 1}, fill {us 2}, line {us 3}, powers {us 4}, large {us 5}, survivors {us 6}, prefilter {us 7}, label {us 8}, resieve {us 9}, factor {us 10}"
  IO.println s!"per q: survivors {cnt[0]! / nq}, after gcd {cnt[1]! / nq}, after prefilter {cnt[2]! / nq}, relations {cnt[3]! * 100 / nq / 100}.{cnt[3]! * 100 / nq % 100}"
  IO.println s!"factorSurvivor2 outcomes (total): trivial {cnt[4]!}, rat class {cnt[5]!}, alg class {cnt[6]!}, alg split fail {cnt[7]!}, rat split fail {cnt[8]!}, ok {cnt[9]!}; splits {cnt[10]!}"
  IO.println s!"us/q: both bounds on every survivor {us 11}, exact cofactors (no splits) on every survivor {tmX / 1000 / nq} ({cnt[11]!})"
  IO.println s!"per q: rational bound passed {passR / nq}, both {passB / nq}"
  IO.println s!"gate per q: rat bound {gates[0]! / nq}, rat class {gates[1]! / nq}, alg bound {gates[2]! / nq}, alg class {gates[3]! / nq}, passed (rat?/alg? undecided) {gates[4]! / nq} {gates[5]! / nq} {gates[6]! / nq} {gates[7]! / nq}"
  IO.println s!"gateAll differs from survivorGate on {gateMismatch} special-q; gateAll {tmG / 1000 / nq} us/q"
  IO.println s!"us/q on every survivor: smallLogs rat {tmP[0]! / 1000 / nq}, tinyRat {tmP[1]! / 1000 / nq}, tinyAlg {tmP[2]! / 1000 / nq}, smallHits rat {tmP[3]! / 1000 / nq}"

/-- The floating-point cofactor bounds against the exact cofactors over the
survivors of `count` special-q: histogram of `bound - log₂ cofactor` and the
survivors the bounds would wrongly reject. -/
def boundsCheck (path : String) (q0 count : Nat) : IO Unit := do
  let (n, sel) ← readCadoPoly path
  let params := chooseParams (GNFS.decimalDigits n)
  let params := { params with lpMult := 2 ^ (max params.lpbR params.lpbA) /
      (min params.ratBound params.algBound) + 1 }
  let ctx := mkCtx n sel params
  let lasParams : Las.LasParams :=
    { logI := params.lasLogI, lpbR := params.lpbR, lpbA := params.lpbA, mfbR := params.mfbR,
      mfbA := params.mfbA, fudge := params.lasFudge }
  let las := Las.mkLasCtx ctx lasParams
  let qs := specialQs sel q0 count
  let mut sc := Las.Scratch.new las
  let len := las.I * las.J
  -- differences in tenths of a bit, offset 100
  let mut histR : Array Nat := Array.replicate 201 0
  let mut histA : Array Nat := Array.replicate 201 0
  let mut wrongR := 0
  let mut wrongA := 0
  let mut total := 0
  let mut shown := 0
  for (q, ρ) in qs do
    let (u, v) := reduceLattice q ρ las.skew
    let (ua, ub, va, vb) := (u.1, u.2, v.1, v.2)
    let Rr := Las.latticeRoots las.rat ua ub va vb
    let Ra := Las.latticeRoots las.alg ua ub va vb
    let ⟨b1, b2, bits⟩ := sc
    let Pr := Las.powerRoots las.rat ua ub va vb
    let Pa := Las.powerRoots las.alg ua ub va vb
    let (fR, biasR) := Las.fillSegments las b1 false q ua ub va vb las.params.mfbR (Las.rowExtras las las.rat Rr)
    let (fA, biasA) := Las.fillSegments las b2 true q ua ub va vb las.params.mfbA (Las.rowExtras las las.alg Ra)
    let (bufR, RrB) := Las.sieveLargeCached las las.rat Rr (Las.sievePowers las las.rat Pr (Las.lineSieveSide las las.rat Rr fR))
    let (bufA, RaB) := Las.sieveLargeCached las las.alg Ra (Las.sievePowers las las.alg Pa (Las.lineSieveSide las las.alg Ra fA))
    let surv := Las.prefilterGap4 las q ua ub va vb bufR bufA biasR biasA (Las.tinyPrimes las las.rat RrB)
      (Las.tinyPrimes las las.alg RaB) 3 (Las.dropSmallGcd las (Las.survivors bufR bufA len))
    let (lab, rowStart) := Las.labelSurvivors las (Las.zeroRows las bufA) surv
    let bits := Las.markBits bits surv true
    let listsR := Las.groupLabelled las surv lab rowStart (Las.resieveCached las las.rat RrB bits #[])
    let listsA := Las.groupLabelled las surv lab rowStart (Las.resieveCached las las.alg RaB bits #[])
    let bits := Las.markBits bits surv false
    sc := ⟨bufR, lab, bits⟩
    let bd := Las.mkBounds las q ua ub va vb RrB RaB
    for k in [0:surv.size] do
      let some (cu, cz) := exactCofactors las q ua ub va vb RrB RaB listsR[k]! listsA[k]! surv[k]! | continue
      total := total + 1
      let eR := Las.cofactorBound las bd true listsR[k]! surv[k]!
      let eA := Las.cofactorBound las bd false listsA[k]! surv[k]!
      let lu := Float.log2 (cu.toFloat)
      let lz := Float.log2 (cz.toFloat)
      let dR := ((eR - lu) * 10 + 100).round
      let dA := ((eA - lz) * 10 + 100).round
      histR := histR.modify (min 200 (max 0 dR.toUInt64.toNat)) (· + 1)
      histA := histA.modify (min 200 (max 0 dA.toUInt64.toNat)) (· + 1)
      let okR := Las.cofactorClass cu las.params.lpbR las.params.mfbR las.limR != 0
      let okA := Las.cofactorClass cz las.params.lpbA las.params.mfbA las.limA != 0
      let hR := Las.hopeless eR bd.hiR bd.loR bd.gapR
      let hA := Las.hopeless eA bd.hiA bd.loA bd.gapA
      if okR && hR then
        wrongR := wrongR + 1
        if shown < 12 then
          shown := shown + 1
          IO.println s!"rat wrong: pos {surv[k]!} bound {eR} exact {lu} u {cu} list {listsR[k]!}"
      if okR && okA && hA then
        wrongA := wrongA + 1
        if shown < 24 then
          shown := shown + 1
          IO.println s!"alg wrong: pos {surv[k]!} bound {eA} exact {lz} z {cz} list {listsA[k]!}"
  IO.println s!"{total} survivors; wrongly rejected: rat {wrongR}, alg {wrongA}"
  let fmt (h : Array Nat) : String := Id.run do
    let mut out := ""
    for t in [0:201] do
      if h[t]! > 0 then out := out ++ s!" {(t : Int) - 100}:{h[t]!}"
    return out
  IO.println s!"rat (bound - exact, tenths of a bit):{fmt histR}"
  IO.println s!"alg:{fmt histA}"

/-- The algebraic word cofactor of `survivorGate` against the exact cofactor, for
the first survivors where the word is undecided. -/
def gateDebug (path : String) (q0 count : Nat) : IO Unit := do
  let (n, sel) ← readCadoPoly path
  let params := chooseParams (GNFS.decimalDigits n)
  let params := { params with lpMult := 2 ^ (max params.lpbR params.lpbA) /
      (min params.ratBound params.algBound) + 1 }
  let ctx := mkCtx n sel params
  let lasParams : Las.LasParams :=
    { logI := params.lasLogI, lpbR := params.lpbR, lpbA := params.lpbA, mfbR := params.mfbR,
      mfbA := params.mfbA, fudge := params.lasFudge }
  let las := Las.mkLasCtx ctx lasParams
  let qs := specialQs sel q0 count
  let mut sc := Las.Scratch.new las
  let len := las.I * las.J
  let mut shown := 0
  for (q, ρ) in qs do
    let (u, v) := reduceLattice q ρ las.skew
    let (ua, ub, va, vb) := (u.1, u.2, v.1, v.2)
    let Rr := Las.latticeRoots las.rat ua ub va vb
    let Ra := Las.latticeRoots las.alg ua ub va vb
    let ⟨b1, b2, bits⟩ := sc
    let Pr := Las.powerRoots las.rat ua ub va vb
    let Pa := Las.powerRoots las.alg ua ub va vb
    let (fR, biasR) := Las.fillSegments las b1 false q ua ub va vb las.params.mfbR (Las.rowExtras las las.rat Rr)
    let (fA, biasA) := Las.fillSegments las b2 true q ua ub va vb las.params.mfbA (Las.rowExtras las las.alg Ra)
    let (bufR, RrB) := Las.sieveLargeCached las las.rat Rr (Las.sievePowers las las.rat Pr (Las.lineSieveSide las las.rat Rr fR))
    let (bufA, RaB) := Las.sieveLargeCached las las.alg Ra (Las.sievePowers las las.alg Pa (Las.lineSieveSide las las.alg Ra fA))
    let surv := Las.prefilterGap4 las q ua ub va vb bufR bufA biasR biasA (Las.tinyPrimes las las.rat RrB)
      (Las.tinyPrimes las las.alg RaB) 3 (Las.dropSmallGcd las (Las.survivors bufR bufA len))
    let (lab, rowStart) := Las.labelSurvivors las (Las.zeroRows las bufA) surv
    let bits := Las.markBits bits surv true
    let listsR := Las.groupLabelled las surv lab rowStart (Las.resieveCached las las.rat RrB bits #[])
    let listsA := Las.groupLabelled las surv lab rowStart (Las.resieveCached las las.alg RaB bits #[])
    let bits := Las.markBits bits surv false
    sc := ⟨bufR, lab, bits⟩
    let bd := Las.mkBounds las q ua ub va vb RrB RaB
    for k in [0:surv.size] do
      let g := Las.survivorGate las bd listsR[k]! listsA[k]! surv[k]!
      if g == 4 || g == 6 then
        if shown ≥ 12 then continue
        shown := shown + 1
        let pos := surv[k]!
        let I := las.I
        let j := pos / I
        let c := pos % I
        let (cU, jU, IU) := (c.toUInt64, j.toUInt64, I.toUInt64)
        let x0 := cU - IU / 2
        let a64 := x0 * bd.ua64 + jU * bd.va64
        let b64 := x0 * bd.ub64 + jU * bd.vb64
        let d := bd.cs.size - 1
        let f64 := Las.hornerU bd.cs64 a64 b64 d (bd.cs64[d]!) 1
        let tA := Las.tinyAlgP bd.tq cU jU (IU / 2) 0 0 1 0
        let sA := Las.smallScan bd.tabA las.alg.pinvLim las.alg.lg2 las.alg.sieveStart x0 jU IU 0 0 1
        let i : Int := (c : Int) - (I / 2 : Nat)
        let a := i * ua + (j : Int) * va
        let b := i * ub + (j : Int) * vb
        let fx := homEval sel.coeffs a b
        let ex := exactCofactors las q ua ub va vb RrB RaB listsR[k]! listsA[k]! pos
        let pA := listsA[k]!.foldl (fun acc k => acc * las.alg.primes[k]!.toUInt64) 1
        let fabs := (if fx < 0 then -f64 else f64)
        let odd := bd.qU * tA.prod * sA.prod * pA
        let uw := (fabs >>> tA.v2) * Las.inv64 odd
        let uw := if tA.v2 == 0 then uw else uw &&& ((1 <<< (64 - tA.v2)) - 1)
        let iF := Arith.nf c - Arith.nf (I / 2)
        let jF := Arith.nf j
        let fF := Las.homEvalFA bd.cs (iF * bd.uaf + jF * bd.vaf) (iF * bd.ubf + jF * bd.vbf) d (bd.cs.get! d) 1
        let lA := listsA[k]!.foldl (fun acc k => acc + las.alg.lg2.get! k) 0
        let est := Float.log2 (fF.abs / bd.qF + 1) - tA.lg - sA.lg - lA
        IO.println s!"pos {pos}: q {q} list {listsA[k]!.map (las.alg.primes[·]!)}; tiny v2 {tA.v2} prod {tA.prod}; small prod {sA.prod}; word u {uw} (log {Float.log2 uw.toFloat}) est {est} fF {fF}; exact z {ex.map (·.2)} quotient {fx.natAbs / (q * tA.prod.toNat * sA.prod.toNat * pA.toNat * 2 ^ tA.v2.toNat)} rem {fx.natAbs % (q * tA.prod.toNat * sA.prod.toNat * pA.toNat * 2 ^ tA.v2.toNat)}"

/-- `Merge.mergeLog` + `unmergeLog` against `Merge.merge` + `unmerge` on random
sparse matrices: the same merged rows and the same original-row sets for random
sets of merged rows. -/
def mergeCheck (seed0 : Nat) : IO Unit := do
  let mut seed := seed0
  let mut bad := 0
  for trial in [0:20] do
    let nrows := 2000 + trial * 300
    let ncols := nrows - 40
    let mut rows : Array (Array Nat) := #[]
    for _ in [0:nrows] do
      let mut r : Array Nat := #[]
      for _ in [0:12] do
        seed := (seed * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
        -- skewed: low columns are heavy
        let x := (seed >>> 33) % 1000000
        r := r.push (x * x / 1000000 * ncols / 1000000)
      rows := rows.push r
    let (m1, hist, c1) := Merge.merge ncols 3 rows 40 16
    let (m2, log, c2) := Merge.mergeLog ncols 3 rows 40 16
    if m1 != m2 || c1 != c2 then
      IO.println s!"trial {trial}: merged rows differ"
      bad := bad + 1
      continue
    let mut deps : Array (Array Nat) := #[]
    for _ in [0:64] do
      let mut d : Array Nat := #[]
      for i in [0:m1.size] do
        seed := (seed * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
        if (seed >>> 40) % 3 == 0 then d := d.push i
      deps := deps.push d
    let u1 := Merge.unmerge rows.size hist deps
    let u2 := (Merge.unmergeLog log deps).map fun d => d.qsort (· < ·)
    if u1 != u2 then
      IO.println s!"trial {trial}: dependencies differ ({u1.size} vs {u2.size})"
      bad := bad + 1
  IO.println s!"mergeCheck: {bad} bad of 20"
  -- mergeLog2: every dependency of the merged rows, mapped back, sums to zero
  let mut bad2 := 0
  let mut checked := 0
  for trial in [0:20] do
    let nrows := 1500 + trial * 200
    let ncols := nrows - 60
    let dense := 10
    let mut rows : Array (Array Nat) := #[]
    for _ in [0:nrows] do
      let mut r : Array Nat := #[]
      for _ in [0:14] do
        seed := (seed * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
        let x := (seed >>> 33) % 1000000
        r := r.push (x * x / 1000000 * ncols / 1000000)
      rows := rows.push r
    let (m2, log, c2) := Merge.mergeLog2 ncols dense rows 30 16
    let deps := GF2.dependencies c2 m2 32
    for d in Merge.unmergeLog log deps do
      checked := checked + 1
      -- parity of every column over the original rows of the dependency
      let mut par : Array Bool := Array.replicate ncols false
      for i in d do
        for c in rows[i]! do par := par.set! c (!par[c]!)
      if par.any id then bad2 := bad2 + 1
  IO.println s!"mergeLog2: {bad2} bad of {checked} dependencies"

/-- Relations of a CADO-NFS `las` output file, by special-`q`: `(q, ρ, J, [(a, b)])`. -/
def readCadoRels (path : String) : IO (Array (Nat × Nat × Nat × Array (Int × Nat))) := do
  let lines ← IO.FS.lines path
  let mut out : Array (Nat × Nat × Nat × Array (Int × Nat)) := #[]
  for l in lines do
    if l.startsWith "# Sieving side-1 q=" then
      let fields := (l.drop 2).splitOn "; "
      let get (k : String) : Nat := (fields.findSome? fun f =>
        let f := f.trim
        let f := if f.startsWith "Sieving side-1 " then f.drop 15 else f
        match f.splitOn "=" with
        | [a, b] => if a == k then (b.trimRight.dropRightWhile (· == ';')).toNat? else none
        | _ => none).getD 0
      out := out.push (get "q", get "rho", get "J", #[])
    else if !l.startsWith "#" && l.length > 0 then
      -- (las prints the next special-q's header before the last relations of
      -- the previous one: a relation belongs to the ideal (q, ρ) dividing it)
      match (l.splitOn ":").head? with
      | some ab =>
        match ab.splitOn "," with
        | [a, b] =>
          let (a, b) := (a.toInt!, b.toNat!)
          match out.findIdx? (fun (q, r, _, _) => (a - (b : Int) * (r : Int)) % (q : Int) == 0) with
          | some k => out := out.modify k fun (q, r, J, rs) => (q, r, J, rs.push (a, b))
          | none => pure ()
        | _ => pure ()
      | none => pure ()
  return out

/-- Where our siever loses the relations CADO-NFS finds on the same special-q:
outside our region, below a sieve threshold, dropped by the small-gcd filter or
the prefilter, rejected by the gate, or not found by the exact factoring. -/
def lasMiss (polyPath cadoPath : String) : IO Unit := do
  let (n, sel) ← readCadoPoly polyPath
  let params := chooseParams (GNFS.decimalDigits n)
  let params := { params with lpMult := 2 ^ (max params.lpbR params.lpbA) /
      (min params.ratBound params.algBound) + 1 }
  let ctx := mkCtx n sel params
  let lasParams : Las.LasParams :=
    { logI := params.lasLogI, lpbR := params.lpbR, lpbA := params.lpbA, mfbR := params.mfbR,
      mfbA := params.mfbA, fudge := params.lasFudge }
  let las := Las.mkLasCtx ctx lasParams
  let blocks ← readCadoRels cadoPath
  let mut sc := Las.Scratch.new las
  let len := las.I * las.J
  let I := las.I
  -- outside, below rat byte, below alg byte, gcd filter, prefilter, gate, exact, found
  let mut cnt : Array Nat := Array.replicate 8 0
  let mut ours := 0
  let mut cadoJ := 0
  let mut gateCodes : Array Nat := Array.replicate 8 0
  let mut algHist : Array Nat := Array.replicate 16 0
  let mut tinyHist : Array Nat := Array.replicate 16 0
  for (q, ρ, J, rels) in blocks do
    let (u, v) := reduceLattice q ρ las.skew
    let (ua, ub, va, vb) := (u.1, u.2, v.1, v.2)
    let Rr := Las.latticeRoots las.rat ua ub va vb
    let Ra := Las.latticeRoots las.alg ua ub va vb
    let ⟨b1, b2, bits⟩ := sc
    let Pr := Las.powerRoots las.rat ua ub va vb
    let Pa := Las.powerRoots las.alg ua ub va vb
    let (fR, biasR) := Las.fillSegments las b1 false q ua ub va vb las.params.mfbR (Las.rowExtras las las.rat Rr)
    let (fA, biasA) := Las.fillSegments las b2 true q ua ub va vb las.params.mfbA (Las.rowExtras las las.alg Ra)
    let (bufR, RrB) := Las.sieveLargeCached las las.rat Rr (Las.sievePowers las las.rat Pr (Las.lineSieveSide las las.rat Rr fR))
    let (bufA, RaB) := Las.sieveLargeCached las las.alg Ra (Las.sievePowers las las.alg Pa (Las.lineSieveSide las las.alg Ra fA))
    let s0 := Las.survivors bufR bufA len
    let s1 := Las.dropSmallGcd las s0
    let surv := Las.prefilterGap4 las q ua ub va vb bufR bufA biasR biasA (Las.tinyPrimes las las.rat RrB)
      (Las.tinyPrimes las las.alg RaB) 3 s1
    let (lab, rowStart) := Las.labelSurvivors las (Las.zeroRows las bufA) surv
    let bits := Las.markBits bits surv true
    let listsR := Las.groupLabelled las surv lab rowStart (Las.resieveCached las las.rat RrB bits #[])
    let listsA := Las.groupLabelled las surv lab rowStart (Las.resieveCached las las.alg RaB bits #[])
    let bits := Las.markBits bits surv false
    let bd := Las.mkBounds las q ua ub va vb RrB RaB
    let mut found : Std.HashSet (Int × Nat) := {}
    for k in [0:surv.size] do
      if let some rel := Las.factorSurvivor4 las bd q ρ ua ub va vb RrB RaB listsR[k]! listsA[k]! surv[k]! then
        found := found.insert (rel.a, rel.b)
    ours := ours + found.size
    cadoJ := cadoJ + J
    let det := ua * vb - ub * va
    for (a, b) in rels do
      if found.contains (a, b) then
        cnt := cnt.modify 7 (· + 1)
        continue
      -- (a, b) = i u + j v: i = (a vb - b va) / det, j = (ua b - ub a) / det (or the negated point)
      let solve (a b : Int) : Option (Int × Int) :=
        let ni := a * vb - (b : Int) * va
        let nj := ua * (b : Int) - ub * a
        if ni % det == 0 && nj % det == 0 then some (ni / det, nj / det) else none
      let ij := match solve a b with
        | some (i, j) => if j < 0 then some (-i, -j) else some (i, j)
        | none => none
      match ij with
      | none => cnt := cnt.modify 0 (· + 1)
      | some (i, j) =>
        if i < -(I / 2 : Nat) || i ≥ (I / 2 : Nat) || j ≤ 0 || j ≥ (las.J : Int) then
          cnt := cnt.modify 0 (· + 1)
          if cnt[0]! ≤ 6 then IO.println s!"outside: q {q} ρ {ρ} (a, b) = ({a}, {b}) -> (i, j) = ({i}, {j}); basis {ua} {ub} {va} {vb}"
        else
          let pos := j.toNat * I + (i + (I / 2 : Nat)).toNat
          if bufR.get! pos < 128 then cnt := cnt.modify 1 (· + 1)
          else if bufA.get! pos < 128 then
            cnt := cnt.modify 2 (· + 1)
            -- the segment's threshold against this point's norm, and its tiny primes
            let segs := I / 64
            let c := pos % I
            let seg := j.toNat * segs + c / 64
            let cs := Las.coeffsF las
            let d := cs.size - 1
            let iF := Arith.nf c - Arith.nf (I / 2)
            let jF := Arith.nf j.toNat
            let nb := Las.normBits true cs d (Arith.intF ua) (Arith.intF ub) (Arith.intF va) (Arith.intF vb)
              (Arith.nf sel.m) (Arith.nf sel.y1) (Arith.nf q) iF jF
            let thr := 128 - (biasA.get! seg).toNat   -- sieved bits needed
            let sieved := (bufA.get! pos).toNat - (biasA.get! seg).toNat
            let tq := Las.mkTinyQ las ua ub va vb
            let tiny := Las.tinyAlgU tq c.toUInt64 j.toNat.toUInt64 (I / 2).toUInt64 0 0
            -- needed = norm bits - mfbA - fudge; the threshold's excess over it
            let need := nb - Arith.nf (las.params.mfbA + las.params.fudge)
            let excessT := Arith.nf thr - need
            let bucket := (if excessT < 0 then 0 else min 15 excessT.toUInt64.toNat)
            algHist := algHist.modify bucket (· + 1)
            let tb := min 15 tiny.toUInt64.toNat
            tinyHist := tinyHist.modify tb (· + 1)
          else if !s1.contains pos then cnt := cnt.modify 3 (· + 1)
          else
            match surv.findIdx? (· == pos) with
            | none => cnt := cnt.modify 4 (· + 1)
            | some k =>
              let g := Las.survivorGate las bd listsR[k]! listsA[k]! pos
              gateCodes := gateCodes.modify g (· + 1)
              if g < 4 then cnt := cnt.modify 5 (· + 1) else cnt := cnt.modify 6 (· + 1)
    sc := ⟨bufR, lab, bits⟩
  let total := blocks.foldl (fun acc (_, _, _, rs) => acc + rs.size) 0
  IO.println s!"{blocks.size} special-q: CADO {total} relations (average J {cadoJ / max 1 blocks.size}), ours {ours}"
  IO.println s!"CADO's relations: found by us {cnt[7]!}; missed: outside our region {cnt[0]!}, rational byte below threshold {cnt[1]!}, algebraic byte {cnt[2]!}, gcd filter {cnt[3]!}, prefilter {cnt[4]!}, gate {cnt[5]!} (codes {gateCodes.extract 0 4}), exact factoring {cnt[6]!}"
  IO.println s!"algebraic misses: segment threshold above the point's own (bits, 0..15+): {algHist}"
  IO.println s!"algebraic misses: tiny-prime bits (0..15+): {tinyHist}"
