import PrimeFactorLean.QS
import PrimeFactorLean.SIQS
open PrimeFactorLean PrimeFactorLean.QS

/-- Time the components of one SIQS A-batch. -/
def qsDebug (n : Nat) (params : Params) (numA : Nat) : IO Unit := do
  let .inl ctx := mkContext n params | IO.println "small factor"
  IO.println s!"k={ctx.k} fb={ctx.fb.size} pmax={ctx.fb[ctx.fb.size-1]!} M={ctx.M} thr={ctx.threshold} lp={ctx.lpBound}"
  let target := isqrt (2 * ctx.N) / ctx.M
  let qSize : Nat := if target.log2 > 66 then 2000 else if target.log2 > 40 then 600
    else if target.log2 > 20 then 100 else 20
  let s := max 1 ((target.log2 + qSize.log2 / 2) / max 1 qSize.log2)
  IO.println s!"target bits {target.log2} s={s}"
  let mut tSieve := 0
  let mut tCand := 0
  let mut tPos := 0
  let mut nPolys := 0
  let mut nCands := 0
  let mut nFull := 0
  let mut nPartial := 0
  let mut buf := ctx.zeros
  let skip0 := Array.replicate ctx.fb.size false
  for a in [0:numA] do
    -- emulate: random B shifts of a fixed A-free polynomial via MPQS-like timing
    let some qs := chooseA ctx (a * 7919 + 1) s 1 ctx.fb.size target | continue
    let A := qs.foldl (fun acc i => acc * ctx.fb[i]!) 1
    let mut Bl : Array Nat := #[]
    for l in [0:qs.size] do
      let q := ctx.fb[qs[l]!]!
      let t := ctx.roots[qs[l]!]!
      let aq := A / q
      match PrimeFactorLean.Arith.invMod (aq % q) q with
      | none => pure ()
      | some inv =>
        let mut gamma := t * inv % q
        if 2 * gamma > q then gamma := q - gamma
        Bl := Bl.push (aq * gamma)
    let B : Int := (Bl.foldl (· + ·) 0 : Nat)
    if ((B * B - (ctx.N : Int)) % (A : Int)) != 0 then continue
    let skip := (Array.range ctx.fb.size).map fun i => qs.contains i
    let poly : Poly := { A := A, B := B, C := (B * B - (ctx.N : Int)) / (A : Int), sqA := 1,
                          aExps := qs.toList.map fun i => (i, 1), skip := skip }
    let t0 ← IO.monoNanosNow
    let (p1, p2) ← IO.lazyPure fun _ => positions ctx poly
    let t1 ← IO.monoNanosNow
    let (buf', cands) ← IO.lazyPure fun _ => sieve ctx p1 p2 poly.skip buf
    buf := buf'
    let t2 ← IO.monoNanosNow
    let rels ← IO.lazyPure fun _ => cands.filterMap fun j => candidateRelation ctx poly p1 p2 j
    let t3 ← IO.monoNanosNow
    tPos := tPos + (t1 - t0)
    tSieve := tSieve + (t2 - t1)
    tCand := tCand + (t3 - t2)
    nPolys := nPolys + 1
    nCands := nCands + cands.size
    for r in rels do
      if r.l1 == 1 && r.l2 == 1 then nFull := nFull + 1 else nPartial := nPartial + 1
  IO.println s!"polys {nPolys}: positions {tPos/1000000} ms, sieve+scan {tSieve/1000000} ms, candidates {tCand/1000000} ms"
  IO.println s!"candidates {nCands}, full {nFull}, partial {nPartial}"

/-- Yield rates of the real SIQS batches for given parameters. -/
def qsTune (n : Nat) (params : Params) (rounds threads : Nat) : IO Unit := do
  let .inl ctx := mkContext n params | IO.println "small factor"
  let t0 ← IO.monoNanosNow
  let mut full := 0
  let mut single := 0
  let mut double := 0
  for r in [0:rounds] do
    let tasks := (List.range threads).map fun t =>
      Task.spawn fun _ => siqsBatch ctx (r * threads + t + 1000) 1
    for task in tasks do
      for f in task.get do
        if f.l1 == 1 && f.l2 == 1 then full := full + 1
        else if f.l1 == 1 then single := single + 1
        else double := double + 1
  let t1 ← IO.monoNanosNow
  let secs := (t1 - t0).toFloat / 1.0e9
  IO.println s!"fb={ctx.fb.size} M={ctx.M} lp={params.lpMult} dlp={params.dlpFactor} thr={ctx.threshold}: {secs}s full {full} single {single} double {double} -> full/s {full.toFloat / secs} single/s {single.toFloat / secs} double/s {double.toFloat/secs} need {ctx.fb.size}"

/-- Time relation collection and linear algebra separately for a full SIQS run. -/
def qsPhases (n : Nat) (params : Params) (threads : Nat) : IO Unit := do
  let .inl ctx := mkContext n params | IO.println "small factor"
  let needed := ctx.fb.size + 1 + params.extra
  let t0 ← IO.monoNanosNow
  let rels ← IO.lazyPure fun _ => collect ctx .siqs needed threads 100000
  let t1 ← IO.monoNanosNow
  let rows := rels.map PrimeFactorLean.Squares.parityColumns
  let deps ← IO.lazyPure fun _ => PrimeFactorLean.GF2.dependencies (ctx.fb.size + 1) rows 64
  let t2 ← IO.monoNanosNow
  let result ← IO.lazyPure fun _ => (extract ctx rels).map (·.val)
  let t3 ← IO.monoNanosNow
  IO.println s!"fb={ctx.fb.size} rels={rels.size} collect {(t1-t0)/1000000} ms, GF2 {deps.size} deps {(t2-t1)/1000000} ms, extract (incl. GF2) {(t3-t2)/1000000} ms -> {result}"

/-- A long SIQS run with progress lines (same collection logic as `QS.collect`). -/
def qsLong (n : Nat) (params : Params) (threads : Nat) : IO Unit := do
  let .inl ctx := mkContext n params | IO.println "small factor"
  let needed := ctx.fb.size + 1 + params.extra
  IO.println s!"k={ctx.k} fb={ctx.fb.size} M={ctx.M} thr={ctx.threshold} lp={ctx.lpBound} dlp={ctx.dlpBound} needed={needed}"
  let t0 ← IO.monoNanosNow
  let mut fulls : Array (PrimeFactorLean.Squares.Relation ctx.n ctx.fb) := #[]
  let mut edges : Array (Found ctx.n ctx.fb) := #[]
  let mut uf : UnionFind := {}
  let mut cycles := 0
  let mut seen : Std.HashSet Nat := {}
  let mut round := 0
  while fulls.size + cycles < needed do
    let base := round * threads
    let tasks := (List.range threads).map fun t =>
      Task.spawn fun _ => siqsBatch ctx (base + t) 1
    for task in tasks do
      for f in task.get do
        if seen.contains f.rel.x then continue
        seen := seen.insert f.rel.x
        if f.l1 == 1 && f.l2 == 1 then
          fulls := fulls.push f.rel
        else
          edges := edges.push f
          let (uf', closed) := uf.union f.l1 f.l2
          uf := uf'
          if closed then cycles := cycles + 1
    round := round + 1
    let t1 ← IO.monoNanosNow
    let secs := (t1 - t0).toFloat / 1.0e9
    IO.println s!"round {round} {secs}s: fulls {fulls.size} partials {edges.size} cycles {cycles} total {fulls.size + cycles}/{needed}"
    (← IO.getStdout).flush
  for ids in graphCycles (edges.map fun f => (f.l1, f.l2)) do
    if let some r := combineCycle edges ids then fulls := fulls.push r
  let t2 ← IO.monoNanosNow
  IO.println s!"relations {fulls.size} after cycle extraction ({(t2 - t0) / 1000000} ms)"
  let result ← IO.lazyPure fun _ => (extract ctx fulls).map (·.val)
  let t3 ← IO.monoNanosNow
  IO.println s!"factor {result} (linear algebra and square roots {(t3 - t2) / 1000000} ms, total {(t3 - t0) / 1000000} ms)"

/-- Yield and speed of the fast SIQS: `rounds × threads` values of `A`. -/
def fastTune (n : Nat) (params : SIQS.Params) (rounds threads : Nat) : IO Unit := do
  let .inl ctx := SIQS.mkCtx n params | IO.println "small factor"
  let some ap := SIQS.mkAPoly ctx 1 | IO.println "no A"
  IO.println s!"k={ctx.k} fb={ctx.fb.size} pmax={ctx.fb[ctx.fb.size-1]!} M={ctx.M} bias={ctx.bias} lp={ctx.lpBound} dlp={ctx.dlpBound} s={ap.qs.size} polys/A={2 ^ (ap.qs.size - 1)}"
  let t0 ← IO.monoNanosNow
  let mut full := 0
  let mut single := 0
  let mut double := 0
  for r in [0:rounds] do
    let tasks := (List.range threads).map fun t =>
      Task.spawn fun _ => SIQS.processA ctx (r * threads + t + 1000)
    for task in tasks do
      for f in task.get do
        if f.l1 == 1 && f.l2 == 1 then full := full + 1
        else if f.l1 == 1 then single := single + 1
        else double := double + 1
  let t1 ← IO.monoNanosNow
  let secs := (t1 - t0).toFloat / 1.0e9
  let polys := rounds * threads * 2 ^ (ap.qs.size - 1)
  IO.println s!"{secs}s for {polys} polys ({secs * 1.0e6 * threads.toFloat / polys.toFloat} us/poly/thread): full {full} single {single} double {double}; full/s {full.toFloat / secs} partial/s {(single + double).toFloat / secs}; need {ctx.fb.size}"

/-- Brute force over one polynomial: every position is trial divided by the
whole factor base; compare with the sieve's candidates and relations. -/
def fastCheck (n : Nat) (params : SIQS.Params) (seed : Nat) : IO Unit := do
  let .inl ctx := SIQS.mkCtx n params | IO.println "small factor"
  let some ap := SIQS.mkAPoly ctx seed | IO.println "no A"
  let A : Int := ap.A
  let B : Int := (ap.Bl.foldl (· + ·) 0 : Nat)
  let C : Int := (B * B - (ctx.N : Int)) / (if ctx.q2 then 4 * A else A)
  IO.println s!"A={ap.A} s={ap.qs.size} check (B^2-N)%A={(B * B - (ctx.N : Int)) % A}"
  let len : USize := ctx.size.toUSize
  let mut buf := ctx.template.copySlice 0 ByteArray.empty 0 ctx.template.size
  if h : len.toNat < buf.size ∧ ctx.medEnd ≤ ctx.prime.size ∧ ctx.medEnd ≤ ctx.cnt.size ∧
      ctx.medEnd ≤ ap.roots.size ∧ ctx.medEnd ≤ ap.logp.size then
    buf := SIQS.sieveMed ctx.prime ctx.cnt ap.roots ap.logp buf len h.1 ctx.spv ctx.medEnd h.2.1 h.2.2.1
      h.2.2.2.1 h.2.2.2.2
  if h : len.toNat < buf.size ∧ ctx.fb.size ≤ ap.roots.size ∧ ctx.fb.size ≤ ap.logp.size then
    buf := SIQS.sieveLarge ap.roots ap.logp buf len h.1 ctx.medEnd ctx.fb.size h.2.1 h.2.2
  let cands := SIQS.scan buf ctx.size
  let rels := SIQS.processCands ctx ap B C ap.roots buf cands #[]
  let mut full := 0
  let mut part := 0
  let mut fullCand := 0
  let mut partialCand := 0
  let mut found := 0
  let mut maxMiss : Nat := 0
  let mut mism := 0
  for j in [0:ctx.size] do
    let x : Int := (j : Int) - (ctx.M : Int)
    let v : Int := (if ctx.q2 then (A * x + B) * x + C else (A * x + 2 * B) * x + C)
    if v == 0 then continue
    let mut u := v.natAbs
    let mut sumLog : Nat := 0
    for i in [0:ctx.fb.size] do
      let p := ctx.fb[i]!
      while u % p == 0 do
        u := u / p
        if i ≥ ctx.spv then sumLog := sumLog + (ap.logp.get! i).toNat
    let isCand := buf.get! j ≥ 128
    if (buf.get! j).toNat != (ctx.bias.toNat + sumLog) % 256 then
      mism := mism + 1
      if mism ≤ 5 then IO.println s!"mismatch at j={j}: sieve {buf.get! j} expected {(ctx.bias.toNat + sumLog) % 256}"
    if u == 1 then
      full := full + 1
      if isCand then fullCand := fullCand + 1
      else maxMiss := max maxMiss (128 - (buf.get! j).toNat)
    else if u < ctx.lpBound then
      part := part + 1
      if isCand then partialCand := partialCand + 1
    if isCand then found := found + 0
  found := rels.size
  IO.println s!"positions {ctx.size}: candidates {cands.size}; full {full} (flagged {fullCand}), partial {part} (flagged {partialCand}); relations from candidates {found}; max shortfall of a missed full {maxMiss}; sieve mismatches {mism}"

/-- Phase timings of `SIQS.processA` for one `A` (single thread). -/
def fastProfile (n : Nat) (params : SIQS.Params) (seed : Nat) : IO Unit := do
  let .inl ctx := SIQS.mkCtx n params | IO.println "small factor"
  let t0 ← IO.monoNanosNow
  let some ap ← IO.lazyPure fun _ => SIQS.mkAPoly ctx seed | IO.println "no A"
  let t1 ← IO.monoNanosNow
  let F := ctx.fb.size
  let s := ap.qs.size
  let A : Int := ap.A
  let mut B : Int := (ap.Bl.foldl (· + ·) 0 : Nat)
  let mut roots := ap.roots
  let len : USize := ctx.size.toUSize
  let mut buf := ctx.template.copySlice 0 ByteArray.empty 0 ctx.template.size
  let mut tSwitch := 0
  let mut tScan := 0
  let mut tTdiv := 0
  let mut nCand := 0
  let mut nRel := 0
  let mut nFull := 0
  for g in [1:2 ^ (s - 1)] do
    let v := (g &&& (2 ^ 64 - g)).log2
    let gray := g ^^^ (g >>> 1)
    let negate := gray.testBit v
    let bv : Int := (ap.Bl[v]! : Int)
    B := if negate then B - 2 * bv else B + 2 * bv
    let b ← IO.monoNanosNow
    let drow := ap.delta[v]!
    let st ← IO.lazyPure fun _ => Id.run do
      let mut buf := ctx.template.copySlice 0 buf 0 ctx.template.size
      let mut roots := roots
      if h : len.toNat < buf.size ∧ F ≤ ctx.prime.size ∧ F ≤ drow.size ∧ F ≤ ctx.cnt.size ∧
          F ≤ ap.logp.size ∧ F ≤ roots.size ∧ ctx.medEnd ≤ F ∧ ctx.spv ≤ F then
        let (r', b') := SIQS.switchMed ctx.prime drow ctx.cnt ap.logp negate roots buf len h.1
          ctx.spv ctx.medEnd (by omega) (by omega) (by omega) (by omega) (by omega)
        roots := r'
        buf := b'
      if h : len.toNat < buf.size ∧ F ≤ ctx.prime.size ∧ F ≤ drow.size ∧ F ≤ ap.logp.size ∧
          F ≤ roots.size then
        let (r', b') := SIQS.switchBig ctx.prime drow ap.logp negate roots buf len h.1 ctx.medEnd F
          h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
        roots := r'
        buf := b'
      if h : ctx.spv ≤ ctx.prime.size ∧ ctx.spv ≤ drow.size ∧ ctx.spv ≤ roots.size then
        roots := SIQS.moveTiny ctx.prime drow negate roots 1 ctx.spv h.1 h.2.1 h.2.2
      return (roots, buf)
    roots := st.1
    buf := st.2
    let c ← IO.monoNanosNow
    let cands ← IO.lazyPure fun _ => SIQS.scan buf ctx.size
    let d ← IO.monoNanosNow
    let C := (B * B - (ctx.N : Int)) / A
    let mut nr := 0
    let mut nf := 0
    if !cands.isEmpty then
      let rs ← IO.lazyPure fun _ => SIQS.processCands ctx ap B C roots buf cands #[]
      nr := rs.size
      nf := (rs.filter fun f => f.l1 == 1 && f.l2 == 1).size
    let e ← IO.monoNanosNow
    tSwitch := tSwitch + (c - b)
    tScan := tScan + (d - c)
    tTdiv := tTdiv + (e - d)
    nCand := nCand + cands.size
    nRel := nRel + nr
    nFull := nFull + nf
  let polys := 2 ^ (s - 1) - 1
  let us (t : Nat) : Float := t.toFloat / 1000.0 / polys.toFloat
  IO.println s!"fb={F} M={ctx.M} s={s} smallEnd={ctx.smallEnd} medEnd={ctx.medEnd}: A setup {(t1 - t0) / 1000} us; per poly: switch+sieve {us tSwitch} scan {us tScan} tdiv {us tTdiv} us; candidates/poly {nCand.toFloat / polys.toFloat}, rels/poly {nRel.toFloat / polys.toFloat} (full {nFull.toFloat / polys.toFloat})"

/-- Repeated Lanczos runs on one SIQS matrix (for profiling). -/
def laOnly (n : Nat) (params : SIQS.Params) (threads reps : Nat) : IO Unit := do
  let .inl ctx := SIQS.mkCtx n params | IO.println "small factor"
  let needed := ctx.fb.size + 1 + params.extra
  let rels ← IO.lazyPure fun _ => SIQS.collect ctx needed 16 1000000
  let rows := rels.map PrimeFactorLean.Squares.parityColumns
  let t0 ← IO.monoNanosNow
  let mut tot := 0
  for r in [0:reps] do
    let d ← IO.lazyPure fun _ => PrimeFactorLean.Lanczos.dependencies (ctx.fb.size + 1) rows 64 threads (r + 1)
    tot := tot + d.size
  let t1 ← IO.monoNanosNow
  IO.println s!"{reps} Lanczos runs ({threads} threads): {(t1 - t0) / 1000000 / reps} ms each, {tot} deps; matrix {ctx.fb.size} x {rows.size}"

/-- Collection vs linear algebra for the fast SIQS. -/
def fastPhases (n : Nat) (params : SIQS.Params) (threads : Nat) : IO Unit := do
  let .inl ctx := SIQS.mkCtx n params | IO.println "small factor"
  let needed := ctx.fb.size + 1 + params.extra
  let t0 ← IO.monoNanosNow
  let rels ← IO.lazyPure fun _ => SIQS.collect ctx needed threads 1000000
  let t1 ← IO.monoNanosNow
  let rows := rels.map PrimeFactorLean.Squares.parityColumns
  let t2 ← IO.monoNanosNow
  let deps ← IO.lazyPure fun _ => PrimeFactorLean.GF2.dependencies (ctx.fb.size + 1) rows 64
  let t3 ← IO.monoNanosNow
  let ldeps ← IO.lazyPure fun _ => PrimeFactorLean.Lanczos.dependencies (ctx.fb.size + 1) rows 64 threads
  let t4 ← IO.monoNanosNow
  for th in [1, 2, 4, 8] do
    let a ← IO.monoNanosNow
    let d ← IO.lazyPure fun _ => PrimeFactorLean.Lanczos.dependencies (ctx.fb.size + 1) rows 64 th
    let b ← IO.monoNanosNow
    IO.println s!"  Lanczos threads {th}: {(b - a) / 1000000} ms ({d.size} deps)"
  let rs := rels
  let a ← IO.monoNanosNow
  let ok ← IO.lazyPure fun _ => Id.run do
    let deps := ldeps
    let mut cnt := 0
    for dep in deps do
      let r := dep.map fun i => rs[i]!
      if (PrimeFactorLean.Squares.Relation.prodTree r 0 r.size).toSquares.isSome then cnt := cnt + 1
    return cnt
  let b ← IO.monoNanosNow
  IO.println s!"  square products for all {ldeps.size} deps: {(b - a) / 1000000} ms ({ok} ok)"
  let result ← IO.lazyPure fun _ => (SIQS.extract ctx rels threads).map (·.val)
  let t5 ← IO.monoNanosNow
  -- validity of the Lanczos dependencies (even column counts)
  let mut good := 0
  for dep in ldeps do
    let mut cnt : Std.HashMap Nat Nat := {}
    for i in dep do
      for c in rows[i]! do cnt := cnt.insert c (cnt.getD c 0 + 1)
    if cnt.fold (fun ok _ v => ok && v % 2 == 0) true then good := good + 1
  IO.println s!"fb={ctx.fb.size} rels={rels.size}: collect {(t1-t0)/1000000} ms, GF2 {deps.size} deps {(t3-t2)/1000000} ms, Lanczos {ldeps.size} deps ({good} valid) {(t4-t3)/1000000} ms, extract {(t5-t4)/1000000} ms -> {result}"

/-- Step-by-step diagnostics of block Lanczos on a real SIQS matrix. -/
def lanczosDebug (n : Nat) (params : SIQS.Params) (threads : Nat) : IO Unit := do
  let .inl ctx := SIQS.mkCtx n params | IO.println "small factor"
  let needed := ctx.fb.size + 1 + params.extra
  let rels ← IO.lazyPure fun _ => SIQS.collect ctx needed threads 1000000
  let rows := rels.map PrimeFactorLean.Squares.parityColumns
  let numCols := ctx.fb.size + 1
  let kept := PrimeFactorLean.GF2.removeSingletons numCols rows
  let mut index : Array Nat := Array.replicate numCols numCols
  let mut active := 0
  for i in kept do
    for c in rows[i]! do
      if c < numCols && index[c]! == numCols then
        index := index.set! c active
        active := active + 1
  let take := min kept.size (active + 64)
  let mut cols : Array (Array Nat) := #[]
  for k in [0:take] do
    cols := cols.push ((rows[kept[k]!]!.filter (· < numCols)).map fun c => index[c]!)
  IO.println s!"rels {rels.size} kept {kept.size} active {active} matrix {active} x {cols.size}"
  let B := PrimeFactorLean.Lanczos.Sparse.mk' active cols
  -- primitive timings on real data
  do
    let open_ := 0
    let y0 := PrimeFactorLean.Lanczos.randomBlock B.ncols 9
    let p0 ← IO.monoNanosNow
    let av0 ← IO.lazyPure fun _ => PrimeFactorLean.Lanczos.mulA B y0 threads
    let p1 ← IO.monoNanosNow
    let tt ← IO.lazyPure fun _ => PrimeFactorLean.Lanczos.inner y0 av0
    let p2 ← IO.monoNanosNow
    let acc0 := PrimeFactorLean.Lanczos.Block.zero B.ncols
    let r ← IO.lazyPure fun _ => PrimeFactorLean.Lanczos.mulAcc y0 tt acc0
    let p3 ← IO.monoNanosNow
    let r2 ← IO.lazyPure fun _ => PrimeFactorLean.Lanczos.mulAcc av0 tt r
    let p4 ← IO.monoNanosNow
    let m2 ← IO.lazyPure fun _ => PrimeFactorLean.Lanczos.Block.andMask av0 0xFFFF0000FFFF0000
    let p5 ← IO.monoNanosNow
    IO.println s!"mulA {(p1-p0)/1000} us, inner {(p2-p1)/1000} us, mulAcc(zero acc) {(p3-p2)/1000} us, mulAcc(acc) {(p4-p3)/1000} us, andMask {(p5-p4)/1000} us {r2.get 3} {m2.get 1} {open_}"
  -- run the iteration with tracing
  let nB := B.ncols
  let y := PrimeFactorLean.Lanczos.randomBlock nB 1
  let v0 := PrimeFactorLean.Lanczos.mulA B y threads
  let mut v := v0
  let mut v1 := PrimeFactorLean.Lanczos.Block.zero nB
  let mut v2 := PrimeFactorLean.Lanczos.Block.zero nB
  let mut x := PrimeFactorLean.Lanczos.Block.zero nB
  let mut winv1 := PrimeFactorLean.Lanczos.Mat.zero
  let mut winv2 := PrimeFactorLean.Lanczos.Mat.zero
  let mut vtav1 := PrimeFactorLean.Lanczos.Mat.zero
  let mut vta2v1 := PrimeFactorLean.Lanczos.Mat.zero
  let mut s1 : Array Nat := Array.range 64
  let mut mask1 : UInt64 := 0xFFFFFFFFFFFFFFFF
  let mut it := 0
  let mut dimSum := 0
  let mut tMul := 0
  let mut tInner := 0
  let mut tAcc := 0
  let tStart ← IO.monoNanosNow
  while it < nB / 60 + 100 do
    it := it + 1
    let q0 ← IO.monoNanosNow
    let av ← IO.lazyPure fun _ => PrimeFactorLean.Lanczos.mulA B v threads
    let q1 ← IO.monoNanosNow
    let vtav ← IO.lazyPure fun _ => PrimeFactorLean.Lanczos.inner v av
    let vta2v ← IO.lazyPure fun _ => PrimeFactorLean.Lanczos.inner av av
    let q2 ← IO.monoNanosNow
    tMul := tMul + (q1 - q0)
    tInner := tInner + (q2 - q1)
    if vtav.isZero then
      IO.println s!"converged at iteration {it}, dims {dimSum}"
      break
    match PrimeFactorLean.Lanczos.selectColumns vtav s1 with
    | none =>
      IO.println s!"selectColumns failed at iteration {it}"
      -- diagnostics: columns not in s1, are they zero in V? rank of T on them
      let mut lastMask : UInt64 := 0
      for c in s1 do lastMask := lastMask ||| PrimeFactorLean.Lanczos.bit c
      let mut colsOut : Array Nat := #[]
      for c in [0:64] do
        if (lastMask >>> c.toUInt64) &&& 1 == 0 then colsOut := colsOut.push c
      let mut zeroCols := 0
      for c in colsOut do
        let mut any := false
        for k in [0:v.size] do
          if (v.get k >>> c.toUInt64) &&& 1 == 1 then any := true
        if !any then zeroCols := zeroCols + 1
      IO.println s!"  columns outside last S: {colsOut}, zero in V: {zeroCols}"
      -- rows of T restricted to colsOut x colsOut
      for c in colsOut do
        let row := vtav[c]!
        let mut bits : Array Nat := #[]
        for d in colsOut do
          if (row >>> d.toUInt64) &&& 1 == 1 then bits := bits.push d
        IO.println s!"  T[{c}] on outside cols: {bits}; popcount row {(List.range 64).filter (fun j => (row >>> j.toUInt64) &&& 1 == 1) |>.length}"
      break
    | some (winv, s, mask0) =>
      dimSum := dimSum + s.size
      if it ≤ 3 || it % 100 == 0 then IO.println s!"iter {it}: dim {s.size}"
      if it ≤ 2 then
        let P := vtav.mul winv
        let mut okI := true
        let mut okZ := true
        for i in [0:64] do
          let inS := (mask0 >>> i.toUInt64) &&& 1 == 1
          if !inS && winv[i]! != 0 then okZ := false
          if inS then
            if (P[i]! &&& mask0) != (PrimeFactorLean.Lanczos.bit i) then okI := false
          if (winv[i]! &&& ~~~mask0) != 0 then okZ := false
        IO.println s!"  (T Winv)|S = I: {okI}; Winv zero outside S: {okZ}; T symmetric: {(List.range 64).all fun i => (List.range 64).all fun j => ((vtav[i]! >>> j.toUInt64) &&& 1) == ((vtav[j]! >>> i.toUInt64) &&& 1)}"
      let d := (winv.mul ((vta2v.andMask mask0).xor vtav)).xor PrimeFactorLean.Lanczos.Mat.identity
      let e := winv1.mul (vtav.andMask mask0)
      let f := ((winv2.mul ((vtav1.mul winv1).xor PrimeFactorLean.Lanczos.Mat.identity)).mul
        (((vta2v1.andMask mask1).xor vtav1).andMask mask0))
      let vtv0 := PrimeFactorLean.Lanczos.inner v v0
      let q3 ← IO.monoNanosNow
      x ← IO.lazyPure fun _ => PrimeFactorLean.Lanczos.mulAcc v (winv.mul vtv0) x
      let mut next := av.andMask mask0
      next ← IO.lazyPure fun _ => PrimeFactorLean.Lanczos.mulAcc v d next
      next ← IO.lazyPure fun _ => PrimeFactorLean.Lanczos.mulAcc v1 e next
      next ← IO.lazyPure fun _ => PrimeFactorLean.Lanczos.mulAcc v2 f next
      let q4 ← IO.monoNanosNow
      tAcc := tAcc + (q4 - q3)
      -- orthogonality check: V_{i+1}ᵀ A V_i should vanish
      if it ≤ 3 then
        let chk := PrimeFactorLean.Lanczos.inner next av
        IO.println s!"  check next^T A v zero? {chk.isZero}"
      v2 := v1
      v1 := v
      v := next
      winv2 := winv1
      winv1 := winv
      vtav1 := vtav
      vta2v1 := vta2v
      s1 := s
      mask1 := mask0
  let tEnd ← IO.monoNanosNow
  IO.println s!"iterations {it}: total {(tEnd - tStart) / 1000000} ms; mulA {tMul / 1000000} ms, inner {tInner / 1000000} ms, mulAcc {tAcc / 1000000} ms"
  -- residual: A (x - y) should be 0
  let r := PrimeFactorLean.Lanczos.mulA B (x.xor y) threads
  let mut nz := 0
  for k in [0:r.size] do
    if r.get k != 0 then nz := nz + 1
  IO.println s!"A(x-y) nonzero words: {nz} of {r.size}"
  let deps := PrimeFactorLean.Lanczos.combine B (x.xor y) v threads 64
  IO.println s!"deps {deps.size}"

open PrimeFactorLean.Lanczos in
/-- Brute-force checks of the block Lanczos primitives on small random data. -/
def lanczosUnit : IO Unit := do
  let n := 300
  let V := randomBlock n 7
  let W := randomBlock n 11
  let bitOf (w : UInt64) (j : Nat) : Bool := (w >>> j.toUInt64) &&& 1 == 1
  -- inner: (VᵀW)[i] bit j = parity of #{k : V[k]_i = 1 ∧ W[k]_j = 1}
  let I := inner V W
  let mut ok1 := true
  for i in [0:64] do
    let mut row : UInt64 := 0
    for k in [0:n] do
      if bitOf (V.get k) i then row := row ^^^ W.get k
    if row != I[i]! then ok1 := false
  IO.println s!"inner ok: {ok1}"
  -- mulAcc: (V M)[k] = ⊕_{j ∈ V[k]} M[j]
  let Mx : Mat := Mat.ofFn fun i => (randomBlock 1 (100 + i)).get 0
  let P := mulAcc V Mx (Block.zero n)
  let mut ok2 := true
  for k in [0:n] do
    let mut acc : UInt64 := 0
    for j in [0:64] do
      if bitOf (V.get k) j then acc := acc ^^^ Mx[j]!
    if acc != P.get k then ok2 := false
  IO.println s!"mulAcc ok: {ok2}"
  -- Mat.mul: (M N)[i] = ⊕_{j ∈ M[i]} N[j]
  let Nx : Mat := Mat.ofFn fun i => (randomBlock 1 (300 + i)).get 0
  let MN := Mx.mul Nx
  let mut ok3 := true
  for i in [0:64] do
    let mut acc : UInt64 := 0
    for j in [0:64] do
      if bitOf Mx[i]! j then acc := acc ^^^ Nx[j]!
    if acc != MN[i]! then ok3 := false
  IO.println s!"Mat.mul ok: {ok3}"
  -- tables/applyTables
  let t := tables Mx
  let w : UInt64 := 0x123456789ABCDEF1
  let mut accT : UInt64 := 0
  for j in [0:64] do
    if bitOf w j then accT := accT ^^^ Mx[j]!
  IO.println s!"tables ok: {accT == applyTables t w}"
  -- sparse products: B with random columns
  let nrows := 200
  let cols : Array (Array Nat) := (Array.range n).map fun c =>
    (Array.range 5).map fun t => (c * 7919 + t * 104729 + t * t * 31) % nrows
  let cols := cols.map fun c => (c.qsort (· < ·)).toList.eraseDups.toArray
  let B := Sparse.mk' nrows cols
  let BV := mulB B V 4
  let mut ok4 := true
  for r in [0:nrows] do
    let mut accB : UInt64 := 0
    for c in [0:n] do
      if cols[c]!.contains r then accB := accB ^^^ V.get c
    if accB != BV.get r then ok4 := false
  IO.println s!"mulB ok: {ok4} (size {BV.size})"
  let BtW := mulBT B (randomBlock nrows 5) 4
  let Y := randomBlock nrows 5
  let mut ok5 := true
  for c in [0:n] do
    let mut accC : UInt64 := 0
    for r in cols[c]! do accC := accC ^^^ Y.get r
    if accC != BtW.get c then ok5 := false
  IO.println s!"mulBT ok: {ok5} (size {BtW.size})"

open PrimeFactorLean.Lanczos in
def mulAccBench : IO Unit := do
  let n := 8128
  let V := randomBlock n 3
  let M : Mat := Mat.ofFn fun i => (randomBlock 1 (50 + i)).get 0
  let t0 ← IO.monoNanosNow
  let mut acc := Block.zero n
  for _ in [0:20] do
    acc := mulAcc V M acc
  let t1 ← IO.monoNanosNow
  IO.println s!"mulAcc: {(t1 - t0) / 20000} us per call (n={n}) {acc.get 5}"

open PrimeFactorLean.Lanczos in
def mulABench : IO Unit := do
  let n := 30000
  let nrows := 29500
  let cols : Array (Array Nat) := (Array.range n).map fun c =>
    ((Array.range 35).map fun t => (c * 7919 + t * 104729 + t * t * 31) % nrows).qsort (· < ·)
  let B := Sparse.mk' nrows cols
  let x := randomBlock n 3
  for th in [1, 4, 16] do
    let t0 ← IO.monoNanosNow
    let mut acc : UInt64 := 0
    for _ in [0:20] do
      let r ← IO.lazyPure fun _ => mulA B x th
      acc := acc ^^^ r.get 7
    let t1 ← IO.monoNanosNow
    IO.println s!"mulA threads {th}: {(t1 - t0) / 20000} us per call (nnz {B.colIdx.size}) {acc}"

def cofactorBench (bound : Nat := 70000000) : IO Unit := do
  -- products of two primes near 2^23 .. 2^26 (the bound is an argument so that the
  -- sieve is not hoisted into module initialization)
  let primes := (PrimeFactorLean.Arith.primesUpTo bound).filter (· > 8000000)
  let mut us : Array Nat := #[]
  let mut k := 7
  for _ in [0:300] do
    k := (k * 1103515245 + 12345) % 2147483648
    let a := primes[k % primes.size]!
    k := (k * 1103515245 + 12345) % 2147483648
    let b := primes[k % primes.size]!
    if a != b then us := us.push (a * b)
  let t0 ← IO.monoNanosNow
  let mut ok := 0
  for u in us do
    if (SIQS.splitCofactor u 70000000).isSome then ok := ok + 1
  let t1 ← IO.monoNanosNow
  IO.println s!"splitCofactor: {(t1 - t0) / (us.size * 1000)} us each, {ok}/{us.size} split"
  let t0 ← IO.monoNanosNow
  let mut okr := 0
  for u in us do
    let g ← IO.lazyPure fun _ => SIQS.rho50 u.toUInt64 1 200000
    if g != 0 then okr := okr + 1
  let t1 ← IO.monoNanosNow
  IO.println s!"rho50: {(t1 - t0) / (us.size * 1000)} us each, {okr}/{us.size} found"
  let t0 ← IO.monoNanosNow
  let mut okc := 0
  for u in us do
    let g ← IO.lazyPure fun _ => SIQS.cofactorFactor u
    if g != 0 then okc := okc + 1
  let t1 ← IO.monoNanosNow
  IO.println s!"cofactorFactor: {(t1 - t0) / (us.size * 1000)} us each, {okc}/{us.size}"
  let t0 ← IO.monoNanosNow
  let mut oks := 0
  for u in us do
    let g ← IO.lazyPure fun _ => SIQS.splitCofactor u 70000000
    if g.isSome then oks := oks + 1
  let t1 ← IO.monoNanosNow
  IO.println s!"splitCofactor (lazyPure): {(t1 - t0) / (us.size * 1000)} us each, {oks}/{us.size}"
  let t0 ← IO.monoNanosNow
  let mut acc : UInt64 := 0
  let m : UInt64 := 562949953421231
  let mf := 1.0 / m.toFloat
  for i in [0:1000000] do
    acc := SIQS.mulmod50 (acc + i.toUInt64) 123456789012 m mf
  let t1 ← IO.monoNanosNow
  IO.println s!"mulmod50: {(t1 - t0) / 1000000} ns each ({acc})"
  let t0 ← IO.monoNanosNow
  let mut c := 0
  for u in us do
    if SIQS.sprp2 (u.toUInt64) then c := c + 1
  let t1 ← IO.monoNanosNow
  IO.println s!"sprp2: {(t1 - t0) / us.size} ns each ({c} prp)"

/-- A long fast-SIQS run with progress lines (same logic as `SIQS.collect`). -/
def fastLong (n : Nat) (params : SIQS.Params) (threads : Nat) : IO Unit := do
  let .inl ctx := SIQS.mkCtx n params | IO.println "small factor"
  let needed := ctx.fb.size + 1 + params.extra
  IO.println s!"fb={ctx.fb.size} M={ctx.M} lp={ctx.lpBound} dlp={ctx.dlpBound} needed={needed}"
  let t0 ← IO.monoNanosNow
  let mut fulls := 0
  let mut edges : Array (Nat × Nat) := #[]
  let mut uf : UnionFind := {}
  let mut cycles := 0
  let mut round := 0
  let mut singles := 0
  let mut doubles := 0
  while fulls + cycles < needed do
    let base := round * threads
    let tasks := (List.range threads).map fun t =>
      Task.spawn fun _ => (SIQS.processA ctx (base + t)).map fun f => (f.l1, f.l2)
    for task in tasks do
      for (l1, l2) in task.get do
        if l1 == 1 && l2 == 1 then fulls := fulls + 1
        else
          if l1 == 1 then singles := singles + 1 else doubles := doubles + 1
          edges := edges.push (l1, l2)
          let (uf', closed) := uf.union l1 l2
          uf := uf'
          if closed then cycles := cycles + 1
    round := round + 1
    if round % 5 == 0 then
      let t1 ← IO.monoNanosNow
      IO.println s!"round {round} {(t1 - t0) / 1000000} ms: fulls {fulls} singles {singles} doubles {doubles} cycles {cycles} total {fulls + cycles}/{needed}"
      (← IO.getStdout).flush
  let t1 ← IO.monoNanosNow
  IO.println s!"done in {(t1 - t0) / 1000000} ms after {round} rounds: fulls {fulls} cycles {cycles}"

/-- `SIQS.collect` with per-round timings (sieving wait vs bookkeeping). -/
def collectTimed (n : Nat) (params : SIQS.Params) (threads : Nat) : IO Unit := do
  let .inl ctx := SIQS.mkCtx n params | IO.println "small factor"
  let needed := ctx.fb.size + 1 + params.extra
  let mut fulls := 0
  let mut edges : Array (Nat × Nat) := #[]
  let mut uf : QS.UnionFind := {}
  let mut cycles := 0
  let mut seen : Std.HashSet Nat := {}
  let mut round := 0
  let mut tWait := 0
  let mut tBook := 0
  let mut nrel := 0
  let t0 ← IO.monoNanosNow
  while fulls + cycles < needed do
    let base := round * threads
    let tasks := (List.range threads).map fun t =>
      Task.spawn fun _ => SIQS.processA ctx (base + t)
    let a ← IO.monoNanosNow
    let mut results := #[]
    for task in tasks do results := results.push task.get
    let b ← IO.monoNanosNow
    for r in results do
      for f in r do
        nrel := nrel + 1
        if seen.contains f.rel.x then continue
        seen := seen.insert f.rel.x
        if f.l1 == 1 && f.l2 == 1 then fulls := fulls + 1
        else
          edges := edges.push (f.l1, f.l2)
          let (uf', closed) := uf.union f.l1 f.l2
          uf := uf'
          if closed then cycles := cycles + 1
    let c ← IO.monoNanosNow
    tWait := tWait + (b - a)
    tBook := tBook + (c - b)
    round := round + 1
  let t1 ← IO.monoNanosNow
  IO.println s!"rounds {round}, relations {nrel}, fulls {fulls}, cycles {cycles}: total {(t1 - t0) / 1000000} ms, waiting for tasks {tWait / 1000000} ms, bookkeeping {tBook / 1000000} ms"

/-- Duration of each `processA` task in a few rounds. -/
def taskSpread (n : Nat) (params : SIQS.Params) (threads rounds : Nat) : IO Unit := do
  let .inl ctx := SIQS.mkCtx n params | IO.println "small factor"
  for r in [0:rounds] do
    let tasks ← (List.range threads).mapM fun t => IO.asTask (prio := .dedicated) do
      let a ← IO.monoNanosNow
      let res ← IO.lazyPure fun _ => SIQS.processA ctx (r * threads + t)
      let b ← IO.monoNanosNow
      return ((b - a) / 1000000, res.size)
    let mut line := ""
    for t in tasks do
      match t.get with
      | .ok (ms, k) => line := line ++ s!"{ms}ms/{k} "
      | .error _ => line := line ++ "err "
    IO.println s!"round {r}: {line}"

/-- Brute force on the Gray-code polynomial `steps` of an `A`: the roots are
advanced by the switch kernels, then the polynomial is sieved from scratch and
every position is trial divided. -/
def grayCheck (n : Nat) (params : SIQS.Params) (seed steps : Nat) : IO Unit := do
  let .inl ctx := SIQS.mkCtx n params | IO.println "small factor"
  let some ap := SIQS.mkAPoly ctx seed | IO.println "no A"
  let F := ctx.fb.size
  let A : Int := ap.A
  let mut B : Int := (ap.Bl.foldl (· + ·) 0 : Nat)
  let mut roots := ap.roots
  let len : USize := ctx.size.toUSize
  let mut scratch := ctx.template.copySlice 0 ByteArray.empty 0 ctx.template.size
  for g in [1:steps + 1] do
    let v := (g &&& (2 ^ 64 - g)).log2
    let gray := g ^^^ (g >>> 1)
    let negate := gray.testBit v
    let bv : Int := (ap.Bl[v]! : Int)
    B := if negate then B - 2 * bv else B + 2 * bv
    let drow := ap.delta[v]!
    if h : len.toNat < scratch.size ∧ F ≤ ctx.prime.size ∧ F ≤ drow.size ∧ F ≤ ctx.cnt.size ∧
        F ≤ ap.logp.size ∧ F ≤ roots.size ∧ ctx.medEnd ≤ F ∧ ctx.spv ≤ F then
      let (r', b') := SIQS.switchMed ctx.prime drow ctx.cnt ap.logp negate roots scratch len h.1
        ctx.spv ctx.medEnd (by omega) (by omega) (by omega) (by omega) (by omega)
      roots := r'
      scratch := b'
    if h : len.toNat < scratch.size ∧ F ≤ ctx.prime.size ∧ F ≤ drow.size ∧ F ≤ ap.logp.size ∧
        F ≤ roots.size then
      let (r', b') := SIQS.switchBig ctx.prime drow ap.logp negate roots scratch len h.1 ctx.medEnd F
        h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      roots := r'
      scratch := b'
    if h : ctx.spv ≤ ctx.prime.size ∧ ctx.spv ≤ drow.size ∧ ctx.spv ≤ roots.size then
      roots := SIQS.moveTiny ctx.prime drow negate roots 1 ctx.spv h.1 h.2.1 h.2.2
  let C : Int := (B * B - (ctx.N : Int)) / (if ctx.q2 then 4 * A else A)
  -- check every root against the definition: A x² + 2 B x + C ≡ 0 at j = root (mod p)
  let mut badRoots := 0
  for i in [1:F] do
    if ap.logp.get! i == 0 then continue
    let p := ctx.fb[i]!
    let w := roots[i]!
    for r in [(SIQS.root1 w).toNat, (SIQS.root2 w).toNat] do
      let x : Int := (r : Int) - (ctx.M : Int)
      if ((if ctx.q2 then (A * x + B) * x + C else (A * x + 2 * B) * x + C)) % (p : Int) != 0 then badRoots := badRoots + 1
  let mut buf := ctx.template.copySlice 0 ByteArray.empty 0 ctx.template.size
  if h : len.toNat < buf.size ∧ ctx.medEnd ≤ ctx.prime.size ∧ ctx.medEnd ≤ ctx.cnt.size ∧
      ctx.medEnd ≤ roots.size ∧ ctx.medEnd ≤ ap.logp.size then
    buf := SIQS.sieveMed ctx.prime ctx.cnt roots ap.logp buf len h.1 ctx.spv ctx.medEnd h.2.1 h.2.2.1
      h.2.2.2.1 h.2.2.2.2
  if h : len.toNat < buf.size ∧ F ≤ roots.size ∧ F ≤ ap.logp.size then
    buf := SIQS.sieveLarge roots ap.logp buf len h.1 ctx.medEnd F h.2.1 h.2.2
  buf := buf.set! ctx.size 0
  let cands := SIQS.scan buf ctx.size
  let rels := SIQS.processCands ctx ap B C roots buf cands #[]
  let mut full := 0
  let mut part := 0
  for j in [0:ctx.size] do
    let x : Int := (j : Int) - (ctx.M : Int)
    let v : Int := (if ctx.q2 then (A * x + B) * x + C else (A * x + 2 * B) * x + C)
    if v == 0 then continue
    let mut u := v.natAbs
    let mut e2 := 0
    let mut tinyBits : Float := 0
    for i in [0:ctx.fb.size] do
      let p := ctx.fb[i]!
      while u % p == 0 do
        u := u / p
        if i == 0 then e2 := e2 + 1
        else if i < ctx.spv then tinyBits := tinyBits + Float.log2 p.toFloat
    if u == 1 || u < ctx.lpBound then
      if u == 1 then full := full + 1 else part := part + 1
      let b := (buf.get! j).toNat
      IO.println s!"  rel at j={j}: byte {b} (need 128), log|v| {Float.log2 v.natAbs.toFloat}, 2^{e2}, tiny bits {tinyBits}, LP bits {Float.log2 u.toFloat}"
  IO.println s!"poly {steps}: bad roots {badRoots}; brute force full {full} partial {part}; candidates {cands.size}, relations {rels.size}; bias {ctx.bias}"
