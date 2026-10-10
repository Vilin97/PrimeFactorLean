import PrimeFactorLean.QS
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
