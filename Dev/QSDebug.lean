import PrimeFactorLean.QS
open PrimeFactorLean PrimeFactorLean.QS

/-- Time the components of one SIQS A-batch. -/
def qsDebug (n : Nat) (params : Params) (numA : Nat) : IO Unit := do
  let .inl ctx := mkContext n params | IO.println "small factor"
  IO.println s!"k={ctx.k} fb={ctx.fb.size} pmax={ctx.fb[ctx.fb.size-1]!} M={ctx.M} thr={ctx.threshold} lp={ctx.lpBound}"
  let target := Nat.sqrt (2 * ctx.N) / ctx.M
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
