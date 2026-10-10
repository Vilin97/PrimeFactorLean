import PrimeFactorLean.GNFS
import PrimeFactorLean.Merge
import PrimeFactorLean.NFS.PolySelect

/-! Timed replica of `GNFS.splitCore` (lattice-sieve path). -/

open PrimeFactorLean PrimeFactorLean.NFS PrimeFactorLean.GNFS

def ms (a b : Nat) : Nat := (b - a) / 1000000

/-- Parameter overrides `key=value` (`limR limA lpbR lpbA mfbR mfbA fudge qmin`). -/
def applyOverrides (p : Params) (kvs : List String) : Params :=
  kvs.foldl (fun p kv =>
    match kv.splitOn "=" with
    | [k, v] =>
      let x := v.toNat!
      match k with
      | "limR" => { p with ratBound := x }
      | "limA" => { p with algBound := x }
      | "lpbR" => { p with lpbR := x }
      | "lpbA" => { p with lpbA := x }
      | "mfbR" => { p with mfbR := x }
      | "mfbA" => { p with mfbA := x }
      | "fudge" => { p with lasFudge := x }
      | "qmin" => { p with qmin := x }
      | "logI" => { p with lasLogI := x }
      | _ => p
    | _ => p) p

def gnfsPhases (n threads : Nat) (logI : Nat := 0) (density : Nat := 0)
    (snfs : Option (Selection × Nat) := none) (overrides : List String := []) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let params0 := match snfs with
    | some (sel, digits) => { chooseParams (max 60 (7 * digits / 10)) with degree := sel.degree }
    | none => chooseParams (decimalDigits n)
  let params0 := applyOverrides params0 overrides
  let params0 := if logI > 0 then { params0 with lasLogI := logI } else params0
  let params0 := if density > 0 then { params0 with mergeDensity := density } else params0
  let params := { params0 with lpMult := 2 ^ (max params0.lpbR params0.lpbA) /
      (min params0.ratBound params0.algBound) + 1 }
  let some sel ← IO.lazyPure fun _ => (snfs.map (·.1)).orElse fun _ => (PolySelect.selectCollision n params.degree params.psP
    params.psNq params.psIncr params.psAdMax params.psKeep 16 100000 params.lpbR params.lpbA
    (Float.exp2 (2 * params.lasLogI - 1).toFloat * params.qmin.toFloat) threads).orElse fun _ =>
      selectPolynomial n params.degree params.polyTries params.halfWidth params.expectedLines
    | IO.println "no poly"
  let t1 ← IO.monoNanosNow
  let some st := mkSetup n sel | IO.println "no setup"
  let ctx ← IO.lazyPure fun _ => mkCtx n sel params
  let some p := inertPrime st.g 1000003 | IO.println "no inert prime"
  let t2 ← IO.monoNanosNow
  IO.println s!"poly {sel.coeffs} m {sel.m} y1 {sel.y1} skew {skewness sel}: select {ms t0 t1} ms, setup/fb {ms t1 t2} ms (rat {ctx.fb.ratPrimes.size} alg {ctx.fb.algPrimes.size})"
  let lasParams : Las.LasParams :=
    { logI := params.lasLogI, lpbR := params.lpbR, lpbA := params.lpbA, mfbR := params.mfbR,
      mfbA := params.mfbA, fudge := params.lasFudge }
  let las := Las.mkLasCtx ctx lasParams
  let mut coll : Collection := {}
  let mut rows := Rows.empty ctx.fb
  let mut count := 8 * threads
  let mut scratch : List Las.Scratch := []
  let mut prev : Option (Nat × Int) := none
  let mut lastCheck := 0
  let mut ready := false
  let mut round := 0
  let mut tSieve := 0
  let mut tCheck := 0
  let base := ctx.fb.ratPrimes.size + ctx.fb.algPrimes.size + ctx.fb.chars.size + 2
  while !ready && round < 3000 do
    round := round + 1
    let a ← IO.monoNanosNow
    let before := coll.rels.size
    let (c, sc) ← IO.lazyPure fun _ => collectRoundLas las params threads count coll scratch
    coll := c
    scratch := sc
    let b ← IO.monoNanosNow
    for k in [rows.sparse.size:coll.rels.size] do rows := rows.add coll.rels[k]!
    let mut target := 0
    if coll.rels.size ≥ base && (prev.isSome || coll.rels.size * 10 ≥ lastCheck * 11) then
      lastCheck := coll.rels.size
      let (excess, ok, kept) ← IO.lazyPure fun _ => rowsExcess rows (2 + ctx.fb.chars.size) params.extra
      ready := ok
      IO.eprintln s!"  check: rels {coll.rels.size} kept {kept} excess {excess}"
      if kept == 0 then
        prev := none
        lastCheck := coll.rels.size * 14 / 11
      else
        if let some (r0, e0) := prev then
          if excess > e0 && coll.rels.size > r0 then
            let need := ((params.extra : Int) - excess) * ((coll.rels.size - r0 : Nat) : Int) /
              (excess - e0)
            target := coll.rels.size + (11 * need.toNat) / 10
        prev := some (coll.rels.size, excess)
    let c ← IO.monoNanosNow
    tSieve := tSieve + (b - a)
    tCheck := tCheck + (c - b)
    let gained := coll.rels.size - before
    IO.eprintln s!"round {round}: {count} special-q, q < {coll.nextQ} gained {gained} total {coll.rels.size} ({(b - a) / 1000000} ms)"
    if gained > 0 then
      count := max (6 * threads) (count * (coll.rels.size / 10 + 1) / gained)
      if target > coll.rels.size then
        count := max (6 * threads) (min count ((target - coll.rels.size) * count / gained + 1))
  let t3 ← IO.monoNanosNow
  IO.println s!"rounds {round}, q up to {coll.nextQ}, relations {coll.rels.size}: sieve {tSieve / 1000000} ms, rows+checks {tCheck / 1000000} ms"
  let rels := coll.rels
  let numCols := rows.next
  let matRows ← IO.lazyPure fun _ =>
    let chunk := (rels.size + threads - 1) / threads
    let rowTasks := (List.range threads).map fun t => Task.spawn fun _ =>
      (Array.range (min rels.size ((t + 1) * chunk) - min rels.size (t * chunk))).map fun i =>
        let k := t * chunk + i
        fullRow ctx.fb rels[k]! rows.sparse[k]!
    rowTasks.foldl (fun acc tk => acc ++ tk.get) #[]
  let t4 ← IO.monoNanosNow
  let kept := GF2.removeSingletons numCols matRows
  let t5 ← IO.monoNanosNow
  let (mrows, hist, mcols) ← IO.lazyPure fun _ => Merge.merge numCols (2 + ctx.fb.chars.size)
    (kept.map fun i => matRows[i]!) params.mergeDensity 32
  let t5b ← IO.monoNanosNow
  -- Lanczos components, timed (the dependencies are those of `Lanczos.dependencies`)
  let la0 ← IO.monoNanosNow
  let kept2 ← IO.lazyPure fun _ => GF2.removeSingletons mcols mrows
  let la1 ← IO.monoNanosNow
  let Bm ← IO.lazyPure fun _ => Lanczos.Sparse.mk' mcols (kept2.map fun i => mrows[i]!)
  let la2 ← IO.monoNanosNow
  IO.println s!"lanczos setup: singletons {ms la0 la1}, sparse {ms la1 la2} ({kept2.size} rows)"
  let mdeps ← IO.lazyPure fun _ => Lanczos.dependencies mcols mrows 64 threads
  let deps := (Merge.unmerge kept.size hist mdeps).map fun dep => dep.map fun i => kept[i]!
  let t6 ← IO.monoNanosNow
  let wt := mrows.foldl (fun a r => a + r.size) 0
  IO.println s!"full rows {ms t3 t4} ms, singletons {ms t4 t5} ms (kept {kept.size}), merge {ms t5 t5b} ms -> {mrows.size} x {mcols} (weight {wt / max 1 mrows.size}/row), Lanczos {ms t5b t6} ms ({deps.size} deps)"
  let mut tried := 0
  for dep in deps do
    tried := tried + 1
    let a ← IO.monoNanosNow
    let r ← IO.lazyPure fun _ => (congruence st (dep.toList.map fun i => rels[i]!) p).bind (·.factor)
    let b ← IO.monoNanosNow
    IO.println s!"dep {tried} ({dep.size} rels): sqrt {ms a b} ms -> {r.map (·.val)}"
    if r.isSome then break
  let t7 ← IO.monoNanosNow
  IO.println s!"total {ms t0 t7} ms"
