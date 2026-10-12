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
      | "fudgeA" => { p with lasFudgeA := x }
      | "tinyT" => { p with lasTinyT := x }
      | "tinyTR" => { p with lasTinyTR := x }
      | "qmin" => { p with qmin := x }
      | "logI" => { p with lasLogI := x }
      | "psP" => { p with psP := x }
      | "psNq" => { p with psNq := x }
      | "psIncr" => { p with psIncr := x }
      | "psAdMax" => { p with psAdMax := x }
      | "psKeep" => { p with psKeep := x }
      | "purge" => { p with purgeExcess := x }
      | "extra" => { p with extra := x }
      | "density" => { p with mergeDensity := x }
      | "lasVariant" => { p with lasVariant := x }
      | _ => p
    -- symbolic variants (SNFS tuning): swap the sides' bounds, double the
    -- rational factor base, one more large-prime bit on both sides
    | ["SWAP"] => { p with lpbR := p.lpbA, lpbA := p.lpbR, mfbR := p.mfbA, mfbA := p.mfbR,
                           ratBound := p.algBound, algBound := p.ratBound }
    | ["LIMR2"] => { p with ratBound := 2 * p.ratBound }
    | ["LIM07"] => { p with ratBound := 7 * p.ratBound / 10, algBound := 7 * p.algBound / 10 }
    | ["LIM14"] => { p with ratBound := 14 * p.ratBound / 10, algBound := 14 * p.algBound / 10 }
    | ["LIMA07"] => { p with algBound := 7 * p.algBound / 10 }
    | ["LIMR07"] => { p with ratBound := 7 * p.ratBound / 10 }
    | ["LPBM1"] => { p with lpbR := p.lpbR - 1, lpbA := p.lpbA - 1,
                            mfbR := if p.mfbR ≥ 2 * p.lpbR then p.mfbR - 2 else p.mfbR - 1,
                            mfbA := if p.mfbA ≥ 2 * p.lpbA then p.mfbA - 2 else p.mfbA - 1 }
    | ["LPBRM1"] => { p with lpbR := p.lpbR - 1,
                             mfbR := if p.mfbR ≥ 2 * p.lpbR then p.mfbR - 2 else p.mfbR - 1 }
    | ["MFBA2"] => { p with mfbA := 2 * p.lpbA }
    | ["QMIN2"] => { p with qmin := 2 * p.qmin }
    | ["QMINH"] => { p with qmin := p.qmin / 2 }
    | ["LPB1"] => { p with lpbR := p.lpbR + 1, lpbA := p.lpbA + 1,
                           mfbR := if p.mfbR + 2 ≥ 2 * p.lpbR then p.mfbR + 2 else p.mfbR + 1,
                           mfbA := if p.mfbA + 2 ≥ 2 * p.lpbA then p.mfbA + 2 else p.mfbA + 1 }
    | _ => p) p

/-- Relations as text: a header `n m Y₁ c₀ … c_d`, then one relation per line,
`a b sign|p,e …|p,r,e …`. -/
def dumpRels (path : String) (n : Nat) (sel : Selection) (rels : Array Rel) : IO Unit := do
  let h ← IO.FS.Handle.mk path .write
  h.putStrLn (" ".intercalate ([toString n, toString sel.m, toString sel.y1] ++
    sel.coeffs.toList.map toString))
  for r in rels do
    let rat := " ".intercalate (r.rat.map fun (q, e) => s!"{q},{e}")
    let alg := " ".intercalate (r.alg.map fun (q, x, e) => s!"{q},{x},{e}")
    h.putStrLn s!"{r.a} {r.b} {if r.ratNeg then 1 else 0}|{rat}|{alg}"

/-- The input, polynomial and relations written by `dumpRels`. -/
def loadRels (path : String) : IO (Nat × Selection × Array Rel) := do
  let lines ← IO.FS.lines path
  let hdr := (lines[0]!.splitOn " ").filter (· ≠ "")
  let sel : Selection := { coeffs := (hdr.drop 3).toArray.map String.toInt!, m := hdr[1]!.toNat!,
                           y1 := hdr[2]!.toNat! }
  let mut rels : Array Rel := Array.mkEmpty lines.size
  for i in [1:lines.size] do
    match lines[i]!.splitOn "|" with
    | [head, rat, alg] =>
      let hs := head.splitOn " "
      let ratL := ((rat.splitOn " ").filter (· ≠ "")).map fun t => match t.splitOn "," with
        | [q, e] => (q.toNat!, e.toNat!)
        | _ => (0, 0)
      let algL := ((alg.splitOn " ").filter (· ≠ "")).map fun t => match t.splitOn "," with
        | [q, x, e] => (q.toNat!, x.toNat!, e.toNat!)
        | _ => (0, 0, 0)
      rels := rels.push { a := hs[0]!.toInt!, b := hs[1]!.toNat!, rat := ratL,
                          ratNeg := hs[2]! == "1", alg := algL }
    | _ => pure ()
  return (hdr[0]!.toNat!, sel, rels)

/-- Everything after sieving, timed: filtering, merge, Lanczos, square roots. -/
def gnfsPost (n : Nat) (st : Setup n) (ctx : Ctx) (params : Params) (p threads : Nat)
    (rels : Array Rel) (rows : Rows) (t0 t3 : Nat) (inMatrix : Bool := false)
    (parts : Option (Nat → Array (Array Nat) → IO Unit) := none)
    (preMerge : Option (Nat → Array (Array Nat) → IO Unit) := none)
    (preFilter : Option (Nat → Array (Array Nat) → IO Unit) := none) (tryDeps : Nat := 0)
    (cliSqrt : Bool := false) (sqrtBatches : List Nat := [4]) (lzThreads : Nat := 0) : IO Unit := do
  let numCols := rows.next
  if let some f := preFilter then f numCols rows.sparse
  let dense := 2 + ctx.fb.chars.size
  let t4 ← IO.monoNanosNow
  let kept0 ← IO.lazyPure fun _ => GF2.removeSingletons numCols rows.sparse
  let t5a ← IO.monoNanosNow
  let kept ← IO.lazyPure fun _ => if params.purgeExcess == 0 then kept0
    else Merge.purge numCols dense rows.sparse kept0 params.purgeExcess
  let t5c ← IO.monoNanosNow
  -- (dev: `inMatrix` keeps the dense columns in the matrix, as before `denseCombine`)
  let words ← IO.lazyPure fun _ =>
    let chunk := (kept.size + threads - 1) / threads
    let tasks := (List.range threads).map fun t => Task.spawn fun _ =>
      (Array.range (min kept.size ((t + 1) * chunk) - min kept.size (t * chunk))).map fun i =>
        denseWord ctx.fb rels[kept[t * chunk + i]!]!
    tasks.foldl (fun acc tk => acc ++ tk.get) #[]
  let keptRows ← IO.lazyPure fun _ => if inMatrix then
      kept.map fun k => fullRow ctx.fb rels[k]! rows.sparse[k]!
    else kept.map fun k => rows.sparse[k]!
  let t5 ← IO.monoNanosNow
  IO.println s!"singletons {ms t4 t5a} ms ({kept0.size} rows), purge {ms t5a t5c} ms -> {kept.size} rows, dense words and rows {ms t5c t5} ms"
  let dense := if inMatrix then dense else 0
  if let some f := preMerge then f numCols keptRows
  -- (dev: a density of 1000 + d selects the older `mergeLog` with density d)
  let (mrows, log, mcols) ← IO.lazyPure fun _ => if params.mergeDensity ≥ 1000 then
      Merge.mergeLog numCols dense keptRows (params.mergeDensity - 1000) 32
    else Merge.mergeLog2 numCols dense keptRows params.mergeDensity 32
  let t5b ← IO.monoNanosNow
  if let some f := parts then f mcols mrows
  -- Lanczos components, timed (the dependencies are those of `Lanczos.dependencies`)
  let la0 ← IO.monoNanosNow
  let kept2 ← IO.lazyPure fun _ => GF2.removeSingletons mcols mrows
  let la1 ← IO.monoNanosNow
  let Bm ← IO.lazyPure fun _ => Lanczos.Sparse.mk' mcols (kept2.map fun i => mrows[i]!)
  let la2 ← IO.monoNanosNow
  IO.println s!"lanczos setup: singletons {ms la0 la1}, sparse {ms la1 la2} ({kept2.size} rows)"
  let mdeps ← IO.lazyPure fun _ => Lanczos.dependencies mcols mrows 64
    (if lzThreads == 0 then threads else lzThreads)
  let deps0 := Merge.unmergeLog log mdeps
  let deps := (if inMatrix then deps0 else denseCombine words deps0 kept.size).map fun dep =>
    dep.map fun i => kept[i]!
  let t6 ← IO.monoNanosNow
  let wt := mrows.foldl (fun a r => a + r.size) 0
  IO.println s!"filter {ms t3 t5} ms (kept {kept.size}), merge {ms t5 t5b} ms -> {mrows.size} x {mcols} (weight {wt / max 1 mrows.size}/row), Lanczos {ms t5b t6} ms ({deps.size} deps)"
  if cliSqrt then
    -- as `GNFS.splitWith`: the square roots in parallel batches (of `batch`,
    -- 4 by default); the relations are marked shared first, as they are when
    -- they come from the sieve's tasks
    let _ ← IO.wait (← IO.asTask (pure rels.size))
    for bsz in sqrtBatches do
      let ts0 ← IO.monoNanosNow
      let mut i := 0
      let mut found : Option Nat := none
      while i < deps.size && found.isNone do
        let batch := (deps.extract i (i + bsz)).toList.map fun dep => Task.spawn fun _ =>
          (congruence st (dep.toList.map fun j => rels[j]!) p).bind (·.factor)
        for tk in batch do
          if found.isNone then
            if let some d := tk.get then found := some d.val
        i := i + bsz
      let ts1 ← IO.monoNanosNow
      IO.println s!"square roots (batches of {bsz}, {i / bsz} batch(es)): {ms ts0 ts1} ms -> {found}"
    let t7 ← IO.monoNanosNow
    IO.println s!"total {ms t0 t7} ms"
    return
  let mut tried := 0
  for dep in deps do
    tried := tried + 1
    let a ← IO.monoNanosNow
    -- the parts of `congruence`, timed: the product `γ`, then the lifting
    let drels := dep.toList.map fun i => rels[i]!
    let S : List (Int × Int) := drels.map fun r => (r.a, (r.b : Int))
    let γ ← IO.lazyPure fun _ => NFS.prodTreePar st.g 3
      (st.fp :: st.fp :: S.map fun ab => [(st.cd : Int) * ab.1, -ab.2])
    let a1 ← IO.monoNanosNow
    let lifted ← IO.lazyPure fun _ =>
      (NFS.sqrtFind st.g γ p (fun _ => true)).map NFS.maxBits
    let a2 ← IO.monoNanosNow
    IO.println s!"  gamma {ms a a1} ms ({NFS.maxBits γ} bits), first lift {ms a1 a2} ms (beta {lifted} bits)"
    let a3 ← IO.monoNanosNow
    let c ← IO.lazyPure fun _ => congruence st drels p
    let r := c.bind (·.factor)
    let b ← IO.monoNanosNow
    IO.println s!"  congruence {ms a3 b} ms"
    -- why a dependency fails: no congruence (odd rational exponents or no
    -- square root in ℤ[ω]: missing characters) or a trivial gcd
    let why := if r.isSome then "" else if c.isSome then " (trivial gcd)" else
      match rationalRoot (dep.toList.map fun i => rels[i]!) with
      | none => " (rational product not a square)"
      | some _ => " (no square root in Z[w])"
    IO.println s!"dep {tried} ({dep.size} rels): sqrt {ms a b} ms -> {r.map (·.val)}{why}"
    if r.isSome && tryDeps == 0 then break
    if tryDeps > 0 && tried ≥ tryDeps then break
  let t7 ← IO.monoNanosNow
  IO.println s!"total {ms t0 t7} ms"

def gnfsPhases (n threads : Nat) (logI : Nat := 0) (density : Nat := 0)
    (snfs : Option (Selection × Nat) := none) (overrides : List String := []) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let eff := overrides.findSome? fun kv => match kv.splitOn "=" with
    | ["eff", v] => v.toNat?
    | _ => none
  let params0 := match snfs with
    | some (sel, digits) => match eff with
      | some e => { chooseParams e with degree := sel.degree }
      | none => { GNFS.snfsParams digits with degree := sel.degree }
    | none => chooseParams (eff.getD (decimalDigits n))
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
      mfbA := params.mfbA, fudge := params.lasFudge, fudgeA := params.lasFudgeA,
      tinyT := params.lasTinyT, tinyTR := params.lasTinyTR,
      variant := (overrides.findSome? fun kv => match kv.splitOn "=" with
        | ["variant", v] => v.toNat?
        | _ => none).getD params.lasVariant,
      jDiv := (overrides.findSome? fun kv => match kv.splitOn "=" with
        | ["jDiv", v] => v.toNat?
        | _ => none).getD 2,
      taskMul := (overrides.findSome? fun kv => match kv.splitOn "=" with
        | ["taskMul", v] => v.toNat?
        | _ => none).getD 2 }
  let las := Las.mkLasCtx ctx lasParams
  let mut coll : Collection := {}
  let mut rows := Rows.empty ctx.fb
  let mut count := 8 * threads
  let mut pending : Option (List (Task (Array Rel)) × Nat) := none
  let pipe := (overrides.findSome? fun kv => match kv.splitOn "=" with
    | ["pipe", v] => v.toNat?
    | _ => none).getD 1 == 1
  let lpIdeals (b : Nat) : Float := Float.exp2 b.toFloat / (b.toFloat * Float.log 2)
  let pipeFrac : Nat := (overrides.findSome? fun (kv : String) => match kv.splitOn "=" with
    | ["pipefrac", v] => v.toNat?
    | _ => none).getD 40
  let pipeUntil := pipeFrac.toFloat / 100 * (lpIdeals params.lpbR + lpIdeals params.lpbA)
  let pipeUntil := pipeUntil.toUInt64.toNat
  let mut prev : Option (Nat × Int) := none
  let mut lastCheck := 0
  let mut ready := false
  let mut round := 0
  let mut tSieve := 0
  let mut tCheck := 0
  let base := ctx.fb.ratPrimes.size + ctx.fb.algPrimes.size + ctx.fb.chars.size + 2
  let dense := 2 + ctx.fb.chars.size
  let mut tWait := 0
  let mut predicted := 0
  let mut lastGain := 0
  let mut lastCount := 1
  let syncEnd := overrides.contains "syncend"
  let lateMul := (overrides.findSome? fun kv => match kv.splitOn "=" with
    | ["lateMul", v] => v.toNat?
    | _ => none).getD 4
  while !ready && round < 3000 do
    round := round + 1
    let a ← IO.monoNanosNow
    let before := coll.rels.size
    -- as `GNFS.splitWith`: rows and checks in a task during the round, unless
    -- the round may reach the extrapolated count (`syncend`: the older rule)
    let nearReady := prev.isSome && (syncEnd || (predicted > 0 &&
      (before + lastGain * count / lastCount) * 100 ≥ predicted * 97))
    let due := coll.rels.size ≥ base && coll.rels.size * 100 ≥ pipeUntil * 90 &&
      (prev.isSome || coll.rels.size * 10 ≥ lastCheck * 11)
    let mut bg : Option (Task (Rows × Option (Int × Bool × Nat))) := none
    if !nearReady then
      let fresh := coll.rels.extract rows.sparse.size coll.rels.size
      let r0 := rows
      rows := default
      bg := some (Task.spawn fun _ =>
        let r := fresh.foldl Rows.add r0
        (r, if due then some (rowsExcess r dense params.extra) else none))
    -- as `GNFS.splitWith`: far from ready, the next round is queued first
    let (tasks, hi) := match pending with
      | some p => p
      | none => spawnRoundLas las threads count (max coll.nextQ params.qmin)
          (if prev.isNone && pipe && coll.rels.size < pipeUntil then las.params.taskMul
           else lateMul * las.params.taskMul)
    pending := if prev.isNone && pipe && coll.rels.size < pipeUntil then
        some (spawnRoundLas las threads count hi)
      else none
    let c ← IO.lazyPure fun _ => finishRoundLas coll tasks hi
    coll := c
    let b ← IO.monoNanosNow
    let mut target := 0
    if let some t := bg then
      let (r, chk) ← IO.lazyPure fun _ => t.get
      rows := r
      if let some c := chk then
        lastCheck := before
        let (ok, p', tg) := readiness params.extra before prev c
        IO.eprintln s!"  check (background): rels {before} {repr c}"
        ready := ok
        prev := p'
        target := tg
    let b2 ← IO.monoNanosNow
    if bg.isNone then
      for k in [rows.sparse.size:coll.rels.size] do rows := rows.add coll.rels[k]!
    if !ready && bg.isNone && coll.rels.size ≥ base &&
        (prev.isSome || coll.rels.size * 10 ≥ lastCheck * 11) then
      lastCheck := coll.rels.size
      let chk ← IO.lazyPure fun _ => rowsExcess rows dense params.extra
      IO.eprintln s!"  check: rels {coll.rels.size} {repr chk}"
      let (ok, p', tg) := readiness params.extra coll.rels.size prev chk
      ready := ok
      prev := p'
      target := tg
    let c2 ← IO.monoNanosNow
    tSieve := tSieve + (b - a)
    tWait := tWait + (b2 - b)
    tCheck := tCheck + (c2 - b2)
    let gained := coll.rels.size - before
    if target > 0 then predicted := target
    lastGain := gained
    lastCount := max 1 count
    IO.eprintln s!"round {round}: {count} special-q, q < {coll.nextQ} gained {gained} total {coll.rels.size} ({(b - a) / 1000000} ms)"
    if gained > 0 then
      let growth := if coll.rels.size ≥ pipeUntil then 25 else 10
      count := max (6 * threads) (count * (coll.rels.size / growth + 1) / gained)
      if target > coll.rels.size then
        count := max (6 * threads) (min count ((target - coll.rels.size) * count / gained + 1))
      else if prev.isSome then
        count := max (6 * threads) (min count (count * (coll.rels.size / 25 + 1) / gained))
  for k in [rows.sparse.size:coll.rels.size] do rows := rows.add coll.rels[k]!
  let t3 ← IO.monoNanosNow
  IO.println s!"rounds {round}, q up to {coll.nextQ}, relations {coll.rels.size}: sieve {tSieve / 1000000} ms, background wait {tWait / 1000000} ms, rows+checks {tCheck / 1000000} ms"
  let rels := coll.rels
  if let some path := overrides.findSome? (fun kv => match kv.splitOn "=" with
      | ["dump", v] => some v
      | _ => none) then
    dumpRels path n sel rels
    IO.println s!"relations written to {path}"
  gnfsPost n st ctx params p threads rels rows t0 t3 (overrides.contains "denseInMatrix")
    (cliSqrt := overrides.contains "clisqrt")
    (sqrtBatches := if overrides.contains "sqrtbatches" then [4, 2, 1, 4, 2, 1] else [4])

/-- `gnfsPost` on relations written by `dumpRels` (parameters by size, with overrides). -/
def gnfsPostFile (path : String) (threads : Nat) (overrides : List String)
    (parts : Option (Nat → Array (Array Nat) → IO Unit) := none)
    (preMerge : Option (Nat → Array (Array Nat) → IO Unit) := none)
    (preFilter : Option (Nat → Array (Array Nat) → IO Unit) := none) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let (n, sel, rels) ← loadRels path
  let rels := match overrides.findSome? (fun kv => match kv.splitOn "=" with
      | ["take", v] => v.toNat?
      | _ => none) with
    | some k => rels.extract 0 k
    | none => rels
  let params0 := applyOverrides (chooseParams (decimalDigits n)) overrides
  let params := { params0 with lpMult := 2 ^ (max params0.lpbR params0.lpbA) /
      (min params0.ratBound params0.algBound) + 1 }
  let some st := mkSetup n sel | IO.println "no setup"
  let ctx ← IO.lazyPure fun _ => mkCtx n sel params
  let some p := inertPrime st.g 1000003 | IO.println "no inert prime"
  let rows ← IO.lazyPure fun _ => rels.foldl Rows.add (Rows.empty ctx.fb)
  let t3 ← IO.monoNanosNow
  IO.println s!"loaded {rels.size} relations, rows in {ms t0 t3} ms"
  gnfsPost n st ctx params p threads rels rows t0 t3 (overrides.contains "denseInMatrix") parts preMerge
    preFilter ((overrides.findSome? fun kv => match kv.splitOn "=" with
      | ["trydeps", v] => v.toNat?
      | _ => none).getD 0) (overrides.contains "clisqrt")
    (if overrides.contains "sqrtbatches" then [4, 2, 1, 4, 2, 1, 4, 2, 1] else [4])
    ((overrides.findSome? fun kv => match kv.splitOn "=" with
      | ["lzthreads", v] => v.toNat?
      | _ => none).getD 0)

open PrimeFactorLean.NFS.PolySelect in
/-- `PolySelect.selectCollision` with its two stages timed (collision search,
root optimization of the kept candidates). -/
def polyStages (n threads : Nat) (overrides : List String) : IO Unit := do
  let params := applyOverrides (chooseParams (decimalDigits n)) overrides
  let d := params.degree
  let t := max 1 threads
  let count := (params.psAdMax + params.psIncr - 1) / params.psIncr
  let per := (count + 4 * t - 1) / (4 * t)
  let t0 ← IO.monoNanosNow
  let cands ← IO.lazyPure fun _ =>
    let tasks := (List.range ((count + per - 1) / per)).map fun i =>
      Task.spawn fun _ => collisionSearch n d params.psP params.psNq params.psIncr
        (1 + i * per * params.psIncr) (min (params.psAdMax + 1) (1 + (i + 1) * per * params.psIncr))
        params.psKeep (overrides.contains "lll=1") (!overrides.contains "cadoq=0")
    let all : Array CCand := tasks.foldl (fun acc tk => acc ++ tk.get) #[]
    (all.qsort fun a b => a.score < b.score).extract 0 params.psKeep
  let t1 ← IO.monoNanosNow
  -- the size-optimized candidates, CADO-NFS format (for its polyselect_ropt)
  if let some path := overrides.findSome? (fun (kv : String) => match kv.splitOn "=" with
      | ["rawout", v] => some v
      | _ => none) then
    let mut txt := ""
    for c in cands do
      let (ln, sk) := logNorm c.cs
      txt := txt ++ s!"n: {n}\nY0: {-c.m}\nY1: {c.l}\n" ++
        String.join ((List.range c.cs.size).map fun i => s!"c{i}: {c.cs[i]!}\n") ++
        s!"skew: {sk}\n# lognorm {ln}, alpha {alphaExact c.cs 2000}\n\n"
    IO.FS.writeFile path txt
  let get (key : String) (dflt : Nat) : Nat := (overrides.findSome? fun (kv : String) =>
    match kv.splitOn "=" with
    | [k, v] => if k == key then v.toNat? else none
    | _ => none).getD dflt
  let margin := (get "margin10" 10).toFloat / 10
  let (U, V, top) := (get "ropU" 16, get "ropV" 100000, get "ropTop" 32)
  let tbl0 := dickmanTable
  let area0 := Float.exp2 (2 * params.lasLogI - 1).toFloat * params.qmin.toFloat
  let bf0 := Float.exp2 params.lpbA.toFloat
  let bg0 := Float.exp2 params.lpbR.toFloat
  let rot ← if get "ropt2" 0 == 1 then IO.lazyPure fun _ =>
      (cands.toList.map fun c => Task.spawn fun _ =>
        (rootOpt2 tbl0 c bf0 bg0 area0 (get "uMul" 2) (get "vMul" 8) (get "uCap" 16)
          (get "maxLen" 262144) (get "T" 16) (get "F" 16)).1).map Task.get
    else IO.lazyPure fun _ =>
      (cands.toList.map fun c => Task.spawn fun _ => rootOpt c margin U V top (get "reopt" 0 == 1)).map Task.get
  let t2 ← IO.monoNanosNow
  if get "bounds" 0 == 1 then
    for c in cands do
      let (n0, _) := logNorm c.cs
      let bound := (n0 + expectedRotationGain c.cs c.l c.m) * (1005 / 1000 : Float)
      let ub := rotBounds c.cs c.l c.m 1 bound 62
      let vb := rotBounds c.cs c.l c.m 0 bound 150
      IO.println s!"  l {c.l} ad {c.cs[d]!}: u {ub} v {vb}"
  if get "verbose" 0 == 1 then
    for c in rot do
      let sk := (logNorm c.cs).2
      IO.println s!"  l {c.l} ad {c.cs[d]!}: E*1e7 {(murphyE tbl0 c.cs c.l c.m sk bf0 bg0 area0 * 10000000).round}"
  IO.println s!"collision search {ms t0 t1} ms ({count} leading coefficients, {cands.size} kept), root optimization {ms t1 t2} ms ({rot.length}; margin {margin}, U {U}, V {V}, top {top})"
  let tbl := dickmanTable
  let area := Float.exp2 (2 * params.lasLogI - 1).toFloat * params.qmin.toFloat
  let mut best : Option (Float × CCand) := none
  for c in rot do
    if c.m ≤ 0 || c.cs[d]! ≤ 0 then continue
    let sk := (logNorm c.cs).2
    let e := murphyE tbl c.cs c.l c.m sk (Float.exp2 params.lpbA.toFloat) (Float.exp2 params.lpbR.toFloat) area
    match best with
    | none => best := some (e, c)
    | some (e0, _) => if e > e0 then best := some (e, c)
  if let some (e, c) := best then
    let (ln, sk) := logNorm c.cs
    IO.println s!"best: E*1e7 {(e * 10000000).round}, lognorm {ln}, alpha {alphaExact c.cs 2000}, skew {sk}"
    if let some path := overrides.findSome? (fun (kv : String) => match kv.splitOn "=" with
        | ["out", v] => some v
        | _ => none) then
      let lines := [s!"n: {n}", s!"Y0: {-c.m}", s!"Y1: {c.l}"] ++
        (List.range c.cs.size).map (fun i => s!"c{i}: {c.cs[i]!}") ++ [s!"skew: {sk}"]
      IO.FS.writeFile path (String.intercalate "\n" lines ++ "\n")

open PrimeFactorLean.NFS.PolySelect in
/-- Our `sizeOpt` on the raw polynomials of a CADO-NFS `polyselect` output file,
against CADO-NFS's size-optimized lognorms (the line after each raw block). -/
def soptCompare (path : String) : IO Unit := do
  let lines ← IO.FS.lines path
  let mut i := 0
  let mut raw : Array Int := #[]
  let mut y0 : Int := 0
  let mut y1 : Int := 0
  let mut inRaw := false
  let mut count := 0
  let mut sumOurs : Float := 0
  let mut sumCado : Float := 0
  let mut better := 0
  let mut sum0 : Float := 0
  -- CADO-NFS's size-optimized polynomials (lines `c0: …` without `#`), scored by our norm
  let mut opt : Array Int := #[]
  let mut sumCadoOurs : Float := 0
  let mut nCadoOurs := 0
  for l in lines do
    if l.startsWith "c" && !l.startsWith "#" && (l.splitOn ": ").length == 2 then
      opt := opt.push ((l.splitOn ": ")[1]!).toInt!
      if opt.size == 6 then
        if nCadoOurs < 400 then
          sumCadoOurs := sumCadoOurs + (logNorm opt).1
          nCadoOurs := nCadoOurs + 1
        opt := #[]
    if l.startsWith "# Raw polynomial" then
      inRaw := true
      raw := #[]
      opt := #[]
    else if inRaw && l.startsWith "# Y0: " then y0 := (l.drop 6).toInt!
    else if inRaw && l.startsWith "# Y1: " then y1 := (l.drop 6).toInt!
    else if inRaw && l.startsWith "# c" then
      let parts := (l.drop 3).splitOn ": "
      if parts.length == 2 then raw := raw.push parts[1]!.toInt!
    else if inRaw && l.startsWith "# raw exp_E" then inRaw := false
    else if l.startsWith "# exp_E" && raw.size == 6 then
      -- CADO: "# exp_E e, lognorm L, ..."
      let cadoLn := ((l.splitOn "lognorm ")[1]!.splitOn ",")[0]!.trim
      if count ≥ 400 then break
      let (_, _, ln0) := sizeOpt raw y1 (-y0)
      let (_, _, ln) := sizeOpt2 raw y1 (-y0)
      sum0 := sum0 + ln0
      count := count + 1
      let cl := cadoLn.toNat?.map (·.toFloat) |>.getD 0
      -- parse the float by hand: integer and fractional parts
      let ip := ((cadoLn.splitOn ".")[0]!).toNat!
      let fp := ((cadoLn.splitOn ".")[1]!)
      let cl := ip.toFloat + (fp.toNat!.toFloat / (10 : Float) ^ fp.length.toFloat) + 0 * cl
      sumOurs := sumOurs + ln
      sumCado := sumCado + cl
      if ln < cl - 0.01 then better := better + 1
      if count ≤ 8 then IO.println s!"ours {ln} cado {cl}"
      raw := #[]
    i := i + 1
  IO.println s!"{count} polynomials: mean lognorm ours {sumOurs / count.toFloat} (local descent only {sum0 / count.toFloat}), CADO-NFS {sumCado / count.toFloat}; ours better on {better}"
  IO.println s!"CADO-NFS's size-optimized polynomials by our norm: mean {sumCadoOurs / nCadoOurs.toFloat} ({nCadoOurs})"
