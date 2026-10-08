import PrimeFactorLean.GNFS
open PrimeFactorLean PrimeFactorLean.NFS PrimeFactorLean.GNFS

def nfsDebug (n : Nat) (threads : Nat) (params : Params) (maxRounds : Nat := 50) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let some sel := selectPolynomial n params.degree params.polyTries params.halfWidth
    params.expectedLines | IO.println "no poly"
  IO.println s!"poly {sel.coeffs} m={sel.m}"
  let some st := mkSetup n sel | IO.println "setup failed"
  let ctx := mkCtx n sel params
  let t1 ← IO.monoNanosNow
  IO.println s!"FB: rat {ctx.fb.ratPrimes.size} alg {ctx.fb.algPrimes.size} chars {ctx.fb.chars.size} lpR {ctx.lpR} lpA {ctx.lpA} ({(t1-t0)/1000000} ms)"
  let some p := inertPrime st.g 1000003 | IO.println "no inert prime"
  IO.println s!"inert prime {p}"
  let mut coll : Collection := {}
  let mut round := 0
  let mut ready := false
  while !ready && round < maxRounds do
    round := round + 1
    coll ← IO.lazyPure fun _ => collectRound ctx params threads coll
    let rels := coll.rels
    let (rows, numCols) := buildRows ctx.fb rels
    let kept := PrimeFactorLean.GF2.removeSingletons numCols rows
    let active := activeColumns numCols rows kept
    let full := rels.filter fun r => r.rat.all (fun t => t.1 ≤ params.ratBound) && r.alg.all (fun t => t.1 ≤ params.algBound)
    let t2 ← IO.monoNanosNow
    IO.println s!"round {round} b<{coll.nextB} q={coll.nextQ}: rels {rels.size} (full {full.size}) cols {numCols} kept {kept.size} active {active} ({(t2-t0)/1000000} ms)"
    if kept.size ≥ active + params.extra then ready := true
  let rels := coll.rels
  if !ready then return
  let (rows, numCols) := buildRows ctx.fb rels
  let deps := PrimeFactorLean.GF2.dependencies numCols rows 64
  let t3 ← IO.monoNanosNow
  IO.println s!"deps {deps.size} ({(t3-t0)/1000000} ms)"
  let mut i := 0
  for dep in deps do
    i := i + 1
    let rs := dep.toList.map fun i => rels[i]!
    let S : List (Int × Int) := rs.map fun r => (r.a, (r.b : Int))
    let rr := rationalRoot rs
    let hrat := match rr with
      | some Y0 => (S.map fun (ab : Int × Int) => ab.1 - ab.2 * (st.sel.m : Int)).prod == Y0 * Y0
      | none => false
    let γ := prodTree st.g (st.fp :: st.fp :: S.map fun (ab : Int × Int) => [(st.cd : Int) * ab.1, -ab.2])
    let t4 ← IO.monoNanosNow
    let β := sqrtZ st.g γ p
    let t5 ← IO.monoNanosNow
    IO.println s!"dep {i}: size {dep.size} ratRoot {rr.isSome} ratOK {hrat} gammaBits {maxBits γ} sqrt {β.isSome} ({(t5-t4)/1000000} ms)"
    match congruence st rs p with
    | some sc =>
      match sc.factor with
      | some d => IO.println s!"FACTOR {d.val}"; return
      | none => IO.println "trivial"
    | none => IO.println "no congruence"
