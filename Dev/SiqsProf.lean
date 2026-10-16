import PrimeFactorLean.SIQS

/-! Per-phase timings and candidate statistics of `SIQS.processA` (single thread). -/

open PrimeFactorLean PrimeFactorLean.SIQS PrimeFactorLean.Arith

namespace PrimeFactorLean.SiqsProf

structure Counts where
  cands : Nat := 0
  pre : Nat := 0
  exact : Nat := 0
  full : Nat := 0
  one : Nat := 0
  two : Nat := 0
  unknown : Nat := 0
  rejected : Nat := 0
  accepted : Nat := 0
  mismatch : Nat := 0
  deriving Inhabited

/-- `SIQS.processCands` after the walks, with counters: the candidates, those
passing the first filter, the exact factorizations and the relations by type. -/
def candStats (ctx : Ctx) (ap : APoly) (B C : Int) (roots : Array Nat) (buf : ByteArray)
    (cands : Array Nat) (lists : Array (List Nat)) (cnt : Counts) (check : Bool) : Counts := Id.run do
  let Af := nf ap.A
  let Bf := intF B
  let Cf := intF C
  let Mf := nf ctx.M
  let w64 : Int := 18446744073709551616
  let A64 := (ap.A % 18446744073709551616).toUInt64
  let B64 := ((if ctx.q2 then B else 2 * B) % w64).toNat.toUInt64
  let C64 := (C % w64).toNat.toUInt64
  let M64 := ctx.M.toUInt64
  let biasF := nf ctx.bias.toNat
  let B2f := if ctx.q2 then Bf else fc 2 * Bf
  let pre8F := nf ctx.pre8
  let spvU := ctx.spv.toUSize
  let smallU := ctx.smallEnd.toUSize
  let mut cnt := { cnt with cands := cnt.cands + cands.size }
  for c in [0:cands.size] do
    let j := cands[c]!
    let x := nf j - Mf
    let vs := (Af * x + B2f) * x + Cf
    let vf := vs.abs
    let l8v := if vf < fc 2 then fc 0 else fc 8 * Float.log2 vf
    let x64 := j.toUInt64 - M64
    let v64 := (A64 * x64 + B64) * x64 + C64
    let e2 : Nat := if v64 == 0 then 64 else (v64 &&& (-v64)).toNat.log2
    let (tiny, lt) :=
      if h : spvU.toNat ≤ ap.logp.size ∧ spvU.toNat ≤ ctx.log8.size ∧ spvU.toNat ≤ ctx.prime.size ∧
          spvU.toNat ≤ ctx.pl.size ∧ spvU.toNat ≤ roots.size then
        smallTest ap.logp ctx.log8 ctx.prime ctx.pl roots j.toUInt32 1 spvU h.1 h.2.1 h.2.2.1
          h.2.2.2.1 h.2.2.2.2 [] (8 * e2)
      else ([], 8 * e2)
    let sieved := ((buf.get! j).toUInt64.toFloat - biasF) * ctx.scale * fc 8
    if l8v > nf lt + sieved + pre8F then continue
    cnt := { cnt with pre := cnt.pre + 1 }
    let (hits, l8) :=
      if h : smallU.toNat ≤ ap.logp.size ∧ smallU.toNat ≤ ctx.log8.size ∧
          smallU.toNat ≤ ctx.prime.size ∧ smallU.toNat ≤ ctx.pl.size ∧ smallU.toNat ≤ roots.size then
        smallTest ap.logp ctx.log8 ctx.prime ctx.pl roots j.toUInt32 spvU smallU h.1 h.2.1
          h.2.2.1 h.2.2.2.1 h.2.2.2.2 tiny lt
      else (tiny, lt)
    let mut l8 := l8
    let mut found := hits
    for i in lists[c]! do
      l8 := l8 + (ctx.log8.get! i).toNat
      found := i :: found
    if l8v ≤ (nf (l8 + ctx.allow8)) then
      cnt := { cnt with exact := cnt.exact + 1 }
      let neg := vs < fc 0
      let vmag := (Af * x * x).abs + (B2f * x).abs + Cf.abs
      let cof := if vf * fc 1073741824 < vmag then .unknown
        else fastCofactor ctx ap found (if neg then -v64 else v64) e2 vf
      let r : Option (QS.Found ctx.n ctx.fb) := match cof with
        | .reject => none
        | .accept exps u l1 l2 => relationOf ctx ap B j neg u exps l1 l2
        | .unknown => exactRelation ctx ap B C j found
      match cof with
      | .unknown => cnt := { cnt with unknown := cnt.unknown + 1 }
      | .reject => cnt := { cnt with rejected := cnt.rejected + 1 }
      | .accept .. => cnt := { cnt with accepted := cnt.accepted + 1 }
      -- the exact path as a cross-check of the fast one
      if check then
        let e := exactRelation ctx ap B C j found
        if e.isSome != r.isSome then cnt := { cnt with mismatch := cnt.mismatch + 1 }
      if let some r := r then
        if r.l1 == 1 && r.l2 == 1 then cnt := { cnt with full := cnt.full + 1 }
        else if r.l1 == 1 then cnt := { cnt with one := cnt.one + 1 }
        else cnt := { cnt with two := cnt.two + 1 }
  return cnt

/-- Single-thread phases of `processA` over the `A`s `0 … as - 1` with `params`. -/
def run (n : Nat) (params : Params) (as : Nat) (check : Bool := false) : IO Unit := do
  let .inl ctx := mkCtx n params | IO.println "small factor"
  let F := ctx.fb.size
  let len : USize := ctx.size.toUSize
  let mut tA := 0
  let mut tMed := 0
  let mut tBig := 0
  let mut tScan := 0
  let mut tWalk := 0
  let mut tCand := 0
  let mut polys := 0
  let mut cnt : Counts := {}
  for seed in [0:as] do
    let t0 ← IO.monoNanosNow
    let some ap ← IO.lazyPure fun _ => mkAPoly ctx seed | continue
    let t1 ← IO.monoNanosNow
    tA := tA + (t1 - t0)
    let s := ap.qs.size
    let A : Int := ap.A
    let mut B : Int := (ap.Bl.foldl (· + ·) 0 : Nat)
    let mut roots := ap.roots
    let mut buf := ctx.template.copySlice 0 ByteArray.empty 0 ctx.template.size
    for g in [1:2 ^ (s - 1)] do
      let v := (g.toUInt64 &&& (-g.toUInt64)).toNat.log2
      let gray := g ^^^ (g >>> 1)
      let negate := gray.testBit v
      let bv : Int := (ap.Bl[v]! : Int)
      B := if negate then B - 2 * bv else B + 2 * bv
      let drow := ap.delta[v]!
      let a ← IO.monoNanosNow
      let spvU := ctx.spv.toUSize
      let medU := ctx.medEnd.toUSize
      let FU := F.toUSize
      let st ← IO.lazyPure fun _ => Id.run do
        let mut buf := ctx.template.copySlice 0 buf 0 ctx.template.size
        let mut roots := roots
        if h : len.toNat < buf.size ∧ medU.toNat ≤ ctx.prime.size ∧ medU.toNat ≤ drow.size ∧
            medU.toNat ≤ ctx.cnt.size ∧ medU.toNat ≤ ap.logp.size ∧ medU.toNat ≤ roots.size then
          let (r', b') := switchMed ctx.prime drow ctx.cnt ap.logp negate roots buf len h.1 spvU medU
            h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
          roots := r'
          buf := b'
        if h : spvU.toNat ≤ ctx.prime.size ∧ spvU.toNat ≤ drow.size ∧ spvU.toNat ≤ roots.size then
          roots := moveTiny ctx.prime drow negate roots 1 spvU h.1 h.2.1 h.2.2
        return (roots, buf)
      let b ← IO.monoNanosNow
      let st2 ← IO.lazyPure fun _ => Id.run do
        let mut (roots, buf) := st
        if h : len.toNat < 2 ^ 31 ∧ len.toNat + 64 ≤ buf.size ∧ FU.toNat ≤ ctx.prime.size ∧
            FU.toNat ≤ drow.size ∧ FU.toNat ≤ ap.logp.size ∧ FU.toNat ≤ roots.size then
          let (r', b') := switchBig ctx.prime drow ap.logp negate roots buf len h.1 h.2.1 medU FU
            h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
          roots := r'
          buf := b'
        return (roots, buf.set! ctx.size 0)
      roots := st2.1
      buf := st2.2
      let c ← IO.monoNanosNow
      let cands ← IO.lazyPure fun _ => scan buf ctx.size
      let d ← IO.monoNanosNow
      let C := (B * B - (ctx.N : Int)) / (if ctx.q2 then 4 * A else A)
      let lists ← IO.lazyPure fun _ => walkLists ctx ap roots buf cands
      let e ← IO.monoNanosNow
      cnt ← IO.lazyPure fun _ => candStats ctx ap B C roots buf cands lists cnt check
      let f ← IO.monoNanosNow
      tMed := tMed + (b - a)
      tBig := tBig + (c - b)
      tScan := tScan + (d - c)
      tWalk := tWalk + (e - d)
      tCand := tCand + (f - e)
      polys := polys + 1
  let us (t : Nat) : String :=
    let x := t.toFloat / 1000.0 / polys.toFloat
    toString (Float.round (x * 10.0) / 10.0)
  let per (k : Nat) : String := toString (Float.round (k.toFloat / polys.toFloat * 100.0) / 100.0)
  IO.println s!"fb={F} M={ctx.M} spv={ctx.spv} smallEnd={ctx.smallEnd} medEnd={ctx.medEnd} lp={ctx.lpBound} dlp={ctx.dlpBound} polys={polys}"
  IO.println s!"  per poly us: A {us tA} med {us tMed} big {us tBig} scan {us tScan} walk {us tWalk} cand {us tCand}; total {us (tA + tMed + tBig + tScan + tWalk + tCand)}"
  IO.println s!"  per poly: cands {per cnt.cands} pre {per cnt.pre} exact {per cnt.exact} full {per cnt.full} 1lp {per cnt.one} 2lp {per cnt.two}"
  IO.println s!"  fast cofactor: accepted {per cnt.accepted} rejected {per cnt.rejected} unknown {per cnt.unknown}; mismatches with the exact path {cnt.mismatch}"

end PrimeFactorLean.SiqsProf

namespace PrimeFactorLean.SiqsProf

/-- `SIQS.collect` with statistics: `A`s and polynomials sieved, full relations,
partial relations by type, and cycles, printed at the end. -/
def collectStats (n : Nat) (params : Params) (threads : Nat) : IO Unit := do
  let .inl ctx := mkCtx n params | IO.println "small factor"
  let needed := ctx.fb.size + 1 + params.extra
  let t0 ← IO.monoNanosNow
  let mut fulls := 0
  let mut ones := 0
  let mut twos := 0
  let mut uf : QS.UnionFind := {}
  let mut cycles := 0
  let mut seen : Std.HashSet Nat := {}
  let mut queue : Array (Task (Array (QS.Found ctx.n ctx.fb))) := #[]
  let mut head := 0
  let mut gots : Array Nat := #[]
  let depth := 2 * threads
  let mut polys := 0
  let s := match mkAPoly ctx 0 with | some ap => ap.qs.size | none => 1
  while fulls + cycles < needed && queue.size < 1000000 do
    let got := fulls + cycles
    let recent := if gots.size > threads then got - gots[gots.size - 1 - threads]! else 0
    let mut q := queue
    while q.size - head < depth &&
        (recent == 0 || got + (q.size - head) * recent / threads < needed) do
      let seed := q.size
      q := q.push (Task.spawn fun _ => processA ctx seed)
    queue := q
    if head == queue.size then break
    let batch := queue[head]!.get
    queue := queue.set! head (.pure #[])
    head := head + 1
    polys := polys + 2 ^ (s - 1)
    for f in batch do
      let key := min f.rel.x (ctx.n - f.rel.x)
      if seen.contains key then continue
      seen := seen.insert key
      if f.l1 == 1 && f.l2 == 1 then fulls := fulls + 1
      else
        if f.l1 == 1 then ones := ones + 1 else twos := twos + 1
        let (uf', closed) := uf.union f.l1 f.l2
        uf := uf'
        if closed then cycles := cycles + 1
    gots := gots.push (fulls + cycles)
  let t1 ← IO.monoNanosNow
  IO.println s!"fb {ctx.fb.size} M {ctx.M} lp {ctx.lpBound} dlp {ctx.dlpBound}: {head} A, {polys} polys in {(t1 - t0) / 1000000} ms ({(t1 - t0) * threads / 1000 / polys} us/poly/thread); full {fulls}, 1lp {ones}, 2lp {twos}, cycles {cycles}, needed {needed}; rels/poly {(fulls + ones + twos).toFloat / polys.toFloat}"

end PrimeFactorLean.SiqsProf
