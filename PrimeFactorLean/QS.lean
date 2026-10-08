import Std.Data.HashMap
import Std.Data.HashSet
import PrimeFactorLean.Squares
import PrimeFactorLean.GF2
import PrimeFactorLean.SQUFOF

/-!
# The quadratic sieve family: QS, MPQS and SIQS

All three variants sieve quadratic polynomials

  `Q(x) = (A x + B)² - N = A · (A x² + 2 B x + C)`,   `B² - N = A C`,

over `x ∈ [-M, M)`, where `N = k n` for a Knuth–Schroeppel multiplier `k`.
Modulo `n` this gives `(A x + B)² ≡ A · v(x)` with `v(x) = A x² + 2 B x + C`, so
every `v(x)` that factors over the factor base yields a relation.

* **QS** (Pomerance 1981): `A = 1`, `B = ⌊√N⌋ + 2 M t` for consecutive windows
  `t = 0, 1, -1, 2, -2, …` of one polynomial.
* **MPQS** (Montgomery): `A = q²` for primes `q ≈ (√(2N)/M)^{1/2}`, with `B` a
  Hensel-lifted square root of `N` modulo `q²`; `q` enters each relation as a
  square factor.
* **SIQS** (Alford–Pomerance, Peralta, Contini): `A = q₁ ⋯ q_s` is a product of
  factor-base primes near the optimum `√(2N)/M`; the `2^{s-1}` choices of
  `B = ±B₁ ± ⋯ ± B_s` are enumerated in Gray-code order, so each new polynomial
  costs only one addition per factor-base root.

Sieving uses rounded base-2 logarithms in a `ByteArray`, skips the smallest
primes (small prime variation), and keeps relations with one large prime below
`lpMult · p_max` (large prime variation); partial relations sharing their large
prime are paired. Collection runs on parallel `Task`s.

**What is proved.** Each relation is a `Squares.Relation`, whose defining
congruence is checked when it is created; pairing, multiplication, the
exponent bookkeeping and the final congruence of squares `X² ≡ Y² (mod n)`
are kernel-proved (`Squares.Relation.toSquares`). The returned factor is a
`ProperFactor n`, so `split_sound` holds by construction, and
`Squares.SquareCongruence.factor_isSome` shows that any nontrivial congruence
produced here splits `n`. The sieve, the factor base, polynomial selection and
the GF(2) solver are untrusted search procedures.
-/

namespace PrimeFactorLean.QS

open Arith Squares

/-! ## Parameters -/

structure Params where
  fbSize : Nat
  halfWidth : Nat
  lpMult : Nat
  extra : Nat := 40
  sieveStart : Nat := 6
  /-- Double large prime variation: cofactors up to `dlpFactor⁻¹ · lpBound²`
  that split into two large primes are kept (`0` disables it). -/
  dlpFactor : Nat := 0
  deriving Repr, Inhabited

/-- `(digits, factor-base size, half-width M, large-prime multiplier)`. -/
def paramTable : List (Nat × Nat × Nat × Nat) :=
  [(12, 40, 1024, 10), (15, 50, 2048, 20), (20, 80, 4096, 30), (25, 120, 8192, 30),
   (30, 200, 16384, 40), (35, 300, 16384, 40), (40, 450, 32768, 50),
   (45, 700, 32768, 50), (50, 1100, 65536, 60), (55, 1600, 65536, 70),
   (60, 2400, 65536, 80), (65, 3500, 98304, 90), (70, 5000, 131072, 100),
   (75, 7000, 131072, 100), (80, 9500, 196608, 120), (85, 13000, 196608, 120),
   (90, 18000, 262144, 150), (95, 25000, 262144, 150), (100, 34000, 327680, 150),
   (110, 50000, 393216, 200)]

def chooseParams (digits : Nat) : Params :=
  let entry := (paramTable.find? fun e => digits ≤ e.1).getD
    (paramTable.getLast?.getD (110, 50000, 393216, 200))
  { fbSize := entry.2.1, halfWidth := entry.2.2.1, lpMult := entry.2.2.2 }

def decimalDigits (n : Nat) : Nat := (toString n).length

/-! ## Knuth–Schroeppel multiplier -/

def multiplierCandidates : List Nat :=
  [1, 3, 5, 7, 11, 13, 15, 17, 19, 21, 23, 29, 31, 33, 35, 37, 39, 41, 43, 47, 51, 53,
   55, 57, 59, 61, 65, 67, 69, 71, 73]

/-- Choose a squarefree odd `k` maximizing the Knuth–Schroeppel score. -/
def chooseMultiplier (n : Nat) (primes : Array Nat) : Nat := Id.run do
  let mut best := 1
  let mut bestScore : Float := -1.0e30
  for k in multiplierCandidates do
    let kn := k * n
    let mut score : Float := -0.5 * Float.log k.toFloat
    let r := kn % 8
    if r == 1 then score := score + 2.0 * Float.log 2.0
    else if r == 5 then score := score + Float.log 2.0
    else if r == 3 || r == 7 then score := score + 0.5 * Float.log 2.0
    for p in primes do
      if p == 2 then continue
      if p > 1000 then break
      let lp := Float.log p.toFloat
      if k % p == 0 then score := score + lp / p.toFloat
      else if powMod (kn % p) ((p - 1) / 2) p == 1 then
        score := score + 2.0 * lp / (p.toFloat - 1.0)
    if score > bestScore then
      bestScore := score
      best := k
  return best

/-! ## Context and polynomials -/

structure Context where
  n : Nat
  k : Nat
  N : Nat
  fb : Array Nat
  /-- `√N mod p` for each factor-base prime. -/
  roots : Array Nat
  logp : ByteArray
  M : Nat
  threshold : UInt8
  lpBound : Nat
  /-- Largest double-large-prime cofactor (`0` when the variation is off). -/
  dlpBound : Nat
  sieveStart : Nat
  zeros : ByteArray

structure Poly where
  A : Nat
  B : Int
  C : Int
  sqA : Nat
  aExps : List (Nat × Nat)
  /-- Factor-base primes dividing `A`: trial divided, never sieved. -/
  skip : Array Bool
  deriving Inhabited

/-- A factor base of `N = k n`: `2`, the primes dividing `k`, and primes `p` with
`(N/p) = 1`, together with `√N mod p`. A prime dividing `n` is reported. -/
def buildFactorBase (n N size : Nat) (primes : Array Nat) :
    Array Nat × Array Nat × Option Nat := Id.run do
  let mut fb : Array Nat := #[2]
  let mut roots : Array Nat := #[N % 2]
  for p in primes do
    if fb.size ≥ size then break
    if p == 2 then continue
    if n % p == 0 then
      if p < n then return (fb, roots, some p)
      else continue
    if N % p == 0 then
      fb := fb.push p
      roots := roots.push 0
    else if powMod (N % p) ((p - 1) / 2) p == 1 then
      match sqrtModPrime N p with
      | some t =>
        fb := fb.push p
        roots := roots.push t
      | none => pure ()
  return (fb, roots, none)

def mkContext (n : Nat) (params : Params) : Context ⊕ Nat := Id.run do
  let primes := primesUpTo (max 1000 (params.fbSize * 30))
  let k := chooseMultiplier n primes
  let N := k * n
  let (fb, roots, found) := buildFactorBase n N params.fbSize primes
  if let some p := found then return .inr p
  let logp := ByteArray.mk (fb.map fun p => (Float.round (Float.log2 p.toFloat)).toUInt8)
  let M := params.halfWidth
  let pmax := fb[fb.size - 1]!
  let lpBound := pmax * params.lpMult
  let dlpBound := if params.dlpFactor == 0 then 0 else lpBound * lpBound / params.dlpFactor
  -- Expected contribution of the unsieved small primes.
  let mut small : Float := 0
  for i in [1:min params.sieveStart fb.size] do
    let p := fb[i]!.toFloat
    small := small + 2.0 * Float.log2 p / (p - 1.0)
  let target := Float.log2 M.toFloat + (N.log2.toFloat + 1.0) / 2.0 - 0.5
  let slack := if dlpBound > 0 then Float.log2 dlpBound.toFloat else Float.log2 lpBound.toFloat
  let thr := target - slack - small - 1.0
  let threshold := (if thr < 8.0 then 8.0 else thr).toUInt8
  let mut zeros := ByteArray.emptyWithCapacity (2 * M)
  for _ in [0:2 * M] do zeros := zeros.push 0
  return .inl { n := n, k := k, N := N, fb := fb, roots := roots, logp := logp, M := M,
                threshold := threshold, lpBound := lpBound, dlpBound := dlpBound,
                sieveStart := params.sieveStart, zeros := zeros }

/-- Sentinel for "no root": any position `≥ 2M` is never sieved. -/
def noRoot (ctx : Context) : Nat := 2 * ctx.M + 1

/-- Sieve positions `j = x + M` of the two roots of `Q(x)` modulo each prime. -/
def positions (ctx : Context) (poly : Poly) : Array Nat × Array Nat := Id.run do
  let mut pos1 : Array Nat := Array.mkEmpty ctx.fb.size
  let mut pos2 : Array Nat := Array.mkEmpty ctx.fb.size
  for i in [0:ctx.fb.size] do
    let p := ctx.fb[i]!
    if i == 0 || poly.skip[i]! then
      pos1 := pos1.push (noRoot ctx)
      pos2 := pos2.push (noRoot ctx)
    else
      match invMod (poly.A % p) p with
      | none =>
        pos1 := pos1.push (noRoot ctx)
        pos2 := pos2.push (noRoot ctx)
      | some ainv =>
        let t := ctx.roots[i]!
        let bm := (poly.B % (p : Int)).toNat
        let r1 := ainv * ((t + p - bm) % p) % p
        let r2 := ainv * ((2 * p - t - bm) % p) % p
        pos1 := pos1.push ((r1 + ctx.M) % p)
        pos2 := pos2.push (if t == 0 then noRoot ctx else (r2 + ctx.M) % p)
  return (pos1, pos2)

/-- Logarithmic sieve over `[0, 2M)`; returns the buffer and candidate positions. -/
def sieve (ctx : Context) (pos1 pos2 : Array Nat) (skip : Array Bool) (buf : ByteArray) :
    ByteArray × Array Nat := Id.run do
  let size := 2 * ctx.M
  let mut s := ctx.zeros.copySlice 0 buf 0 size
  for i in [ctx.sieveStart:ctx.fb.size] do
    if skip[i]! then continue
    let p := ctx.fb[i]!
    let lg := ctx.logp.get! i
    let mut j := pos1[i]!
    while j < size do
      s := s.set! j (s.get! j + lg)
      j := j + p
    j := pos2[i]!
    while j < size do
      s := s.set! j (s.get! j + lg)
      j := j + p
  let thr := ctx.threshold
  let mut cands : Array Nat := #[]
  for j in [0:size] do
    if s.get! j ≥ thr then cands := cands.push j
  return (s, cands)

/-- Divide out all factors `p`; returns the cofactor and the exponent. -/
def stripPrime (u p : Nat) : Nat × Nat := Id.run do
  let mut u := u
  let mut e := 0
  while u % p == 0 && u > 0 do
    u := u / p
    e := e + 1
  return (u, e)

/-- A relation together with its large primes (`1` when absent): a full
relation has `l1 = l2 = 1`, a partial one an edge `(l1, l2)` of the large-prime
graph (`l1 = 1` for a single large prime). -/
structure Found (n : Nat) (fb : Array Nat) where
  rel : Relation n fb
  l1 : Nat
  l2 : Nat

instance (n : Nat) (fb : Array Nat) : Inhabited (Found n fb) := ⟨⟨default, 1, 1⟩⟩

/-- Classify a cofactor: full, one large prime, or two large primes. -/
def splitCofactor (ctx : Context) (u : Nat) : Option (Nat × Nat) :=
  if u == 1 then some (1, 1)
  else if u < ctx.lpBound then some (1, u)
  else if ctx.dlpBound > 0 && u < ctx.dlpBound && !isProbablePrime u then
    match SQUFOF.split u with
    | some d =>
      let a := min d.val (u / d.val)
      let b := max d.val (u / d.val)
      if a < ctx.lpBound && b < ctx.lpBound && a * b == u && a != b then some (a, b) else none
    | none => none
  else none

/-- Trial-divide `v(x)` at sieve position `j` and build a checked relation. -/
def candidateRelation (ctx : Context) (poly : Poly) (pos1 pos2 : Array Nat) (j : Nat) :
    Option (Found ctx.n ctx.fb) := Id.run do
  let x : Int := (j : Int) - (ctx.M : Int)
  let v : Int := (poly.A : Int) * x * x + 2 * poly.B * x + poly.C
  if v == 0 then return none
  let mut u := v.natAbs
  let mut exps := poly.aExps
  let (u2, e2) := stripPrime u 2
  u := u2
  if e2 > 0 then exps := (0, e2) :: exps
  for i in [1:ctx.fb.size] do
    let p := ctx.fb[i]!
    let hit :=
      if poly.skip[i]! || ctx.N % p == 0 then u % p == 0
      else
        let jm := j % p
        jm == pos1[i]! || jm == pos2[i]!
    if hit then
      let (u', e) := stripPrime u p
      if e > 0 then
        u := u'
        exps := (i, e) :: exps
  let some (l1, l2) := splitCofactor ctx u | return none
  let X := (((poly.A : Int) * x + poly.B) % (ctx.n : Int)).toNat
  match Relation.mk? ctx.n ctx.fb X poly.sqA u (decide (v < 0)) exps with
  | some r => return some ⟨r, l1, l2⟩
  | none => return none

/-- Sieve one polynomial and return its relations (full and partial). -/
def sievePoly (ctx : Context) (poly : Poly) (pos1 pos2 : Array Nat) (buf : ByteArray) :
    ByteArray × Array (Found ctx.n ctx.fb) := Id.run do
  let (buf, cands) := sieve ctx pos1 pos2 poly.skip buf
  let mut rels : Array (Found ctx.n ctx.fb) := #[]
  for j in cands do
    if let some r := candidateRelation ctx poly pos1 pos2 j then
      rels := rels.push r
  return (buf, rels)

/-! ## Polynomial sources -/

/-- QS: windows of the single polynomial `(x + B₀ + 2Mt)² - N`. -/
def qsBatch (ctx : Context) (batch : Nat) (windows : Nat) :
    Array (Found ctx.n ctx.fb) := Id.run do
  let b0 : Int := (Nat.sqrt ctx.N : Int)
  let mut buf := ctx.zeros
  let mut rels := #[]
  let skip := Array.replicate ctx.fb.size false
  for w in [0:windows] do
    let idx := batch * windows + w
    -- t = 0, 1, -1, 2, -2, ...
    let t : Int := if idx % 2 == 1 then ((idx + 1) / 2 : Nat) else -((idx / 2 : Nat) : Int)
    let B := b0 + 2 * (ctx.M : Int) * t
    let poly : Poly := { A := 1, B := B, C := B * B - (ctx.N : Int), sqA := 1, aExps := [],
                         skip := skip }
    let (p1, p2) := positions ctx poly
    let (buf', found) := sievePoly ctx poly p1 p2 buf
    buf := buf'
    rels := rels ++ found
  return rels

/-- Hensel lift of a square root of `N` from `q` to `q²`. -/
def sqrtModPrimeSquare (N q : Nat) : Option Nat := do
  let t ← sqrtModPrime N q
  if t == 0 then none
  let q2 := q * q
  let inv ← invMod ((2 * t) % q) q
  -- (t + q·s)² ≡ N (mod q²) with s ≡ (N - t²)/q · (2t)⁻¹ (mod q).
  let diff : Int := (N : Int) - (t : Int) * (t : Int)
  let s := ((diff / (q : Int)) % (q : Int)).toNat * inv % q
  let b := (t + q * s) % q2
  if (b * b) % q2 == N % q2 then some b else none

/-- MPQS: `A = q²` for consecutive suitable primes `q` from a per-batch start. -/
def mpqsBatch (ctx : Context) (batch : Nat) (polys : Nat) :
    Array (Found ctx.n ctx.fb) := Id.run do
  let ideal := Nat.sqrt (Nat.sqrt (2 * ctx.N) / ctx.M)
  let mut q := max 3 (ideal + batch * polys * 8) ||| 1
  let mut buf := ctx.zeros
  let mut rels := #[]
  let mut done := 0
  let mut fuel := polys * 200
  while done < polys && fuel > 0 do
    fuel := fuel - 1
    q := q + 2
    if ctx.N % q == 0 || !isProbablePrime q then continue
    if powMod (ctx.N % q) ((q - 1) / 2) q != 1 then continue
    match sqrtModPrimeSquare ctx.N q with
    | none => continue
    | some b =>
      let A := q * q
      let B : Int := if 2 * b > A then (b : Int) - A else b
      let C := (B * B - (ctx.N : Int)) / (A : Int)
      let skip := ctx.fb.map fun p => q % p == 0
      let poly : Poly := { A := A, B := B, C := C, sqA := q, aExps := [], skip := skip }
      let (p1, p2) := positions ctx poly
      let (buf', found) := sievePoly ctx poly p1 p2 buf
      buf := buf'
      rels := rels ++ found
      done := done + 1
  return rels

/-- A small deterministic xorshift generator for polynomial selection. -/
def nextRand (s : Nat) : Nat :=
  let s := s % 2 ^ 64
  let s := (s ^^^ (s <<< 13)) % 2 ^ 64
  let s := s ^^^ (s >>> 7)
  (s ^^^ (s <<< 17)) % 2 ^ 64

/-- Choose `s` distinct factor-base indices with product near `target`. -/
def chooseA (ctx : Context) (seed s lo hi target : Nat) : Option (Array Nat) := Id.run do
  if hi ≤ lo + s then return none
  let mut rng := seed * 2654435761 + 12345
  let mut chosen : Array Nat := #[]
  let mut prod := 1
  let mut fuel := 100 * s + 100
  while chosen.size + 1 < s && fuel > 0 do
    fuel := fuel - 1
    rng := nextRand rng
    let i := lo + rng % (hi - lo)
    if chosen.contains i then continue
    chosen := chosen.push i
    prod := prod * ctx.fb[i]!
  if chosen.size + 1 < s then return none
  -- Final prime: the factor-base prime closest to target / prod.
  let want := target / max 1 prod
  let mut best := 0
  let mut bestDist := target
  let mut found := false
  for i in [1:ctx.fb.size] do
    if chosen.contains i then continue
    if ctx.N % ctx.fb[i]! == 0 then continue
    let p := ctx.fb[i]!
    let d := if p ≤ want then want - p else p - want
    if !found || d < bestDist then
      best := i
      bestDist := d
      found := true
  if !found then return none
  return some (chosen.push best)

/-- SIQS: `numA` values of `A`, each with its `2^{s-1}` Gray-code polynomials. -/
def siqsBatch (ctx : Context) (batch : Nat) (numA : Nat) :
    Array (Found ctx.n ctx.fb) := Id.run do
  let target := Nat.sqrt (2 * ctx.N) / ctx.M
  -- Number of A-factors: aim for factors of roughly 2000 (smaller for small N).
  let qSize : Nat := if target.log2 > 66 then 2000 else if target.log2 > 40 then 600
    else if target.log2 > 20 then 100 else 20
  let s := max 1 ((target.log2 + qSize.log2 / 2) / max 1 qSize.log2)
  -- Index window of factor-base primes around qSize.
  let mut lo := 1
  while lo < ctx.fb.size && ctx.fb[lo]! < qSize / 2 do lo := lo + 1
  let mut hi := lo
  while hi < ctx.fb.size && ctx.fb[hi]! < qSize * 2 do hi := hi + 1
  if hi ≤ lo + s + 2 then
    lo := max 1 (ctx.fb.size / 3)
    hi := ctx.fb.size
  let mut buf := ctx.zeros
  let mut rels := #[]
  for a in [0:numA] do
    let some qs := chooseA ctx (batch * 1000003 + a * 7919 + 1) s lo hi target | continue
    let A := qs.foldl (fun acc i => acc * ctx.fb[i]!) 1
    -- B_l ≡ √N mod q_l and ≡ 0 mod q_j (j ≠ l).
    let mut Bl : Array Nat := #[]
    let mut ok := true
    for l in [0:qs.size] do
      let q := ctx.fb[qs[l]!]!
      let t := ctx.roots[qs[l]!]!
      let aq := A / q
      match invMod (aq % q) q with
      | none => ok := false
      | some inv =>
        let mut gamma := t * inv % q
        if 2 * gamma > q then gamma := q - gamma
        Bl := Bl.push (aq * gamma)
    if !ok || Bl.size == 0 then continue
    let mut B : Int := (Bl.foldl (· + ·) 0 : Nat)
    if ((B * B - (ctx.N : Int)) % (A : Int)) != 0 then continue
    let skip := (Array.range ctx.fb.size).map fun i => qs.contains i
    let aExps := qs.toList.map fun i => (i, 1)
    let poly0 : Poly := { A := A, B := B, C := (B * B - (ctx.N : Int)) / (A : Int), sqA := 1,
                          aExps := aExps, skip := skip }
    let (p1, p2) := positions ctx poly0
    let mut pos1 := p1
    let mut pos2 := p2
    -- 2·B_l·A⁻¹ mod p, for the Gray-code root updates.
    let mut deltas : Array (Array Nat) := #[]
    for l in [0:Bl.size] do
      let mut row : Array Nat := Array.mkEmpty ctx.fb.size
      for i in [0:ctx.fb.size] do
        let p := ctx.fb[i]!
        if i == 0 || skip[i]! then row := row.push 0
        else
          match invMod (A % p) p with
          | none => row := row.push 0
          | some ainv => row := row.push (2 * (Bl[l]! % p) * ainv % p)
      deltas := deltas.push row
    let (buf', found) := sievePoly ctx poly0 pos1 pos2 buf
    buf := buf'
    rels := rels ++ found
    let count := 2 ^ (Bl.size - 1)
    for g in [1:count] do
      -- Gray code: bit v flips between g-1 and g.
      let v := (g &&& (2 ^ 64 - g)).log2
      let gray := g ^^^ (g >>> 1)
      let negate := gray.testBit v
      let bv : Int := (Bl[v]! : Int)
      B := if negate then B - 2 * bv else B + 2 * bv
      let drow := deltas[v]!
      for i in [1:ctx.fb.size] do
        if skip[i]! then continue
        let p := ctx.fb[i]!
        let d := drow[i]!
        let a1 := pos1[i]!
        if a1 < p then
          pos1 := pos1.set! i (if negate then (a1 + d) % p else (a1 + p - d) % p)
        let a2 := pos2[i]!
        if a2 < p then
          pos2 := pos2.set! i (if negate then (a2 + d) % p else (a2 + p - d) % p)
      let poly : Poly := { poly0 with B := B, C := (B * B - (ctx.N : Int)) / (A : Int) }
      let (buf', found) := sievePoly ctx poly pos1 pos2 buf
      buf := buf'
      rels := rels ++ found
  return rels

/-! ## Driver -/

inductive Variant where
  | qs | mpqs | siqs
  deriving Repr, Inhabited, BEq

/-- Union–find over large primes (vertex `1` stands for "no large prime"),
used to count the independent cycles of the large-prime graph while relations
are collected. -/
structure UnionFind where
  parent : Std.HashMap Nat Nat := {}
  size : Std.HashMap Nat Nat := {}
  deriving Inhabited

def UnionFind.find (g : UnionFind) (v : Nat) : Nat := Id.run do
  let mut v := v
  let mut fuel := 64
  while fuel > 0 do
    fuel := fuel - 1
    match g.parent.get? v with
    | some p => if p == v then break else v := p
    | none => break
  return v

/-- Union by size; returns `true` when the edge closes a cycle. -/
def UnionFind.union (g : UnionFind) (a b : Nat) : UnionFind × Bool :=
  let ra := g.find a
  let rb := g.find b
  if ra == rb then (g, true)
  else
    let sa := g.size.getD ra 1
    let sb := g.size.getD rb 1
    let (small, big) := if sa < sb then (ra, rb) else (rb, ra)
    ({ parent := (g.parent.insert small big).insert big big,
       size := g.size.insert big (sa + sb) }, false)

/-- Cycles of the large-prime graph, as lists of edge ids: a breadth-first
spanning forest is built once; every non-forest edge closes one cycle through
the forest paths to the lowest common ancestor. -/
def graphCycles (ends : Array (Nat × Nat)) : Array (Array Nat) := Id.run do
  let mut adj : Std.HashMap Nat (Array (Nat × Nat)) := {}
  for e in [0:ends.size] do
    let (a, b) := ends[e]!
    adj := adj.insert a ((adj.getD a #[]).push (b, e))
    adj := adj.insert b ((adj.getD b #[]).push (a, e))
  -- parent vertex, parent edge, depth
  let mut info : Std.HashMap Nat (Nat × Nat × Nat) := {}
  let mut treeEdge : Array Bool := Array.replicate ends.size false
  for (root, _) in adj.toList do
    if info.contains root then continue
    info := info.insert root (root, ends.size, 0)
    let mut queue : Array Nat := #[root]
    let mut head := 0
    while head < queue.size do
      let v := queue[head]!
      head := head + 1
      let dv := (info.getD v (v, 0, 0)).2.2
      for (w, e) in adj.getD v #[] do
        if !info.contains w then
          info := info.insert w (v, e, dv + 1)
          treeEdge := treeEdge.set! e true
          queue := queue.push w
  let mut cycles : Array (Array Nat) := #[]
  for e in [0:ends.size] do
    if treeEdge[e]! then continue
    let (a, b) := ends[e]!
    let mut path : Array Nat := #[e]
    let mut x := a
    let mut y := b
    let mut fuel := 2 * ends.size + 2
    while x != y && fuel > 0 do
      fuel := fuel - 1
      let (px, ex, dx) := info.getD x (x, 0, 0)
      let (py, ey, dy) := info.getD y (y, 0, 0)
      if dx ≥ dy then
        path := path.push ex
        x := px
      else
        path := path.push ey
        y := py
    if x == y then cycles := cycles.push path
  return cycles

/-- Multiply the relations of a cycle; their large-prime product is the square of
the product of the cycle's vertices, which `absorb` checks. -/
def combineCycle {n : Nat} {fb : Array Nat} (edges : Array (Found n fb)) (ids : Array Nat) :
    Option (Relation n fb) := Id.run do
  if ids.isEmpty then return none
  let rels := ids.toList.map fun i => edges[i]!.rel
  let mut vertices : Std.HashSet Nat := {}
  for i in ids do
    vertices := (vertices.insert edges[i]!.l1).insert edges[i]!.l2
  let s := vertices.fold (fun acc v => acc * v) 1
  match rels with
  | [] => return none
  | r :: rest =>
    let R := r.prod rest
    if h : R.large = s * s then return some (R.absorb s h) else return none

/-- Collect relations on `threads` parallel tasks until `needed` full relations
(counting the cycles of partial relations) are available or `maxRounds` is
reached; then turn every cycle into a full relation. -/
def collect (ctx : Context) (variant : Variant) (needed threads maxRounds : Nat) :
    Array (Relation ctx.n ctx.fb) := Id.run do
  let mut fulls : Array (Relation ctx.n ctx.fb) := #[]
  let mut edges : Array (Found ctx.n ctx.fb) := #[]
  let mut uf : UnionFind := {}
  let mut cycles := 0
  let mut seen : Std.HashSet Nat := {}
  let mut round := 0
  let perTask : Nat := match variant with
    | .qs => 4
    | .mpqs => 8
    | .siqs => 1
  while fulls.size + cycles < needed && round < maxRounds do
    let base := round * threads
    let tasks := (List.range threads).map fun t =>
      Task.spawn fun _ => match variant with
        | .qs => qsBatch ctx (base + t) perTask
        | .mpqs => mpqsBatch ctx (base + t) perTask
        | .siqs => siqsBatch ctx (base + t) perTask
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
  for ids in graphCycles (edges.map fun f => (f.l1, f.l2)) do
    if let some r := combineCycle edges ids then fulls := fulls.push r
  return fulls

/-- Linear algebra and square roots: try each dependency until one splits `n`. -/
def extract (ctx : Context) (rels : Array (Relation ctx.n ctx.fb)) :
    Option (ProperFactor ctx.n) := Id.run do
  let rows := rels.map parityColumns
  let deps := GF2.dependencies (ctx.fb.size + 1) rows 64
  for dep in deps do
    match dep.toList.map (fun i => rels[i]!) with
    | [] => continue
    | r :: rest =>
      match (r.prod rest).toSquares with
      | none => continue
      | some sc =>
        match sc.factor with
        | some d => return some d
        | none => continue
  return none

/-- Configuration of a sieve run. -/
structure Config where
  variant : Variant := .siqs
  threads : Nat := 8
  maxRounds : Nat := 100000
  params : Option Params := none
  deriving Inhabited

/-- Split an odd composite `n` that is not a perfect power. Small factors in the
factor base are returned directly. -/
def splitCore (n : Nat) (cfg : Config := {}) : Option (ProperFactor n) :=
  if n < 1000 then none else
  let params := cfg.params.getD (chooseParams (decimalDigits n))
  match mkContext n params with
  | .inr p => checkFactor n p
  | .inl ctx =>
    let needed := ctx.fb.size + 1 + params.extra
    let rels := collect ctx cfg.variant needed (max 1 cfg.threads) cfg.maxRounds
    if h : ctx.n = n then h ▸ extract ctx rels else none

/-- The public splitter: even numbers and perfect powers are handled first. -/
def split (n : Nat) (cfg : Config := {}) : Option (ProperFactor n) :=
  if n < 4 then none
  else if n % 2 = 0 then checkFactor n 2
  else match perfectPower n with
    | some (r, _) => checkFactor n r
    | none => splitCore n cfg

/-- Every factor returned by the quadratic sieves is a proper divisor. -/
theorem split_sound {n : Nat} {cfg : Config} {d : ProperFactor n}
    (_h : split n cfg = some d) : 1 < d.val ∧ d.val < n ∧ d.val ∣ n := d.property

end PrimeFactorLean.QS
