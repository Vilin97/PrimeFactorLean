import PrimeFactorLean.NFS.ModP
import PrimeFactorLean.NFS.Poly
import PrimeFactorLean.Arith

/-!
# Number field sieve: polynomial selection, factor bases and line sieving

* **Polynomial selection.** For a degree `d` and leading coefficients
  `c_d = 1, 2, …`, take `m = ⌊(n / c_d)^{1/d}⌋` and the balanced base-`m`
  digits of `n`, so that `F(m) = n` with `|c_i| ≤ m/2` below the top two
  coefficients. Candidates are ranked by the logarithmic size of `F` over the
  sieve region plus Murphy's root property `α(F)`.
* **Factor bases.** Rational primes `p ≤ B_r` (root `m mod p`); algebraic prime
  ideals `(p, r)` with `F(r) ≡ 0 (mod p)`, `p ≤ B_a`, plus projective ideals for
  `p ∣ c_d`; quadratic characters `(q, s)` with `q` above the large-prime bound
  and `F'(s) ≢ 0`.
* **Line sieving.** For each `b`, rounded logarithms of the rational and
  algebraic factor-base primes are added over `a ∈ [-A, A)`; survivors on both
  sides are trial divided, allowing one large prime per side. Lines are
  distributed over parallel tasks.

All of this is search code. The number field sieve's correctness
(`PrimeFactorLean.GNFS`) does not depend on it.
-/

namespace PrimeFactorLean.NFS

open Arith

/-! ## Parameters -/

structure Params where
  degree : Nat
  ratBound : Nat
  algBound : Nat
  halfWidth : Nat
  lpMult : Nat := 30
  linesPerTask : Nat := 50
  chars : Nat := 48
  extra : Nat := 80
  fudge : Nat := 4
  sieveFrom : Nat := 40
  polyTries : Nat := 40
  /-- Lines expected to be sieved (shapes the polynomial-selection score). -/
  expectedLines : Nat := 2000
  /-- Half-width `I` of special-`q` lattice sieving (`0` selects line sieving). -/
  latticeI : Nat := 0
  /-- Rows `J` per special-`q`. -/
  latticeJ : Nat := 256
  /-- Special-`q` ideals per task and round. -/
  qPerTask : Nat := 4
  /-- Franke–Kleinjung lattice siever (`NFS.Las`): `log₂ I` (`0` selects the
  older sievers), large-prime and cofactor bits per side, first special-`q`. -/
  lasLogI : Nat := 0
  lpbR : Nat := 0
  lpbA : Nat := 0
  mfbR : Nat := 0
  mfbA : Nat := 0
  qmin : Nat := 0
  deriving Repr, Inhabited

/-- `(digits, params)`: line sieving for small inputs, special-`q` lattice
sieving from 35 digits (measured on balanced semiprimes, 16 threads). -/
def paramTable : List (Nat × Params) :=
  [(20, { degree := 3, ratBound := 1500, algBound := 1500, halfWidth := 4096, lpMult := 15,
          linesPerTask := 10 }),
   (25, { degree := 3, ratBound := 3000, algBound := 3000, halfWidth := 8192, lpMult := 20,
          linesPerTask := 10 }),
   (30, { degree := 3, ratBound := 8000, algBound := 8000, halfWidth := 32768, lpMult := 20,
          linesPerTask := 5 }),
   (35, { degree := 3, ratBound := 12000, algBound := 12000, halfWidth := 65536, lpMult := 25,
          latticeI := 2048, latticeJ := 256, qPerTask := 2 }),
   (40, { degree := 3, ratBound := 20000, algBound := 20000, halfWidth := 131072, lpMult := 30,
          latticeI := 2048, latticeJ := 256, qPerTask := 2 }),
   (45, { degree := 4, ratBound := 35000, algBound := 35000, halfWidth := 262144, lpMult := 40,
          latticeI := 4096, latticeJ := 256, qPerTask := 2 }),
   (50, { degree := 4, ratBound := 60000, algBound := 60000, halfWidth := 262144, lpMult := 50,
          latticeI := 4096, latticeJ := 256, qPerTask := 4 }),
   (55, { degree := 4, ratBound := 90000, algBound := 90000, halfWidth := 262144, lpMult := 60,
          latticeI := 4096, latticeJ := 512, qPerTask := 2 }),
   -- From 60 digits: the Franke–Kleinjung siever (`NFS.Las`) with CADO-NFS-like
   -- bounds: factor bases, large-prime bits `lpb` and cofactor bits `mfb`.
   (60, { degree := 4, ratBound := 80000, algBound := 110000, halfWidth := 262144,
          lasLogI := 10, lpbR := 18, lpbA := 19, mfbR := 18, mfbA := 38, qmin := 62000,
          qPerTask := 4 }),
   (65, { degree := 4, ratBound := 160000, algBound := 160000, halfWidth := 262144,
          lasLogI := 10, lpbR := 19, lpbA := 20, mfbR := 19, mfbA := 40, qmin := 80000,
          qPerTask := 4 }),
   (70, { degree := 4, ratBound := 340000, algBound := 245000, halfWidth := 262144,
          lasLogI := 11, lpbR := 20, lpbA := 21, mfbR := 20, mfbA := 42, qmin := 100000,
          qPerTask := 2 }),
   (80, { degree := 4, ratBound := 293000, algBound := 340000, halfWidth := 262144,
          lasLogI := 11, lpbR := 21, lpbA := 21, mfbR := 41, mfbA := 42, qmin := 66600,
          qPerTask := 2 }),
   (90, { degree := 4, ratBound := 404000, algBound := 811000, halfWidth := 262144,
          lasLogI := 11, lpbR := 23, lpbA := 23, mfbR := 46, mfbA := 46, qmin := 200000,
          qPerTask := 2 }),
   (100, { degree := 5, ratBound := 650000, algBound := 800000, halfWidth := 262144,
           lasLogI := 11, lpbR := 25, lpbA := 26, mfbR := 48, mfbA := 51, qmin := 180000,
           qPerTask := 2 })]

def chooseParams (digits : Nat) : Params :=
  ((paramTable.find? fun e => digits ≤ e.1).map Prod.snd).getD
    ((paramTable.getLast?.map Prod.snd).getD default)

/-! ## Polynomial selection -/

structure Selection where
  /-- `c_0, …, c_d` with `c_d > 0`. -/
  coeffs : Array Int
  m : Nat
  deriving Repr, Inhabited

def Selection.degree (s : Selection) : Nat := s.coeffs.size - 1

def Selection.lead (s : Selection) : Nat := (s.coeffs[s.coeffs.size - 1]!).toNat

/-- Homogenized `F(a, b) = Σ c_i a^i b^{d-i}` by Horner's rule. -/
def homEval (cs : Array Int) (a b : Int) : Int := Id.run do
  let d := cs.size - 1
  let mut acc := cs[d]!
  let mut bp : Int := 1
  for i' in [0:d] do
    let i := d - 1 - i'
    bp := bp * b
    acc := acc * a + cs[i]! * bp
  return acc

/-- Balanced base-`m` digits of `n` with `d + 1` digits. -/
def baseM (n m d : Nat) : Array Int := Id.run do
  let mut r : Int := n
  let mut cs : Array Int := #[]
  for _ in [0:d] do
    let c := r % (m : Int)
    let c := if 2 * c > (m : Int) then c - m else c
    cs := cs.push c
    r := (r - c) / (m : Int)
  return cs.push r

/-- Murphy's root property over the primes below 200 (in bits). -/
def alphaScore (cs : Array Int) : Float := Id.run do
  let mut alpha : Float := 0
  for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
            79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163,
            167, 173, 179, 181, 191, 193, 197, 199] do
    let mut roots := 0
    for r in [0:p] do
      if homEval cs r 1 % (p : Int) == 0 then roots := roots + 1
    if cs[cs.size - 1]! % (p : Int) == 0 then roots := roots + 1
    let pf := p.toFloat
    alpha := alpha + (1.0 / (pf - 1.0) - roots.toFloat * pf / (pf * pf - 1.0)) * Float.log2 pf
  return alpha

/-- Average `log₂ |F(a,b)| + log₂ |a - b m|` over a grid of the sieve region
`[-A, A) × [1, lines]`: the quantity that governs the relation yield. -/
def regionScore (sel : Selection) (A lines : Nat) : Float := Id.run do
  let mut total : Float := 0
  let mut count : Float := 0
  for i in [1:9] do
    for j in [1:5] do
      let a : Int := ((2 * i * A / 9 : Nat) : Int) - (A : Int) + 1
      let b : Int := ((j * lines / 5 : Nat) + 1 : Nat)
      let alg := (homEval sel.coeffs a b).natAbs
      let rat := (a - b * (sel.m : Int)).natAbs
      total := total + Float.log2 (alg.toFloat + 1.0) + Float.log2 (rat.toFloat + 1.0)
      count := count + 1
  return total / count

/-- Choose a base-`m` polynomial of the given degree: leading coefficients are
scanned geometrically up to about `n^{1/(d+1)}` (where all coefficients have
size about `m`), each candidate is scored by its sampled norms over the sieve
region plus Murphy's `α`, and the best one is refined locally. -/
def selectPolynomial (n d tries : Nat) (A lines : Nat) : Option Selection := Id.run do
  let candidate (lead : Nat) : Option Selection :=
    let m := iroot (n / lead) d
    if m < 2 then none else
    let cs := baseM n m d
    if cs[d]! ≤ 0 || homEval cs m 1 != (n : Int) then none else some ⟨cs, m⟩
  let cap := 4 * iroot n (d + 1) + 2
  let mut scored : Array (Float × Selection) := #[]
  let mut lead := 1
  while lead ≤ cap do
    if let some sel := candidate lead then
      scored := scored.push (regionScore sel A lines, sel)
    lead := lead + max 1 (lead / 8)
  if scored.isEmpty then return none
  let sorted := scored.qsort (fun x y => x.1 < y.1)
  -- Local refinement around the best few leading coefficients.
  let mut refined := sorted.extract 0 (min 4 sorted.size)
  for k in [0:min 4 sorted.size] do
    let base := sorted[k]!.2.lead
    for delta in [1:tries + 1] do
      for lead' in [base + delta, base - delta] do
        if lead' ≥ 1 then
          if let some sel := candidate lead' then
            refined := refined.push (regionScore sel A lines, sel)
  let ranked := refined.qsort (fun x y => x.1 < y.1)
  let mut best : Option Selection := none
  let mut bestScore : Float := 1.0e30
  for k in [0:min 24 ranked.size] do
    let (sz, sel) := ranked[k]!
    let score := sz + alphaScore sel.coeffs
    if score < bestScore then
      bestScore := score
      best := some sel
  return best

/-- The monic polynomial `f(y) = c_d^{d-1} F(y / c_d)`: its lower coefficients
`g_i = c_i c_d^{d-1-i}`, so that `ω = c_d α` is an algebraic integer. -/
def monicLower (cs : Array Int) : List Int := Id.run do
  let d := cs.size - 1
  let cd := cs[d]!
  let mut g : List Int := []
  for i' in [0:d] do
    let i := d - 1 - i'
    g := (cs[i]! * cd ^ (d - 1 - i)) :: g
  return g

/-- `f'(ω)` as an element of `ℤ[ω]` (coefficients of the derivative). -/
def derivative (g : List Int) : List Int :=
  let d := g.length
  ((List.range d).map fun i => if i + 1 < d then ((i + 1 : Nat) : Int) * g[i + 1]! else (d : Int))

/-! ## Factor bases -/

structure FactorBase where
  ratPrimes : Array Nat
  ratRoots : Array Nat
  ratLogs : ByteArray
  algPrimes : Array Nat
  /-- The root `r`, or `p` itself for a projective ideal. -/
  algRoots : Array Nat
  algLogs : ByteArray
  chars : Array (Nat × Nat)
  deriving Inhabited

def logByte (p : Nat) : UInt8 := (Float.round (Float.log2 p.toFloat)).toUInt8

def buildFactorBase (sel : Selection) (params : Params) (lpA : Nat) : FactorBase := Id.run do
  let limit := max params.ratBound params.algBound
  let primes := primesUpTo limit
  let mut ratPrimes := #[]
  let mut ratRoots := #[]
  let mut ratLogs := ByteArray.emptyWithCapacity primes.size
  let mut algPrimes := #[]
  let mut algRoots := #[]
  let mut algLogs := ByteArray.emptyWithCapacity primes.size
  let cs := sel.coeffs
  let d := sel.degree
  for p in primes do
    if p ≤ params.ratBound then
      ratPrimes := ratPrimes.push p
      ratRoots := ratRoots.push (sel.m % p)
      ratLogs := ratLogs.push (logByte p)
    if p ≤ params.algBound then
      let f := ModP.ofInts p cs.toList
      for r in ModP.roots p f do
        algPrimes := algPrimes.push p
        algRoots := algRoots.push r
        algLogs := algLogs.push (logByte p)
      if cs[d]! % (p : Int) == 0 then
        algPrimes := algPrimes.push p
        algRoots := algRoots.push p
        algLogs := algLogs.push (logByte p)
  -- Quadratic characters above the algebraic large-prime bound.
  let mut chars : Array (Nat × Nat) := #[]
  let mut q := lpA + 1
  let deriv : Array Int := (Array.range d).map fun i => ((i + 1 : Nat) : Int) * cs[i + 1]!
  while chars.size < params.chars do
    q := q + 1
    if !isProbablePrime q then continue
    if cs[d]! % (q : Int) == 0 then continue
    let f := ModP.ofInts q cs.toList
    for s in ModP.roots q f do
      if chars.size < params.chars then
        if ModP.evalAt q (ModP.ofInts q deriv.toList) s != 0 then
          chars := chars.push (q, s)
  return { ratPrimes, ratRoots, ratLogs, algPrimes, algRoots, algLogs, chars }

/-! ## Relations and line sieving -/

structure Rel where
  a : Int
  b : Nat
  /-- `(prime, exponent)` for `|a - b m|`, including a large prime. -/
  rat : List (Nat × Nat)
  ratNeg : Bool
  /-- `(p, r, exponent)` prime ideals of `F(a, b)`, including a large ideal. -/
  alg : List (Nat × Nat × Nat)
  deriving Inhabited, Repr

structure Ctx where
  n : Nat
  sel : Selection
  fb : FactorBase
  A : Nat
  lpR : Nat
  lpA : Nat
  fudge : Nat
  ratStart : Nat
  algStart : Nat
  zeros : ByteArray

def mkCtx (n : Nat) (sel : Selection) (params : Params) : Ctx := Id.run do
  let lpR := params.lpMult * params.ratBound
  let lpA := params.lpMult * params.algBound
  let fb := buildFactorBase sel params lpA
  let mut ratStart := 0
  while ratStart < fb.ratPrimes.size && fb.ratPrimes[ratStart]! < params.sieveFrom do
    ratStart := ratStart + 1
  let mut algStart := 0
  while algStart < fb.algPrimes.size && fb.algPrimes[algStart]! < params.sieveFrom do
    algStart := algStart + 1
  let size := 2 * params.halfWidth
  let mut zeros := ByteArray.emptyWithCapacity size
  for _ in [0:size] do zeros := zeros.push 0
  return { n, sel, fb, A := params.halfWidth, lpR, lpA, fudge := params.fudge,
           ratStart, algStart, zeros }

def stripPrime (u p : Nat) : Nat × Nat := Id.run do
  let mut u := u
  let mut e := 0
  while u % p == 0 && u > 0 do
    u := u / p
    e := e + 1
  return (u, e)

/-- Trial-divide both norms of `(a, b)`; `none` unless both sides are smooth up
to one large prime each. -/
def verify (ctx : Ctx) (b j : Nat) : Option Rel := Id.run do
  let a : Int := (j : Int) - (ctx.A : Int)
  if Nat.gcd a.natAbs b != 1 then return none
  let fb := ctx.fb
  -- Rational side.
  let v : Int := a - (b : Int) * (ctx.sel.m : Int)
  if v == 0 then return none
  let mut u := v.natAbs
  let mut rat : List (Nat × Nat) := []
  for i in [0:fb.ratPrimes.size] do
    let p := fb.ratPrimes[i]!
    if j % p == (b % p * fb.ratRoots[i]! + ctx.A) % p then
      let (u', e) := stripPrime u p
      if e > 0 then
        u := u'
        rat := (p, e) :: rat
  if u > 1 then
    if u < ctx.lpR then rat := (u, 1) :: rat else return none
  -- Algebraic side.
  let w := homEval ctx.sel.coeffs a b
  if w == 0 then return none
  let mut z := w.natAbs
  let mut alg : List (Nat × Nat × Nat) := []
  for i in [0:fb.algPrimes.size] do
    let p := fb.algPrimes[i]!
    let r := fb.algRoots[i]!
    let hit := if r == p then b % p == 0 else j % p == (b % p * r + ctx.A) % p
    if hit then
      let (z', e) := stripPrime z p
      if e > 0 then
        z := z'
        alg := (p, r, e) :: alg
  if z > 1 then
    if z < ctx.lpA then
      let L := z
      let r := if b % L == 0 then L else
        match invMod (b % L) L with
        | some inv => (a % (L : Int)).toNat * inv % L
        | none => L
      alg := (L, r, 1) :: alg
    else return none
  return some ⟨a, b, rat, decide (v < 0), alg⟩

/-- Threshold in bits for a value of absolute size `x`, after allowing a large
prime of `lpBits` bits and `fudge` bits of rounding slack. -/
def threshold (x : Nat) (lpBits fudge : Nat) : UInt8 :=
  let bits := x.log2 + 1
  if bits > lpBits + fudge + 1 then (min 255 (bits - lpBits - fudge)).toUInt8 else 1

/-- Positions in `[lo, hi)` whose byte reaches `thr`, testing blocks by a fold
first and scanning only blocks that contain a candidate. -/
def scanRange (s : ByteArray) (thr : UInt8) (lo hi : Nat) (out : Array Nat) : Array Nat := Id.run do
  let block := 1024
  let mut cands := out
  let mut b := lo
  while b < hi do
    let e := min hi (b + block)
    if s.foldl (fun acc x => acc || x ≥ thr) false b e then
      for j in [b:e] do
        if s.get! j ≥ thr then cands := cands.push j
    b := e
  return cands

def scanAbove (s : ByteArray) (thr : UInt8) (size : Nat) : Array Nat := scanRange s thr 0 size #[]

/-- Sieve one line `b`; return the verified relations. -/
def sieveLine (ctx : Ctx) (b : Nat) (bufR bufA : ByteArray) :
    ByteArray × ByteArray × Array Rel := Id.run do
  let size := 2 * ctx.A
  let fb := ctx.fb
  -- Rational side.
  let mut s := ctx.zeros.copySlice 0 bufR 0 size
  for i in [ctx.ratStart:fb.ratPrimes.size] do
    let p := fb.ratPrimes[i]!
    let lg := fb.ratLogs.get! i
    let mut k := (b % p * fb.ratRoots[i]! + ctx.A) % p
    while k < size do
      s := s.set! k (s.get! k + lg)
      k := k + p
  let thrR := threshold (b * ctx.sel.m + ctx.A) (ctx.lpR.log2 + 1) ctx.fudge
  let cands := scanAbove s thrR size
  if cands.isEmpty then return (s, bufA, #[])
  -- Algebraic side.
  let mut t := ctx.zeros.copySlice 0 bufA 0 size
  for i in [ctx.algStart:fb.algPrimes.size] do
    let p := fb.algPrimes[i]!
    let r := fb.algRoots[i]!
    if r == p then continue
    let lg := fb.algLogs.get! i
    let mut k := (b % p * r + ctx.A) % p
    while k < size do
      t := t.set! k (t.get! k + lg)
      k := k + p
  -- Algebraic thresholds per chunk of 4096 positions.
  let chunk := 4096
  let lpBitsA := ctx.lpA.log2 + 1
  let mut rels : Array Rel := #[]
  for k in cands do
    let c := k / chunk
    let lo : Int := (c * chunk : Nat) - (ctx.A : Int)
    let hi : Int := lo + chunk
    let mid : Int := lo + chunk / 2
    let size1 := (homEval ctx.sel.coeffs lo b).natAbs
    let size2 := (homEval ctx.sel.coeffs hi b).natAbs
    let size3 := (homEval ctx.sel.coeffs mid b).natAbs
    let thrA := threshold (max size1 (max size2 size3)) lpBitsA ctx.fudge
    if t.get! k ≥ thrA then
      if let some rel := verify ctx b k then rels := rels.push rel
  return (s, t, rels)

/-- Sieve lines `first, …, first + count - 1`. -/
def sieveLines (ctx : Ctx) (first count : Nat) : Array Rel := Id.run do
  let mut bufR := ctx.zeros
  let mut bufA := ctx.zeros
  let mut rels := #[]
  for b in [first:first + count] do
    let (r', a', found) := sieveLine ctx b bufR bufA
    bufR := r'
    bufA := a'
    rels := rels ++ found
  return rels

end PrimeFactorLean.NFS
