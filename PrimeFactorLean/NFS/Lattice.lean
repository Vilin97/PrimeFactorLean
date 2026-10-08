import PrimeFactorLean.NFS.Sieve

/-!
# Special-`q` lattice sieving (Pollard)

For an algebraic prime ideal `(q, ρ)` above the factor base, every coprime pair
with `a ≡ ρ b (mod q)` has `q ∣ F(a, b)`. These pairs form the lattice with
basis `(q, 0), (ρ, 1)`; after Gauss reduction (weighted by the polynomial's
skewness) it has a short basis `u, v`, and `(a, b) = i u + j v` with small
`(i, j)` covers the region near the origin where both norms are smallest, with
the algebraic norm already divided by `q`.

A factor-base prime `p` with root `r` divides `a - b r` exactly when
`i (u_a - u_b r) + j (v_a - v_b r) ≡ 0 (mod p)`, i.e. on the progression
`i ≡ j R_p (mod p)`; projective roots use `b` instead of `a - b r`. The sieve
runs over rows `j` with cache-sized arrays indexed by `i`, advancing each
start by `R_p` from one row to the next.

Search code only: relations are checked by exact trial division, and the
number field sieve's congruence is proved independently (`GNFS.nfs_square`).
-/

namespace PrimeFactorLean.NFS

open Arith

/-- Gauss–Lagrange reduction of the lattice `{(a, b) : a ≡ ρ b (mod q)}` for the
norm `a² + s² b²`. -/
def reduceLattice (q ρ s : Nat) : (Int × Int) × (Int × Int) := Id.run do
  let s2 : Int := (s * s : Nat)
  let dot (x y : Int × Int) : Int := x.1 * y.1 + s2 * x.2 * y.2
  let mut u : Int × Int := ((q : Int), 0)
  let mut v : Int × Int := ((ρ : Int), 1)
  let mut fuel := 200
  while fuel > 0 do
    fuel := fuel - 1
    if dot v v < dot u u then
      let t := u
      u := v
      v := t
    let uu := dot u u
    if uu == 0 then break
    let uv := dot u v
    -- nearest integer to uv / uu
    let μ := (2 * uv + uu) / (2 * uu)
    if μ == 0 then break
    v := (v.1 - μ * u.1, v.2 - μ * u.2)
  return (u, v)

/-- `R` with `i ≡ j R (mod p)` for the root `r` (or `p` if projective);
`p` itself means the progression is degenerate (only rows `j ≡ 0`). -/
def latticeRoot (p r : Nat) (u v : Int × Int) : Nat :=
  let pi : Int := p
  let α : Int := if r == p then u.2 % pi else (u.1 - u.2 * (r : Int)) % pi
  let β : Int := if r == p then v.2 % pi else (v.1 - v.2 * (r : Int)) % pi
  if α == 0 then p
  else match invMod α.toNat p with
    | some inv => (((pi - β) % pi).toNat * inv) % p
    | none => p

/-- Algebraic prime ideals `(q, ρ)` with `q ≥ start`, for special-`q` sieving. -/
def specialQs (sel : Selection) (start count : Nat) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  let mut q := start
  let cs := sel.coeffs
  while out.size < count do
    q := q + 1
    if !isProbablePrime q then continue
    if cs[cs.size - 1]! % (q : Int) == 0 then continue
    for ρ in ModP.roots q (ModP.ofInts q cs.toList) do
      out := out.push (q, ρ)
  return out

/-- Trial-divide the norms of a lattice point. A factor-base prime `p` with a
nondegenerate progression divides the norm exactly when the position `k` is
congruent to that row's start (`ratCur`/`algCur`), so most primes cost one
small remainder; degenerate progressions are tested on `(a, b)` directly. The
special-`q` ideal is divided out first. -/
def verifyLattice (ctx : Ctx) (a : Int) (b : Nat) (q ρ k : Nat)
    (ratR ratCur algR algCur : Array Nat) : Option Rel := Id.run do
  if b == 0 || Nat.gcd a.natAbs b != 1 then return none
  let fb := ctx.fb
  let v : Int := a - (b : Int) * (ctx.sel.m : Int)
  if v == 0 then return none
  let bi : Int := b
  let mut u := v.natAbs
  let mut rat : List (Nat × Nat) := []
  for i in [0:fb.ratPrimes.size] do
    let p := fb.ratPrimes[i]!
    let hit := if ratR[i]! == p then (a - bi * (fb.ratRoots[i]! : Int)) % (p : Int) == 0
      else k % p == ratCur[i]!
    if hit then
      let (u', e) := stripPrime u p
      if e > 0 then
        u := u'
        rat := (p, e) :: rat
  if u > 1 then
    if u < ctx.lpR then rat := (u, 1) :: rat else return none
  let w := homEval ctx.sel.coeffs a b
  if w == 0 then return none
  let (z0, eq) := stripPrime w.natAbs q
  if eq == 0 then return none
  let mut z := z0
  let mut alg : List (Nat × Nat × Nat) := [(q, ρ, eq)]
  for i in [0:fb.algPrimes.size] do
    let p := fb.algPrimes[i]!
    let r := fb.algRoots[i]!
    let hit :=
      if algR[i]! == p then
        if r == p then b % p == 0 else (a - bi * (r : Int)) % (p : Int) == 0
      else k % p == algCur[i]!
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

/-- Sieve the region `i ∈ [-I, I)`, `1 ≤ j ≤ J` of one special-`q` lattice. -/
def sieveSpecialQ (ctx : Ctx) (q ρ I J skew : Nat) : Array Rel := Id.run do
  let (u, v) := reduceLattice q ρ skew
  let fb := ctx.fb
  let width := 2 * I
  let ratR := (Array.range fb.ratPrimes.size).map fun k =>
    latticeRoot fb.ratPrimes[k]! fb.ratRoots[k]! u v
  let algR := (Array.range fb.algPrimes.size).map fun k =>
    latticeRoot fb.algPrimes[k]! fb.algRoots[k]! u v
  -- Row starts k ≡ j R + I (mod p) for the current row j (initially j = 1).
  let mut ratCur := (Array.range fb.ratPrimes.size).map fun k =>
    let p := fb.ratPrimes[k]!
    (ratR[k]! + I) % p
  let mut algCur := (Array.range fb.algPrimes.size).map fun k =>
    let p := fb.algPrimes[k]!
    (algR[k]! + I) % p
  let zeros := ctx.zeros.extract 0 width
  let mut sR := zeros
  let mut sA := zeros
  let mut rels : Array Rel := #[]
  let lpBitsR := ctx.lpR.log2 + 1
  let lpBitsA := ctx.lpA.log2 + 1
  let chunk := 1024
  let chunks := (width + chunk - 1) / chunk
  for j in [1:J + 1] do
    -- Rational side.
    sR := zeros.copySlice 0 sR 0 width
    for k in [ctx.ratStart:fb.ratPrimes.size] do
      let p := fb.ratPrimes[k]!
      if ratR[k]! == p then continue
      let lg := fb.ratLogs.get! k
      let mut pos := ratCur[k]!
      while pos < width do
        sR := sR.set! pos (sR.get! pos + lg)
        pos := pos + p
    -- Per-chunk thresholds from the norms at chunk midpoints.
    let mut thrR : Array UInt8 := Array.mkEmpty chunks
    let mut thrA : Array UInt8 := Array.mkEmpty chunks
    for c in [0:chunks] do
      let i : Int := ((c * chunk + chunk / 2 : Nat) : Int) - (I : Int)
      let a := i * u.1 + (j : Int) * v.1
      let b := i * u.2 + (j : Int) * v.2
      let rn := (a - b * (ctx.sel.m : Int)).natAbs
      let an := (homEval ctx.sel.coeffs a b).natAbs / q
      thrR := thrR.push (threshold (rn + 1) lpBitsR ctx.fudge)
      thrA := thrA.push (threshold (an + 1) lpBitsA ctx.fudge)
    let mut cands : Array Nat := #[]
    for c in [0:chunks] do
      cands := scanRange sR thrR[c]! (c * chunk) (min width ((c + 1) * chunk)) cands
    if !cands.isEmpty then
      sA := zeros.copySlice 0 sA 0 width
      for k in [ctx.algStart:fb.algPrimes.size] do
        let p := fb.algPrimes[k]!
        if algR[k]! == p then continue
        let lg := fb.algLogs.get! k
        let mut pos := algCur[k]!
        while pos < width do
          sA := sA.set! pos (sA.get! pos + lg)
          pos := pos + p
      for k in cands do
        if sA.get! k ≥ thrA[k / chunk]! then
          let i : Int := (k : Int) - (I : Int)
          let a := i * u.1 + (j : Int) * v.1
          let b := i * u.2 + (j : Int) * v.2
          let (a, b) := if b < 0 then (-a, -b) else (a, b)
          if let some rel := verifyLattice ctx a b.toNat q ρ k ratR ratCur algR algCur then
            rels := rels.push rel
    -- Advance every progression to the next row.
    for k in [0:fb.ratPrimes.size] do
      let p := fb.ratPrimes[k]!
      let r := ratR[k]!
      if r != p then
        let c := ratCur[k]! + r
        ratCur := ratCur.set! k (if c ≥ p then c - p else c)
    for k in [0:fb.algPrimes.size] do
      let p := fb.algPrimes[k]!
      let r := algR[k]!
      if r != p then
        let c := algCur[k]! + r
        algCur := algCur.set! k (if c ≥ p then c - p else c)
  return rels

/-- Natural skewness of `F`: balances the leading and constant coefficients. -/
def skewness (sel : Selection) : Nat :=
  let d := sel.degree
  let c0 := (sel.coeffs[0]!).natAbs
  let cd := (sel.coeffs[d]!).natAbs
  max 1 (iroot (c0 / max 1 cd) d)

end PrimeFactorLean.NFS
