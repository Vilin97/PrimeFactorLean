import PrimeFactorLean.NFS.Poly
import PrimeFactorLean.NFS.ModP

/-!
# Square roots in `ℤ[ω]` by `p`-adic Newton iteration

Given `γ ∈ ℤ[ω]` that is (hopefully) a square, choose an *inert* prime `p`
(`f` irreducible modulo `p`, so `ℤ[ω]/p = 𝔽_{p^d}`), take a square root of
`γ mod p` in the finite field, and lift an inverse square root `z` with the
Newton step `z ← z (3 - γ z²) / 2`, which doubles the `p`-adic precision. Then
`β = γ z mod p^k`, read with centered coefficients, is the square root of `γ`
in `ℤ[ω]` once `p^k` exceeds twice its coefficients.

This module is a candidate generator only: the number field sieve accepts `β`
only after checking `β · β = γ` exactly (`PrimeFactorLean.GNFS`).
-/

namespace PrimeFactorLean.NFS

open Arith

/-- Coefficients reduced to `[0, P)` (in parallel tasks once they are large: each
reduction is a long division). -/
def modList (P : Nat) (xs : List Int) : List Int :=
  if xs.any (fun c => c.natAbs.log2 ≥ 65536) then
    (xs.map fun c => Task.spawn fun _ => c % (P : Int)).map Task.get
  else xs.map fun c => c % (P : Int)

/-- Centered representatives in `(-P/2, P/2]`. -/
def centerList (P : Nat) (xs : List Int) : List Int :=
  normalize (xs.map fun c =>
    let c := c % (P : Int)
    if 2 * c > (P : Int) then c - P else c)

/-- Multiplication in `(ℤ/P)[ω]`. -/
def mulMod (g : List Int) (P : Nat) (x y : List Int) : List Int :=
  modList P (mulZ g x y)

/-- An inert prime for `f = g + X^d` at or above `start`. -/
def inertPrime (g : List Int) (start : Nat) (tries : Nat := 5000) : Option Nat := Id.run do
  let mut p := start ||| 1
  for _ in [0:tries] do
    if isProbablePrime p then
      let f := ModP.ofInts p (g ++ [1])
      if f.size == g.length + 1 && ModP.isIrreducible p f then return some p
    p := p + 2
  return none

/-- Bit length of the largest coefficient. -/
def maxBits (xs : List Int) : Nat := xs.foldl (fun acc c => max acc (c.natAbs.log2 + 1)) 0

/-- Candidate square root of `γ`, lifted until `p^k` has at least `bits` bits:
Newton's iteration `z ← z (3 - γ z²) / 2` for `γ^(-1/2)` modulo `P = p^(2^k)`,
`γ` reduced once at the last precision and from each precision to the one
below, the halving a shift (`P` is odd). -/
def sqrtCandidate (g γ : List Int) (p bits : Nat) : Option (List Int) := Id.run do
  let f := ModP.ofInts p (g ++ [1])
  let γp := ModP.rem p (ModP.ofInts p γ) f
  if γp.size == 0 then return none
  let some s := ModP.fqSqrt p f γp | return none
  let z0 := ModP.fqInv p f s
  -- the precisions `p^2, p^4, …`
  let mut Ps : Array Nat := #[]
  let mut P := p
  let mut fuel := 64
  while P.log2 < bits + 1 && fuel > 0 do
    fuel := fuel - 1
    P := P * P
    Ps := Ps.push P
  -- `γ` modulo each of them, from the last down
  let mut γs : Array (List Int) := Array.replicate Ps.size []
  let mut cur := γ
  for i in [0:Ps.size] do
    let k := Ps.size - 1 - i
    cur := modList Ps[k]! cur
    γs := γs.set! k cur
  let mut z : List Int := z0.toList.map (fun (c : Nat) => (c : Int))
  -- coefficients in `[0, Q)`: halving modulo the odd `Q` is a shift
  let halve (Q : Nat) (c : Int) : Int := if c % 2 == 0 then c / 2 else (c + Q) / 2
  -- (the last precision by Karp and Markstein's step below)
  let last := if Ps.size ≥ 2 then Ps.size - 1 else Ps.size
  for k in [0:last] do
    let Q := Ps[k]!
    let z2 := mulMod g Q z z
    let t := mulMod g Q γs[k]! z2
    let three := addL [3] (t.map fun c => -c)
    z := (mulMod g Q z three).map (halve Q)
  if last == Ps.size then
    let β := mulMod g P (if Ps.isEmpty then modList P γ else γs[Ps.size - 1]!) z
    return some (centerList P β)
  -- `z ≡ γ^(-1/2)` modulo `h`; `x₀ = γ z` has `x₀² ≡ γ (mod h)`, and
  -- `x₀ + z (γ - x₀²) / 2` is the square root modulo `h²`: `γ - x₀² = h e`, so
  -- only products modulo `h` (half the size) are needed
  let h := Ps[last - 1]!
  let x0 := mulMod g h γs[last - 1]! z
  let x0sq := mulMod g P x0 x0
  let e := (addL γs[last]! (x0sq.map fun c => -c)).map fun c => (c % (P : Int)) / (h : Int)
  let d := (mulMod g h z e).map (halve h)
  let β := addL x0 (d.map fun c => c * (h : Int))
  return some (centerList P β)

/-- Square root of `γ` in `ℤ[ω]`, verified by exact squaring (`none` if the
candidate fails, e.g. because `γ` is not a square); the check is returned. -/
def sqrtZ (g γ : List Int) (p : Nat) : Option {β : List Int // mulZ g β β = normalize γ} :=
  Id.run do
  let fBits := maxBits g
  let base := maxBits γ / 2 + 2 * (g.length + 1) * (fBits + 1) + 64
  for bits in [base, 2 * base, maxBits γ + 4 * (g.length + 1) * (fBits + 1) + 128] do
    if let some β := sqrtCandidate g γ p bits then
      if h : mulZ g β β = normalize γ then return some ⟨β, h⟩
  return none

/-- The first candidate square root of `γ` (at the precisions `sqrtZ` tries)
that `ok` accepts: the caller checks a cheap consequence of `β² = γ` instead of
the exact square. -/
def sqrtFind (g γ : List Int) (p : Nat) (ok : List Int → Bool) : Option (List Int) := Id.run do
  let fBits := maxBits g
  let base := maxBits γ / 2 + 2 * (g.length + 1) * (fBits + 1) + 64
  for bits in [base, 2 * base, maxBits γ + 4 * (g.length + 1) * (fBits + 1) + 128] do
    if let some β := sqrtCandidate g γ p bits then
      if ok β then return some β
  return none

end PrimeFactorLean.NFS
