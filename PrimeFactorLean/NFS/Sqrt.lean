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

/-- Coefficients reduced to `[0, P)`. -/
def modList (P : Nat) (xs : List Int) : List Int := xs.map fun c => c % (P : Int)

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

/-- Candidate square root of `γ`, lifted until `p^k` has at least `bits` bits. -/
def sqrtCandidate (g γ : List Int) (p bits : Nat) : Option (List Int) := Id.run do
  let f := ModP.ofInts p (g ++ [1])
  let γp := ModP.rem p (ModP.ofInts p γ) f
  if γp.size == 0 then return none
  let some s := ModP.fqSqrt p f γp | return none
  let z0 := ModP.fqInv p f s
  let mut P := p
  let mut z : List Int := z0.toList.map (fun (c : Nat) => (c : Int))
  let mut fuel := 64
  while P.log2 < bits + 1 && fuel > 0 do
    fuel := fuel - 1
    P := P * P
    let γP := modList P γ
    let z2 := mulMod g P z z
    let t := mulMod g P γP z2
    let three := addL [3] (t.map fun c => -c)
    let inv2 := (P + 1) / 2
    z := modList P ((mulMod g P z three).map fun c => c * (inv2 : Int))
  let β := mulMod g P (modList P γ) z
  return some (centerList P β)

/-- Square root of `γ` in `ℤ[ω]`, verified by exact squaring (`none` if the
candidate fails, e.g. because `γ` is not a square). -/
def sqrtZ (g γ : List Int) (p : Nat) : Option (List Int) := Id.run do
  let fBits := maxBits g
  let base := maxBits γ / 2 + 2 * (g.length + 1) * (fBits + 1) + 64
  for bits in [base, 2 * base, maxBits γ + 4 * (g.length + 1) * (fBits + 1) + 128] do
    if let some β := sqrtCandidate g γ p bits then
      if mulZ g β β == normalize γ then return some β
  return none

end PrimeFactorLean.NFS
