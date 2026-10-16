/-!
# Montgomery arithmetic: the interface

`Arith α μ` describes residues `α` modulo a modulus description `μ` in
Montgomery form (`x` is represented by `x R mod n` for a power of two `R`).
The fixed-width instances `N1 … N12` (28-bit limbs) are generated in
`PrimeFactorLean.MontGen` by `scripts/gen_mont.py`; generic algorithms (ECM,
`p - 1`) are written against this class and specialize to each width.

Everything here is untrusted search arithmetic: callers only ever use it to
produce a candidate `z` whose `gcd(z, n)` is then checked.
-/

namespace PrimeFactorLean.Mont

/-- `-p⁻¹ mod 2^28` for odd `p` (Newton's iteration). -/
def negInv28 (p : UInt64) : UInt64 := Id.run do
  let mut x : UInt64 := p
  for _ in [0:6] do x := x * (2 - p * x)
  return (-x) &&& 0xFFFFFFF

class Arith (α : Type) (μ : outParam Type) where
  mul : μ → α → α → α
  sqr : μ → α → α
  add : μ → α → α → α
  sub : μ → α → α → α
  modulus : μ → Nat
  /-- A residue from its limbs (no conversion). -/
  ofLimbs : μ → Nat → α
  /-- The limbs as a natural number (the Montgomery representative). -/
  limbNat : α → Nat
  isZero : α → Bool
  limbs : Nat

namespace Arith

variable {α μ : Type} [Arith α μ]

/-- `x` in Montgomery form. -/
@[inline] def toMont (m : μ) (x : Nat) : α :=
  let n := modulus (α := α) m
  ofLimbs m (((x % n) <<< (28 * limbs (α := α) (μ := μ))) % n)

/-- The plain residue of a Montgomery representative. -/
@[inline] def fromMont (m : μ) (a : α) : Nat :=
  limbNat (mul m a (ofLimbs m 1))

/-- `gcd` of the represented value with `n` (`R` is a power of two and `n` is odd,
so the Montgomery representative has the same gcd). -/
@[inline] def gcdN (m : μ) (a : α) : Nat := Nat.gcd (limbNat a) (modulus (α := α) m)

end Arith

end PrimeFactorLean.Mont
