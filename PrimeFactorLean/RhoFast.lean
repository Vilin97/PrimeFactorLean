import PrimeFactorLean.MontGen
import PrimeFactorLean.Core

/-!
# Brent's rho on fixed-width Montgomery arithmetic

Pollard's rho with Brent's cycle detection, iterating `y ↦ y² + c` on the
Montgomery representatives of `PrimeFactorLean.MontGen` (a different but
equally random map modulo every prime factor), with the products
`∏ (x - y)` batched between gcds and a single-step replay when a batch's gcd is
`n`. The reported factor is checked like every other splitter (`checkFactor`),
so `split_sound` holds for all inputs.
-/

namespace PrimeFactorLean.RhoF

open Mont Mont.Arith

structure Pair (α : Type) where
  y : α
  q : α

section Generic

variable {α μ : Type} [Arith α μ]

@[specialize] def step (m : μ) (c y : α) : α := add m (sqr m y) c

/-- `k` steps. -/
@[specialize] def iter (m : μ) (c y : α) (k : Nat) : α := Id.run do
  let mut y := y
  for _ in [0:k] do
    y := step m c y
  return y

/-- `k` steps from `y`, multiplying `q` by `x - y` after each.

The loop keeps both accumulators in mutable state. This avoids allocating an
intermediate `Pair` for every recursive step and lets native compilation emit
a tight loop for the fixed-width Montgomery instances.
-/
@[specialize] def batch (m : μ) (c x y q : α) (k : Nat) : Pair α := Id.run do
  let mut y := y
  let mut q := q
  for _ in [0:k] do
    y := step m c y
    q := mul m q (sub m x y)
  return ⟨y, q⟩

/-- Single steps from `ys` until `gcd(x - ys, n) ≠ 1` (after a batch whose gcd was `n`).

This is the recovery path for a collapsed product. Keeping the point and gcd
in a loop avoids constructing a recursive closure for every replay step.
-/
@[specialize] def single (m : μ) (c x ys : α) (k : Nat) : Nat := Id.run do
  let mut ys := ys
  let mut remaining := k
  let mut g := 1
  while remaining > 0 && g == 1 do
    ys := step m c ys
    g := gcdN m (sub m x ys)
    remaining := remaining - 1
  return g

/-- Brent's rho for `y ↦ y² + c₀` from `y = 2`, about `maxSteps` steps at most:
the final gcd (`1` when nothing was found). -/
@[specialize] def brentW (m : μ) (c0 maxSteps batchLen : Nat) : Nat := Id.run do
  let n := modulus (α := α) m
  let c : α := toMont m c0
  let mut y : α := toMont m 2
  let mut x := y
  let mut ys := y
  let mut q : α := toMont m 1
  let mut r := 1
  let mut g := 1
  let mut steps := 0
  while g == 1 && steps < maxSteps do
    x := y
    y := iter m c y r
    let mut k := 0
    while k < r && g == 1 do
      ys := y
      let len := min batchLen (r - k)
      let p := batch m c x y q len
      y := p.y
      q := p.q
      g := gcdN m q
      k := k + len
    steps := steps + r
    r := 2 * r
  if g == n then g := single m c x ys (2 * r + batchLen)
  return g

end Generic

/-- One Brent run at the width that fits `n` (`1` beyond 336 bits). -/
def brent (n c maxSteps : Nat) : Nat :=
  let batch := if n < 2 ^ 48 then 256 else 128
  match (n.log2 + 28) / 28 with
  | 1 => brentW (α := N1) (Mod1.ofNat n) c maxSteps batch
  | 2 => brentW (α := N2) (Mod2.ofNat n) c maxSteps batch
  | 3 => brentW (α := N3) (Mod3.ofNat n) c maxSteps batch
  | 4 => brentW (α := N4) (Mod4.ofNat n) c maxSteps batch
  | 5 => brentW (α := N5) (Mod5.ofNat n) c maxSteps batch
  | 6 => brentW (α := N6) (Mod6.ofNat n) c maxSteps batch
  | 7 => brentW (α := N7) (Mod7.ofNat n) c maxSteps batch
  | 8 => brentW (α := N8) (Mod8.ofNat n) c maxSteps batch
  | 9 => brentW (α := N9) (Mod9.ofNat n) c maxSteps batch
  | 10 => brentW (α := N10) (Mod10.ofNat n) c maxSteps batch
  | 11 => brentW (α := N11) (Mod11.ofNat n) c maxSteps batch
  | 12 => brentW (α := N12) (Mod12.ofNat n) c maxSteps batch
  | _ => 1

/-- Up to `restarts` runs with `c = 1, 3, 5, …`; even `n` is answered by `2`. -/
def split (n maxSteps restarts : Nat) : Option (ProperFactor n) := Id.run do
  if n < 4 then return none
  if n % 2 == 0 then return checkFactor n 2
  for t in [0:restarts] do
    let g := brent n (2 * t + 1) maxSteps
    if 1 < g && g < n then
      if let some d := checkFactor n g then return some d
  return none

/-- Every factor returned by the fast rho is a proper divisor. -/
theorem split_sound {n s r : Nat} {d : ProperFactor n} (_h : split n s r = some d) :
    1 < d.val ∧ d.val < n ∧ d.val ∣ n := d.property

end PrimeFactorLean.RhoF
