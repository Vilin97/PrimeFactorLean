import PrimeFactorLean.ECMFast
import PrimeFactorLean.PMinusOne

/-!
# Pollard `p - 1` on fixed-width Montgomery arithmetic

The method of `PrimeFactorLean.PMinusOne` with the residues of
`PrimeFactorLean.MontGen`: stage 1 is one left-to-right exponentiation of the
base `3` by `E = ∏ q` (maximal prime powers `q ≤ B1`), stage 2 the standard
continuation over the primes of `(B1, B2]` (stepping `x^q ↦ x^{q'}` by
precomputed even powers and accumulating `∏ (x^q - 1)`), each with a single gcd.
When a gcd is `n` (every factor caught at once) the `Nat` implementation, which
backtracks, is run instead.

Every factor is `gcd(z, n)` for a computed `z`, checked by `PMinusOne.gcdFactor`.
-/

namespace PrimeFactorLean.PM1F

open Mont Mont.Arith

section Generic

variable {α μ : Type} [Arith α μ] [Inhabited α]

/-- `x ↦ x² (· b)` over `bits[i-1], …, bits[0]`. -/
@[specialize] def powLoop (m : μ) (b : α) (bits : ByteArray) (x : α) : Nat → α
  | 0 => x
  | i + 1 =>
    let y := sqr m x
    powLoop m b bits (if bits.get! i == 1 then mul m y b else y) i

/-- Stage 2 accumulation over `primes[t:]`: `y = x^{primes[t-1]}` on entry. -/
@[specialize] def accLoop (m : μ) (steps : Array α) (primes : Array Nat) (one : α)
    (prev : Nat) (y acc : α) (t : Nat) (fuel : Nat) : α :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
    if h : t < primes.size then
      let q := primes[t]
      let y := mul m y steps[(q - prev) / 2]!
      accLoop m steps primes one q y (mul m acc (sub m y one)) (t + 1) fuel
    else acc

/-- `gcd` candidates of stages 1 and 2 (`none`: the gcd of stage 1 is `n`). -/
@[specialize] def run (m : μ) (bits : ByteArray) (primes : Array Nat) (start : Nat) :
    Option (Nat × Nat) :=
  let n := modulus (α := α) m
  let one : α := toMont m 1
  let b : α := toMont m 3
  let x := if bits.size == 0 then b else powLoop m b bits b (bits.size - 1)
  let z1 := limbNat (sub m x one)
  let g := Nat.gcd z1 n
  if g == n then none
  else if g > 1 || start ≥ primes.size then some (z1, 0)
  else Id.run do
    -- `steps[j] = x^(2j)`
    let mut maxGap := 2
    for t in [start + 1:primes.size] do
      maxGap := max maxGap (primes[t]! - primes[t - 1]!)
    let x2 := sqr m x
    let mut steps : Array α := #[one]
    for j in [0:maxGap / 2] do
      steps := steps.push (mul m steps[j]! x2)
    let q0 := primes[start]!
    let y0 := toMont m (Arith.powMod (fromMont m x) q0 n)
    let acc0 := sub m y0 one
    let acc := accLoop m steps primes one q0 y0 acc0 (start + 1) primes.size
    return some (z1, limbNat acc)

end Generic

/-- Stage data: bits of `E` and the primes up to `B2`. -/
structure Plan where
  b1 : Nat
  b2 : Nat
  bits : ByteArray
  primes : Array Nat
  start : Nat

def mkPlan (b1 b2 : Nat) : Plan :=
  let primes := Arith.primesUpTo (max b1 b2)
  let powers := PMinusOne.stageOnePowers primes b1
  let start := (primes.findIdx? (· > b1)).getD primes.size
  { b1, b2, bits := ECMF.natBits (powers.foldl (· * ·) 1), primes, start }

/-- The plan of the automatic pipeline (`B1 = 20000`), built on first use. -/
def plan20000 : Thunk Plan := Thunk.mk fun _ => mkPlan 20000 2000000

def runWidth (n : Nat) (plan : Plan) : Option (Option (Nat × Nat)) :=
  match (n.log2 + 28) / 28 with
  | 1 => some (run (α := N1) (Mod1.ofNat n) plan.bits plan.primes plan.start)
  | 2 => some (run (α := N2) (Mod2.ofNat n) plan.bits plan.primes plan.start)
  | 3 => some (run (α := N3) (Mod3.ofNat n) plan.bits plan.primes plan.start)
  | 4 => some (run (α := N4) (Mod4.ofNat n) plan.bits plan.primes plan.start)
  | 5 => some (run (α := N5) (Mod5.ofNat n) plan.bits plan.primes plan.start)
  | 6 => some (run (α := N6) (Mod6.ofNat n) plan.bits plan.primes plan.start)
  | 7 => some (run (α := N7) (Mod7.ofNat n) plan.bits plan.primes plan.start)
  | 8 => some (run (α := N8) (Mod8.ofNat n) plan.bits plan.primes plan.start)
  | 9 => some (run (α := N9) (Mod9.ofNat n) plan.bits plan.primes plan.start)
  | 10 => some (run (α := N10) (Mod10.ofNat n) plan.bits plan.primes plan.start)
  | 11 => some (run (α := N11) (Mod11.ofNat n) plan.bits plan.primes plan.start)
  | 12 => some (run (α := N12) (Mod12.ofNat n) plan.bits plan.primes plan.start)
  | _ => none

/-- Pollard `p - 1` with bounds `B1 = b1`, `B2 = 100 b1`: the fast path, and the
`Nat` implementation (with backtracking) when a gcd is `n` or `n` is too wide. -/
def split (n : Nat) (b1 : Nat) : Option (ProperFactor n) :=
  if n < 4 then none
  else if n % 2 == 0 then checkFactor n 2
  else
    let plan := if b1 == 20000 then plan20000.get else mkPlan b1 (100 * b1)
    match runWidth n plan with
    | some (some (z1, z2)) => (PMinusOne.gcdFactor n z1).orElse fun _ => PMinusOne.gcdFactor n z2
    | _ => PMinusOne.splitPMinusOne n b1

/-- Every factor returned by the fast `p - 1` is a proper divisor. -/
theorem split_sound {n b1 : Nat} {d : ProperFactor n} (_h : split n b1 = some d) :
    1 < d.val ∧ d.val < n ∧ d.val ∣ n := d.property

end PrimeFactorLean.PM1F
