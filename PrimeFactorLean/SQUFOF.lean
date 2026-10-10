import PrimeFactorLean.Core
import PrimeFactorLean.Arith

/-!
# Shanks' square forms factorization (SQUFOF)

SQUFOF (Shanks 1975; analysed by Gower and Wagstaff 2008) walks the principal
cycle of reduced quadratic forms of discriminant `4D`, `D = k n`, which is the
continued fraction expansion of `√D`. With `s = ⌊√D⌋`, `P₀ = s`, `Q₀ = 1`,
`Q₁ = D - s²`:

  `b_i = ⌊(s + P_{i-1}) / Q_i⌋`,  `P_i = b_i Q_i - P_{i-1}`,
  `Q_{i+1} = Q_{i-1} + b_i (P_{i-1} - P_i)`.

* **Forward cycle.** When `Q_i = r²` at an even index, the form at `i` is, in
  the class group, the square of the form `(r, 2P_{i-1}, …)`.
* **Reverse cycle.** Starting from that square root
  (`P = P_{i-1} + r ⌊(s - P_{i-1})/r⌋`, `Q_prev = r`, `Q = (D - P²)/r`), the same
  recurrence reaches an ambiguous form at the first step with `P_j = P_{j-1}`.
  There `Q_j ∣ 2P_j`, hence `Q_j ∣ 4D`, and `gcd(Q_j, n)` is a proper factor
  unless the square root was itself on the principal cycle; in that case the
  forward cycle simply continues.

All forward and reverse quantities stay below `2√D`; for the intended range
`n < 2^62` and multipliers up to `1155` they are machine-word sized, so each step
costs a handful of word operations. The sixteen multipliers
`k ∈ {1, 3, 5, 7, 11, 15, …, 1155}` (the products of subsets of `{3, 5, 7, 11}`)
are *raced*: every multiplier advances in round-robin chunks of forward steps,
and the first proper square to split `n` wins. A proper square is expected
after `O((kn)^{1/4})` steps; each forward cycle is cut off at the customary
`3L ≈ 8.5 (kn)^{1/4}` steps, `L = 2√(2√D)`.

**What is proved.** Every returned divisor is `gcd(Q, n)` for a computed `Q`
(`gcdFactor`, divisibility by `Nat.gcd_dvd_right`, nontriviality checked) or a
checked even/perfect-power divisor, so `split_sound` holds for all inputs. The
class-group theory explaining why SQUFOF succeeds is not formalized.
-/

namespace PrimeFactorLean.SQUFOF

open Arith

/-- A proper factor obtained from a gcd: divisibility holds by construction. -/
def gcdFactor (n z : Nat) : Option (ProperFactor n) :=
  let g := Nat.gcd z n
  if h : 1 < g ∧ g < n then some ⟨g, h.1, h.2, Nat.gcd_dvd_right z n⟩ else none

/-- Shanks' multipliers: the sixteen products of subsets of `{3, 5, 7, 11}`. -/
def multipliers : Array Nat :=
  #[1, 3, 5, 7, 11, 15, 21, 33, 35, 55, 77, 105, 165, 231, 385, 1155]

/-- Bit `t` is set exactly when `t` is a square modulo `64`. -/
def squaresMod64 : Nat := 0x0202021202030213

/-- `some r` when `q = r²`; residues modulo `64` reject most non-squares cheaply. -/
@[inline] def squareRoot? (q : Nat) : Option Nat :=
  if (squaresMod64 >>> (q % 64)) % 2 == 0 then none
  else
    let r := isqrt q
    if r * r == q then some r else none

/-- One step of the cycle, from `(P_{i-1}, Q_{i-1}, Q_i)` to `(P_i, Q_{i+1})`.
The new `Q` is positive, so the natural-number subtraction is exact. -/
@[inline] def step (s P Qprev Q : Nat) : Nat × Nat :=
  let b := (s + P) / Q
  let P' := b * Q - P
  if P' ≤ P then (P', Qprev + b * (P - P')) else (P', Qprev - b * (P' - P))

/-- The reverse cycle from the square root `(r, 2P, …)` of a square form, run for
at most `fuel` steps to its symmetry point `P_j = P_{j-1}`, where `gcd(Q_j, n)`
is tried. -/
def reverseCycle (n D s P r fuel : Nat) : Option (ProperFactor n) := Id.run do
  let mut P := (s - P) / r * r + P
  let mut Qprev := r
  let mut Q := (D - P * P) / r
  for _ in [0:fuel] do
    if Q == 0 then return none
    let (P', Q') := step s P Qprev Q
    if P' == P then return gcdFactor n Q
    P := P'
    Qprev := Q
    Q := Q'
  return none

/-! ## Racing the multipliers -/

/-- The forward cycle of one multiplier at index `i`: `P = P_{i-1}`,
`Qprev = Q_{i-1}`, `Q = Q_i`; it gives up at index `bound`. -/
structure Racer where
  D : Nat
  s : Nat
  P : Nat
  Qprev : Nat
  Q : Nat
  i : Nat
  bound : Nat
  deriving Inhabited

/-- The cycle of `√(k n)` at index `1`. A square `k n` is answered at once by
`gcd(√(kn), n)`. -/
def Racer.start (n k : Nat) : Except (Option (ProperFactor n)) Racer :=
  let D := k * n
  let s := isqrt D
  if s * s == D then .error (gcdFactor n s)
  else .ok { D := D, s := s, P := s, Qprev := 1, Q := D - s * s, i := 1,
             bound := 6 * isqrt (2 * s) }

/-- Advance by up to `steps` forward steps, sending every square form at an even
index through its reverse cycle. -/
def Racer.advance (n : Nat) (r : Racer) (steps : Nat) :
    Racer × Option (ProperFactor n) := Id.run do
  let mut P := r.P
  let mut Qprev := r.Qprev
  let mut Q := r.Q
  let mut i := r.i
  for _ in [0:steps] do
    if i ≥ r.bound then break
    let (P', Q') := step r.s P Qprev Q
    P := P'
    Qprev := Q
    Q := Q'
    i := i + 1
    if i % 2 == 0 then
      if let some root := squareRoot? Q then
        if root > 1 then
          if let some f := reverseCycle n r.D r.s P root r.bound then
            return ({ r with P := P, Qprev := Qprev, Q := Q, i := i }, some f)
  return ({ r with P := P, Qprev := Qprev, Q := Q, i := i }, none)

/-- Race all multipliers in round-robin chunks of `chunk` forward steps until one
splits `n` or every cycle reaches its bound. -/
def race (n : Nat) (chunk : Nat := 256) : Option (ProperFactor n) := Id.run do
  let mut racers : Array Racer := #[]
  for k in multipliers do
    match Racer.start n k with
    | .error (some f) => return some f
    | .error none => pure ()
    | .ok r => racers := racers.push r
  let mut live := true
  while live do
    live := false
    for j in [0:racers.size] do
      let r := racers[j]!
      if r.i ≥ r.bound then continue
      let (r', found) := r.advance n chunk
      if let some f := found then return some f
      racers := racers.set! j r'
      if r'.i < r'.bound then live := true
  return none

/-! ## Public splitter -/

/-- SQUFOF for `4 ≤ n < 2^62`: even numbers and perfect powers are handled first,
probable primes are declined, everything else is raced over the multipliers. -/
def split (n : Nat) : Option (ProperFactor n) :=
  if n < 4 ∨ 2 ^ 62 ≤ n then none
  else if n % 2 = 0 then checkFactor n 2
  else match perfectPower n with
    | some (r, _) => checkFactor n r
    | none => if isProbablePrime n then none else race n

/-- Every factor returned by SQUFOF is a proper divisor. -/
theorem split_sound {n : Nat} {d : ProperFactor n} (_h : split n = some d) :
    1 < d.val ∧ d.val < n ∧ d.val ∣ n := d.property

end PrimeFactorLean.SQUFOF
