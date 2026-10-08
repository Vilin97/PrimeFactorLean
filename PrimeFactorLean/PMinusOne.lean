import Mathlib.Tactic.LinearCombination
import PrimeFactorLean.Core
import PrimeFactorLean.Arith

/-!
# Pollard's `p - 1` and Williams' `p + 1` methods

Both methods find a prime `p ∣ n` once the order of a suitable group modulo `p`
divides a known smooth exponent.

* **Pollard `p - 1`** (1974). Stage 1 computes `x = a^E mod n` with
  `E = ∏_{q ≤ B1} q^{⌊log_q B1⌋}`; if `p - 1 ∣ E` then `p ∣ gcd(x - 1, n)`.
  The prime powers are applied in chunks with one gcd per chunk. When a chunk
  makes the gcd jump from `1` to `n` (every prime factor caught at once), the
  chunk is replayed from its checkpoint one prime at a time.
  Stage 2 (the standard continuation) catches `p - 1 = (B1-smooth) · q` with a
  single prime `q ∈ (B1, B2]`: it walks over consecutive primes, stepping
  `x^q ↦ x^{q'}` by a precomputed power `x^d` for the even gap `d = q' - q`, and
  accumulates `∏ (x^q - 1)` with one gcd per block of primes (again replayed
  prime by prime if a block's gcd is `n`).
* **Williams `p + 1`** (1982). With `V_0 = 2`, `V_1 = P`,
  `V_{j+1} = P V_j - V_{j-1}`, i.e. `V_j = α^j + α^{-j}` for a root `α` of
  `X² - P X + 1`, the value `V_E(P)` is `≡ 2 (mod p)` when `p - (D/p) ∣ E`,
  `D = P² - 4`. Stage 1 composes `V_{ab}(P) = V_a(V_b(P))` over the prime powers,
  each by a ladder on `(V_j, V_{j+1})` using `V_{2j} = V_j² - 2` and
  `V_{2j+1} = V_j V_{j+1} - P`. A seed with `(D/p) = +1` only repeats the `p - 1`
  method, so the seeds `P = 3, 4, 6, 5, 11, 6/5` are chosen to make `D` run
  through the independent quadratic characters `5, 3, 2, 21, 13, -1` (note that
  `P = 7` would give `D = 45 = 9 · 5`, the same character as `P = 3`).

**What is proved.** Every reported factor is `gcd(z, n)` for a computed `z`, so
it divides `n` by `Nat.gcd_dvd_right`, and nontriviality is checked
(`gcdFactor`); hence `splitPMinusOne_sound` and `splitPPlusOne_sound` hold for
all inputs. In addition, `applyPowers_mod` proves that the update used by the
chunked stage 1 of `p - 1` computes exactly `a^{∏ q} mod n`, and `lucas_double` and
`lucas_double_add_one` prove the two ladder identities for `V_j = α^j + β^j`,
`αβ = 1`, in every commutative ring. The success conditions (smoothness of
`p ∓ 1`) are not formalized.
-/

namespace PrimeFactorLean.PMinusOne

open Arith

/-- A proper factor obtained from a gcd: divisibility holds by construction. -/
def gcdFactor (n z : Nat) : Option (ProperFactor n) :=
  let g := Nat.gcd z n
  if h : 1 < g ∧ g < n then some ⟨g, h.1, h.2, Nat.gcd_dvd_right z n⟩ else none

/-! ## Stage-1 exponents -/

/-- The maximal prime powers `p^e ≤ B1`, one for each prime `p ≤ B1` of `primes`
(an increasing list), in the same order. -/
def stageOnePowers (primes : Array Nat) (b1 : Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for p in primes do
    if p > b1 || p < 2 then break
    let mut q := p
    while q * p ≤ b1 do q := q * p
    out := out.push q
  return out

/-- Raise `x` to each exponent in turn modulo `n`: the stage-1 update of `p - 1`,
applied by `stageOne` to every chunk of prime powers and to every replayed prime. -/
def applyPowers (n x : Nat) (qs : List Nat) : Nat :=
  qs.foldl (fun acc q => powMod acc q n) x

/-- Stage 1 of `p - 1` computes the intended power: after any list of exponents
`qs`, the residue is `x ^ (∏ qs) mod n`. Chaining over the chunks, the residue
after a chunk boundary is `a^{∏ q} mod n` for the prime powers applied so far. -/
theorem applyPowers_mod (n x : Nat) (qs : List Nat) :
    applyPowers n x qs % n = x ^ qs.prod % n := by
  induction qs generalizing x with
  | nil => simp [applyPowers]
  | cons q qs ih =>
    have h := ih (powMod x q n)
    simp only [applyPowers, List.foldl_cons] at h ⊢
    rw [h, powMod_eq, List.prod_cons, ← Nat.pow_mod, ← Nat.pow_mul]

/-! ## Lucas sequences -/

/-- `V_{2j} = V_j² - 2` for `V_j = α^j + β^j` with `αβ = 1`. -/
theorem lucas_double {R : Type*} [CommRing R] {α β : R} (h : α * β = 1) (j : Nat) :
    (α ^ j + β ^ j) ^ 2 - 2 = α ^ (2 * j) + β ^ (2 * j) := by
  have hj : α ^ j * β ^ j = 1 := by rw [← mul_pow, h, one_pow]
  linear_combination 2 * hj

/-- `V_{2j+1} = V_j V_{j+1} - V_1` for `V_j = α^j + β^j` with `αβ = 1`. -/
theorem lucas_double_add_one {R : Type*} [CommRing R] {α β : R} (h : α * β = 1)
    (j : Nat) :
    (α ^ j + β ^ j) * (α ^ (j + 1) + β ^ (j + 1)) - (α + β) =
      α ^ (2 * j + 1) + β ^ (2 * j + 1) := by
  have hj : α ^ j * β ^ j = 1 := by rw [← mul_pow, h, one_pow]
  linear_combination (α + β) * hj

/-- `V_m(P) mod n` for `n ≥ 3`, by the ladder on `(V_j, V_{j+1})` reading `m` from
its top bit (`lucas_double`, `lucas_double_add_one`). -/
def lucasV (n P m : Nat) : Nat := Id.run do
  if m == 0 then return 2 % n
  let P := P % n
  let mut v0 := P
  let mut v1 := (P * P + n - 2) % n
  let top := m.log2
  for t in [0:top] do
    if m.testBit (top - 1 - t) then
      v0 := (v0 * v1 + n - P) % n
      v1 := (v1 * v1 + n - 2) % n
    else
      v1 := (v0 * v1 + n - P) % n
      v0 := (v0 * v0 + n - 2) % n
  return v0

/-- Compose `V_q` over the exponents in turn: the stage-1 update of `p + 1`
(`V_{ab}(P) = V_a(V_b(P))`). -/
def applyLucas (n v : Nat) (qs : List Nat) : Nat :=
  qs.foldl (fun acc q => lucasV n acc q) v

/-! ## The two stages -/

/-- How a stage ended. -/
inductive Outcome (n : Nat) where
  /-- A proper factor. -/
  | found (d : ProperFactor n)
  /-- The gcd jumped to `n` within a single prime: try another base or seed. -/
  | collapsed
  /-- No factor; the residue reached at the end of the stage. -/
  | residue (x : Nat)

/-- Stage 1 for a group whose exponentiation by a list of exponents is `apply`:
apply the prime powers in chunks of `chunk`, taking `gcd(test x, n)` after each
chunk; on a jump to `n`, replay the chunk from its checkpoint one prime at a
time. -/
def stageOne (n : Nat) (apply : Nat → List Nat → Nat) (test : Nat → Nat)
    (primes powers : Array Nat) (x0 : Nat) (chunk : Nat := 64) : Outcome n := Id.run do
  let chunk := max 1 chunk
  let mut x := x0
  let mut i := 0
  while i < powers.size do
    let j := min powers.size (i + chunk)
    let saved := x
    x := apply x (powers.extract i j).toList
    let z := test x
    if Nat.gcd z n == 1 then
      i := j
      continue
    if let some d := gcdFactor n z then return .found d
    x := saved
    for t in [i:j] do
      let p := primes[t]!
      let mut q := powers[t]!
      while q > 1 && p > 1 do
        x := apply x [p]
        q := q / p
        let z := test x
        if let some d := gcdFactor n z then return .found d
        if Nat.gcd z n == n then return .collapsed
    return .collapsed
  return .residue x

/-- Stage 2 of `p - 1` (standard continuation) over the primes `primes[start:]`:
accumulate `∏ (x^q - 1) mod n`, stepping between consecutive primes by the
precomputed `x^d` for the even gaps `d`, with one gcd per `block` primes. -/
def stageTwo (n x : Nat) (primes : Array Nat) (start : Nat) (block : Nat := 1024) :
    Outcome n := Id.run do
  if start ≥ primes.size then return .residue x
  let block := max 1 block
  let mut maxGap := 2
  for t in [start + 1:primes.size] do
    maxGap := max maxGap (primes[t]! - primes[t - 1]!)
  -- `steps[j] = x^(2j)`.
  let x2 := x * x % n
  let mut steps : Array Nat := #[1 % n]
  for j in [0:maxGap / 2] do
    steps := steps.push (steps[j]! * x2 % n)
  let mut prev := primes[start]!
  let mut y := powMod x prev n
  let mut t := start
  while t < primes.size do
    let stop := min primes.size (t + block)
    let (savedPrev, savedY) := (prev, y)
    let mut acc := 1 % n
    for u in [t:stop] do
      let q := primes[u]!
      y := y * steps[(q - prev) / 2]! % n
      prev := q
      acc := acc * ((y + n - 1) % n) % n
    let g := Nat.gcd acc n
    if g == 1 then
      t := stop
      continue
    if let some d := gcdFactor n acc then return .found d
    -- The block's product is `0 mod n`: retry it with a gcd per prime.
    prev := savedPrev
    y := savedY
    for u in [t:stop] do
      let q := primes[u]!
      y := y * steps[(q - prev) / 2]! % n
      prev := q
      if let some d := gcdFactor n (y + n - 1) then return .found d
    return .collapsed
  return .residue x

/-! ## Public splitters -/

/-- Pollard `p - 1` with bounds `B1 = b1` and `B2 = b2` (`b2 = 0` means
`100 · b1`; `b2 ≤ b1` skips stage 2), trying the bases `3, 5, 7` only when a
stage collapses. Even `n` is answered by `2`. -/
def splitPMinusOne (n : Nat) (b1 : Nat := 10000) (b2 : Nat := 0) :
    Option (ProperFactor n) := Id.run do
  if n < 4 then return none
  if n % 2 == 0 then return checkFactor n 2
  let b2 := if b2 == 0 then 100 * b1 else b2
  let primes := primesUpTo b1
  let powers := stageOnePowers primes b1
  for a in [3, 5, 7] do
    if let some d := gcdFactor n a then return some d
    match stageOne n (applyPowers n) (fun x => x + n - 1) primes powers (a % n) with
    | .found d => return some d
    | .collapsed => continue
    | .residue x =>
      if b2 ≤ b1 then return none
      -- The primes up to `B2` are only sieved when stage 1 has failed.
      match stageTwo n x (primesUpTo b2) powers.size with
      | .found d => return some d
      | .collapsed => continue
      | .residue _ => return none
  return none

/-- Seeds `P = a / b` for `p + 1`: `D = P² - 4` runs through the independent
quadratic characters `5, 3, 2, 21, 13, -1` (modulo squares). -/
def seeds : List (Nat × Nat) := [(3, 1), (4, 1), (6, 1), (5, 1), (11, 1), (6, 5)]

/-- Williams `p + 1` stage 1 with bound `B1 = b1`, over the `seeds` in turn.
Even `n` is answered by `2`. -/
def splitPPlusOne (n : Nat) (b1 : Nat := 10000) : Option (ProperFactor n) := Id.run do
  if n < 4 then return none
  if n % 2 == 0 then return checkFactor n 2
  let primes := primesUpTo b1
  let powers := stageOnePowers primes b1
  for (a, b) in seeds do
    if let some d := gcdFactor n b then return some d
    let some inv := invMod (b % n) n | continue
    let P := a * inv % n
    -- A prime dividing `D = P² - 4` is met directly.
    if let some d := gcdFactor n (P * P + n - 4) then return some d
    match stageOne n (applyLucas n) (fun v => v + n - 2) primes powers P with
    | .found d => return some d
    | _ => continue
  return none

/-- Every factor returned by Pollard `p - 1` is a proper divisor. -/
theorem splitPMinusOne_sound {n b1 b2 : Nat} {d : ProperFactor n}
    (_h : splitPMinusOne n b1 b2 = some d) : 1 < d.val ∧ d.val < n ∧ d.val ∣ n :=
  d.property

/-- Every factor returned by Williams `p + 1` is a proper divisor. -/
theorem splitPPlusOne_sound {n b1 : Nat} {d : ProperFactor n}
    (_h : splitPPlusOne n b1 = some d) : 1 < d.val ∧ d.val < n ∧ d.val ∣ n :=
  d.property

end PrimeFactorLean.PMinusOne
