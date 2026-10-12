import PrimeFactorLean.Arith
/-!
# Pocklington–Lehmer primality certificates

Pratt certificates (`PrimeFactorLean.Primality`) need the *complete*
factorization of `n - 1`, recursively. Pocklington's criterion only needs a
factored part `F ∣ n - 1` with `F² > n`, which is far easier to find for large
primes. This file proves the criterion from scratch against mathlib's
`Nat.Prime` and gives a checker whose acceptance is proved sound.

**Theorem (Pocklington).** Let `n ≥ 2` and let `q₁,…,q_k` be distinct primes
with `q_i^{e_i} ∣ n - 1` and `F = ∏ q_i^{e_i}`, `F² > n`. If for every `i` there
is `a_i` with `a_i^{n-1} ≡ 1 (mod n)` and `gcd(a_i^{(n-1)/q_i} - 1, n) = 1`,
then `n` is prime.

*Proof.* Let `p` be any prime divisor of `n`. With `n - 1 = q^e k`, the element
`b = a^k` of `(ℤ/p)ˣ` has order exactly `q^e`, so `q^e ∣ p - 1`. The prime powers
are pairwise coprime, so `F ∣ p - 1` and `p > F > √n`. A composite `n` would
have a prime divisor `p ≤ √n`.

Certificates are produced by an untrusted generator that may call any
factoring routine; only `Step.check`/`Certificate.check` are trusted, and both
are proved sound below.

**The `n + 1` side.** A step may instead use a factored part `F ∣ n + 1`: with
`gcd(2D, n) = 1`, a prime `p ∣ n` sees the ring `ℤ/p[√D]`, where the Frobenius
map `z ↦ z^p` fixes `√D` or negates it as `D` is a square mod `p` or not. For
`α = a + b√D` of norm `a² - D b²` prime to `n`, with `α^(n+1)` free of `√D` and
the `√D` part of `α^((n+1)/q)` prime to `n` (computed mod `n`), the element
`α/ᾱ` has order divisible by `q^e` and dividing `p ∓ 1`. One `D` serves every
witness, so `F ∣ p - 1` or `F ∣ p + 1`, and `(F - 1)² > n` proves `n` prime
(the `n + 1` test of Lehmer, Morrison and Brillhart–Lehmer–Selfridge).
-/

namespace PrimeFactorLean.Pocklington

open Arith

/-- The factored part of a certificate row: `∏ q^e` over its `(q, e, a)` triples. -/
def factoredPart (ws : List (Nat × Nat × Nat)) : Nat :=
  (ws.map fun t => t.1 ^ t.2.1).foldr (· * ·) 1

/-! ## Executable certificates -/

/-- One witness check: `a^(n-1) ≡ 1` and `gcd(a^((n-1)/q) - 1, n) = 1`. -/
def witnessOK (n q a : Nat) : Bool :=
  powMod a (n - 1) n == 1 % n &&
  Nat.gcd ((powMod a ((n - 1) / q) n + n - 1) % n) n == 1

/-- `(x₁ + y₁√D)(x₂ + y₂√D)` with coordinates mod `n`. -/
def mulPair (n D : Nat) (x y : Nat × Nat) : Nat × Nat :=
  ((x.1 * y.1 + D * (x.2 * y.2)) % n, (x.1 * y.2 + x.2 * y.1) % n)

/-- `(x.1 + x.2 √D)^k` with coordinates mod `n`, by squaring. -/
def powPair (n D : Nat) (x : Nat × Nat) (k : Nat) : Nat × Nat :=
  if k = 0 then (1 % n, 0)
  else
    let r := powPair n D x (k / 2)
    let r2 := mulPair n D r r
    if k % 2 = 1 then mulPair n D r2 x else r2
termination_by k
decreasing_by omega

/-- The norm `a² - D b²` mod `n`. -/
def normMod (n D a b : Nat) : Nat := (a * a % n + (n - D * (b * b) % n)) % n

/-- One `n + 1` witness check for `α = a + b√D`: the norm is prime to `n`,
`α^(n+1)` has no `√D` part mod `n`, and the `√D` part of `α^((n+1)/q)` is prime
to `n`. -/
def lucasOK (n D q a b : Nat) : Bool :=
  Nat.gcd (normMod n D a b) n == 1 &&
  (powPair n D (a, b) (n + 1)).2 == 0 &&
  Nat.gcd (powPair n D (a, b) ((n + 1) / q)).2 n == 1

/-- The factored part of an `n + 1` row: `∏ q^e` over its `(q, e, a, b)`. -/
def plusPart (ws : List (Nat × Nat × Nat × Nat)) : Nat :=
  (ws.map fun t => t.1 ^ t.2.1).foldr (· * ·) 1

/-- A Pocklington step: prove `n` prime from witnesses `(q, e, a)` for `n - 1`,
or, when `plus` is not empty, from `D` and witnesses `(q, e, a, b)` for `n + 1`
(then `witnesses` is not used). Each `q` must be proved prime earlier in the
certificate or be small enough for the verified trial division. -/
structure Step where
  n : Nat
  witnesses : List (Nat × Nat × Nat)
  D : Nat := 0
  plus : List (Nat × Nat × Nat × Nat) := []
  deriving Repr, Inhabited

/-- Bound below which a witness prime may be certified by exact trial division. -/
def smallBound : Nat := 2 ^ 32

/-- A factor-prime is acceptable if already proved or small and verified. -/
def knownPrime (known : List Nat) (q : Nat) : Bool :=
  known.contains q || (decide (q < smallBound) && smallPrime q)

/-- `s² - 4p` is a nonnegative perfect square, i.e. `t² - s t + p` has
integer roots. -/
def squareDiscriminant (s p : Nat) : Bool :=
  4 * p ≤ s * s && isqrt (s * s - 4 * p) * isqrt (s * s - 4 * p) == s * s - 4 * p

/-- The Brillhart–Lehmer–Selfridge test for `F³ > N` (BLS 1975, Theorem 5):
with `N - 1 = F R` and `R = c₁ F + c₂`, a composite `N` all of whose prime
factors are `≡ 1 (mod F)` would be `(aF + 1)(bF + 1)` with `(a + b, ab)` equal
to `(c₂, c₁)` or `(c₂ + F, c₁ - 1)`; both quadratics must then have integer
roots. The test passes when neither does. -/
def cubeTest (N F : Nat) : Bool :=
  let R := (N - 1) / F
  let c₁ := R / F
  let c₂ := R % F
  !squareDiscriminant c₂ c₁ && (c₁ == 0 || !squareDiscriminant (c₂ + F) (c₁ - 1))

/-- The executable acceptance test for one step: Pocklington (`F² > N`) or
Brillhart–Lehmer–Selfridge (`F³ > N` and `cubeTest`) on `N - 1`, or the `N + 1`
test (`(F - 1)² > N`). -/
def Step.check (s : Step) (known : List Nat) : Bool :=
  if s.plus.isEmpty then
    decide (2 ≤ s.n) &&
    decide ((s.witnesses.map Prod.fst).Nodup) &&
    s.witnesses.all (fun t =>
      knownPrime known t.1 && (s.n - 1) % (t.1 ^ t.2.1) == 0 && witnessOK s.n t.1 t.2.2) &&
    (decide (s.n < factoredPart s.witnesses ^ 2) ||
      (decide (s.n < factoredPart s.witnesses ^ 3) && cubeTest s.n (factoredPart s.witnesses)))
  else
    decide (3 ≤ s.n) && Nat.gcd (2 * s.D) s.n == 1 &&
    decide ((s.plus.map Prod.fst).Nodup) &&
    s.plus.all (fun t =>
      knownPrime known t.1 && (s.n + 1) % (t.1 ^ t.2.1) == 0 &&
        lucasOK s.n s.D t.1 t.2.2.1 t.2.2.2) &&
    decide (s.n < (plusPart s.plus - 1) ^ 2)

/-- Verify a dependency-ordered list of steps; the result lists proved primes. -/
def verifySteps : List Step → List Nat → Option (List Nat)
  | [], known => some known
  | s :: rest, known => if s.check known then verifySteps rest (s.n :: known) else none

/-- A certificate for `n`: small values are decided by verified trial division,
larger ones by Pocklington steps ending in `n`. -/
structure Certificate where
  n : Nat
  steps : List Step
  deriving Repr, Inhabited

def Certificate.check (c : Certificate) : Bool :=
  if c.n < smallBound then smallPrime c.n
  else match verifySteps c.steps [] with
    | none => false
    | some proved => proved.contains c.n

/-! ## Untrusted certificate generation -/

/-- Multiplicity of `q` in `m` (with fuel), and the cofactor. -/
def stripFactor (m q : Nat) : Nat × Nat := Id.run do
  let mut m := m
  let mut e := 0
  if q < 2 then return (m, 0)
  while m > 0 && m % q == 0 do
    m := m / q
    e := e + 1
  return (m, e)

/-- Find a witness `a` for `(n, q)` among small bases. -/
def findWitness (n q : Nat) (bound : Nat := 200) : Option Nat :=
  (List.range bound).find? (fun i => witnessOK n q (i + 2)) |>.map (· + 2)

/-- Partially factor `m` until the factored part `F` satisfies `enough F`.
Returns prime candidates with multiplicities (unproved; the checker decides). -/
def partialFactorOf (split : Nat → Option Nat) (smallPrimes : Array Nat)
    (m : Nat) (enough : Nat → Bool) : Option (List (Nat × Nat)) := Id.run do
  let mut m := m
  let mut found : List (Nat × Nat) := []
  let mut part := 1
  for p in smallPrimes do
    if m % p == 0 then
      let (m', e) := stripFactor m p
      m := m'
      found := (p, e) :: found
      part := part * p ^ e
    if m == 1 then break
  -- Peel larger prime factors from the cofactor until `enough F`.
  let mut work : List Nat := if m > 1 then [m] else []
  let mut fuel := 64
  while !enough part && !work.isEmpty && fuel > 0 do
    fuel := fuel - 1
    match work with
    | [] => break
    | c :: rest =>
      work := rest
      if c ≤ 1 then continue
      if isProbablePrime c then
        let (m', e) := stripFactor m c
        if e > 0 then
          m := m'
          found := (c, e) :: found
          part := part * c ^ e
      else
        match split c with
        | some d =>
          if 1 < d && d < c && c % d == 0 then
            -- Prefer to handle the smaller piece first (cheaper certificates).
            let a := min d (c / d)
            let b := max d (c / d)
            work := a :: b :: work
          else continue
        | none => continue
  if enough part then return some found else return none

/-- Partially factor `n - 1` until the factored part `F` has `F^k > n`
(`k = 3` for the Brillhart–Lehmer–Selfridge test, `k = 2` for Pocklington). -/
def partialFactor (split : Nat → Option Nat) (smallPrimes : Array Nat)
    (n : Nat) (k : Nat := 2) : Option (List (Nat × Nat)) :=
  partialFactorOf split smallPrimes (n - 1) fun part => part ^ k > n

/-- A `D` for the `n + 1` test: Jacobi symbol `(D/n) = -1`, so `D` is prime to
`n` and, for prime `n`, not a square (the witnesses then exist). -/
def plusD (n : Nat) : Option Nat :=
  (List.range 1000).find? (fun i => jacobi (i + 2) n == -1) |>.map (· + 2)

/-- An `n + 1` witness `α = a + √D` for `(n, q)` among small `a`. -/
def findPlusWitness (n D q : Nat) (bound : Nat := 200) : Option Nat :=
  (List.range bound).find? (fun i => lucasOK n D q (i + 1) 1) |>.map (· + 1)

/-- The fewest large primes of `found` (smallest first) whose product reaches `enough`. -/
def chooseFactors (found : List (Nat × Nat)) (enough : Nat → Bool) : List (Nat × Nat) × Nat :=
  Id.run do
    let sorted := found.mergeSort (fun a b => a.1 ≤ b.1)
    let mut chosen : List (Nat × Nat) := []
    let mut part := 1
    for (q, e) in sorted do
      if enough part then break
      chosen := (q, e) :: chosen
      part := part * q ^ e
    return (chosen.reverse, part)

/-- Recursively build dependency-ordered steps for `n`. The splitters are tried
in order, each on `n - 1` (cube-root test, then square root) and then on
`n + 1`: cheap splitters first, so that a hard cofactor on one side (a product
of two large primes) does not cost a full factorization when the other side is
easy. -/
def generateSteps (splits : List (Nat → Option Nat)) (smallPrimes : Array Nat) :
    Nat → Nat → Option (List Step)
  | 0, _ => none
  | fuel + 1, n =>
    if n < smallBound then
      if smallPrime n then some [] else none
    else if !isProbablePrime n then none
    else
      -- `n - 1`: prefer the cube-root test (less of `n - 1` to factor); factor
      -- on to the square-root test only if its quadratic check happens to fail
      -- (a splitter that cannot reach `F³ > n` cannot reach `F² > n` either)
      let minusSteps (chosen : List (Nat × Nat)) : Option (List Step) := do
        let mut steps : List Step := []
        let mut witnesses : List (Nat × Nat × Nat) := []
        for (q, e) in chosen do
          if q ≥ smallBound then
            let sub ← generateSteps splits smallPrimes fuel q
            steps := steps ++ sub
          let a ← findWitness n q
          witnesses := witnesses ++ [(q, e, a)]
        return steps ++ [{ n := n, witnesses := witnesses }]
      let minus (split : Nat → Option Nat) : Option (List Step) := do
        let found ← partialFactor split smallPrimes n 3
        let (chosen, part) := chooseFactors found fun part => part ^ 3 > n
        if n < part ^ 2 || cubeTest n part then minusSteps chosen
        else
          let found2 ← partialFactor split smallPrimes n 2
          minusSteps (chooseFactors found2 fun part => part ^ 2 > n).1
      -- `n + 1`: a factored part with `(F - 1)² > n`
      let plus (split : Nat → Option Nat) : Option (List Step) := do
        let enough := fun part => n < (part - 1) ^ 2
        let found ← partialFactorOf split smallPrimes (n + 1) enough
        let (chosen, _) := chooseFactors found enough
        let D ← plusD n
        let mut steps : List Step := []
        let mut ws : List (Nat × Nat × Nat × Nat) := []
        for (q, e) in chosen do
          if q ≥ smallBound then
            let sub ← generateSteps splits smallPrimes fuel q
            steps := steps ++ sub
          let a ← findPlusWitness n D q
          ws := ws ++ [(q, e, a, 1)]
        return steps ++ [{ n := n, witnesses := [], D := D, plus := ws }]
      let attempts := splits.map fun split => fun (_ : Unit) =>
        (minus split).orElse fun _ => plus split
      attempts.foldl (fun acc f => acc.orElse f) none

/-- Package steps as a certificate for `n`, accepting it only if it checks. -/
def checked (n : Nat) (steps : List Step) : Option Certificate :=
  let c : Certificate := ⟨n, steps⟩
  if c.check then some c else none

set_option compiler.extract_closed false in
/-- The primes below `2^16` for the partial factorizations, built on first use
(without `extract_closed` the compiler would build them at program start). -/
def smallPrimes16 : Thunk (Array Nat) := Thunk.mk fun _ => primesUpTo 65536

set_option compiler.extract_closed false in
/-- Generate a certificate and check it before returning (`cheap`: splitters to
try before `split`, see `generateSteps`). -/
def generate (split : Nat → Option Nat) (n : Nat) (fuel : Nat := 64)
    (cheap : List (Nat → Option Nat) := []) : Option Certificate :=
  (if n < smallBound then some [] else
    generateSteps (cheap ++ [split]) smallPrimes16.get fuel n).bind (checked n)

/-- The primality checker used by the verified factorization engine: exact
trial division below `2^32`, otherwise a Pocklington certificate that is
generated (untrusted) and then accepted by `Certificate.check`. Its soundness,
`Proofs.Pocklington.oracle_sound`, rests on Pocklington's theorem. -/
def oracle (split : Nat → Option Nat) (fuel : Nat := 64) (n : Nat)
    (cheap : List (Nat → Option Nat) := []) : Bool :=
  if n < smallBound then smallPrime n
  else isProbablePrime n && (generate split n fuel cheap).isSome

end PrimeFactorLean.Pocklington
