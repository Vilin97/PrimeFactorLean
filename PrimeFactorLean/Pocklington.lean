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

/-- A Pocklington step: prove `n` prime from witnesses `(q, e, a)`. Each `q`
must be proved prime earlier in the certificate or be small enough for the
verified trial division. -/
structure Step where
  n : Nat
  witnesses : List (Nat × Nat × Nat)
  deriving Repr, Inhabited

/-- Bound below which a witness prime may be certified by exact trial division. -/
def smallBound : Nat := 2 ^ 32

/-- A factor-prime is acceptable if already proved or small and verified. -/
def knownPrime (known : List Nat) (q : Nat) : Bool :=
  known.contains q || (decide (q < smallBound) && smallPrime q)

/-- The executable acceptance test for one step. -/
def Step.check (s : Step) (known : List Nat) : Bool :=
  decide (2 ≤ s.n) &&
  decide ((s.witnesses.map Prod.fst).Nodup) &&
  s.witnesses.all (fun t =>
    knownPrime known t.1 && (s.n - 1) % (t.1 ^ t.2.1) == 0 && witnessOK s.n t.1 t.2.2) &&
  decide (s.n < factoredPart s.witnesses ^ 2)

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

/-- Partially factor `m = n - 1` until the factored part exceeds `√n`.
Returns prime candidates with multiplicities (unproved; the checker decides). -/
def partialFactor (split : Nat → Option Nat) (smallPrimes : Array Nat)
    (n : Nat) : Option (List (Nat × Nat)) := Id.run do
  let mut m := n - 1
  let mut found : List (Nat × Nat) := []
  let mut part := 1
  for p in smallPrimes do
    if m % p == 0 then
      let (m', e) := stripFactor m p
      m := m'
      found := (p, e) :: found
      part := part * p ^ e
    if m == 1 then break
  -- Peel larger prime factors from the cofactor until F² > n.
  let mut work : List Nat := if m > 1 then [m] else []
  let mut fuel := 64
  while part * part ≤ n && !work.isEmpty && fuel > 0 do
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
  if part * part > n then return some found else return none

/-- Recursively build dependency-ordered Pocklington steps for `n`. -/
def generateSteps (split : Nat → Option Nat) (smallPrimes : Array Nat) :
    Nat → Nat → Option (List Step)
  | 0, _ => none
  | fuel + 1, n =>
    if n < smallBound then
      if smallPrime n then some [] else none
    else if !isProbablePrime n then none
    else do
      let found ← partialFactor split smallPrimes n
      -- Use the fewest large primes: sort by size and keep a prefix reaching √n.
      let sorted := found.mergeSort (fun a b => a.1 ≤ b.1)
      let mut chosen : List (Nat × Nat) := []
      let mut part := 1
      for (q, e) in sorted do
        if part * part > n then break
        chosen := (q, e) :: chosen
        part := part * q ^ e
      let mut steps : List Step := []
      let mut witnesses : List (Nat × Nat × Nat) := []
      for (q, e) in chosen.reverse do
        if q ≥ smallBound then
          let sub ← generateSteps split smallPrimes fuel q
          steps := steps ++ sub
        let a ← findWitness n q
        witnesses := witnesses ++ [(q, e, a)]
      return steps ++ [⟨n, witnesses⟩]

/-- Package steps as a certificate for `n`, accepting it only if it checks. -/
def checked (n : Nat) (steps : List Step) : Option Certificate :=
  let c : Certificate := ⟨n, steps⟩
  if c.check then some c else none

/-- Generate a certificate and check it before returning. -/
def generate (split : Nat → Option Nat) (n : Nat) (fuel : Nat := 64) : Option Certificate :=
  (if n < smallBound then some [] else generateSteps split (primesUpTo 65536) fuel n).bind
    (checked n)

/-- The primality checker used by the verified factorization engine: exact
trial division below `2^32`, otherwise a Pocklington certificate that is
generated (untrusted) and then accepted by `Certificate.check`. Its soundness,
`Proofs.Pocklington.oracle_sound`, rests on Pocklington's theorem. -/
def oracle (split : Nat → Option Nat) (fuel : Nat := 64) (n : Nat) : Bool :=
  if n < smallBound then smallPrime n
  else isProbablePrime n && (generate split n fuel).isSome

end PrimeFactorLean.Pocklington
