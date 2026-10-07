import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Prime.Basic
import Init.Data.Nat.Bitwise.Lemmas
import Lean.Elab.Tactic.Omega

/-!
# Bounded single- and multiple-polynomial quadratic sieves

This module implements a single-polynomial quadratic sieve.  It sieves the
positive values `(ceil (sqrt n) + i)^2 - n` in blocks.  The factor base contains
the primes up to the requested bound for which `n` has a square root modulo the
prime.  Exact division at the corresponding residue classes replaces the usual
logarithmic score sieve; it needs no floating point threshold or approximation.

Smooth relations are reduced by incremental Gaussian elimination over F₂.  The
row operations carry bitsets of relation indices, so a zero parity row gives an
actual product of relations.  Both gcd signs of the resulting congruence of
squares are tried.  The interval and factor-base bounds are explicit, and failure
to find a factor is represented by `none`.

`splitMPQS` additionally selects squarefree factor-base products `A` near the
usual `sqrt(2n)/M` target.  CRT constructs square roots `B` of `n` modulo `A`, and
Gray-code changes of root signs update `B` through precomputed CRT components.
It sieves the exact quotient `((Ax+B)^2-n)/A` and adds the prime exponents of `A`
to each relation.  Roots at primes dividing `A` use the resulting linear
polynomial.  Both public splitters independently validate and prove that every
successful output is a proper divisor.
-/

namespace PrimeFactorLean.QuadraticSieve

/-- Remove powers of `p`, with an explicit recursion budget. -/
def stripPowerAux (p : Nat) : Nat → Nat → Nat × Nat
  | 0, q => (q, 0)
  | fuel + 1, q =>
      if 1 < p ∧ 0 < q ∧ q % p = 0 then
        let result := stripPowerAux p fuel (q / p)
        (result.1, result.2 + 1)
      else (q, 0)

/-- The original value is preserved by every exact-division step. -/
theorem stripPowerAux_factorization (p fuel q : Nat) :
    q = (stripPowerAux p fuel q).1 * p ^ (stripPowerAux p fuel q).2 := by
  induction fuel generalizing q with
  | zero => simp [stripPowerAux]
  | succ fuel ih =>
      simp only [stripPowerAux]
      split
      · rename_i h
        dsimp only
        rw [Nat.pow_succ, ← Nat.mul_assoc, ← ih (q / p)]
        have hdiv := Nat.mod_add_div q p
        rw [h.2.2, Nat.zero_add] at hdiv
        simpa [Nat.mul_comm] using hdiv.symm
      · simp

/-- A budget of `q` suffices for all divisions of a positive value by `p ≥ 2`. -/
def stripPower (p q : Nat) : Nat × Nat := stripPowerAux p q q

theorem stripPower_factorization (p q : Nat) :
    q = (stripPower p q).1 * p ^ (stripPower p q).2 :=
  stripPowerAux_factorization p q q

/-- Product represented by a prime/exponent list. -/
def powerProduct : List (Nat × Nat) → Nat
  | [] => 1
  | (p, e) :: rest => p ^ e * powerProduct rest

/-- Product obtained by halving each exponent. -/
def halfPowerProduct : List (Nat × Nat) → Nat
  | [] => 1
  | (p, e) :: rest => p ^ (e / 2) * halfPowerProduct rest

/-- Exact factor-base decomposition, also used to reconstruct smooth relations. -/
def factorOverBase : List Nat → Nat → Nat × List (Nat × Nat)
  | [], q => (q, [])
  | p :: rest, q =>
      let step := stripPower p q
      let tail := factorOverBase rest step.1
      (tail.1, (p, step.2) :: tail.2)

/-- Relation reconstruction preserves the complete polynomial value. -/
theorem factorOverBase_factorization (base : List Nat) (q : Nat) :
    q = (factorOverBase base q).1 * powerProduct (factorOverBase base q).2 := by
  induction base generalizing q with
  | nil => simp [factorOverBase, powerProduct]
  | cons p rest ih =>
      simp only [factorOverBase, powerProduct]
      calc
        q = (stripPower p q).1 * p ^ (stripPower p q).2 :=
          stripPower_factorization p q
        _ = ((factorOverBase rest (stripPower p q).1).1 *
            powerProduct (factorOverBase rest (stripPower p q).1).2) *
            p ^ (stripPower p q).2 := by
              rw [← ih (stripPower p q).1]
        _ = (factorOverBase rest (stripPower p q).1).1 *
            (p ^ (stripPower p q).2 *
              powerProduct (factorOverBase rest (stripPower p q).1).2) := by
              rw [Nat.mul_assoc, Nat.mul_comm (powerProduct _) (p ^ _)]

/-- Every reconstructed smooth polynomial value gives a congruence relation. -/
theorem smooth_relation_congruence (n x : Nat) (base : List Nat)
    (hx : n ≤ x * x) (hsmooth : (factorOverBase base (x * x - n)).1 = 1) :
    (x * x) % n = powerProduct (factorOverBase base (x * x - n)).2 % n := by
  have hfactor := factorOverBase_factorization base (x * x - n)
  rw [hsmooth, Nat.one_mul] at hfactor
  calc
    (x * x) % n = (x * x - n) % n := by
      calc
        (x * x) % n = (x * x - n + n) % n :=
          congrArg (fun a => a % n) (Nat.sub_add_cancel hx).symm
        _ = (x * x - n) % n := by simp
    _ = powerProduct (factorOverBase base (x * x - n)).2 % n := by
      exact congrArg (fun a => a % n) hfactor

/-- This is the square reconstruction used after a parity dependency. -/
theorem even_powerProduct_is_square (factors : List (Nat × Nat))
    (h : ∀ pe ∈ factors, pe.2 % 2 = 0) :
    powerProduct factors = halfPowerProduct factors ^ 2 := by
  induction factors with
  | nil => simp [powerProduct, halfPowerProduct]
  | cons pe rest ih =>
      rcases pe with ⟨p, e⟩
      have he : e % 2 = 0 := h (p, e) (by simp)
      have hrest : ∀ pe ∈ rest, pe.2 % 2 = 0 := by
        intro pe hpe
        exact h pe (by simp [hpe])
      have hexp : e = (e / 2) * 2 := by omega
      have hp : p ^ e = (p ^ (e / 2)) ^ 2 := by
        rw [← Nat.pow_mul, ← hexp]
      simp only [powerProduct, halfPowerProduct]
      rw [ih hrest, hp, Nat.mul_pow]

/-- The parity vector represented by a bitset of selected relation indices. -/
def dependencyParity (relations : List Nat) (dependency : Nat) (index : Nat := 0) : Nat :=
  match relations with
  | [] => 0
  | parity :: rest =>
      (if dependency.testBit index then parity else 0) ^^^
        dependencyParity rest dependency (index + 1)

private theorem xor_shuffle (a b c d : Nat) :
    (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;>
    cases c.testBit i <;> cases d.testBit i <;> rfl

private theorem xor_selection (a b : Bool) (parity : Nat) :
    (if a ^^ b then parity else 0) =
      (if a then parity else 0) ^^^ (if b then parity else 0) := by
  cases a <;> cases b <;> simp

/-- Dependency interpretation is linear over F₂. -/
theorem dependencyParity_xor (relations : List Nat) (a b index : Nat) :
    dependencyParity relations (a ^^^ b) index =
      dependencyParity relations a index ^^^ dependencyParity relations b index := by
  induction relations generalizing index with
  | nil => simp [dependencyParity]
  | cons parity rest ih =>
      simp only [dependencyParity, Nat.testBit_xor]
      rw [xor_selection, ih]
      exact xor_shuffle _ _ _ _

/-- The coupled XOR operation used in elimination preserves row/dependency semantics. -/
theorem row_xor_preserves_dependency (relations : List Nat)
    (parity dependency rowParity rowDependency : Nat)
    (h : parity = dependencyParity relations dependency)
    (hrow : rowParity = dependencyParity relations rowDependency) :
    parity ^^^ rowParity = dependencyParity relations (dependency ^^^ rowDependency) := by
  rw [dependencyParity_xor, ← h, ← hrow]

/-- The addition recurrence used to avoid repeated squaring in a sieve block. -/
theorem quadraticValue_step (n x : Nat) (hx : n ≤ x * x) :
    (x + 1) * (x + 1) - n = (x * x - n) + (2 * x + 1) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

/-- The MPQS addition recurrence avoids multiplication and division at each point. -/
theorem quotientValue_step (n z a : Nat) (ha : 0 < a) (hz : n ≤ z * z) :
    ((z + a) * (z + a) - n) / a = (z * z - n) / a + (2 * z + a) := by
  have hsq : (z + a) * (z + a) = z * z + a * (2 * z + a) := by
    simp only [Nat.add_mul, Nat.mul_add]
    rw [Nat.mul_comm z a, ← Nat.mul_assoc, Nat.mul_comm a 2, Nat.mul_assoc]
    omega
  have hnum : (z + a) * (z + a) - n = (z * z - n) + a * (2 * z + a) := by
    omega
  rw [hnum, Nat.add_mul_div_left _ _ ha]

private structure BasePrime where
  prime : Nat
  roots : Array Nat
  deriving Inhabited

private structure Relation where
  x : Nat
  exponents : Array Nat
  parity : Nat
  deriving Inhabited

private structure PivotRow where
  parity : Nat
  dependency : Nat
  deriving Inhabited

private def rootsModulo (n p : Nat) : Array Nat := Id.run do
  let mut roots := #[]
  for r in [:p] do
    if r * r % p == n % p then
      roots := roots.push r
  return roots

private def factorBase (n bound : Nat) : Array BasePrime := Id.run do
  let mut base := #[]
  for p in [2:bound + 1] do
    if Nat.Prime p then
      let roots := rootsModulo n p
      if !roots.isEmpty then
        base := base.push ⟨p, roots⟩
  return base

/-- Exact modular-root sieving of a block of positive polynomial values. -/
private def sieveBlock (n first count : Nat) (base : Array BasePrime) : Array Nat :=
    Id.run do
  let mut residues := #[]
  let square := first * first
  if n ≤ square then
    let mut value := square - n
    let mut difference := 2 * first + 1
    for _ in [:count] do
      residues := residues.push value
      value := value + difference
      difference := difference + 2
  else
    for i in [:count] do
      let x := first + i
      residues := residues.push (x * x - n)
  for entry in base do
    let p := entry.prime
    for root in entry.roots do
      let start := (root + p - first % p) % p
      for t in [:(count + p - 1) / p] do
        let j := start + t * p
        if j < count then
          let reduced := (stripPower p residues[j]!).1
          residues := residues.set! j reduced
  return residues

private def makeRelation (n x : Nat) (base : Array BasePrime) : Relation := Id.run do
  let decomposition := factorOverBase (base.toList.map BasePrime.prime) (x * x - n)
  let exponents := decomposition.2.toArray.map Prod.snd
  let mut parity := 0
  for j in [:base.size] do
    if exponents[j]! % 2 == 1 then
      parity := parity + 2 ^ j
  return ⟨x, exponents, parity⟩

/-- Insert a parity row, carrying the same XOR operations on relation indices. -/
private def eliminate (rows : Array (Option PivotRow)) (parity dependency : Nat) :
    Array (Option PivotRow) × Option Nat := Id.run do
  let mut rows := rows
  let mut parity := parity
  let mut dependency := dependency
  for j in [:rows.size] do
    if parity.testBit j then
      match rows[j]! with
      | some row =>
          parity := Nat.xor parity row.parity
          dependency := Nat.xor dependency row.dependency
      | none =>
          rows := rows.set! j (some ⟨parity, dependency⟩)
          return (rows, none)
  if parity == 0 then
    return (rows, some dependency)
  return (rows, none)

private def modPow (a exponent modulus : Nat) : Nat :=
  if h : exponent = 0 then 1 % modulus
  else
    let half := modPow a (exponent / 2) modulus
    let square := half * half % modulus
    if exponent % 2 == 1 then square * a % modulus else square
termination_by exponent
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

private def properGcd (n a : Nat) : Option Nat :=
  let d := Nat.gcd a n
  if 1 < d ∧ d < n then some d else none

private def factorFromDependency (n : Nat) (base : Array BasePrime)
    (relations : Array Relation) (dependency : Nat) : Option Nat := Id.run do
  let mut x := 1 % n
  let mut exponents := Array.replicate base.size 0
  for i in [:relations.size] do
    if dependency.testBit i then
      let relation := relations[i]!
      x := x * relation.x % n
      for j in [:base.size] do
        exponents := exponents.set! j (exponents[j]! + relation.exponents[j]!)
  let mut y := 1 % n
  for j in [:base.size] do
    if exponents[j]! % 2 != 0 then
      return none
    y := y * modPow base[j]!.prime (exponents[j]! / 2) n % n
  let difference := if x ≤ y then y - x else x - y
  match properGcd n difference with
  | some d => return some d
  | none => return properGcd n (x + y)

/--
A bounded executable quadratic-sieve splitter.  A successful result is a proper
factor.  Exhausting the requested interval, including on a prime, returns `none`.
The generic checked splitter in the surrounding library certifies divisibility.
-/
private def rawSplit (n : Nat) (factorBaseBound : Nat) (interval : Nat) :
    Option Nat := Id.run do
  if n < 4 then return none
  if n % 2 == 0 then return some 2
  let root := Nat.sqrt n
  if root * root == n then return some root
  let base := factorBase n factorBaseBound
  for entry in base do
    if n % entry.prime == 0 && entry.prime < n then
      return some entry.prime
  if base.isEmpty then return none
  let mut relations : Array Relation := #[]
  let mut rows : Array (Option PivotRow) := Array.replicate base.size none
  for block in [:(interval + 255) / 256] do
    let offset := block * 256
    let count := min 256 (interval - offset)
    let first := root + 1 + offset
    let residues := sieveBlock n first count base
    for i in [:count] do
      if residues[i]! == 1 then
        let relation := makeRelation n (first + i) base
        let index := relations.size
        relations := relations.push relation
        let result := eliminate rows relation.parity (2 ^ index)
        rows := result.1
        match result.2 with
        | none => pure ()
        | some dependency =>
            match factorFromDependency n base relations dependency with
            | none => pure ()
            | some d => return some d
  return none

/-- Independently validate every exit path of the raw search. -/
def validateOutput (n : Nat) : Option Nat → Option Nat
  | none => none
  | some d => if 1 < d ∧ d < n ∧ n % d = 0 then some d else none

theorem validateOutput_sound (n d : Nat) (candidate : Option Nat)
    (h : validateOutput n candidate = some d) : 1 < d ∧ d < n ∧ d ∣ n := by
  cases candidate with
  | none => simp [validateOutput] at h
  | some c =>
      simp only [validateOutput] at h
      split at h
      · rename_i hc
        have heq : c = d := Option.some.inj h
        subst d
        exact ⟨hc.1, hc.2.1, Nat.dvd_of_mod_eq_zero hc.2.2⟩
      · cases h

/-- A bounded quadratic sieve whose every successful output is a proper divisor. -/
def split (n : Nat) (factorBaseBound : Nat := 100) (interval : Nat := 20000) :
    Option Nat := validateOutput n (rawSplit n factorBaseBound interval)

theorem split_sound (n factorBaseBound interval d : Nat)
    (h : split n factorBaseBound interval = some d) : 1 < d ∧ d < n ∧ d ∣ n :=
  validateOutput_sound n d _ h

/-- Parameters for the multiple-polynomial sieve; `interval` is per polynomial. -/
structure MPQSConfig where
  factorBaseBound : Nat := 300
  interval : Nat := 2048
  polynomials : Nat := 64
  factorsPerA : Nat := 3
  deriving Inhabited, Repr

/-- The exact integer identity behind an MPQS relation. -/
theorem mpqs_polynomial_identity (n a b x : Nat)
    (hx : n ≤ (a * x + b) * (a * x + b))
    (hdiv : a ∣ (a * x + b) * (a * x + b) - n) :
    (a * x + b) * (a * x + b) =
      n + a * (((a * x + b) * (a * x + b) - n) / a) := by
  rw [Nat.mul_div_cancel' hdiv]
  omega

/-- Smooth quotient reconstruction supplies the actual MPQS congruence. -/
theorem mpqs_relation_congruence (n a b x : Nat) (base : List Nat)
    (hx : n ≤ (a * x + b) * (a * x + b))
    (hdiv : a ∣ (a * x + b) * (a * x + b) - n)
    (hsmooth : (factorOverBase base
      (((a * x + b) * (a * x + b) - n) / a)).1 = 1) :
    ((a * x + b) * (a * x + b)) % n =
      (a * powerProduct (factorOverBase base
        (((a * x + b) * (a * x + b) - n) / a)).2) % n := by
  have hfactor := factorOverBase_factorization base
    (((a * x + b) * (a * x + b) - n) / a)
  rw [hsmooth, Nat.one_mul] at hfactor
  calc
    ((a * x + b) * (a * x + b)) % n =
        (n + a * (((a * x + b) * (a * x + b) - n) / a)) % n :=
      congrArg (fun z => z % n) (mpqs_polynomial_identity n a b x hx hdiv)
    _ = (a * (((a * x + b) * (a * x + b) - n) / a)) % n := by simp
    _ = (a * powerProduct (factorOverBase base
        (((a * x + b) * (a * x + b) - n) / a)).2) % n :=
      congrArg (fun q => (a * q) % n) hfactor

private structure MPQSPolynomial where
  a : Nat
  b : Nat
  aExponents : Array Nat
  deriving Inhabited

private def polynomialValue (n : Nat) (poly : MPQSPolynomial) (x : Nat) : Nat :=
  let z := poly.a * x + poly.b
  (z * z - n) / poly.a

private def selectionProduct (base : Array BasePrime) (selected : Array Nat) : Nat :=
  selected.foldl (fun product i => product * base[i]!.prime) 1

/-- Rank distinct-prime products by distance from the standard `sqrt(2n)/M` target. -/
private def polynomialSelections (base : Array BasePrime) (target requested : Nat) :
    Array (Array Nat) := Id.run do
  let mut eligible := #[]
  for i in [:base.size] do
    if base[i]!.prime > 2 && base[i]!.roots.size > 1 then
      eligible := eligible.push i
  if eligible.isEmpty then return #[]
  let count := max 1 (min requested eligible.size)
  let mut choices : List (Nat × Array Nat) := []
  for start in [:eligible.size] do
    let mut selected := #[]
    for j in [:count] do
      selected := selected.push eligible[(start + j) % eligible.size]!
    let a := selectionProduct base selected
    let distance := if a ≤ target then target - a else a - target
    choices := (distance, selected) :: choices
  let sorted := choices.mergeSort (fun left right => decide (left.1 ≤ right.1))
  return sorted.toArray.map Prod.snd

/-- Initialize CRT components and the all-first-roots polynomial for one `A`. -/
private def initializePolynomial (base : Array BasePrime) (selected : Array Nat) :
    MPQSPolynomial × Array Nat := Id.run do
  let a := selectionProduct base selected
  let mut b := 0
  let mut coefficients := #[]
  let mut aExponents := Array.replicate base.size 0
  for index in selected do
    let entry := base[index]!
    let p := entry.prime
    let cofactor := a / p
    let coefficient := cofactor * modPow (cofactor % p) (p - 2) p % a
    coefficients := coefficients.push coefficient
    b := (b + entry.roots[0]! * coefficient) % a
    aExponents := aExponents.set! index 1
  return (⟨a, b, aExponents⟩, coefficients)

/-- Gray-code root changes update `B` by CRT deltas while retaining the same `A`. -/
private def advancePolynomial (base : Array BasePrime) (selected coefficients : Array Nat)
    (poly : MPQSPolynomial) (previousGray gray : Nat) : MPQSPolynomial := Id.run do
  let mut b := poly.b
  for j in [:selected.size] do
    if previousGray.testBit j != gray.testBit j then
      let entry := base[selected[j]!]!
      let oldRoot := entry.roots[if previousGray.testBit j then 1 else 0]!
      let newRoot := entry.roots[if gray.testBit j then 1 else 0]!
      let delta := ((newRoot + entry.prime - oldRoot) % entry.prime) *
        coefficients[j]! % poly.a
      b := (b + delta) % poly.a
  return { poly with b := b }

/-- Roots of the quotient polynomial, including its linear roots at primes dividing `A`. -/
private def quotientFactorBase (n : Nat) (poly : MPQSPolynomial)
    (base : Array BasePrime) : Array BasePrime := Id.run do
  let mut result := #[]
  for entry in base do
    let p := entry.prime
    if poly.a % p == 0 then
      let modulus := poly.a * p
      let c := ((poly.b * poly.b % modulus + modulus - n % modulus) % modulus) / poly.a
      let root := ((p - c % p) % p) * modPow (2 * poly.b % p) (p - 2) p % p
      result := result.push ⟨p, #[root]⟩
    else
      let inverse := modPow (poly.a % p) (p - 2) p
      let roots := entry.roots.map
        (fun r => (r + p - poly.b % p) % p * inverse % p)
      result := result.push ⟨p, roots⟩
  return result

private def sievePolynomialBlock (n first count : Nat) (poly : MPQSPolynomial)
    (base : Array BasePrime) : Array Nat := Id.run do
  let mut residues := #[]
  let z := poly.a * first + poly.b
  let square := z * z
  if 0 < poly.a ∧ n ≤ square then
    let mut value := (square - n) / poly.a
    let mut difference := 2 * z + poly.a
    for _ in [:count] do
      residues := residues.push value
      value := value + difference
      difference := difference + 2 * poly.a
  else
    for i in [:count] do
      residues := residues.push (polynomialValue n poly (first + i))
  for entry in base do
    let p := entry.prime
    for root in entry.roots do
      let start := (root + p - first % p) % p
      for t in [:(count + p - 1) / p] do
        let j := start + t * p
        if j < count then
          residues := residues.set! j (stripPower p residues[j]!).1
  return residues

private def makePolynomialRelation (n x : Nat) (poly : MPQSPolynomial)
    (base : Array BasePrime) : Option Relation := Id.run do
  let decomposition := factorOverBase (base.toList.map BasePrime.prime)
    (polynomialValue n poly x)
  if decomposition.1 != 1 then return none
  let mut exponents := decomposition.2.toArray.map Prod.snd
  let mut parity := 0
  for j in [:base.size] do
    let exponent := exponents[j]! + poly.aExponents[j]!
    exponents := exponents.set! j exponent
    if exponent % 2 == 1 then parity := parity + 2 ^ j
  return some ⟨poly.a * x + poly.b, exponents, parity⟩

private def rawSplitMPQS (n : Nat) (config : MPQSConfig) : Option Nat := Id.run do
  if n < 4 then return none
  if n % 2 == 0 then return some 2
  let root := Nat.sqrt n
  if root * root == n then return some root
  let base := factorBase n config.factorBaseBound
  for entry in base do
    if n % entry.prime == 0 && entry.prime < n then return some entry.prime
  let target := max 3 (Nat.sqrt (2 * n) / max 1 config.interval)
  let selections := polynomialSelections base target config.factorsPerA
  if selections.isEmpty then return none
  let patterns := 2 ^ selections[0]!.size
  let mut selected : Array Nat := #[]
  let mut coefficients : Array Nat := #[]
  let mut poly : MPQSPolynomial := default
  let mut previousGray := 0
  let mut relations : Array Relation := #[]
  let mut rows : Array (Option PivotRow) := Array.replicate base.size none
  for index in [:config.polynomials] do
    let pattern := index % patterns
    let gray := Nat.xor pattern (pattern / 2)
    if pattern == 0 then
      selected := selections[(index / patterns) % selections.size]!
      let initialized := initializePolynomial base selected
      poly := initialized.1
      coefficients := initialized.2
    else
      poly := advancePolynomial base selected coefficients poly previousGray gray
    previousGray := gray
    -- The quotient is exact for every x when this CRT invariant holds.
    if poly.a > 1 && poly.b * poly.b % poly.a == n % poly.a then
      let sieveBase := quotientFactorBase n poly base
      let first := if root + 1 ≤ poly.b then 0
        else (root + 1 - poly.b + poly.a - 1) / poly.a
      for block in [:(config.interval + 255) / 256] do
        let offset := block * 256
        let count := min 256 (config.interval - offset)
        let residues := sievePolynomialBlock n (first + offset) count poly sieveBase
        for i in [:count] do
          if residues[i]! == 1 then
            match makePolynomialRelation n (first + offset + i) poly base with
            | none => pure ()
            | some relation =>
                let relationIndex := relations.size
                relations := relations.push relation
                let reduced := eliminate rows relation.parity (2 ^ relationIndex)
                rows := reduced.1
                match reduced.2 with
                | none => pure ()
                | some dependency =>
                    match factorFromDependency n base relations dependency with
                    | none => pure ()
                    | some d => return some d
  return none

/--
A bounded multiple-polynomial quadratic sieve with CRT-selected squarefree `A`,
Gray-code updates of `B`, quotient sieving, and the factors of `A` in each relation.
All polynomial values used here are positive; interval exhaustion returns `none`.
-/
def splitMPQS (n : Nat) (config : MPQSConfig := {}) : Option Nat :=
  validateOutput n (rawSplitMPQS n config)

theorem splitMPQS_sound (n d : Nat) (config : MPQSConfig)
    (h : splitMPQS n config = some d) : 1 < d ∧ d < n ∧ d ∣ n :=
  validateOutput_sound n d _ h

end PrimeFactorLean.QuadraticSieve
