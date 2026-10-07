import PrimeFactorLean.Core
import PrimeFactorLean.QuadraticSieve
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# A bounded quadratic number-field sieve prototype

For `m = floor(sqrt n)` and `c = n - m²`, use the monic algebraic
polynomial `f(X) = X² + c` and the rational polynomial `g(X) = X - m`.
For nonsquare positive inputs `c > 0`, the algebraic side is the imaginary
quadratic order `Z[alpha]`, where `alpha² = -c`.  Relations consist of genuine
algebraic elements `a + b*alpha` and their rational images `a + b*m`.

This prototype sieves both the rational values and the algebraic norms,
reduces their exponent-parity vectors over F₂, and checks an *actual algebraic
square root* before extracting a divisor.  Square norm alone is never accepted
as evidence of an algebraic square.  The square-root step uses the exact
quadratic formula and verifies both integer coefficients of the result.

This is a bounded degree-two number-field method, not a competitive GNFS
implementation.  It does not implement higher-degree polynomial selection,
prime-ideal factor-base columns, character columns, lattice sieving, or the
large sparse matrix and algebraic-root algorithms needed by modern GNFS.
Its norm-parity matrix is a necessary-condition prefilter; exact square-root
validation rejects false dependencies.  It can return `none` on composites.
-/

namespace PrimeFactorLean.NumberFieldSieve

/-- Coefficients of `re + im*alpha` in the order with `alpha² = -c`. -/
structure Algebraic where
  re : Int
  im : Int
  deriving Repr, BEq, DecidableEq, Inhabited

theorem Algebraic.ext {x y : Algebraic} (hre : x.re = y.re) (him : x.im = y.im) :
    x = y := by
  cases x
  cases y
  cases hre
  cases him
  rfl

def one : Algebraic := ⟨1, 0⟩

/-- Exact multiplication after reduction modulo `X² + c`. -/
def mul (c : Nat) (x y : Algebraic) : Algebraic :=
  ⟨x.re * y.re - (c : Int) * x.im * y.im,
    x.re * y.im + x.im * y.re⟩

/-- The determinant of multiplication by `re + im*alpha`. -/
def norm (c : Nat) (x : Algebraic) : Int :=
  x.re * x.re + (c : Int) * x.im * x.im

def evaluate (m : Nat) (x : Algebraic) : Int := x.re + x.im * (m : Int)

def product (c : Nat) : List Algebraic → Algebraic
  | [] => one
  | x :: xs => mul c x (product c xs)

theorem mul_assoc (c : Nat) (x y z : Algebraic) :
    mul c (mul c x y) z = mul c x (mul c y z) := by
  apply Algebraic.ext <;> simp only [mul] <;> ring

theorem mul_comm (c : Nat) (x y : Algebraic) : mul c x y = mul c y x := by
  apply Algebraic.ext <;> simp only [mul] <;> ring

@[simp] theorem one_mul (c : Nat) (x : Algebraic) : mul c one x = x := by
  apply Algebraic.ext <;> simp [mul, one]

@[simp] theorem mul_one (c : Nat) (x : Algebraic) : mul c x one = x := by
  rw [mul_comm, one_mul]

theorem norm_mul (c : Nat) (x y : Algebraic) :
    norm c (mul c x y) = norm c x * norm c y := by
  simp only [norm, mul]
  ring

/-- Integer evaluation differs from a homomorphism by a multiple of `f(m)`. -/
theorem evaluate_mul_identity (c m : Nat) (x y : Algebraic) :
    evaluate m (mul c x y) = evaluate m x * evaluate m y -
      ((c : Int) + (m : Int) * (m : Int)) * x.im * y.im := by
  simp only [evaluate, mul]
  ring

def modulusParameter (n : Nat) : Nat := n - Nat.sqrt n * Nat.sqrt n

/-- The selected algebraic polynomial has the advertised integer value. -/
theorem selected_polynomial (n : Nat) :
    Nat.sqrt n * Nat.sqrt n + modulusParameter n = n := by
  exact Nat.add_sub_of_le (Nat.sqrt_le n)

/-- Nonsquare inputs select a strictly positive parameter, so `X²+c` has
no rational root and the algebraic side is genuinely quadratic. -/
theorem selected_parameter_positive (n : Nat)
    (hn : Nat.sqrt n * Nat.sqrt n ≠ n) : 0 < modulusParameter n := by
  have hs := Nat.sqrt_le n
  unfold modulusParameter
  omega

/-- The selected positive-parameter quadratic has no rational root. -/
theorem polynomial_no_rational_root (c : Nat) (hc : 0 < c) (q : Rat) :
    q * q + (c : Rat) ≠ 0 := by
  have hq := mul_self_nonneg q
  have hc' : (0 : Rat) < (c : Rat) := by exact_mod_cast hc
  linarith

/-- Reduction at `alpha = m` is multiplicative modulo `n` when `f(m) = n`. -/
theorem evaluate_mul_mod (c m n : Nat) (h : m * m + c = n)
    (x y : Algebraic) :
    (evaluate m (mul c x y) : ZMod n) =
      (evaluate m x : ZMod n) * (evaluate m y : ZMod n) := by
  have hroot : (m : ZMod n) * (m : ZMod n) + (c : ZMod n) = 0 := by
    have hh := congrArg (fun t : Nat => (t : ZMod n)) h
    simpa using hh
  have hc : (c : ZMod n) = -((m : ZMod n) * (m : ZMod n)) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa [add_comm] using hroot
  simp only [evaluate, mul, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  rw [hc]
  ring

theorem evaluate_product_mod (c m n : Nat) (h : m * m + c = n)
    (xs : List Algebraic) :
    (evaluate m (product c xs) : ZMod n) =
      ((xs.map (evaluate m)).prod : ZMod n) := by
  induction xs with
  | nil => simp [product, one, evaluate]
  | cons x xs ih =>
      simp only [product, evaluate_mul_mod c m n h, List.map_cons, List.prod_cons,
        Int.cast_mul, ih]

/-- The actual two square roots give the NFS congruence of squares. -/
theorem square_roots_congruence (c m n : Nat) (h : m * m + c = n)
    (xs : List Algebraic) (root : Algebraic) (rationalRoot : Int)
    (halg : mul c root root = product c xs)
    (hrat : rationalRoot * rationalRoot = (xs.map (evaluate m)).prod) :
    (evaluate m root : ZMod n) ^ 2 = (rationalRoot : ZMod n) ^ 2 := by
  have hp := evaluate_product_mod c m n h xs
  rw [← halg, evaluate_mul_mod c m n h, ← hrat, Int.cast_mul] at hp
  simpa [pow_two] using hp

/-- A finite exact integer square-root checker; negative inputs fail. -/
def integerSquareRoot (z : Int) : Option {r : Int // r * r = z} :=
  let r : Int := Nat.sqrt z.natAbs
  if h : r * r = z then some ⟨r, h⟩ else none

/-- A checked root in `Z[alpha]`.  The formula is only a candidate generator;
the defining algebraic square equality is checked before a result is returned. -/
def algebraicSquareRoot (c : Nat) (z : Algebraic) :
    Option {r : Algebraic // mul c r r = z} := do
  let nr ← integerSquareRoot (norm c z)
  let uSquared := (z.re + nr.val) / 2
  let u ← integerSquareRoot uSquared
  let candidate : Algebraic :=
    if u.val = 0 then
      ⟨0, (Nat.sqrt ((-z.re) / (c : Int)).natAbs : Int)⟩
    else ⟨u.val, z.im / (2 * u.val)⟩
  if h : mul c candidate candidate = z then some ⟨candidate, h⟩ else none

/-- Bounds on relation collection and kernel-combination search. -/
structure Config where
  factorBaseBound : Nat := 31
  aRadius : Nat := 40
  bBound : Nat := 8
  relationLimit : Nat := 40
  dependencyLimit : Nat := 14
  deriving Repr, Inhabited

private structure Relation where
  element : Algebraic
  parity : Nat
  deriving Inhabited

private structure Pivot where
  parity : Nat
  mask : Nat
  deriving Inhabited

private def basePrimes (bound : Nat) : List Nat :=
  (List.range (bound + 1)).filter fun p => decide (Nat.Prime p)

private def parityMask (factors : List (Nat × Nat)) (offset : Nat) : Nat := Id.run do
  let mut parity := 0
  let mut j := offset
  for (_, e) in factors do
    if e % 2 == 1 then parity := parity + 2 ^ j
    j := j + 1
  return parity

/-- Simultaneous exact smoothness sieve over rational values and algebraic norms.
Norm columns are a prefilter; the later algebraic root must be checked exactly. -/
private def collect (c m : Nat) (base : List Nat) (cfg : Config) : Array Relation :=
    Id.run do
  let mut relations := #[]
  for b in [1:cfg.bBound + 1] do
    for offset in [:2 * cfg.aRadius + 1] do
      let a : Int := (offset : Int) - (cfg.aRadius : Int)
      if Nat.gcd a.natAbs b != 1 then continue
      let element : Algebraic := ⟨a, b⟩
      let rational := evaluate m element
      let algebraicNorm := norm c element
      if rational == 0 || algebraicNorm <= 0 then continue
      let rationalFactors := QuadraticSieve.factorOverBase base rational.natAbs
      if rationalFactors.1 != 1 then continue
      let algebraicFactors := QuadraticSieve.factorOverBase base algebraicNorm.natAbs
      if algebraicFactors.1 != 1 then continue
      let sign : Nat := if rational < 0 then 1 else 0
      let parity := sign + parityMask rationalFactors.2 1 +
        parityMask algebraicFactors.2 (base.length + 1)
      relations := relations.push ⟨element, parity⟩
      if relations.size >= cfg.relationLimit then return relations
  return relations

private def eliminate (pivots : Array (Option Pivot)) (parity mask : Nat) :
    Array (Option Pivot) × Option Nat := Id.run do
  let mut pivots := pivots
  let mut parity := parity
  let mut mask := mask
  for j in [:pivots.size] do
    if parity.testBit j then
      match pivots[j]! with
      | some p =>
          parity := Nat.xor parity p.parity
          mask := Nat.xor mask p.mask
      | none =>
          pivots := pivots.set! j (some ⟨parity, mask⟩)
          return (pivots, none)
  if parity == 0 then return (pivots, some mask)
  return (pivots, none)

private def kernelBasis (relations : Array Relation) (columns limit : Nat) : Array Nat :=
    Id.run do
  let mut pivots := Array.replicate columns none
  let mut dependencies := #[]
  for i in [:relations.size] do
    let result := eliminate pivots relations[i]!.parity (2 ^ i)
    pivots := result.1
    if let some mask := result.2 then
      dependencies := dependencies.push mask
      if dependencies.size >= limit then return dependencies
  return dependencies

private def selectedElements (relations : Array Relation) (mask : Nat) : List Algebraic :=
    Id.run do
  let mut elements := []
  for i in [:relations.size] do
    if mask.testBit i then elements := relations[i]!.element :: elements
  return elements

/-- Exact roots are proof-carrying values.  The final divisor is checked as well. -/
private def extract (n c m : Nat) (relations : Array Relation) (mask : Nat) :
    Option (ProperFactor n) := do
  let xs := selectedElements relations mask
  let rationalRoot ← integerSquareRoot (xs.map (evaluate m)).prod
  let algebraicRoot ← algebraicSquareRoot c (product c xs)
  let x := evaluate m algebraicRoot.val
  let y := rationalRoot.val
  match checkFactor n (Nat.gcd (x - y).natAbs n) with
  | some d => some d
  | none => checkFactor n (Nat.gcd (x + y).natAbs n)

/-- Bounded degree-two NFS splitter, with a certified result on success. -/
def splitCertified (n : Nat) (cfg : Config := {}) : Option (ProperFactor n) :=
    Id.run do
  if n < 4 then return none
  let m := Nat.sqrt n
  let c := modulusParameter n
  if c == 0 then return checkFactor n m
  let base := basePrimes cfg.factorBaseBound
  let relations := collect c m base cfg
  let dependencies := kernelBasis relations (2 * base.length + 1) cfg.dependencyLimit
  for combination in [1:2 ^ dependencies.size] do
    let mut mask := 0
    for j in [:dependencies.size] do
      if combination.testBit j then mask := Nat.xor mask dependencies[j]!
    if let some d := extract n c m relations mask then return some d
  return none

/-- Interface shared with the other fallible raw searches. -/
def split (n : Nat) (cfg : Config := {}) : Option Nat :=
  (splitCertified n cfg).map Subtype.val

theorem split_correct {n d : Nat} {cfg : Config} (h : split n cfg = some d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  unfold split at h
  rcases Option.map_eq_some_iff.mp h with ⟨result, _, heq⟩
  subst d
  exact result.property

/-- The complete factorization engine can use the bounded number-field search. -/
theorem factorization_correct (n : Nat) (hn : n ≠ 0) (cfg : Config := {}) :
    IsFactorization n (factorCore (fun n => splitCertified n cfg) n) :=
  factorCore_correct (fun n => splitCertified n cfg) n hn

end PrimeFactorLean.NumberFieldSieve
