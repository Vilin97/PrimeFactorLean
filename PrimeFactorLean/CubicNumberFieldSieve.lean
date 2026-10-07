import PrimeFactorLean.NumberFieldSieve
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Bounded cubic number-field sieve

This extends the quadratic prototype with a monic cubic selected from the
base-`m` expansion of `n`, a checked irreducibility certificate modulo a prime,
exact arithmetic in the resulting cubic order, degree-one prime-ideal columns
`(p,r)` on the algebraic side, and actual algebraic square-root extraction.
The algebraic norm is computed as the determinant of multiplication, and its
multiplicativity is proved for the executable coefficient arithmetic.

The square-root stage enumerates bounded integer coefficient triples and
indexes their exact squares in a hash map.  Every recovered root is checked
again by exact multiplication.  Ideal parity is never assumed to imply that
an algebraic element is a square.  Matrix bounds and root bounds are explicit.

This is a *cubic* educational NFS implementation,
not an arbitrary-degree or competitive modern GNFS implementation.  It has no
large-prime variants, character columns, lattice sieve, sparse block Lanczos,
or efficient general number-field square-root algorithm.  Bounded searches
can fail, and the surrounding complete factorizer supplies its verified
fallback.
-/

namespace PrimeFactorLean.CubicNumberFieldSieve

structure Cubic where
  a : Int
  b : Int
  c : Int
  deriving Repr, BEq, DecidableEq, Inhabited

structure Algebraic where
  u : Int
  v : Int
  w : Int
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

theorem Algebraic.ext {x y : Algebraic} (hu : x.u = y.u) (hv : x.v = y.v)
    (hw : x.w = y.w) : x = y := by
  cases x
  cases y
  cases hu
  cases hv
  cases hw
  rfl

def one : Algebraic := ⟨1, 0, 0⟩

/-- Exact reduction of the convolution by `alpha³ = -a*alpha²-b*alpha-c`. -/
def mul (f : Cubic) (x y : Algebraic) : Algebraic :=
  let t3 := x.v * y.w + x.w * y.v
  let t4 := x.w * y.w
  ⟨x.u * y.u - f.c * t3 + f.a * f.c * t4,
    x.u * y.v + x.v * y.u - f.b * t3 + (f.a * f.b - f.c) * t4,
    x.u * y.w + x.v * y.v + x.w * y.u - f.a * t3 +
      (f.a * f.a - f.b) * t4⟩

def evaluate (m : Int) (x : Algebraic) : Int := x.u + x.v * m + x.w * m * m

def polynomialEvaluate (f : Cubic) (m : Int) : Int :=
  m * m * m + f.a * m * m + f.b * m + f.c

noncomputable def polynomial (f : Cubic) : Polynomial Int :=
  Polynomial.C 1 * Polynomial.X ^ 3 + Polynomial.C f.a * Polynomial.X ^ 2 +
    Polynomial.C f.b * Polynomial.X + Polynomial.C f.c

theorem polynomial_monic (f : Cubic) : (polynomial f).Monic := by
  unfold Polynomial.Monic polynomial
  exact Polynomial.leadingCoeff_cubic (by decide : (1 : Int) ≠ 0)

theorem polynomial_natDegree (f : Cubic) : (polynomial f).natDegree = 3 := by
  exact Polynomial.natDegree_cubic (by decide : (1 : Int) ≠ 0)

theorem mul_assoc (f : Cubic) (x y z : Algebraic) :
    mul f (mul f x y) z = mul f x (mul f y z) := by
  apply Algebraic.ext <;> simp only [mul] <;> ring

theorem mul_comm (f : Cubic) (x y : Algebraic) : mul f x y = mul f y x := by
  apply Algebraic.ext <;> simp only [mul] <;> ring

theorem evaluate_mul_identity (f : Cubic) (m : Int) (x y : Algebraic) :
    evaluate m (mul f x y) = evaluate m x * evaluate m y -
      polynomialEvaluate f m *
        ((x.v * y.w + x.w * y.v) + (m - f.a) * x.w * y.w) := by
  simp only [evaluate, polynomialEvaluate, mul]
  ring

theorem evaluate_mul_mod (f : Cubic) (m : Int) (n : Nat)
    (h : (polynomialEvaluate f m : ZMod n) = 0) (x y : Algebraic) :
    (evaluate m (mul f x y) : ZMod n) =
      (evaluate m x : ZMod n) * (evaluate m y : ZMod n) := by
  rw [evaluate_mul_identity]
  simp only [Int.cast_sub, Int.cast_mul, h, zero_mul, sub_zero]

/-- The linear transformation for multiplication by an algebraic element. -/
def multiplicationMatrix (f : Cubic) (x : Algebraic) : Matrix (Fin 3) (Fin 3) Int :=
  fun i j =>
    if i = 0 then
      if j = 0 then x.u else if j = 1 then -f.c * x.w
      else -f.c * x.v + f.a * f.c * x.w
    else if i = 1 then
      if j = 0 then x.v else if j = 1 then x.u - f.b * x.w
      else -f.b * x.v + (f.a * f.b - f.c) * x.w
    else
      if j = 0 then x.w else if j = 1 then x.v - f.a * x.w
      else x.u - f.a * x.v + (f.a * f.a - f.b) * x.w

/-- A computable 3×3 determinant of the actual multiplication matrix. -/
def norm (f : Cubic) (x : Algebraic) : Int :=
  let a := multiplicationMatrix f x
  a 0 0 * a 1 1 * a 2 2 - a 0 0 * a 1 2 * a 2 1 -
    a 0 1 * a 1 0 * a 2 2 + a 0 1 * a 1 2 * a 2 0 +
    a 0 2 * a 1 0 * a 2 1 - a 0 2 * a 1 1 * a 2 0

theorem norm_eq_determinant (f : Cubic) (x : Algebraic) :
    norm f x = (multiplicationMatrix f x).det := by
  rw [Matrix.det_fin_three]
  rfl

theorem multiplicationMatrix_mul (f : Cubic) (x y : Algebraic) :
    multiplicationMatrix f (mul f x y) = multiplicationMatrix f x * multiplicationMatrix f y := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [multiplicationMatrix, mul, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem norm_mul (f : Cubic) (x y : Algebraic) :
    norm f (mul f x y) = norm f x * norm f y := by
  rw [norm_eq_determinant, multiplicationMatrix_mul, Matrix.det_mul,
    ← norm_eq_determinant, ← norm_eq_determinant]

/-- The homogeneous cubic algebraic norm used by the relation sieve. -/
theorem norm_linear (f : Cubic) (a b : Int) :
    norm f ⟨a, b, 0⟩ = a ^ 3 - f.a * a * a * b +
      f.b * a * b * b - f.c * b ^ 3 := by
  simp [norm, multiplicationMatrix]
  ring

private def relationSylvester (f : Cubic) (a b : Int) : Matrix (Fin 4) (Fin 4) Int :=
  fun i j => if i = 0 then (if j = 0 then f.c else if j = 1 then a else 0)
  else if i = 1 then (if j = 0 then f.b else if j = 1 then b else if j = 2 then a else 0)
  else if i = 2 then (if j = 0 then f.a else if j = 2 then b else if j = 3 then a else 0)
  else (if j = 0 then 1 else if j = 3 then b else 0)

private theorem relationSylvester_eq (f : Cubic) (a b : Int) :
    Polynomial.sylvester (polynomial f)
      (Polynomial.C a + Polynomial.C b * Polynomial.X) 3 1 = relationSylvester f a b := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Polynomial.sylvester, polynomial, relationSylvester]
  all_goals norm_num [Fin.addCases, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X, Fin.subNat]
  all_goals simp only [← Polynomial.C_eq_intCast, Polynomial.coeff_C, Fin.ext_iff]
  all_goals norm_num

/-- The sieved determinant norm is the homogeneous linear resultant.  The
minus sign follows mathlib's ascending-coefficient Sylvester orientation. -/
theorem norm_linear_eq_resultant (f : Cubic) (a b : Int) :
    norm f ⟨a, b, 0⟩ = -(Polynomial.resultant (polynomial f)
      (Polynomial.C a + Polynomial.C b * Polynomial.X) 3 1) := by
  rw [norm_linear]
  unfold Polynomial.resultant
  rw [relationSylvester_eq, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply]
  norm_num [relationSylvester, Fin.succAbove, Fin.ext_iff, Fin.lt_def, Fin.le_def]
  ring

def product (f : Cubic) : List Algebraic → Algebraic
  | [] => one
  | x :: xs => mul f x (product f xs)

theorem evaluate_product_mod (f : Cubic) (m : Int) (n : Nat)
    (h : (polynomialEvaluate f m : ZMod n) = 0) (xs : List Algebraic) :
    (evaluate m (product f xs) : ZMod n) = ((xs.map (evaluate m)).prod : ZMod n) := by
  induction xs with
  | nil => simp [product, one, evaluate]
  | cons x xs ih =>
      simp only [product, evaluate_mul_mod f m n h, List.map_cons, List.prod_cons,
        Int.cast_mul, ih]

theorem square_roots_congruence (f : Cubic) (m : Int) (n : Nat)
    (h : (polynomialEvaluate f m : ZMod n) = 0) (xs : List Algebraic)
    (root : Algebraic) (rationalRoot : Int)
    (halg : mul f root root = product f xs)
    (hrat : rationalRoot * rationalRoot = (xs.map (evaluate m)).prod) :
    (evaluate m root : ZMod n) ^ 2 = (rationalRoot : ZMod n) ^ 2 := by
  have hp := evaluate_product_mod f m n h xs
  rw [← halg, evaluate_mul_mod f m n h, ← hrat, Int.cast_mul] at hp
  simpa [pow_two] using hp

/-- A cubic without roots over a prime field is irreducible over the integers. -/
theorem irreducible_of_no_roots_mod (f : Cubic) (p : Nat) (hp : Nat.Prime p)
    (hcheck : ∀ r : Fin p, polynomialEvaluate f r.val % (p : Int) ≠ 0) :
    Irreducible (polynomial f) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  apply Polynomial.Monic.irreducible_of_irreducible_map (φ := Int.castRingHom (ZMod p))
    (polynomial f) (polynomial_monic f)
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hd : ((polynomial f).map (Int.castRingHom (ZMod p))).natDegree = 3 := by
      simpa [polynomial, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow] using
        (Polynomial.natDegree_cubic (b := (f.a : ZMod p)) (c := (f.b : ZMod p))
          (d := (f.c : ZMod p)) (one_ne_zero : (1 : ZMod p) ≠ 0))
    simp [hd]
  · intro x hx
    have hcast : (polynomialEvaluate f x.val : ZMod p) = 0 := by
      simpa [Polynomial.IsRoot, polynomial, Polynomial.eval_map, polynomialEvaluate,
        pow_succ, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val,
        _root_.mul_assoc]
        using hx
    have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hcast
    exact hcheck ⟨x.val, ZMod.val_lt x⟩ (Int.emod_eq_zero_of_dvd hdiv)

structure Choice (n : Nat) where
  m : Nat
  f : Cubic
  rootEquation : polynomialEvaluate f m = (n : Int)
  irreducible : Irreducible (polynomial f)

theorem Choice.root_mod {n : Nat} (choice : Choice n) :
    (polynomialEvaluate choice.f choice.m : ZMod n) = 0 := by
  rw [choice.rootEquation]
  simp

/-- The central NFS identity specialized to the actual checked polynomial
selection contract used by the executable search. -/
theorem selected_square_roots_congruence {n : Nat} (choice : Choice n)
    (xs : List Algebraic) (root : Algebraic) (rationalRoot : Int)
    (halg : mul choice.f root root = product choice.f xs)
    (hrat : rationalRoot * rationalRoot = (xs.map (evaluate choice.m)).prod) :
    (evaluate choice.m root : ZMod n) ^ 2 = (rationalRoot : ZMod n) ^ 2 :=
  square_roots_congruence choice.f choice.m n choice.root_mod xs root rationalRoot halg hrat

private def cubicRootAux (n : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if hi <= lo + 1 then lo else
      let mid := (lo + hi) / 2
      if mid * mid * mid <= n then cubicRootAux n fuel mid hi
      else cubicRootAux n fuel lo mid

private def irreducibilityCheck (f : Cubic) (p : Nat) :
    Option {u : Unit // Irreducible (polynomial f)} :=
  if hp : Nat.Prime p then
    if hcheck : ∀ r : Fin p, polynomialEvaluate f r.val % (p : Int) ≠ 0 then
      some ⟨(), irreducible_of_no_roots_mod f p hp hcheck⟩
    else none
  else none

/-- Select a monic cubic from the base-`m` digits of the input.  Its common
root equation and irreducibility are both checked and carried in the result. -/
def select (n : Nat) : Option (Choice n) := Id.run do
  let m := max 2 (cubicRootAux n (n.log2 + 2) 0 (n + 1))
  let c := n % m
  let q := n / m
  let b := q % m
  let q := q / m
  let a := q % m
  if q / m != 1 then return none
  let f : Cubic := ⟨a, b, c⟩
  if hroot : polynomialEvaluate f m = (n : Int) then
    for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] do
      if let some proof := irreducibilityCheck f p then
        return some ⟨m, f, hroot, proof.property⟩
  return none

structure Config where
  factorBaseBound : Nat := 31
  aRadius : Nat := 60
  bBound : Nat := 12
  relationLimit : Nat := 60
  dependencyLimit : Nat := 14
  rootCoefficientBound : Nat := 12
  deriving Repr, Inhabited

private structure IdealPrime where
  p : Nat
  root : Nat
  primeIndex : Nat
  deriving Inhabited

private structure Relation where
  element : Algebraic
  parity : Nat
  deriving Inhabited

private structure Pivot where
  parity : Nat
  mask : Nat
  deriving Inhabited

private def discriminant (f : Cubic) : Int :=
  f.a ^ 2 * f.b ^ 2 - 4 * f.b ^ 3 - 4 * f.a ^ 3 * f.c -
    27 * f.c ^ 2 + 18 * f.a * f.b * f.c

/-- Degree-one unramified prime-ideal labels.  A root `r` describes evaluation
at `alpha = r` modulo `p`, whose multiplicativity is `evaluate_mul_mod`. -/
private def idealBase (f : Cubic) (base : Array Nat) : Array IdealPrime := Id.run do
  let mut ideals := #[]
  for j in [:base.size] do
    let p := base[j]!
    if discriminant f % (p : Int) == 0 then continue
    for r in [:p] do
      if polynomialEvaluate f r % (p : Int) == 0 then
        ideals := ideals.push ⟨p, r, j⟩
  return ideals

private def collect (m : Nat) (f : Cubic) (base : Array Nat)
    (ideals : Array IdealPrime) (cfg : Config) : Array Relation := Id.run do
  let mut relations := #[]
  for b in [1:cfg.bBound + 1] do
    for offset in [:2 * cfg.aRadius + 1] do
      let a : Int := (offset : Int) - (cfg.aRadius : Int)
      if Nat.gcd a.natAbs b != 1 then continue
      let element : Algebraic := ⟨a, b, 0⟩
      let rational := evaluate m element
      let algebraicNorm := norm f element
      if rational == 0 || algebraicNorm == 0 then continue
      let rationalFactors := QuadraticSieve.factorOverBase base.toList rational.natAbs
      if rationalFactors.1 != 1 then continue
      let algebraicFactors := QuadraticSieve.factorOverBase base.toList algebraicNorm.natAbs
      if algebraicFactors.1 != 1 then continue
      let algebraicExponents := algebraicFactors.2.toArray.map Prod.snd
      let mut bad := false
      for j in [:base.size] do
        if algebraicExponents[j]! > 0 && discriminant f % (base[j]! : Int) == 0 then
          bad := true
      if bad then continue
      let mut parity : Nat := if rational < 0 then 1 else 0
      if algebraicNorm < 0 then parity := parity + 2
      let rationalExponents := rationalFactors.2.toArray.map Prod.snd
      for j in [:base.size] do
        if rationalExponents[j]! % 2 == 1 then parity := parity + 2 ^ (2 + j)
      for j in [:ideals.size] do
        let ideal := ideals[j]!
        if (a + (b : Int) * ideal.root) % (ideal.p : Int) == 0 then
          if algebraicExponents[ideal.primeIndex]! % 2 == 1 then
            parity := parity + 2 ^ (2 + base.size + j)
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

private def squareDictionary (f : Cubic) (bound : Nat) : Std.HashMap Algebraic Algebraic :=
    Id.run do
  let mut squares := {}
  for u in [:bound + 1] do
    for vi in [:2 * bound + 1] do
      for wi in [:2 * bound + 1] do
        let root : Algebraic := ⟨u, (vi : Int) - bound, (wi : Int) - bound⟩
        squares := squares.insert (mul f root root) root
  return squares

private def squareRoot (f : Cubic) (dictionary : Std.HashMap Algebraic Algebraic)
    (z : Algebraic) : Option {r : Algebraic // mul f r r = z} := do
  let r ← dictionary[z]?
  if h : mul f r r = z then some ⟨r, h⟩ else none

private def selectedElements (relations : Array Relation) (mask : Nat) : List Algebraic :=
    Id.run do
  let mut elements := []
  for i in [:relations.size] do
    if mask.testBit i then elements := relations[i]!.element :: elements
  return elements

private def extract (n m : Nat) (f : Cubic) (relations : Array Relation)
    (dictionary : Std.HashMap Algebraic Algebraic) (mask : Nat) :
    Option (ProperFactor n) := do
  let xs := selectedElements relations mask
  let rationalRoot ← NumberFieldSieve.integerSquareRoot (xs.map (evaluate m)).prod
  let algebraicRoot ← squareRoot f dictionary (product f xs)
  let x := evaluate m algebraicRoot.val
  let y := rationalRoot.val
  match checkFactor n (Nat.gcd (x - y).natAbs n) with
  | some d => some d
  | none => checkFactor n (Nat.gcd (x + y).natAbs n)

/-- Bounded, certified cubic NFS using both-side relation sieving and actual
square roots in an order whose defining cubic is certified irreducible. -/
def splitCertified (n : Nat) (cfg : Config := {}) : Option (ProperFactor n) := Id.run do
  let some choice := select n | return none
  let base := ((List.range (cfg.factorBaseBound + 1)).filter
    fun p => decide (Nat.Prime p)).toArray
  let ideals := idealBase choice.f base
  let relations := collect choice.m choice.f base ideals cfg
  let dependencies := kernelBasis relations (2 + base.size + ideals.size) cfg.dependencyLimit
  if dependencies.isEmpty then return none
  let dictionary := squareDictionary choice.f cfg.rootCoefficientBound
  for combination in [1:2 ^ dependencies.size] do
    let mut mask := 0
    for j in [:dependencies.size] do
      if combination.testBit j then mask := Nat.xor mask dependencies[j]!
    if let some d := extract n choice.m choice.f relations dictionary mask then return some d
  return none

def split (n : Nat) (cfg : Config := {}) : Option Nat :=
  (splitCertified n cfg).map Subtype.val

theorem split_correct {n d : Nat} {cfg : Config} (h : split n cfg = some d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  unfold split at h
  rcases Option.map_eq_some_iff.mp h with ⟨result, _, heq⟩
  subst d
  exact result.property

theorem factorization_correct (n : Nat) (hn : n ≠ 0) (cfg : Config := {}) :
    IsFactorization n (factorCore (fun n => splitCertified n cfg) n) :=
  factorCore_correct (fun n => splitCertified n cfg) n hn

/-! A small independently inspectable NFS certificate.  The executable above
does not contain these constants: its default search discovers this dependency.
Both factors of `2479 = 37*67` lie outside the default factor base up to 31. -/

theorem example_2479_polynomial_irreducible :
    Irreducible (polynomial ⟨1, 8, 9⟩) :=
  irreducible_of_no_roots_mod ⟨1, 8, 9⟩ 2 Nat.prime_two (by decide)

theorem example_2479_algebraic_root :
    mul ⟨1, 8, 9⟩ ⟨9, 3, 2⟩ ⟨9, 3, 2⟩ =
      product ⟨1, 8, 9⟩ [⟨-9, 1, 0⟩, ⟨-1, 5, 0⟩] := by
  decide

theorem example_2479_rational_root :
    (16 : Int) * 16 =
      ([⟨-9, 1, 0⟩, ⟨-1, 5, 0⟩].map (evaluate 13)).prod := by
  decide

theorem example_2479_congruence :
    (386 : ZMod 2479) ^ 2 = (16 : ZMod 2479) ^ 2 := by
  have hroot : (polynomialEvaluate ⟨1, 8, 9⟩ 13 : ZMod 2479) = 0 := by decide
  have h := square_roots_congruence ⟨1, 8, 9⟩ 13 2479 hroot
    [⟨-9, 1, 0⟩, ⟨-1, 5, 0⟩] ⟨9, 3, 2⟩ 16
    example_2479_algebraic_root example_2479_rational_root
  simpa [evaluate] using h

theorem example_2479_gcd : Nat.gcd (386 - 16) 2479 = 37 := by decide

end PrimeFactorLean.CubicNumberFieldSieve
