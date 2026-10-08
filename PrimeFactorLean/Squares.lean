import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Coprime.Lemmas
import PrimeFactorLean.Core
import PrimeFactorLean.Arith

/-!
# Congruences of squares from proof-carrying relations

Continued fractions, the quadratic sieves, and (on the rational side) the number
field sieve all collect *relations*

  `x² ≡ ± s² · L · ∏ fb[j]^{e_j}  (mod n)`

over a factor base `fb`, and multiply a subset of them whose exponent vectors
sum to an even vector. This file makes that pipeline proof-carrying:

* `Relation n fb` stores the identity above as a field. It is established once,
  when a relation is created (`Relation.mk?` checks it modulo `n`; the expensive
  sieving and trial division that *find* the relation are untrusted).
* `Relation.mul` and `Relation.pair` (large-prime matching) preserve validity by
  proof.
* `Relation.toSquares` sorts and merges the exponent list, checks that every
  merged exponent is even (the dependency found by linear algebra is untrusted),
  and *proves* `X² ≡ Y² (mod n)`.
* `SquareCongruence.factor` returns `gcd(X - Y, n)` when it is proper, and
  `factor_isSome` proves that this final step succeeds for every nontrivial
  congruence (`X ≢ ±Y`).
-/

namespace PrimeFactorLean.Squares

open Arith

/-! ## Signs and sparse exponent products -/

/-- `-1` or `1` in `ZMod n`. -/
def sgn (n : Nat) (neg : Bool) : ZMod n := if neg then -1 else 1

theorem sgn_xor (n : Nat) (a b : Bool) : sgn n (a != b) = sgn n a * sgn n b := by
  cases a <;> cases b <;> simp [sgn]

/-- `∏ fb[j]^e` over a sparse list of `(j, e)` pairs, in `ZMod n`. -/
def evalExps (n : Nat) (fb : Array Nat) (exps : List (Nat × Nat)) : ZMod n :=
  (exps.map fun t => ((fb[t.1]! : Nat) : ZMod n) ^ t.2).prod

@[simp] theorem evalExps_nil (n : Nat) (fb : Array Nat) : evalExps n fb [] = 1 := rfl

@[simp] theorem evalExps_cons (n : Nat) (fb : Array Nat) (t : Nat × Nat)
    (l : List (Nat × Nat)) :
    evalExps n fb (t :: l) = ((fb[t.1]! : Nat) : ZMod n) ^ t.2 * evalExps n fb l := by
  simp [evalExps]

theorem evalExps_append (n : Nat) (fb : Array Nat) (a b : List (Nat × Nat)) :
    evalExps n fb (a ++ b) = evalExps n fb a * evalExps n fb b := by
  simp [evalExps, List.map_append, List.prod_append]

theorem evalExps_perm (n : Nat) (fb : Array Nat) {a b : List (Nat × Nat)}
    (h : a.Perm b) : evalExps n fb a = evalExps n fb b :=
  (h.map _).prod_eq

/-- The executable counterpart of `evalExps`: the product reduced modulo `n`. -/
def evalExpsAux (n : Nat) (fb : Array Nat) : Nat → List (Nat × Nat) → Nat
  | acc, [] => acc
  | acc, t :: rest => evalExpsAux n fb (acc * powMod fb[t.1]! t.2 n % n) rest

def evalExpsNat (n : Nat) (fb : Array Nat) (exps : List (Nat × Nat)) : Nat :=
  evalExpsAux n fb (1 % n) exps

theorem evalExpsAux_cast (n : Nat) (fb : Array Nat) (acc : Nat) (l : List (Nat × Nat)) :
    (evalExpsAux n fb acc l : ZMod n) = (acc : ZMod n) * evalExps n fb l := by
  induction l generalizing acc with
  | nil => simp [evalExpsAux]
  | cons t rest ih =>
    simp only [evalExpsAux, ih, evalExps_cons, powMod_eq, ZMod.natCast_mod, Nat.cast_mul,
      Nat.cast_pow]
    ring

theorem evalExpsNat_cast (n : Nat) (fb : Array Nat) (l : List (Nat × Nat)) :
    (evalExpsNat n fb l : ZMod n) = evalExps n fb l := by
  simp [evalExpsNat, evalExpsAux_cast, ZMod.natCast_mod]

/-! ## Relations -/

/-- A relation `x² ≡ ±sq² · large · ∏ fb[j]^e (mod n)`, with its proof. -/
structure Relation (n : Nat) (fb : Array Nat) where
  x : Nat
  sq : Nat
  large : Nat
  neg : Bool
  exps : List (Nat × Nat)
  valid : (x : ZMod n) ^ 2 =
    sgn n neg * (sq : ZMod n) ^ 2 * (large : ZMod n) * evalExps n fb exps

instance (n : Nat) (fb : Array Nat) : Inhabited (Relation n fb) :=
  ⟨⟨0, 0, 0, false, [], by simp⟩⟩

/-- The right-hand side `sq² · large · ∏ fb^e`, reduced modulo `n`. -/
def rhsNat (n : Nat) (fb : Array Nat) (sq large : Nat) (exps : List (Nat × Nat)) : Nat :=
  sq * sq % n * (large % n) % n * evalExpsNat n fb exps % n

theorem rhsNat_cast (n : Nat) (fb : Array Nat) (sq large : Nat) (exps : List (Nat × Nat)) :
    (rhsNat n fb sq large exps : ZMod n) =
      (sq : ZMod n) ^ 2 * (large : ZMod n) * evalExps n fb exps := by
  simp only [rhsNat, ZMod.natCast_mod, Nat.cast_mul, evalExpsNat_cast]
  ring

/-- The defining check of a relation, computed with natural numbers modulo `n`. -/
def relationHolds (n : Nat) (fb : Array Nat) (x sq large : Nat) (neg : Bool)
    (exps : List (Nat × Nat)) : Prop :=
  if neg then (x * x % n + rhsNat n fb sq large exps) % n = 0
  else x * x % n = rhsNat n fb sq large exps

instance (n : Nat) (fb : Array Nat) (x sq large : Nat) (neg : Bool)
    (exps : List (Nat × Nat)) : Decidable (relationHolds n fb x sq large neg exps) := by
  unfold relationHolds; split <;> infer_instance

theorem relationHolds_valid {n : Nat} {fb : Array Nat} {x sq large : Nat} {neg : Bool}
    {exps : List (Nat × Nat)} (h : relationHolds n fb x sq large neg exps) :
    (x : ZMod n) ^ 2 =
      sgn n neg * (sq : ZMod n) ^ 2 * (large : ZMod n) * evalExps n fb exps := by
  unfold relationHolds at h
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    have hc := congrArg (fun t : Nat => (t : ZMod n)) h
    simp only [ZMod.natCast_mod, Nat.cast_mul, rhsNat_cast] at hc
    rw [sgn, if_neg (by simp)]
    linear_combination hc
  | true =>
    simp only [↓reduceIte] at h
    have hc := congrArg (fun t : Nat => (t : ZMod n)) h
    simp only [ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, rhsNat_cast,
      Nat.cast_zero] at hc
    rw [sgn, if_pos rfl]
    linear_combination hc

/-- Create a relation after checking its defining congruence modulo `n`. -/
def Relation.mk? (n : Nat) (fb : Array Nat) (x sq large : Nat) (neg : Bool)
    (exps : List (Nat × Nat)) : Option (Relation n fb) :=
  if h : relationHolds n fb x sq large neg exps then
    some ⟨x, sq, large, neg, exps, relationHolds_valid h⟩
  else none

/-- The product of two relations is a relation. -/
def Relation.mul {n : Nat} {fb : Array Nat} (r s : Relation n fb) : Relation n fb where
  x := r.x * s.x % n
  sq := r.sq * s.sq % n
  large := r.large * s.large
  neg := r.neg != s.neg
  exps := r.exps ++ s.exps
  valid := by
    simp only [ZMod.natCast_mod, Nat.cast_mul, sgn_xor, evalExps_append]
    rw [mul_pow, r.valid, s.valid]
    ring

/-- Two partial relations with the same large prime `L` combine into a full
relation whose square part absorbs `L`. -/
def Relation.pair {n : Nat} {fb : Array Nat} (r s : Relation n fb)
    (h : r.large = s.large) : Relation n fb where
  x := r.x * s.x % n
  sq := r.sq * s.sq * r.large % n
  large := 1
  neg := r.neg != s.neg
  exps := r.exps ++ s.exps
  valid := by
    simp only [ZMod.natCast_mod, Nat.cast_mul, sgn_xor, evalExps_append, Nat.cast_one]
    rw [mul_pow, r.valid, s.valid, ← h]
    ring

/-- A relation whose large-prime part is a perfect square `s²` (e.g. the product
of the relations along a cycle of the large-prime graph) becomes a full relation. -/
def Relation.absorb {n : Nat} {fb : Array Nat} (r : Relation n fb) (s : Nat)
    (h : r.large = s * s) : Relation n fb where
  x := r.x
  sq := r.sq * s % n
  large := 1
  neg := r.neg
  exps := r.exps
  valid := by
    rw [r.valid, h]
    simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_one]
    ring

/-- Multiply a nonempty list of relations. -/
def Relation.prod {n : Nat} {fb : Array Nat} (r : Relation n fb) :
    List (Relation n fb) → Relation n fb
  | [] => r
  | s :: rest => (r.mul s).prod rest

/-! ## Congruences of squares -/

/-- A proved congruence `x² ≡ y² (mod n)`. -/
structure SquareCongruence (n : Nat) where
  x : Nat
  y : Nat
  valid : (x : ZMod n) ^ 2 = (y : ZMod n) ^ 2

/-- Merge adjacent entries with the same index (after sorting, all of them). -/
def mergeRuns : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | a :: rest =>
    match mergeRuns rest with
    | b :: tail => if a.1 = b.1 then (a.1, a.2 + b.2) :: tail else a :: b :: tail
    | [] => [a]

theorem evalExps_mergeRuns (n : Nat) (fb : Array Nat) (l : List (Nat × Nat)) :
    evalExps n fb (mergeRuns l) = evalExps n fb l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    rw [evalExps_cons, ← ih]
    simp only [mergeRuns]
    split
    · rename_i b tail hm
      rw [hm]
      split_ifs with he
      · simp only [evalExps_cons]
        rw [he, pow_add]
        ring
      · simp
    · rename_i hm
      rw [hm]
      simp

/-- Halve every exponent. -/
def halfExps (l : List (Nat × Nat)) : List (Nat × Nat) := l.map fun t => (t.1, t.2 / 2)

theorem evalExps_half (n : Nat) (fb : Array Nat) (l : List (Nat × Nat))
    (h : ∀ t ∈ l, t.2 % 2 = 0) : evalExps n fb l = (evalExps n fb (halfExps l)) ^ 2 := by
  induction l with
  | nil => simp [halfExps]
  | cons t rest ih =>
    simp only [halfExps, List.map_cons] at ih ⊢
    rw [evalExps_cons, evalExps_cons, ih (fun u hu => h u (by simp [hu]))]
    have ht : t.2 = t.2 / 2 * 2 := by have := h t (by simp); omega
    conv_lhs => rw [ht, pow_mul]
    ring

/-- Sort-merge the exponents of a combined relation and extract `X² ≡ Y²`. The
evenness of every merged exponent and the absence of sign and large prime are
checked; everything else is proved. -/
def Relation.toSquares {n : Nat} {fb : Array Nat} (r : Relation n fb) :
    Option (SquareCongruence n) :=
  let merged := mergeRuns (r.exps.mergeSort (fun a b => a.1 ≤ b.1))
  if h : r.neg = false ∧ r.large = 1 ∧ ∀ t ∈ merged, t.2 % 2 = 0 then
    some ⟨r.x, r.sq * evalExpsNat n fb (halfExps merged) % n, by
      have hv := r.valid
      rw [h.1, h.2.1] at hv
      have hperm : evalExps n fb r.exps = evalExps n fb merged := by
        rw [evalExps_mergeRuns]
        exact evalExps_perm n fb (List.mergeSort_perm _ _).symm
      rw [hv, hperm, evalExps_half n fb merged h.2.2]
      simp only [sgn, Bool.false_eq_true, ↓reduceIte, Nat.cast_one, ZMod.natCast_mod,
        Nat.cast_mul, evalExpsNat_cast]
      ring⟩
  else none

/-- The gcd step: `gcd(x - y, n)` divides `n`; return it when it is proper. -/
def SquareCongruence.factor {n : Nat} (c : SquareCongruence n) : Option (ProperFactor n) :=
  checkFactor n (Int.gcd ((c.x : Int) - (c.y : Int)) (n : Int))

theorem SquareCongruence.factor_sound {n : Nat} (c : SquareCongruence n) {d : ProperFactor n}
    (_h : c.factor = some d) : 1 < d.val ∧ d.val < n ∧ d.val ∣ n := d.property

/-- **Completeness of the gcd step.** A nontrivial congruence of squares
(`x ≢ ±y`) always yields a proper factor. -/
theorem SquareCongruence.factor_isSome {n : Nat} (hn : 1 < n) (c : SquareCongruence n)
    (h1 : (c.x : ZMod n) ≠ (c.y : ZMod n)) (h2 : (c.x : ZMod n) ≠ -(c.y : ZMod n)) :
    c.factor.isSome := by
  set d := Int.gcd ((c.x : Int) - (c.y : Int)) (n : Int) with hd
  have hprod : (n : Int) ∣ ((c.x : Int) - c.y) * ((c.x : Int) + c.y) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    linear_combination c.valid
  have hdn : d ∣ n := by
    have := Int.gcd_dvd_right ((c.x : Int) - (c.y : Int)) (n : Int)
    exact Int.natCast_dvd_natCast.mp (by simpa using this)
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn (by omega)
  have hd1 : d ≠ 1 := by
    intro hd1
    apply h2
    have hco : IsCoprime ((c.x : Int) - c.y) (n : Int) := Int.isCoprime_iff_gcd_eq_one.mpr hd1
    have hdiv : (n : Int) ∣ (c.x : Int) + c.y := hco.symm.dvd_of_dvd_mul_left hprod
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr hdiv
    push_cast at this
    linear_combination this
  have hdn' : d ≠ n := by
    intro hdeq
    apply h1
    have hdiv : (n : Int) ∣ (c.x : Int) - c.y := by
      have := Int.gcd_dvd_left ((c.x : Int) - (c.y : Int)) (n : Int)
      rw [← hd, hdeq] at this
      exact this
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mpr hdiv
    push_cast at this
    linear_combination this
  have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdn
  unfold SquareCongruence.factor
  rw [← hd, checkFactor_some ⟨by omega, by omega, hdn⟩]
  rfl

/-! ## Parity vectors for the (untrusted) linear algebra -/

/-- Columns with odd total exponent: column `0` is the sign, column `j + 1` is
`fb[j]`. Large-prime relations should be paired before entering the matrix. -/
def parityColumns {n : Nat} {fb : Array Nat} (r : Relation n fb) : Array Nat := Id.run do
  let merged := mergeRuns (r.exps.mergeSort (fun a b => a.1 ≤ b.1))
  let mut cols : Array Nat := if r.neg then #[0] else #[]
  for t in merged do
    if t.2 % 2 == 1 then cols := cols.push (t.1 + 1)
  return cols

end PrimeFactorLean.Squares
