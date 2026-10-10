import PrimeFactorLean.Core
import PrimeFactorLean.Arith

/-!
# Congruences of squares from proof-carrying relations

Continued fractions, the quadratic sieves, and (on the rational side) the number
field sieve all collect *relations*

  `x² ≡ ± s² · L · ∏ fb[j]^{e_j}  (mod n)`

over a factor base `fb`, and multiply a subset of them whose exponent vectors
sum to an even vector. This file makes that pipeline proof-carrying:

* `Relation n fb` stores the identity above as a field (a congruence of
  integers, `ModEq`). It is established once, when a relation is created
  (`Relation.mk?` checks it modulo `n`; the expensive sieving and trial
  division that *find* the relation are untrusted).
* `Relation.mul`, `Relation.pair` (large-prime matching) and `Relation.absorb`
  preserve validity by proof.
* `Relation.toSquares` sorts and merges the exponent list, checks that every
  merged exponent is even (the dependency found by linear algebra is untrusted),
  and *proves* `X² ≡ Y² (mod n)`.
* `SquareCongruence.factor` returns `gcd(X - Y, n)` when it is proper;
  `Proofs.Squares` proves that this final step succeeds for every nontrivial
  congruence (`X ≢ ±Y`).

Everything here uses only Lean's core library, so the factoring executable
does not load mathlib.
-/

namespace PrimeFactorLean.Squares

open Arith

/-! ## Signs and sparse exponent products -/

/-- `-1` or `1`. -/
def sgn (neg : Bool) : Int := if neg then -1 else 1

theorem sgn_xor (a b : Bool) : sgn (a != b) = sgn a * sgn b := by
  cases a <;> cases b <;> simp [sgn]

/-- `∏ fb[j]^e` over a sparse list of `(j, e)` pairs (a specification: never
computed at run time). -/
def evalExps (fb : Array Nat) : List (Nat × Nat) → Int
  | [] => 1
  | t :: l => ((fb[t.1]! : Nat) : Int) ^ t.2 * evalExps fb l

@[simp] theorem evalExps_nil (fb : Array Nat) : evalExps fb [] = 1 := rfl

@[simp] theorem evalExps_cons (fb : Array Nat) (t : Nat × Nat) (l : List (Nat × Nat)) :
    evalExps fb (t :: l) = ((fb[t.1]! : Nat) : Int) ^ t.2 * evalExps fb l := rfl

theorem evalExps_append (fb : Array Nat) (a b : List (Nat × Nat)) :
    evalExps fb (a ++ b) = evalExps fb a * evalExps fb b := by
  induction a with
  | nil => simp
  | cons t a ih => simp only [List.cons_append, evalExps_cons, ih]; grind

theorem evalExps_perm (fb : Array Nat) {a b : List (Nat × Nat)}
    (h : a.Perm b) : evalExps fb a = evalExps fb b := by
  induction h with
  | nil => rfl
  | cons t _ ih => simp only [evalExps_cons, ih]
  | swap s t l => simp only [evalExps_cons]; grind
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- The executable counterpart of `evalExps`: the product reduced modulo `n`. -/
def evalExpsAux (n : Nat) (fb : Array Nat) : Nat → List (Nat × Nat) → Nat
  | acc, [] => acc
  | acc, t :: rest => evalExpsAux n fb (acc * powMod fb[t.1]! t.2 n % n) rest

def evalExpsNat (n : Nat) (fb : Array Nat) (exps : List (Nat × Nat)) : Nat :=
  evalExpsAux n fb (1 % n) exps

theorem evalExpsAux_modEq (n : Nat) (fb : Array Nat) (acc : Nat) (l : List (Nat × Nat)) :
    ModEq n (evalExpsAux n fb acc l) ((acc : Int) * evalExps fb l) := by
  induction l generalizing acc with
  | nil => exact ModEq.of_eq (by simp [evalExpsAux])
  | cons t rest ih =>
    simp only [evalExpsAux, evalExps_cons]
    refine (ih _).trans ?_
    have h1 : ModEq n ((acc * powMod fb[t.1]! t.2 n % n : Nat) : Int)
        ((acc : Int) * ((fb[t.1]! : Nat) : Int) ^ t.2) := by
      refine (ModEq.natCast_mod _ n).trans ?_
      rw [Int.natCast_mul]
      refine ModEq.mul (ModEq.refl n _) ?_
      rw [powMod_eq]
      refine (ModEq.natCast_mod _ n).trans (ModEq.of_eq ?_)
      push_cast; rfl
    exact (h1.mul (ModEq.refl n _)).trans (ModEq.of_eq (by grind))

theorem evalExpsNat_modEq (n : Nat) (fb : Array Nat) (l : List (Nat × Nat)) :
    ModEq n (evalExpsNat n fb l) (evalExps fb l) := by
  refine (evalExpsAux_modEq n fb (1 % n) l).trans ?_
  have := (ModEq.natCast_mod 1 n).mul (ModEq.refl n (evalExps fb l))
  exact this.trans (ModEq.of_eq (by simp))

/-! ## Relations -/

/-- The right-hand side `± sq² · large · ∏ fb^e` of a relation. -/
def rhs (fb : Array Nat) (sq large : Nat) (neg : Bool) (exps : List (Nat × Nat)) : Int :=
  sgn neg * (sq : Int) ^ 2 * (large : Int) * evalExps fb exps

/-- A relation `x² ≡ ±sq² · large · ∏ fb[j]^e (mod n)`, with its proof. -/
structure Relation (n : Nat) (fb : Array Nat) where
  x : Nat
  sq : Nat
  large : Nat
  neg : Bool
  exps : List (Nat × Nat)
  valid : ModEq n ((x : Int) ^ 2) (rhs fb sq large neg exps)

instance (n : Nat) (fb : Array Nat) : Inhabited (Relation n fb) :=
  ⟨⟨0, 0, 0, false, [], ModEq.of_eq (by simp [rhs])⟩⟩

/-- The right-hand side `sq² · large · ∏ fb^e`, reduced modulo `n`. -/
def rhsNat (n : Nat) (fb : Array Nat) (sq large : Nat) (exps : List (Nat × Nat)) : Nat :=
  sq * sq % n * (large % n) % n * evalExpsNat n fb exps % n

theorem rhsNat_modEq (n : Nat) (fb : Array Nat) (sq large : Nat) (exps : List (Nat × Nat)) :
    ModEq n (rhsNat n fb sq large exps) ((sq : Int) ^ 2 * (large : Int) * evalExps fb exps) := by
  unfold rhsNat
  refine (ModEq.natCast_mod _ n).trans ?_
  rw [Int.natCast_mul]
  refine ModEq.mul ?_ (evalExpsNat_modEq n fb exps)
  refine (ModEq.natCast_mod _ n).trans ?_
  rw [Int.natCast_mul]
  refine ModEq.mul ((ModEq.natCast_mod _ n).trans (ModEq.of_eq ?_)) (ModEq.natCast_mod _ n)
  push_cast; grind

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
    ModEq n ((x : Int) ^ 2) (rhs fb sq large neg exps) := by
  have hx : ModEq n ((x : Int) ^ 2) ((x * x % n : Nat) : Int) :=
    ((ModEq.natCast_mod (x * x) n).trans (ModEq.of_eq (by push_cast; grind))).symm
  have hr := rhsNat_modEq n fb sq large exps
  unfold relationHolds at h
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    rw [h] at hx
    exact hx.trans (hr.trans (ModEq.of_eq (by simp only [rhs, sgn, Bool.false_eq_true, ↓reduceIte]; grind)))
  | true =>
    simp only [↓reduceIte] at h
    -- `n ∣ x² mod n + rhsNat`, so `x² ≡ -rhsNat`.
    have hd : ModEq n (((x * x % n : Nat) : Int) + (rhsNat n fb sq large exps : Int)) 0 := by
      refine ModEq.zero_of_dvd ?_
      have := Nat.dvd_of_mod_eq_zero h
      exact_mod_cast this
    have hneg : ModEq n ((x * x % n : Nat) : Int) (-(rhsNat n fb sq large exps : Int)) := by
      have := hd.add (ModEq.refl n (-(rhsNat n fb sq large exps : Int)))
      exact (ModEq.of_eq (by grind)).trans (this.trans (ModEq.of_eq (by grind)))
    exact hx.trans (hneg.trans ((hr.neg).trans (ModEq.of_eq (by simp only [rhs, sgn, ↓reduceIte]; grind))))

/-- Create a relation after checking its defining congruence modulo `n`. -/
def Relation.mk? (n : Nat) (fb : Array Nat) (x sq large : Nat) (neg : Bool)
    (exps : List (Nat × Nat)) : Option (Relation n fb) :=
  if h : relationHolds n fb x sq large neg exps then
    some ⟨x, sq, large, neg, exps, relationHolds_valid h⟩
  else none

/-- `((a * b) % n)²` is congruent to `a² b²`. -/
theorem sq_mul_mod (n a b : Nat) :
    ModEq n (((a * b % n : Nat) : Int) ^ 2) ((a : Int) ^ 2 * (b : Int) ^ 2) :=
  ((ModEq.natCast_mod (a * b) n).pow 2).trans (ModEq.of_eq (by push_cast; grind))

/-- The product of two relations is a relation. -/
def Relation.mul {n : Nat} {fb : Array Nat} (r s : Relation n fb) : Relation n fb where
  x := r.x * s.x % n
  sq := r.sq * s.sq % n
  large := r.large * s.large
  neg := r.neg != s.neg
  exps := r.exps ++ s.exps
  valid := by
    have h1 := sq_mul_mod n r.x s.x
    have h2 := r.valid.mul s.valid
    have h3 : ModEq n (rhs fb (r.sq * s.sq % n) (r.large * s.large) (r.neg != s.neg)
        (r.exps ++ s.exps)) (rhs fb r.sq r.large r.neg r.exps * rhs fb s.sq s.large s.neg s.exps) := by
      unfold rhs
      have := (((ModEq.refl n (sgn (r.neg != s.neg))).mul (sq_mul_mod n r.sq s.sq)).mul
        (ModEq.refl n ((r.large * s.large : Nat) : Int))).mul
        (ModEq.refl n (evalExps fb (r.exps ++ s.exps)))
      refine this.trans (ModEq.of_eq ?_)
      rw [sgn_xor, evalExps_append]
      push_cast
      grind
    exact h1.trans (h2.trans h3.symm)

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
    have h1 := sq_mul_mod n r.x s.x
    have h2 := r.valid.mul s.valid
    have h3 : ModEq n (rhs fb (r.sq * s.sq * r.large % n) 1 (r.neg != s.neg) (r.exps ++ s.exps))
        (rhs fb r.sq r.large r.neg r.exps * rhs fb s.sq s.large s.neg s.exps) := by
      unfold rhs
      have := (((ModEq.refl n (sgn (r.neg != s.neg))).mul
        ((ModEq.natCast_mod (r.sq * s.sq * r.large) n).pow 2)).mul
        (ModEq.refl n ((1 : Nat) : Int))).mul (ModEq.refl n (evalExps fb (r.exps ++ s.exps)))
      refine this.trans (ModEq.of_eq ?_)
      rw [sgn_xor, evalExps_append, ← h]
      push_cast
      grind
    exact h1.trans (h2.trans h3.symm)

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
    refine r.valid.trans ?_
    unfold rhs
    have := (((ModEq.refl n (sgn r.neg)).mul ((ModEq.natCast_mod (r.sq * s) n).pow 2)).mul
      (ModEq.refl n ((1 : Nat) : Int))).mul (ModEq.refl n (evalExps fb r.exps))
    refine (this.trans (ModEq.of_eq ?_)).symm
    rw [h]
    push_cast
    grind

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
  valid : ModEq n ((x : Int) ^ 2) ((y : Int) ^ 2)

/-- Merge adjacent entries with the same index into the current run `cur`
(tail recursive: dependency lists reach hundreds of thousands of entries). -/
def mergeRunsAux : Nat × Nat → List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | cur, [], acc => (cur :: acc).reverse
  | cur, a :: rest, acc =>
    if a.1 = cur.1 then mergeRunsAux (cur.1, cur.2 + a.2) rest acc
    else mergeRunsAux a rest (cur :: acc)

/-- Merge adjacent entries with the same index (after sorting, all of them). -/
def mergeRuns : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | a :: rest => mergeRunsAux a rest []

theorem evalExps_mergeRunsAux (fb : Array Nat) (cur : Nat × Nat)
    (l acc : List (Nat × Nat)) :
    evalExps fb (mergeRunsAux cur l acc) =
      evalExps fb acc * ((fb[cur.1]! : Nat) : Int) ^ cur.2 * evalExps fb l := by
  induction l generalizing cur acc with
  | nil =>
    simp only [mergeRunsAux, evalExps_nil, Int.mul_one]
    rw [evalExps_perm fb (List.reverse_perm _), evalExps_cons]
    grind
  | cons a rest ih =>
    simp only [mergeRunsAux]
    split
    · rename_i he
      rw [ih, evalExps_cons, he, Int.pow_add]
      grind
    · rw [ih, evalExps_cons, evalExps_cons]
      grind

theorem evalExps_mergeRuns (fb : Array Nat) (l : List (Nat × Nat)) :
    evalExps fb (mergeRuns l) = evalExps fb l := by
  cases l with
  | nil => rfl
  | cons a rest =>
    rw [mergeRuns, evalExps_mergeRunsAux, evalExps_nil, evalExps_cons, Int.one_mul]

theorem pow_two_mul (a : Int) (k : Nat) : a ^ (2 * k) = (a ^ k) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, Int.pow_succ, Int.pow_succ, ih, Int.pow_succ]
    grind

/-- Halve every exponent. -/
def halfExps (l : List (Nat × Nat)) : List (Nat × Nat) := l.map fun t => (t.1, t.2 / 2)

theorem evalExps_half (fb : Array Nat) (l : List (Nat × Nat))
    (h : ∀ t ∈ l, t.2 % 2 = 0) : evalExps fb l = (evalExps fb (halfExps l)) ^ 2 := by
  induction l with
  | nil => simp [halfExps]
  | cons t rest ih =>
    simp only [halfExps, List.map_cons] at ih ⊢
    rw [evalExps_cons, evalExps_cons, ih (fun u hu => h u (by simp [hu]))]
    have ht : t.2 = 2 * (t.2 / 2) := by have := h t (by simp); omega
    have hp : ((fb[t.1]! : Nat) : Int) ^ t.2 = (((fb[t.1]! : Nat) : Int) ^ (t.2 / 2)) ^ 2 := by
      rw [← pow_two_mul, ← ht]
    rw [hp]
    grind

/-- Sort-merge the exponents of a combined relation and extract `X² ≡ Y²`. The
evenness of every merged exponent and the absence of sign and large prime are
checked; everything else is proved. -/
def Relation.toSquares {n : Nat} {fb : Array Nat} (r : Relation n fb) :
    Option (SquareCongruence n) :=
  let merged := mergeRuns (r.exps.mergeSort (fun a b => a.1 ≤ b.1))
  if h : r.neg = false ∧ r.large = 1 ∧ ∀ t ∈ merged, t.2 % 2 = 0 then
    some ⟨r.x, r.sq * evalExpsNat n fb (halfExps merged) % n, by
      have hv := r.valid
      have hperm : evalExps fb r.exps = evalExps fb merged := by
        rw [evalExps_mergeRuns]
        exact evalExps_perm fb (List.mergeSort_perm _ _).symm
      refine hv.trans ?_
      unfold rhs
      rw [h.1, h.2.1, hperm, evalExps_half fb merged h.2.2]
      have hy := ((ModEq.natCast_mod (r.sq * evalExpsNat n fb (halfExps merged)) n).trans
        ((ModEq.of_eq (Int.natCast_mul _ _)).trans
          ((ModEq.refl n (r.sq : Int)).mul (evalExpsNat_modEq n fb (halfExps merged))))).pow 2
      refine (hy.trans (ModEq.of_eq ?_)).symm
      simp [sgn]
      grind⟩
  else none

/-- The gcd step: `gcd(x - y, n)` divides `n`; return it when it is proper. -/
def SquareCongruence.factor {n : Nat} (c : SquareCongruence n) : Option (ProperFactor n) :=
  checkFactor n (Int.gcd ((c.x : Int) - (c.y : Int)) (n : Int))

theorem SquareCongruence.factor_sound {n : Nat} (c : SquareCongruence n) {d : ProperFactor n}
    (_h : c.factor = some d) : 1 < d.val ∧ d.val < n ∧ d.val ∣ n := d.property

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
