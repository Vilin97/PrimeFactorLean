import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-!
# A total, verified factorization engine

Search routines may be incomplete, randomized, or time limited. A successful
split must carry a checked proof that it is a proper divisor. The engine always
terminates and returns a prime factorization of every positive input; failed
searches fall back to exact trial division through `Nat.minFac`.
-/

namespace PrimeFactorLean

/-- A nontrivial divisor, strictly smaller than its input. -/
abbrev ProperFactor (n : Nat) := {d : Nat // 1 < d ∧ d < n ∧ d ∣ n}

/-- A searcher is allowed to give up; every successful result is certified. -/
abbrev Splitter := (n : Nat) → Option (ProperFactor n)

/-- An optional proof-producing primality test. A failure does not mean composite. -/
abbrev PrimeOracle := (n : Nat) → Option {_u : Unit // Nat.Prime n}

/-- The auditable specification: every output is prime and the product is the input. -/
def IsFactorization (n : Nat) (factors : List Nat) : Prop :=
  (∀ p ∈ factors, Nat.Prime p) ∧ factors.prod = n

/-- Check an arbitrary proposed factor before trusting a search algorithm. -/
def checkFactor (n d : Nat) : Option (ProperFactor n) :=
  if h : 1 < d ∧ d < n ∧ d ∣ n then some ⟨d, h⟩ else none

/-- Turn any fallible raw divisor search into a certified splitter. -/
def checkedSplitter (search : Nat → Option Nat) : Splitter :=
  fun n => (search n).bind (checkFactor n)

@[simp] theorem checkFactor_some {n d : Nat} (h : 1 < d ∧ d < n ∧ d ∣ n) :
    checkFactor n d = some ⟨d, h⟩ := by simp [checkFactor, h]

@[simp] theorem checkFactor_none {n d : Nat} (h : ¬(1 < d ∧ d < n ∧ d ∣ n)) :
    checkFactor n d = none := by simp [checkFactor, h]

private theorem quotient_pos {n d : Nat} (hn : 0 < n) (hd : d ∣ n) :
    0 < n / d := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  exact Nat.div_pos (Nat.le_of_dvd hn hd) hdpos

private theorem quotient_lt {n d : Nat} (hn : 0 < n) (hd : 1 < d) :
    n / d < n := Nat.div_lt_self hn hd

/-- Search before testing primality: fast methods can split large composites
without paying the cost of exhaustive trial division first. -/
def factorCoreWith (oracle : PrimeOracle) (splitter : Splitter) (n : Nat) : List Nat :=
  if _hn : n ≤ 1 then []
  else
    match oracle n with
    | some _ => [n]
    | none =>
      match splitter n with
      | some d => factorCoreWith oracle splitter d.val ++ factorCoreWith oracle splitter (n / d.val)
      | none =>
        let p := n.minFac
        if p = n then [n]
        else p :: factorCoreWith oracle splitter (n / p)
termination_by n
decreasing_by
  · exact d.property.2.1
  · exact quotient_lt (by omega) d.property.1
  · exact quotient_lt (by omega) (Nat.minFac_prime (by omega)).one_lt

/-- Universal soundness and completeness of the engine, regardless of the
behavior of the search algorithm. No probabilistic or heuristic assumption is
needed for correctness. -/
theorem factorCoreWith_correct (oracle : PrimeOracle) (splitter : Splitter) (n : Nat)
    (hn : n ≠ 0) : IsFactorization n (factorCoreWith oracle splitter n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold factorCoreWith
    split_ifs with hsmall
    · have : n = 1 := by omega
      subst n
      simp [IsFactorization]
    · cases ho : oracle n with
      | some primeProof =>
        constructor
        · intro p hp
          have : p = n := by simpa using hp
          subst p
          exact primeProof.property
        · simp
      | none =>
        cases hs : splitter n with
        | some d =>
          have hd := d.property
          have hqpos := quotient_pos (by omega : 0 < n) hd.2.2
          have hf := ih d.val hd.2.1 (by omega)
          have hq := ih (n / d.val) (quotient_lt (by omega) hd.1) (by omega)
          constructor
          · intro p hp
            rcases List.mem_append.mp hp with hp | hp
            · exact hf.1 p hp
            · exact hq.1 p hp
          · rw [List.prod_append, hf.2, hq.2]
            exact Nat.mul_div_cancel' hd.2.2
        | none =>
          dsimp only
          split_ifs with hp
          · constructor
            · intro p hmem
              have heq : p = n := by simpa using hmem
              subst p
              exact hp ▸ Nat.minFac_prime (by omega)
            · simp
          · have hprime : Nat.Prime n.minFac := Nat.minFac_prime (by omega)
            have hqpos := quotient_pos (by omega : 0 < n) (Nat.minFac_dvd n)
            have hq := ih (n / n.minFac) (quotient_lt (by omega) hprime.one_lt) (by omega)
            constructor
            · intro p hmem
              rcases List.mem_cons.mp hmem with rfl | hmem
              · exact hprime
              · exact hq.1 p hmem
            · rw [List.prod_cons, hq.2]
              exact Nat.mul_div_cancel' (Nat.minFac_dvd n)

/-- The basic engine uses exact trial division when no divisor search succeeds. -/
abbrev factorCore (splitter : Splitter) (n : Nat) : List Nat :=
  factorCoreWith (fun _ => none) splitter n

theorem factorCore_correct (splitter : Splitter) (n : Nat) (hn : n ≠ 0) :
    IsFactorization n (factorCore splitter n) :=
  factorCoreWith_correct (fun _ => none) splitter n hn

/-- Zero has no finite factorization into primes; represent this explicitly. -/
def factorNat (splitter : Splitter) (n : Nat) : Option (List Nat) :=
  if n = 0 then none else some (factorCore splitter n)

@[simp] theorem factorNat_zero (splitter : Splitter) : factorNat splitter 0 = none := by
  simp [factorNat]

theorem factorNat_correct {splitter : Splitter} {n : Nat} {factors : List Nat}
    (h : factorNat splitter n = some factors) : IsFactorization n factors := by
  unfold factorNat at h
  split_ifs at h with hn
  have heq := Option.some.inj h
  subst factors
  exact factorCore_correct splitter n hn

/-- Signed integer factorization. The sign is a unit; factors are positive primes. -/
def factorInt (splitter : Splitter) (z : Int) : Option (Int × List Nat) :=
  (factorNat splitter z.natAbs).map fun factors => (z.sign, factors)

def IsIntFactorization (z sign : Int) (factors : List Nat) : Prop :=
  (sign = 1 ∨ sign = -1) ∧ (∀ p ∈ factors, Nat.Prime p) ∧
    sign * (factors.prod : Int) = z

theorem factorInt_correct {splitter : Splitter} {z sign : Int} {factors : List Nat}
    (h : factorInt splitter z = some (sign, factors)) :
    IsIntFactorization z sign factors := by
  unfold factorInt factorNat at h
  split_ifs at h with hz
  · simp at h
  · have heq : (z.sign, factorCore splitter z.natAbs) = (sign, factors) :=
      Option.some.inj h
    cases heq
    have hf := factorCore_correct splitter z.natAbs hz
    have hz' : z ≠ 0 := Int.natAbs_ne_zero.mp hz
    refine ⟨?_, hf.1, ?_⟩
    · by_cases hpos : 0 < z
      · exact Or.inl (Int.sign_eq_one_of_pos hpos)
      · exact Or.inr (Int.sign_eq_neg_one_of_neg (by omega))
    · rw [hf.2]
      exact Int.sign_mul_natAbs z

end PrimeFactorLean
