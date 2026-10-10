import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.SplitIfs
import PrimeFactorLean.Core

/-!
# Correctness of the factorization engine

The runtime engine `factorCoreWith` (in `PrimeFactorLean.Core`, which imports
only Lean's core library) is proved correct here against mathlib's `Nat.Prime`:
for every Boolean prime checker that is *sound* (accepts only primes), and every
splitter, the output is a prime factorization of the input.
-/

namespace PrimeFactorLean

/-- The auditable specification: every output is prime and the product is the input. -/
def IsFactorization (n : Nat) (factors : List Nat) : Prop :=
  (∀ p ∈ factors, Nat.Prime p) ∧ factors.prod = n

def IsIntFactorization (z sign : Int) (factors : List Nat) : Prop :=
  (sign = 1 ∨ sign = -1) ∧ (∀ p ∈ factors, Nat.Prime p) ∧
    sign * (factors.prod : Int) = z

/-- The trial-division search finds the least divisor `≥ d`, which is prime, or
proves `n` prime once `d² > n`. -/
theorem minFacAux_prime {n : Nat} (hn : 2 ≤ n) : ∀ fuel d, 2 ≤ d →
    (∀ m, 2 ≤ m → m < d → ¬ m ∣ n) → n < d + fuel → Nat.Prime (minFacAux n d fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro d _ hsmall hfuel
    exact absurd (Nat.dvd_refl n) (hsmall n hn (by omega))
  | succ fuel ih =>
    intro d hd hsmall hfuel
    simp only [minFacAux]
    split_ifs with hsq hdiv
    · -- every divisor of `n` below `n` would be `< d` or have a cofactor `< d`
      refine Nat.prime_def_lt'.mpr ⟨hn, fun m hm hmn hdvd => ?_⟩
      by_cases hmd : m < d
      · exact hsmall m hm hmd hdvd
      · obtain ⟨k, hk⟩ := hdvd
        have hk2 : 2 ≤ k := by
          rcases Nat.lt_or_ge k 2 with hk' | hk'
          · have : k = 0 ∨ k = 1 := by omega
            rcases this with rfl | rfl <;> simp at hk <;> omega
          · exact hk'
        have hkd : k < d := by
          by_contra hkd
          have : d * d ≤ m * k := Nat.mul_le_mul (by omega) (by omega)
          omega
        exact hsmall k hk2 hkd ⟨m, by rw [hk, Nat.mul_comm]⟩
    · refine Nat.prime_def_lt'.mpr ⟨hd, fun m hm hmd hdvd => ?_⟩
      exact hsmall m hm hmd (Nat.dvd_trans hdvd (Nat.dvd_of_mod_eq_zero hdiv))
    · apply ih (d + 1) (by omega) _ (by omega)
      intro m hm hmd
      by_cases hmeq : m = d
      · subst hmeq
        intro h
        exact hdiv (Nat.mod_eq_zero_of_dvd h)
      · exact hsmall m hm (by omega)

theorem minFac_prime {n : Nat} (hn : 2 ≤ n) : Nat.Prime (minFac n) := by
  unfold minFac
  rw [if_neg (by omega)]
  exact minFacAux_prime hn n 2 (Nat.le_refl 2) (fun m hm hlt => absurd hlt (by omega)) (by omega)

private theorem quotient_pos {n d : Nat} (hn : 0 < n) (hd : d ∣ n) :
    0 < n / d := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  exact Nat.div_pos (Nat.le_of_dvd hn hd) hdpos

private theorem quotient_lt' {n d : Nat} (hn : 0 < n) (hd : 1 < d) :
    n / d < n := Nat.div_lt_self hn hd

/-- Universal soundness and completeness of the engine, regardless of the
behavior of the search algorithm: only the prime checker must be sound. No
probabilistic or heuristic assumption is needed for correctness. -/
theorem factorCoreWith_correct (isPrime : Nat → Bool)
    (hPrime : ∀ m, isPrime m = true → Nat.Prime m) (splitter : Splitter) (n : Nat)
    (hn : n ≠ 0) : IsFactorization n (factorCoreWith isPrime splitter n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold factorCoreWith
    split_ifs with hsmall hp
    · have : n = 1 := by omega
      subst n
      simp [IsFactorization]
    · constructor
      · intro p hmem
        have : p = n := by simpa using hmem
        subst p
        exact hPrime n hp
      · simp
    · cases hs : splitter n with
      | some d =>
        have hd := d.property
        have hqpos := quotient_pos (by omega : 0 < n) hd.2.2
        have hf := ih d.val hd.2.1 (by omega)
        have hq := ih (n / d.val) (quotient_lt' (by omega) hd.1) (by omega)
        constructor
        · intro p hmem
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact hf.1 p hmem
          · exact hq.1 p hmem
        · rw [List.prod_append, hf.2, hq.2]
          exact Nat.mul_div_cancel' hd.2.2
      | none =>
        dsimp only
        have hprime : Nat.Prime (minFac n) := minFac_prime (by omega)
        split_ifs with hpn
        · constructor
          · intro p hmem
            have heq : p = n := by simpa using hmem
            subst p
            exact hpn ▸ hprime
          · simp
        · have hdvd := (minFac_spec (n := n) (by omega)).2
          have hqpos := quotient_pos (by omega : 0 < n) hdvd
          have hq := ih (n / minFac n) (quotient_lt' (by omega) hprime.one_lt) (by omega)
          constructor
          · intro p hmem
            rcases List.mem_cons.mp hmem with rfl | hmem
            · exact hprime
            · exact hq.1 p hmem
          · rw [List.prod_cons, hq.2]
            exact Nat.mul_div_cancel' hdvd

theorem factorCore_correct (splitter : Splitter) (n : Nat) (hn : n ≠ 0) :
    IsFactorization n (factorCore splitter n) :=
  factorCoreWith_correct (fun _ => false) (by simp) splitter n hn

theorem factorNat_correct {splitter : Splitter} {n : Nat} {factors : List Nat}
    (h : factorNat splitter n = some factors) : IsFactorization n factors := by
  unfold factorNat at h
  split_ifs at h with hn
  have heq := Option.some.inj h
  subst factors
  exact factorCore_correct splitter n hn

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

/-- The integer square root agrees with mathlib's `Nat.sqrt`. -/
theorem isqrt_eq_sqrt (n : Nat) : isqrt n = Nat.sqrt n := by
  have h := isqrt_spec n
  apply le_antisymm
  · exact Nat.le_sqrt.mpr h.1
  · exact Nat.lt_succ_iff.mp (Nat.sqrt_lt.mpr h.2)

end PrimeFactorLean
