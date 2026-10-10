import PrimeFactorLean.Proofs.Core
import PrimeFactorLean.Trial

/-!
# Correctness of trial division

Unsuccessful square-root searches certify primality (the classical small-divisor
theorem), so `trialCore` and `trialWheelCore` are total and exact.
-/

namespace PrimeFactorLean

/-- Finding no divisor through sqrt(n) proves that n is prime. -/
theorem trialSearch_none_prime {n : Nat} (hn : 2 ≤ n)
    (h : trialSearch n = none) : Nat.Prime n := by
  apply Nat.prime_def_le_sqrt.mpr
  refine ⟨hn, ?_⟩
  unfold trialSearch at h
  rw [isqrt_eq_sqrt] at h
  have hnone := (trialSearchAux_none_iff n 2 (Nat.sqrt n - 1)).mp h
  intro p hp hpsqrt hdvd
  exact hnone p hp (by omega)
    ⟨by omega, lt_of_le_of_lt hpsqrt (Nat.sqrt_lt_self hn), hdvd⟩


theorem trialCore_correct (n : Nat) (hn : n ≠ 0) : IsFactorization n (trialCore n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold trialCore
    split_ifs with hsmall
    · have : n = 1 := by omega
      subst n
      simp [IsFactorization]
    · split
      · rename_i hs
        constructor
        · intro p hp
          have heq : p = n := by simpa using hp
          subst p
          exact trialSearch_none_prime (by omega) hs
        · simp
      · rename_i d hs
        have hd := trialSearch_sound hs
        have hdpos : 0 < d := by omega
        have hqpos := Nat.div_pos (Nat.le_of_dvd (by omega) hd.2.2) hdpos
        have hf := ih d hd.2.1 (by omega)
        have hq := ih (n / d) (Nat.div_lt_self (by omega) hd.1) (by omega)
        constructor
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hf.1 p hp
          · exact hq.1 p hp
        · rw [List.prod_append, hf.2, hq.2]
          exact Nat.mul_div_cancel' hd.2.2


theorem trialFactorReference_correct {n : Nat} {factors : List Nat}
    (h : trialFactorReference n = some factors) : IsFactorization n factors :=
  factorNat_correct h

theorem trialFactor_correct {n : Nat} {factors : List Nat}
    (h : trialFactor n = some factors) : IsFactorization n factors := by
  unfold trialFactor at h
  split_ifs at h with hn
  have heq := Option.some.inj h
  subst factors
  exact trialCore_correct n hn


/-- Completeness of the wheel optimization, including primality of its leaves. -/
theorem trialWheelSearch_none_prime {n : Nat} (hn : 2 ≤ n)
    (h : trialWheelSearch n = none) : Nat.Prime n := by
  by_cases hsmall : n ≤ 3
  · have hcases : n = 2 ∨ n = 3 := by omega
    rcases hcases with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  have hn4 : 4 ≤ n := by omega
  have h2 : ¬2 ∣ n := by
    intro hd
    have hp : 1 < 2 ∧ 2 < n ∧ 2 ∣ n := ⟨by omega, by omega, hd⟩
    simp [trialWheelSearch, hp] at h
  have h3 : ¬3 ∣ n := by
    intro hd
    have hp : 1 < 3 ∧ 3 < n ∧ 3 ∣ n := ⟨by omega, by omega, hd⟩
    simp [trialWheelSearch, h2, hp] at h
  have h2' : ¬(1 < 2 ∧ 2 < n ∧ 2 ∣ n) := fun hp => h2 hp.2.2
  have h3' : ¬(1 < 3 ∧ 3 < n ∧ 3 ∣ n) := fun hp => h3 hp.2.2
  rw [trialWheelSearch, if_neg h2', if_neg h3', isqrt_eq_sqrt] at h
  have hnone := (trialWheelAux_none_iff n 5 (Nat.sqrt n / 6 + 1)).mp h
  apply Nat.prime_def_le_sqrt.mpr
  refine ⟨hn, ?_⟩
  intro p hp hpsqrt hdvd
  have hp2 : ¬2 ∣ p := fun hdiv => h2 (dvd_trans hdiv hdvd)
  have hp3 : ¬3 ∣ p := fun hdiv => h3 (dvd_trans hdiv hdvd)
  rw [Nat.dvd_iff_mod_eq_zero] at hp2 hp3
  have hmod : p % 6 = 1 ∨ p % 6 = 5 := by omega
  have hproper : 1 < p ∧ p < n ∧ p ∣ n :=
    ⟨by omega, lt_of_le_of_lt hpsqrt (Nat.sqrt_lt_self hn), hdvd⟩
  rcases hmod with hmod | hmod
  · have heq : p = 5 + 6 * (p / 6 - 1) + 2 := by omega
    have hi : p / 6 - 1 < Nat.sqrt n / 6 + 1 := by omega
    apply (hnone (p / 6 - 1) hi).2
    simpa only [← heq] using hproper
  · have heq : p = 5 + 6 * (p / 6) := by omega
    have hi : p / 6 < Nat.sqrt n / 6 + 1 := by omega
    apply (hnone (p / 6) hi).1
    simpa only [← heq] using hproper


theorem trialWheelCore_correct (n : Nat) (hn : n ≠ 0) :
    IsFactorization n (trialWheelCore n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold trialWheelCore
    split_ifs with hsmall
    · have : n = 1 := by omega
      subst n
      simp [IsFactorization]
    · split
      · rename_i hs
        constructor
        · intro p hp
          have heq : p = n := by simpa using hp
          subst p
          exact trialWheelSearch_none_prime (by omega) hs
        · simp
      · rename_i d hs
        have hd := trialWheelSearch_sound hs
        have hdpos : 0 < d := by omega
        have hqpos := Nat.div_pos (Nat.le_of_dvd (by omega) hd.2.2) hdpos
        have hf := ih d hd.2.1 (by omega)
        have hq := ih (n / d) (Nat.div_lt_self (by omega) hd.1) (by omega)
        constructor
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hf.1 p hp
          · exact hq.1 p hp
        · rw [List.prod_append, hf.2, hq.2]
          exact Nat.mul_div_cancel' hd.2.2


theorem trialWheelFactor_correct {n : Nat} {factors : List Nat}
    (h : trialWheelFactor n = some factors) : IsFactorization n factors := by
  unfold trialWheelFactor at h
  split_ifs at h with hn
  have heq := Option.some.inj h
  subst factors
  exact trialWheelCore_correct n hn

end PrimeFactorLean
