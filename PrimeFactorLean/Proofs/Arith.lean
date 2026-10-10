import PrimeFactorLean.Proofs.Trial
import PrimeFactorLean.Arith

/-! # Verified small primality (proof layer) -/

namespace PrimeFactorLean.Arith

theorem smallPrime_sound {n : Nat} (h : smallPrime n = true) : n.Prime := by
  unfold smallPrime at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
  exact trialWheelSearch_none_prime h.1 h.2

end PrimeFactorLean.Arith
