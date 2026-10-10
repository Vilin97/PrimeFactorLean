import PrimeFactorLean.Proofs.Core
import PrimeFactorLean.Proofs.Trial
import PrimeFactorLean.Proofs.Pocklington
import PrimeFactorLean.Algorithms

/-! Proof layer: see the runtime module for documentation. -/

namespace PrimeFactorLean

/-- The same universal theorem covers each named executable implementation. -/
theorem factor_correct (algorithm : Algorithm) (n : Nat) (cfg : Config)
    (factors : List Nat) (h : factor algorithm n cfg = some factors) :
    IsFactorization n factors := by
  unfold factor at h
  split at h
  · contradiction
  · rename_i hn
    cases algorithm <;> simp only [Option.some.injEq] at h
    all_goals subst factors
    · exact factorCore_correct trialSplitterReference n hn
    · exact trialCore_correct n hn
    · exact trialWheelCore_correct n hn
    all_goals exact factorCoreWith_correct _ (fun _ h => Pocklington.oracle_sound h) _ n hn

/-- Every positive input finishes with a complete prime factorization. -/
theorem factor_total_correct (algorithm : Algorithm) (n : Nat) (cfg : Config)
    (hn : n ≠ 0) :
    ∃ ps, factor algorithm n cfg = some ps ∧ IsFactorization n ps := by
  cases hf : factor algorithm n cfg with
  | none => cases algorithm <;> simp [factor, hn] at hf
  | some ps => exact ⟨ps, rfl, factor_correct algorithm n cfg ps hf⟩

@[simp] theorem factor_zero (algorithm : Algorithm) (cfg : Config) :
    factor algorithm 0 cfg = none := by simp [factor]

/-- Signed factorization with the same verified natural-number implementation. -/
def factorSigned (algorithm : Algorithm) (z : Int) (cfg : Config := {}) :
    Option (Int × List Nat) :=
  (factor algorithm z.natAbs cfg).map fun ps => (z.sign, ps)

theorem factorSigned_correct (algorithm : Algorithm) (z : Int) (cfg : Config)
    (sign : Int) (ps : List Nat)
    (h : factorSigned algorithm z cfg = some (sign, ps)) :
    IsIntFactorization z sign ps := by
  unfold factorSigned at h
  cases hf : factor algorithm z.natAbs cfg with
  | none => simp [hf] at h
  | some fs =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    have hc := factor_correct algorithm z.natAbs cfg fs hf
    cases h
    have hz : z ≠ 0 := by
      intro hz
      subst z
      simp [factor] at hf
    refine ⟨?_, hc.1, ?_⟩
    · by_cases hpos : 0 < z
      · exact Or.inl (Int.sign_eq_one_of_pos hpos)
      · exact Or.inr (Int.sign_eq_neg_one_of_neg (by omega))
    · rw [hc.2]
      exact Int.sign_mul_natAbs z

theorem factorSigned_total_correct (algorithm : Algorithm) (z : Int)
    (cfg : Config) (hz : z ≠ 0) :
    ∃ sign ps, factorSigned algorithm z cfg = some (sign, ps) ∧
      IsIntFactorization z sign ps := by
  obtain ⟨ps, hf, _⟩ := factor_total_correct algorithm z.natAbs cfg
    (Int.natAbs_ne_zero.mpr hz)
  have hi : factorSigned algorithm z cfg = some (z.sign, ps) := by
    simp [factorSigned, hf]
  exact ⟨z.sign, ps, hi, factorSigned_correct algorithm z cfg z.sign ps hi⟩

end PrimeFactorLean
