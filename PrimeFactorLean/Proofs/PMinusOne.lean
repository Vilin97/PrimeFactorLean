import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.LinearCombination
import PrimeFactorLean.PMinusOne

/-! # Stage-one exponent and Lucas-sequence identities for `p ± 1` (proof layer) -/

namespace PrimeFactorLean.PMinusOne

open Arith

/-- Stage 1 of `p - 1` computes the intended power: after any list of exponents
`qs`, the residue is `x ^ (∏ qs) mod n`. Chaining over the chunks, the residue
after a chunk boundary is `a^{∏ q} mod n` for the prime powers applied so far. -/
theorem applyPowers_mod (n x : Nat) (qs : List Nat) :
    applyPowers n x qs % n = x ^ qs.prod % n := by
  induction qs generalizing x with
  | nil => simp [applyPowers]
  | cons q qs ih =>
    have h := ih (powMod x q n)
    simp only [applyPowers, List.foldl_cons] at h ⊢
    rw [h, powMod_eq, List.prod_cons, ← Nat.pow_mod, ← Nat.pow_mul]

/-- `V_{2j} = V_j² - 2` for `V_j = α^j + β^j` with `αβ = 1`. -/
theorem lucas_double {R : Type*} [CommRing R] {α β : R} (h : α * β = 1) (j : Nat) :
    (α ^ j + β ^ j) ^ 2 - 2 = α ^ (2 * j) + β ^ (2 * j) := by
  have hj : α ^ j * β ^ j = 1 := by rw [← mul_pow, h, one_pow]
  linear_combination 2 * hj

/-- `V_{2j+1} = V_j V_{j+1} - V_1` for `V_j = α^j + β^j` with `αβ = 1`. -/
theorem lucas_double_add_one {R : Type*} [CommRing R] {α β : R} (h : α * β = 1)
    (j : Nat) :
    (α ^ j + β ^ j) * (α ^ (j + 1) + β ^ (j + 1)) - (α + β) =
      α ^ (2 * j + 1) + β ^ (2 * j + 1) := by
  have hj : α ^ j * β ^ j = 1 := by rw [← mul_pow, h, one_pow]
  linear_combination (α + β) * hj

end PrimeFactorLean.PMinusOne
