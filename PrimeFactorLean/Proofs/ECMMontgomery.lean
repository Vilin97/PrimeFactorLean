import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import PrimeFactorLean.ECMMontgomery

/-! # Montgomery-curve formulas (proof layer) -/

namespace PrimeFactorLean.ECMM

/-! ## Correctness of the formulas over a field

On `B y² = x³ + A x² + x`, the affine x-coordinates satisfy
`x(2P) = (x² - 1)² / (4x(x² + A x + 1))` and, for `P ≠ ±Q`,
`x(P+Q) x(P-Q) = (x_P x_Q - 1)² / (x_P - x_Q)²`. The projective formulas used
by `dbl` and `add` compute exactly these values (with `a24 = (A + 2)/4`). -/

theorem xDBL_correct {K : Type*} [Field K] (A x : K) (h2 : (2 : K) ≠ 0) :
    let a24 := (A + 2) / 4
    let t1 := (x + 1) ^ 2
    let t2 := (x - 1) ^ 2
    let t3 := t1 - t2
    t1 * t2 = (x ^ 2 - 1) ^ 2 ∧ t3 * (t2 + a24 * t3) = 4 * x * (x ^ 2 + A * x + 1) := by
  intro a24 t1 t2 t3
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  constructor
  · simp only [t1, t2]; ring
  · simp only [a24, t1, t2, t3]; field_simp; ring

theorem xADD_correct {K : Type*} [Field K] (xP xQ : K) :
    let u := (xP - 1) * (xQ + 1)
    let w := (xP + 1) * (xQ - 1)
    (u + w) ^ 2 = 4 * (xP * xQ - 1) ^ 2 ∧ (u - w) ^ 2 = 4 * (xP - xQ) ^ 2 := by
  intro u w
  constructor <;> simp only [u, w] <;> ring

end PrimeFactorLean.ECMM
