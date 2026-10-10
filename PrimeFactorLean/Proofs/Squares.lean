import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Coprime.Lemmas
import PrimeFactorLean.Squares

/-!
# Congruences of squares in `ℤ/n` (proof layer)

The runtime layer states validity as a divisibility of integers
(`Squares.ModEq`). Here it is identified with equality in `ZMod n`, and the
final gcd step is proved complete: every nontrivial congruence of squares
splits `n`.
-/

namespace PrimeFactorLean.Squares

/-- `ModEq` is equality in `ZMod n`. -/
theorem modEq_iff_zmod {n : Nat} {a b : Int} : ModEq n a b ↔ (a : ZMod n) = (b : ZMod n) := by
  unfold ModEq
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  constructor <;> intro h <;> linear_combination h

/-- The defining identity of a relation, in `ZMod n`. -/
theorem Relation.valid_zmod {n : Nat} {fb : Array Nat} (r : Relation n fb) :
    ((r.x : Int) : ZMod n) ^ 2 = ((rhs fb r.sq r.large r.neg r.exps : Int) : ZMod n) := by
  have := modEq_iff_zmod.mp r.valid
  push_cast at this ⊢
  exact this

/-- **Completeness of the gcd step.** A nontrivial congruence of squares
(`x ≢ ±y`) always yields a proper factor. -/
theorem SquareCongruence.factor_isSome {n : Nat} (hn : 1 < n) (c : SquareCongruence n)
    (h1 : (c.x : ZMod n) ≠ (c.y : ZMod n)) (h2 : (c.x : ZMod n) ≠ -(c.y : ZMod n)) :
    c.factor.isSome := by
  set d := Int.gcd ((c.x : Int) - (c.y : Int)) (n : Int) with hd
  have hprod : (n : Int) ∣ ((c.x : Int) - c.y) * ((c.x : Int) + c.y) := by
    have hv := c.valid
    unfold ModEq at hv
    have : ((c.x : Int) - c.y) * ((c.x : Int) + c.y) = (c.x : Int) ^ 2 - (c.y : Int) ^ 2 := by ring
    rw [this]
    exact hv
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

end PrimeFactorLean.Squares
