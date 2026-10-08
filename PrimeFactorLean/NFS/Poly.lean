import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Arithmetic in `ℤ[ω] = ℤ[X]/(f)` for a monic `f`, with an evaluation theorem

Elements are coefficient lists (lowest degree first). The monic defining
polynomial `f = g + X^d` is stored through its lower coefficients `g`
(`d = g.length`).

The number field sieve maps `ℤ[ω]` to `ℤ/n` by `ω ↦ r`, where `f(r) ≡ 0`.
`eval_mulZ` proves that the *executable* multiplication (convolution followed by
reduction modulo `f`) is compatible with this map in every commutative ring in
which `r` is a root of `f`. Consequently an exactly checked square
`β · β = γ` in `ℤ[ω]` gives `eval(β)² = eval(γ)` modulo `n`.
-/

namespace PrimeFactorLean.NFS

/-! ## Coefficient lists and their evaluation -/

/-- Horner evaluation of a coefficient list at `r`. -/
def eval {R : Type*} [CommRing R] (r : R) : List Int → R
  | [] => 0
  | c :: cs => (c : R) + r * eval r cs

section Eval

variable {R : Type*} [CommRing R] (r : R)

@[simp] theorem eval_nil : eval r [] = 0 := rfl

@[simp] theorem eval_cons (c : Int) (cs : List Int) :
    eval r (c :: cs) = (c : R) + r * eval r cs := rfl

/-- Pointwise sum with zero padding. -/
def addL : List Int → List Int → List Int
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: addL xs ys

theorem eval_addL (xs ys : List Int) : eval r (addL xs ys) = eval r xs + eval r ys := by
  induction xs generalizing ys with
  | nil => simp [addL]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addL]
    | cons y ys =>
      simp only [addL, eval_cons, ih, Int.cast_add]
      ring

def scaleL (a : Int) (ys : List Int) : List Int := ys.map (a * ·)

theorem eval_scaleL (a : Int) (ys : List Int) : eval r (scaleL a ys) = (a : R) * eval r ys := by
  induction ys with
  | nil => simp [scaleL]
  | cons y ys ih =>
    simp only [scaleL, List.map_cons, eval_cons] at ih ⊢
    rw [ih, Int.cast_mul]
    ring

/-- Multiplication by `X^k`. -/
def shiftL : Nat → List Int → List Int
  | 0, ys => ys
  | k + 1, ys => 0 :: shiftL k ys

theorem eval_shiftL (k : Nat) (ys : List Int) : eval r (shiftL k ys) = r ^ k * eval r ys := by
  induction k with
  | zero => simp [shiftL]
  | succ k ih =>
    simp only [shiftL, eval_cons, ih, Int.cast_zero, zero_add]
    ring

/-- Convolution product of coefficient lists. -/
def mulL : List Int → List Int → List Int
  | [], _ => []
  | x :: xs, ys => addL (scaleL x ys) (0 :: mulL xs ys)

theorem eval_mulL (xs ys : List Int) : eval r (mulL xs ys) = eval r xs * eval r ys := by
  induction xs with
  | nil => simp [mulL]
  | cons x xs ih =>
    simp only [mulL, eval_addL, eval_scaleL, eval_cons, ih, Int.cast_zero, zero_add]
    ring

theorem eval_append_singleton (ys : List Int) (c : Int) :
    eval r (ys ++ [c]) = eval r ys + (c : R) * r ^ ys.length := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    simp only [List.cons_append, eval_cons, ih, List.length_cons]
    ring

/-- Dropping trailing zero coefficients does not change the value. -/
def normalize (xs : List Int) : List Int :=
  (xs.reverse.dropWhile (· == 0)).reverse

theorem eval_normalize (xs : List Int) : eval r (normalize xs) = eval r xs := by
  unfold normalize
  -- Induct on the reversed list.
  suffices h : ∀ ys : List Int, eval r ((ys.dropWhile (· == 0)).reverse) = eval r ys.reverse by
    simpa using h xs.reverse
  intro ys
  induction ys with
  | nil => simp
  | cons y ys ih =>
    by_cases hy : y = 0
    · subst hy
      simp only [List.dropWhile_cons, beq_self_eq_true, ↓reduceIte, List.reverse_cons,
        eval_append_singleton, Int.cast_zero, zero_mul, add_zero]
      exact ih
    · have : (y == 0) = false := by simpa using hy
      simp only [List.dropWhile_cons, this, Bool.false_eq_true, ↓reduceIte]

/-! ## Reduction modulo a monic polynomial -/

/-- One reduction step: remove the top coefficient `c` of `xs` (degree `k ≥ d`)
using `X^k ≡ -X^(k-d) g`. -/
def reduceTop (g xs : List Int) : List Int :=
  match xs.getLast? with
  | none => xs
  | some c => addL xs.dropLast (shiftL (xs.length - 1 - g.length) (scaleL (-c) g))

theorem eval_reduceTop (g xs : List Int) (hlen : g.length < xs.length)
    (hroot : eval r g + r ^ g.length = 0) : eval r (reduceTop g xs) = eval r xs := by
  unfold reduceTop
  cases hl : xs.getLast? with
  | none => rfl
  | some c =>
    simp only
    have hne : xs ≠ [] := by
      intro h; subst h; simp at hlen
    have hlast : xs.getLast hne = c := by
      rw [List.getLast?_eq_getLast hne] at hl
      exact Option.some.inj hl
    have hxs : xs = xs.dropLast ++ [c] := by
      rw [← hlast]; exact (List.dropLast_append_getLast hne).symm
    have hdl : xs.dropLast.length = xs.length - 1 := List.length_dropLast
    conv_rhs => rw [hxs]
    rw [eval_addL, eval_shiftL, eval_scaleL, eval_append_singleton, hdl]
    have hk : xs.length - 1 = (xs.length - 1 - g.length) + g.length := by omega
    have hg : eval r g = -(r ^ g.length) := by linear_combination hroot
    rw [hg]
    conv_rhs => rw [hk, pow_add]
    push_cast
    ring

/-- Repeated top reduction, `fuel` steps at most. -/
def reduceFuel (g : List Int) : Nat → List Int → List Int
  | 0, xs => xs
  | fuel + 1, xs =>
    if g.length < xs.length then reduceFuel g fuel (reduceTop g xs) else xs

theorem eval_reduceFuel (g : List Int) (hroot : eval r g + r ^ g.length = 0) :
    ∀ (fuel : Nat) (xs : List Int), eval r (reduceFuel g fuel xs) = eval r xs := by
  intro fuel
  induction fuel with
  | zero => intro xs; rfl
  | succ fuel ih =>
    intro xs
    simp only [reduceFuel]
    split_ifs with h
    · rw [ih, eval_reduceTop r g xs h hroot]
    · rfl

/-- Canonical reduction modulo `f = g + X^d`. -/
def reduce (g xs : List Int) : List Int := normalize (reduceFuel g xs.length xs)

theorem eval_reduce (g xs : List Int) (hroot : eval r g + r ^ g.length = 0) :
    eval r (reduce g xs) = eval r xs := by
  rw [reduce, eval_normalize, eval_reduceFuel r g hroot]

/-- Multiplication in `ℤ[ω]`. -/
def mulZ (g xs ys : List Int) : List Int := reduce g (mulL xs ys)

/-- **Evaluation is multiplicative** at every root of `f`. -/
theorem eval_mulZ (g xs ys : List Int) (hroot : eval r g + r ^ g.length = 0) :
    eval r (mulZ g xs ys) = eval r xs * eval r ys := by
  rw [mulZ, eval_reduce r g _ hroot, eval_mulL]

/-- Balanced product of a list of elements of `ℤ[ω]` (a product tree). -/
def prodTree (g : List Int) (xs : List (List Int)) : List Int :=
  match h : xs.length with
  | 0 => [1]
  | 1 => xs.head (by intro hx; subst hx; simp at h)
  | k + 2 =>
    have h1 : (xs.take ((k + 2) / 2)).length < xs.length := by
      simp only [List.length_take, h]; omega
    have h2 : (xs.drop ((k + 2) / 2)).length < xs.length := by
      simp only [List.length_drop, h]; omega
    mulZ g (prodTree g (xs.take ((k + 2) / 2))) (prodTree g (xs.drop ((k + 2) / 2)))
termination_by xs.length

theorem eval_prodTree_le (g : List Int) (hroot : eval r g + r ^ g.length = 0) :
    ∀ (k : Nat) (xs : List (List Int)), xs.length ≤ k →
      eval r (prodTree g xs) = (xs.map (eval r)).prod := by
  intro k
  induction k with
  | zero =>
    intro xs hk
    have : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    simp [prodTree]
  | succ k ih =>
    intro xs hk
    rw [prodTree]
    split
    · rename_i h
      rw [List.length_eq_zero_iff.mp h]
      simp
    · rename_i h
      obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp h
      simp
    · rename_i j h
      rw [eval_mulZ r g _ _ hroot, ih _ (by simp only [List.length_take, h]; omega),
        ih _ (by simp only [List.length_drop, h]; omega), ← List.prod_append,
        ← List.map_append, List.take_append_drop]

theorem eval_prodTree (g : List Int) (hroot : eval r g + r ^ g.length = 0)
    (xs : List (List Int)) : eval r (prodTree g xs) = (xs.map (eval r)).prod :=
  eval_prodTree_le r g hroot xs.length xs le_rfl

end Eval

/-! ## Evaluation modulo `n` as a natural number -/

/-- `eval r xs` computed in `ℤ/n` and returned as a residue in `[0, n)`. -/
def evalMod (n r : Nat) : List Int → Nat
  | [] => 0
  | c :: cs => ((c % (n : Int)).toNat + r * evalMod n r cs) % n

theorem toNat_emod_cast {n : Nat} (hn : 0 < n) (c : Int) :
    (((c % (n : Int)).toNat : Nat) : ZMod n) = (c : ZMod n) := by
  have h0 : 0 ≤ c % (n : Int) := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
  have h1 : (((c % (n : Int)).toNat : Nat) : Int) = c % (n : Int) := Int.toNat_of_nonneg h0
  rw [← Int.cast_natCast, h1, ZMod.intCast_mod]

theorem evalMod_cast {n : Nat} (hn : 0 < n) (r : Nat) (xs : List Int) :
    ((evalMod n r xs : Nat) : ZMod n) = eval (r : ZMod n) xs := by
  induction xs with
  | nil => simp [evalMod]
  | cons c cs ih =>
    simp only [evalMod, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, ih, eval_cons,
      toNat_emod_cast hn]

end PrimeFactorLean.NFS
