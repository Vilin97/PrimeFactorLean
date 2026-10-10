import PrimeFactorLean.Core

/-!
# Arithmetic in `ℤ[ω] = ℤ[X]/(f)` for a monic `f`, with an evaluation theorem

Elements are coefficient lists (lowest degree first). The monic defining
polynomial `f = g + X^d` is stored through its lower coefficients `g`
(`d = g.length`).

The number field sieve maps `ℤ[ω]` to `ℤ/n` by `ω ↦ r`, where `f(r) ≡ 0`.
`eval_mulZ` proves that the *executable* multiplication (convolution followed by
reduction modulo `f`) is compatible with this map: evaluation at `r` is
multiplicative modulo every `n` with `f(r) ≡ 0 (mod n)`. Consequently an
exactly checked square `β · β = γ` in `ℤ[ω]` gives `eval(β)² ≡ eval(γ)`
modulo `n`.
-/

namespace PrimeFactorLean.NFS

/-! ## Coefficient lists and their evaluation -/

/-- Horner evaluation of a coefficient list at `r` (over the integers). -/
def eval (r : Int) : List Int → Int
  | [] => 0
  | c :: cs => c + r * eval r cs

/-- The product of a list of integers. -/
def prodL : List Int → Int
  | [] => 1
  | x :: xs => x * prodL xs

theorem prodL_append (a b : List Int) : prodL (a ++ b) = prodL a * prodL b := by
  induction a with
  | nil => simp [prodL]
  | cons x xs ih => simp only [List.cons_append, prodL, ih]; grind

/-- Balanced product of a list of integers (`prodL` multiplies a growing product
by one factor at a time: quadratic in the size of the result). The two halves
of the top `depth` levels are computed in parallel tasks. -/
def prodTreeInt (depth : Nat) (xs : List Int) : Int :=
  match h : xs.length with
  | 0 => 1
  | 1 => xs.head (by intro hx; subst hx; simp at h)
  | k + 2 =>
    have h1 : (xs.take ((k + 2) / 2)).length < xs.length := by
      simp only [List.length_take, h]; omega
    have h2 : (xs.drop ((k + 2) / 2)).length < xs.length := by
      simp only [List.length_drop, h]; omega
    if depth = 0 then
      prodTreeInt 0 (xs.take ((k + 2) / 2)) * prodTreeInt 0 (xs.drop ((k + 2) / 2))
    else
      let left := Task.spawn fun _ => prodTreeInt (depth - 1) (xs.take ((k + 2) / 2))
      left.get * prodTreeInt (depth - 1) (xs.drop ((k + 2) / 2))
termination_by xs.length

theorem prodTreeInt_eq_le : ∀ (k depth : Nat) (xs : List Int), xs.length ≤ k →
    prodTreeInt depth xs = prodL xs := by
  intro k
  induction k with
  | zero =>
    intro depth xs hk
    have : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    simp [prodTreeInt, prodL]
  | succ k ih =>
    intro depth xs hk
    rw [prodTreeInt]
    split
    · rename_i h
      rw [List.length_eq_zero_iff.mp h]
      simp [prodL]
    · rename_i h
      obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp h
      simp [prodL]
    · rename_i j h
      split
      · rw [ih _ _ (by simp only [List.length_take, h]; omega),
          ih _ _ (by simp only [List.length_drop, h]; omega), ← prodL_append, List.take_append_drop]
      · simp only [Task.spawn]
        rw [ih _ _ (by simp only [List.length_take, h]; omega),
          ih _ _ (by simp only [List.length_drop, h]; omega), ← prodL_append, List.take_append_drop]

theorem prodTreeInt_eq (depth : Nat) (xs : List Int) : prodTreeInt depth xs = prodL xs :=
  prodTreeInt_eq_le xs.length depth xs (Nat.le_refl _)

section Eval

variable (r : Int)

@[simp] theorem eval_nil : eval r [] = 0 := rfl

@[simp] theorem eval_cons (c : Int) (cs : List Int) :
    eval r (c :: cs) = c + r * eval r cs := rfl

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
      simp only [addL, eval_cons, ih]
      grind

def scaleL (a : Int) (ys : List Int) : List Int := ys.map (a * ·)

theorem eval_scaleL (a : Int) (ys : List Int) : eval r (scaleL a ys) = a * eval r ys := by
  induction ys with
  | nil => simp [scaleL]
  | cons y ys ih =>
    simp only [scaleL, List.map_cons, eval_cons] at ih ⊢
    rw [ih]
    grind

/-- Multiplication by `X^k`. -/
def shiftL : Nat → List Int → List Int
  | 0, ys => ys
  | k + 1, ys => 0 :: shiftL k ys

theorem eval_shiftL (k : Nat) (ys : List Int) : eval r (shiftL k ys) = r ^ k * eval r ys := by
  induction k with
  | zero => simp [shiftL]
  | succ k ih =>
    simp only [shiftL, eval_cons, ih, Int.pow_succ]
    grind

/-- Convolution product of coefficient lists. -/
def mulL : List Int → List Int → List Int
  | [], _ => []
  | x :: xs, ys => addL (scaleL x ys) (0 :: mulL xs ys)

theorem eval_mulL (xs ys : List Int) : eval r (mulL xs ys) = eval r xs * eval r ys := by
  induction xs with
  | nil => simp [mulL]
  | cons x xs ih =>
    simp only [mulL, eval_addL, eval_scaleL, eval_cons, ih]
    grind

theorem eval_append_singleton (ys : List Int) (c : Int) :
    eval r (ys ++ [c]) = eval r ys + c * r ^ ys.length := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    simp only [List.cons_append, eval_cons, ih, List.length_cons, Int.pow_succ]
    grind

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
        eval_append_singleton, Int.zero_mul, Int.add_zero]
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

variable {n : Nat}

theorem eval_reduceTop (g xs : List Int) (hlen : g.length < xs.length)
    (hroot : ModEq n (eval r g + r ^ g.length) 0) :
    ModEq n (eval r (reduceTop g xs)) (eval r xs) := by
  unfold reduceTop
  cases hl : xs.getLast? with
  | none => exact ModEq.refl n _
  | some c =>
    simp only
    have hne : xs ≠ [] := by
      intro h; subst h; simp at hlen
    have hlast : xs.getLast hne = c := by
      rw [List.getLast?_eq_getLast hne] at hl
      exact Option.some.inj hl
    have hxs : xs = xs.dropLast ++ [c] := by
      rw [← hlast]; exact (List.dropLast_concat_getLast hne).symm
    have hdl : xs.dropLast.length = xs.length - 1 := List.length_dropLast
    rw [eval_addL, eval_shiftL, eval_scaleL]
    conv => rhs; rw [hxs]
    rw [eval_append_singleton, hdl]
    have hpow : r ^ (xs.length - 1) = r ^ (xs.length - 1 - g.length) * r ^ g.length := by
      rw [← Int.pow_add]; congr 1; omega
    rw [hpow]
    generalize r ^ (xs.length - 1 - g.length) = u at *
    generalize r ^ g.length = v at *
    -- the difference is `-c u (g(r) + v)`, a multiple of `f(r)`
    have key := (((ModEq.refl n (-c * u)).mul hroot).add
      (ModEq.refl n (eval r xs.dropLast))).add (ModEq.refl n (c * u * v))
    refine (ModEq.of_eq ?_).trans (key.trans (ModEq.of_eq ?_))
    · grind
    · grind

/-- Repeated top reduction, `fuel` steps at most. -/
def reduceFuel (g : List Int) : Nat → List Int → List Int
  | 0, xs => xs
  | fuel + 1, xs =>
    if g.length < xs.length then reduceFuel g fuel (reduceTop g xs) else xs

theorem eval_reduceFuel (g : List Int) (hroot : ModEq n (eval r g + r ^ g.length) 0) :
    ∀ (fuel : Nat) (xs : List Int), ModEq n (eval r (reduceFuel g fuel xs)) (eval r xs) := by
  intro fuel
  induction fuel with
  | zero => intro xs; exact ModEq.refl n _
  | succ fuel ih =>
    intro xs
    simp only [reduceFuel]
    split
    · rename_i h
      exact (ih _).trans (eval_reduceTop r g xs h hroot)
    · exact ModEq.refl n _

/-- Canonical reduction modulo `f = g + X^d`. -/
def reduce (g xs : List Int) : List Int := normalize (reduceFuel g xs.length xs)

theorem eval_reduce (g xs : List Int) (hroot : ModEq n (eval r g + r ^ g.length) 0) :
    ModEq n (eval r (reduce g xs)) (eval r xs) := by
  rw [reduce, eval_normalize]
  exact eval_reduceFuel r g hroot _ _

/-- The rows `x · ys` of `mulL xs ys` summed as `mulL` does. -/
def sumRows : List (Task (List Int)) → List Int
  | [] => []
  | t :: ts => addL t.get (0 :: sumRows ts)

/-- `mulL` with its rows `x · ys` computed in parallel tasks. -/
def mulLPar (xs ys : List Int) : List Int :=
  sumRows (xs.map fun x => Task.spawn fun _ => scaleL x ys)

theorem mulLPar_eq (xs ys : List Int) : mulLPar xs ys = mulL xs ys := by
  unfold mulLPar
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, sumRows, ih]
    rfl

/-- `mulL`, in parallel once a coefficient of `xs` has `2^16` bits (spawning
tasks costs more than small products). -/
def mulLAuto (xs ys : List Int) : List Int :=
  if xs.any (fun c => c.natAbs.log2 ≥ 65536) then mulLPar xs ys else mulL xs ys

theorem mulLAuto_eq (xs ys : List Int) : mulLAuto xs ys = mulL xs ys := by
  unfold mulLAuto
  split
  · exact mulLPar_eq xs ys
  · rfl

/-- Multiplication in `ℤ[ω]`. -/
def mulZ (g xs ys : List Int) : List Int := reduce g (mulLAuto xs ys)

/-- **Evaluation is multiplicative** modulo every `n` at a root `r` of `f`. -/
theorem eval_mulZ (g xs ys : List Int) (hroot : ModEq n (eval r g + r ^ g.length) 0) :
    ModEq n (eval r (mulZ g xs ys)) (eval r xs * eval r ys) := by
  rw [mulZ, mulLAuto_eq, ← eval_mulL]
  exact eval_reduce r g _ hroot

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

/-- The recursive case of `prodTree`. -/
theorem prodTree_split (g : List Int) (xs : List (List Int)) (k : Nat) (h : xs.length = k + 2) :
    prodTree g xs =
      mulZ g (prodTree g (xs.take ((k + 2) / 2))) (prodTree g (xs.drop ((k + 2) / 2))) := by
  conv => lhs; rw [prodTree]
  split
  · omega
  · omega
  · rename_i j h'
    have : j = k := by omega
    subst this
    rfl

/-- `prodTree` with the two halves of the top `depth` levels computed in
parallel tasks (`prodTreePar_eq`). -/
def prodTreePar (g : List Int) (depth : Nat) (xs : List (List Int)) : List Int :=
  match h : xs.length with
  | 0 => [1]
  | 1 => xs.head (by intro hx; subst hx; simp at h)
  | k + 2 =>
    have h1 : (xs.take ((k + 2) / 2)).length < xs.length := by
      simp only [List.length_take, h]; omega
    have h2 : (xs.drop ((k + 2) / 2)).length < xs.length := by
      simp only [List.length_drop, h]; omega
    if depth = 0 then prodTree g xs
    else
      let left := Task.spawn fun _ => prodTreePar g (depth - 1) (xs.take ((k + 2) / 2))
      mulZ g left.get (prodTreePar g (depth - 1) (xs.drop ((k + 2) / 2)))
termination_by xs.length

theorem prodTreePar_eq_le (g : List Int) : ∀ (k depth : Nat) (xs : List (List Int)),
    xs.length ≤ k → prodTreePar g depth xs = prodTree g xs := by
  intro k
  induction k with
  | zero =>
    intro depth xs hk
    have : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    simp [prodTreePar, prodTree]
  | succ k ih =>
    intro depth xs hk
    rw [prodTreePar]
    split
    · rename_i h
      rw [List.length_eq_zero_iff.mp h]
      simp [prodTree]
    · rename_i h
      obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp h
      simp [prodTree]
    · rename_i j h
      split
      · rfl
      · simp only [Task.spawn]
        rw [ih _ _ (by simp only [List.length_take, h]; omega),
          ih _ _ (by simp only [List.length_drop, h]; omega), prodTree_split g xs j h]

theorem prodTreePar_eq (g : List Int) (depth : Nat) (xs : List (List Int)) :
    prodTreePar g depth xs = prodTree g xs :=
  prodTreePar_eq_le g xs.length depth xs (Nat.le_refl _)

theorem eval_prodTree_le (g : List Int) (hroot : ModEq n (eval r g + r ^ g.length) 0) :
    ∀ (k : Nat) (xs : List (List Int)), xs.length ≤ k →
      ModEq n (eval r (prodTree g xs)) (prodL (xs.map (eval r))) := by
  intro k
  induction k with
  | zero =>
    intro xs hk
    have : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst this
    exact ModEq.of_eq (by simp [prodTree, prodL])
  | succ k ih =>
    intro xs hk
    rw [prodTree]
    split
    · rename_i h
      rw [List.length_eq_zero_iff.mp h]
      exact ModEq.of_eq (by simp [prodL])
    · rename_i h
      obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp h
      exact ModEq.of_eq (by simp [prodL])
    · rename_i j h
      refine (eval_mulZ r g _ _ hroot).trans ?_
      refine ((ih _ (by simp only [List.length_take, h]; omega)).mul
        (ih _ (by simp only [List.length_drop, h]; omega))).trans (ModEq.of_eq ?_)
      rw [← prodL_append, ← List.map_append, List.take_append_drop]

theorem eval_prodTree (g : List Int) (hroot : ModEq n (eval r g + r ^ g.length) 0)
    (xs : List (List Int)) : ModEq n (eval r (prodTree g xs)) (prodL (xs.map (eval r))) :=
  eval_prodTree_le r g hroot xs.length xs (Nat.le_refl _)

end Eval

/-! ## Evaluation modulo `n` as a natural number -/

/-- `eval r xs` computed in `ℤ/n` and returned as a residue in `[0, n)`. -/
def evalMod (n r : Nat) : List Int → Nat
  | [] => 0
  | c :: cs => ((c % (n : Int)).toNat + r * evalMod n r cs) % n

theorem toNat_emod_modEq {n : Nat} (hn : 0 < n) (c : Int) :
    ModEq n (((c % (n : Int)).toNat : Nat) : Int) c := by
  have h0 : 0 ≤ c % (n : Int) := Int.emod_nonneg _ (by omega)
  rw [Int.toNat_of_nonneg h0]
  unfold ModEq
  rw [Int.emod_def]
  exact ⟨-(c / n), by grind⟩

theorem evalMod_modEq {n : Nat} (hn : 0 < n) (r : Nat) (xs : List Int) :
    ModEq n (evalMod n r xs : Int) (eval (r : Int) xs) := by
  induction xs with
  | nil => exact ModEq.of_eq (by simp [evalMod])
  | cons c cs ih =>
    simp only [evalMod, eval_cons]
    refine (ModEq.natCast_mod _ n).trans ?_
    push_cast
    exact (toNat_emod_modEq hn c).add ((ModEq.refl n (r : Int)).mul ih)

end PrimeFactorLean.NFS
