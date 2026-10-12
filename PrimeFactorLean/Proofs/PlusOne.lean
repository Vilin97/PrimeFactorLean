import Mathlib.Algebra.QuadraticAlgebra
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.GroupTheory.OrderOfElement
import PrimeFactorLean.Pocklington

/-! Proof layer of the `n + 1` certificate steps (see `PrimeFactorLean.Pocklington`):
Frobenius in `ℤ/p[√D]`, the order argument, and the pair arithmetic of the checker. -/

namespace PrimeFactorLean.Pocklington

open QuadraticAlgebra

/-- `ℤ/p[√D]`. -/
abbrev QA (p : ℕ) (D : ZMod p) := QuadraticAlgebra (ZMod p) D 0

variable {p : ℕ} [hp : Fact p.Prime] {D : ZMod p}

/-- Conjugation `x + y√D ↦ x - y√D`. -/
def qconj (z : QA p D) : QA p D := ⟨z.re, -z.im⟩

@[simp] theorem qconj_re (z : QA p D) : (qconj z).re = z.re := rfl
@[simp] theorem qconj_im (z : QA p D) : (qconj z).im = -z.im := rfl

theorem qconj_mul (z w : QA p D) : qconj (z * w) = qconj z * qconj w := by
  ext <;> simp [qconj]; ring

theorem qconj_one : qconj (1 : QA p D) = 1 := by ext <;> simp [qconj]

theorem qconj_pow (z : QA p D) (k : ℕ) : qconj (z ^ k) = qconj z ^ k := by
  induction k with
  | zero => simp [qconj_one]
  | succ k ih => rw [pow_succ, qconj_mul, ih, pow_succ]

theorem mul_qconj (z : QA p D) : z * qconj z = ⟨z.re ^ 2 - D * z.im ^ 2, 0⟩ := by
  ext <;> simp [qconj] <;> ring

instance : CharP (QA p D) p := charP_of_injective_algebraMap algebraMap_injective p

theorem qa_decomp (z : QA p D) :
    z = (z.re : QA p D) + (z.im : QA p D) * (⟨0, 1⟩ : QA p D) := by
  ext <;> simp

theorem qa_omega_sq : (⟨0, 1⟩ : QA p D) ^ 2 = ((D : ZMod p) : QA p D) := by
  ext <;> simp [pow_two]

theorem qa_coe_mul_omega (r : ZMod p) : (r : QA p D) * ⟨0, 1⟩ = ⟨0, r⟩ := by
  ext <;> simp

/-- Frobenius: `(x + y√D)^p = x + y D^((p-1)/2) √D` for odd `p`. -/
theorem qa_frob (hp2 : p ≠ 2) (z : QA p D) : z ^ p = ⟨z.re, z.im * D ^ (p / 2)⟩ := by
  have hodd : p = 2 * (p / 2) + 1 := by
    have h2 : p % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one p with h | h
      · exfalso
        rcases hp.out.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h) with h1 | h1 <;> omega
      · exact h
    omega
  conv_lhs => rw [qa_decomp z]
  rw [add_pow_char, mul_pow, ← coe_pow, ← coe_pow, ZMod.pow_card, ZMod.pow_card]
  have hw : (⟨0, 1⟩ : QA p D) ^ p = ⟨0, D ^ (p / 2)⟩ := by
    calc (⟨0, 1⟩ : QA p D) ^ p = (⟨0, 1⟩ : QA p D) ^ (2 * (p / 2) + 1) := congrArg _ hodd
      _ = ((D ^ (p / 2) : ZMod p) : QA p D) * ⟨0, 1⟩ := by
        rw [pow_succ, pow_mul, qa_omega_sq, ← coe_pow]
      _ = _ := qa_coe_mul_omega _
  rw [hw]
  ext <;> simp

theorem two_ne_zero_of_ne_two (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h2)

theorem eq_qconj_iff (h2 : (2 : ZMod p) ≠ 0) (w : QA p D) : w = qconj w ↔ w.im = 0 := by
  constructor
  · intro h
    have him : w.im = -w.im := congrArg QuadraticAlgebra.im h
    have h' : (2 : ZMod p) * w.im = 0 := by
      calc (2 : ZMod p) * w.im = w.im + w.im := two_mul _
        _ = -w.im + w.im := by rw [← him]
        _ = 0 := neg_add_cancel _
    exact (mul_eq_zero.mp h').resolve_left h2
  · intro h
    ext <;> simp [h]

theorem qa_isUnit (z : QA p D) (h : z.re ^ 2 - D * z.im ^ 2 ≠ 0) : IsUnit z := by
  refine isUnit_of_mul_eq_one z (qconj z * ⟨(z.re ^ 2 - D * z.im ^ 2)⁻¹, 0⟩) ?_
  rw [← mul_assoc, mul_qconj]
  ext <;> simp [h]

/-- **The `n + 1` order argument.** For an odd prime `p` and `z = x + y√D` of
nonzero norm whose `M`-th power has no `√D` part while its `(M/q)`-th power has
one, `q^e ∣ M` forces `q^e ∣ p - 1` when `D` is a square mod `p` and
`q^e ∣ p + 1` when it is not (through the order of `z / z̄`). -/
theorem plus_prime_pow_dvd (hp2 : p ≠ 2) {q e M : ℕ} (hq : q.Prime) (z : QA p D)
    (hnorm : z.re ^ 2 - D * z.im ^ 2 ≠ 0)
    (hqe : q ^ e ∣ M) (hfull : (z ^ M).im = 0) (hpart : (z ^ (M / q)).im ≠ 0) :
    (D ^ (p / 2) = 1 → q ^ e ∣ p - 1) ∧ (D ^ (p / 2) = -1 → q ^ e ∣ p + 1) := by
  have h2 := two_ne_zero_of_ne_two hp2
  obtain ⟨u, hu⟩ := qa_isUnit z hnorm
  obtain ⟨v, hv⟩ := qa_isUnit (qconj z) (by simpa [qconj] using hnorm)
  have key : ∀ k, (u * v⁻¹) ^ k = 1 ↔ (z ^ k).im = 0 := by
    intro k
    rw [← eq_qconj_iff h2, qconj_pow, mul_pow, inv_pow, mul_inv_eq_one, Units.ext_iff,
      Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu, hv]
  -- the order of `(z / z̄)^k` is exactly `q^e`, where `M = q^e k`
  have hord : ∀ m, (z ^ m).im = 0 → q ^ e ∣ m := by
    intro m hm
    haveI := Fact.mk hq
    rcases e with _ | e
    · simp
    obtain ⟨k, hk⟩ := hqe
    set b := (u * v⁻¹) ^ k with hb
    have hfin : b ^ q ^ (e + 1) = 1 := by
      rw [hb, ← pow_mul, Nat.mul_comm k, ← hk]
      exact (key M).mpr hfull
    have hnot : ¬ b ^ q ^ e = 1 := by
      intro h
      apply hpart
      have hdiv : M / q = k * q ^ e := by
        rw [hk, pow_succ, show q ^ e * q * k = (k * q ^ e) * q by ring]
        exact Nat.mul_div_cancel _ hq.pos
      rw [hdiv]
      apply (key _).mp
      rw [pow_mul]
      exact h
    have hordb : orderOf b = q ^ (e + 1) := orderOf_eq_prime_pow hnot hfin
    rw [← hordb]
    apply orderOf_dvd_of_pow_eq_one
    rw [hb, ← pow_mul, Nat.mul_comm k m, pow_mul, (key m).mpr hm, one_pow]
  constructor
  · intro hD
    apply hord
    have hfr := qa_frob hp2 z
    rw [hD, mul_one] at hfr
    have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.out.one_lt.le
    have : z ^ (p - 1) * z = 1 * z := by
      rw [← pow_succ, hp1, one_mul, hfr]
    rw [(hu ▸ Units.isUnit u : IsUnit z).mul_right_cancel this]
    simp
  · intro hD
    apply hord
    have hfr := qa_frob hp2 z
    rw [hD, mul_neg_one] at hfr
    rw [pow_succ, hfr]
    have : (⟨z.re, -z.im⟩ : QA p D) * z = z * qconj z := by rw [mul_comm]; rfl
    rw [this, mul_qconj]

/-! ## The checker's arithmetic -/

/-- A pair of residues mod `n` as an element of `ℤ/p[√D]`. -/
def toQA (p D : ℕ) (x : ℕ × ℕ) : QA p (D : ZMod p) := ⟨(x.1 : ZMod p), (x.2 : ZMod p)⟩

theorem natCast_mod_of_dvd {n : ℕ} (h : p ∣ n) (u : ℕ) : ((u % n : ℕ) : ZMod p) = u :=
  (ZMod.natCast_eq_natCast_iff' _ _ p).mpr (Nat.mod_mod_of_dvd u h)

theorem toQA_mulPair {n D : ℕ} (h : p ∣ n) (x y : ℕ × ℕ) :
    toQA p D (mulPair n D x y) = toQA p D x * toQA p D y := by
  ext
  · simp [toQA, mulPair, natCast_mod_of_dvd h]; ring
  · simp [toQA, mulPair, natCast_mod_of_dvd h]

theorem toQA_powPair {n D : ℕ} (h : p ∣ n) (x : ℕ × ℕ) (k : ℕ) :
    toQA p D (powPair n D x k) = toQA p D x ^ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [powPair]
    split_ifs with h0 hodd
    · subst h0
      ext <;> simp [toQA, natCast_mod_of_dvd h]
    · rw [toQA_mulPair h, toQA_mulPair h, ih (k / 2) (by omega), ← pow_add, ← pow_succ]
      congr 1
      omega
    · rw [toQA_mulPair h, ih (k / 2) (by omega), ← pow_add]
      congr 1
      omega

/-- A passed `n + 1` witness check, read in `ℤ/p[√D]` for a prime `p ∣ n`. -/
theorem lucasOK_sound {n D q a b : ℕ} (hn : 0 < n) (hpn : p ∣ n)
    (h : lucasOK n D q a b = true) :
    (toQA p D (a, b)).re ^ 2 - (D : ZMod p) * (toQA p D (a, b)).im ^ 2 ≠ 0 ∧
    (toQA p D (a, b) ^ (n + 1)).im = 0 ∧ (toQA p D (a, b) ^ ((n + 1) / q)).im ≠ 0 := by
  simp only [lucasOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hnorm, hfull⟩, hpart⟩ := h
  have hcop : ∀ x : ℕ, Nat.gcd x n = 1 → (x : ZMod p) ≠ 0 := by
    intro x hx h0
    have hpx : p ∣ x := (ZMod.natCast_eq_zero_iff x p).mp h0
    have : p ∣ Nat.gcd x n := Nat.dvd_gcd hpx hpn
    rw [hx] at this
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp this)
  refine ⟨?_, ?_, ?_⟩
  · have hle : D * (b * b) % n ≤ n := (Nat.mod_lt _ hn).le
    have hn0 : ((n : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hpn
    have hval : ((normMod n D a b : ℕ) : ZMod p) =
        (toQA p D (a, b)).re ^ 2 - (D : ZMod p) * (toQA p D (a, b)).im ^ 2 := by
      simp only [normMod, natCast_mod_of_dvd hpn, Nat.cast_add, Nat.cast_sub hle, hn0, toQA]
      push_cast
      ring
    rw [← hval]
    exact hcop _ hnorm
  · have := congrArg QuadraticAlgebra.im (toQA_powPair (D := D) hpn (a, b) (n + 1))
    rw [← this]
    simp [toQA, hfull]
  · have := congrArg QuadraticAlgebra.im (toQA_powPair (D := D) hpn (a, b) ((n + 1) / q))
    rw [← this]
    exact hcop _ hpart

end PrimeFactorLean.Pocklington
