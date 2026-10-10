import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Group.List.Basic
import PrimeFactorLean.Search

/-! # Execution invariants of the bounded searches (proof layer) -/

namespace PrimeFactorLean.Search


/-- Reducing polynomial iterates modulo `n` preserves every divisor modulus. -/
theorem rhoStep_congruent {p n c x y : Nat} (hpn : p ∣ n)
    (hxy : Nat.ModEq p x y) : Nat.ModEq p (rhoStep n c x) (rhoStep n c y) := by
  change ((x * x + c) % n) % p = ((y * y + c) % n) % p
  rw [Nat.mod_mod_of_dvd _ hpn, Nat.mod_mod_of_dvd _ hpn]
  exact (hxy.mul hxy).add_right c

/-- A collision modulo a divisor is precisely the arithmetic detected by rho's gcd. -/
theorem rho_collision_divides_gcd {p n x y : Nat} (hpn : p ∣ n)
    (hxy : Nat.ModEq p x y) : p ∣ Nat.gcd (absDiff x y) n := by
  apply Nat.dvd_gcd _ hpn
  by_cases h : x < y
  · rw [absDiff, if_pos h]
    exact (Nat.modEq_iff_dvd' (Nat.le_of_lt h)).mp hxy
  · rw [absDiff, if_neg h]
    exact (Nat.modEq_iff_dvd' (by omega : y ≤ x)).mp hxy.symm

theorem rhoIterate_add (n c i j y : Nat) :
    rhoIterate n c (i + j) y = rhoIterate n c j (rhoIterate n c i y) := by
  induction i generalizing y with
  | zero => simp [rhoIterate]
  | succ i ih =>
    simpa only [Nat.succ_add, rhoIterate] using ih (rhoStep n c y)

/-- Floyd's actual loop states advance one and two polynomial iterates. -/
theorem floydIterate_correct (n c k x y : Nat) :
    floydIterate n c k (x, y) =
      (rhoIterate n c k x, rhoIterate n c (2 * k) y) := by
  induction k generalizing x y with
  | zero => simp [floydIterate, rhoIterate]
  | succ k ih =>
    simp only [floydIterate, floydStep, ih, rhoIterate]
    congr 1

/-- Fermat's successful square equality gives the exact product identity. -/
theorem fermat_difference_identity {n a b : Nat} (hna : n ≤ a * a)
    (hb : b * b = a * a - n) : (a + b) * (a - b) = n := by
  have hsq : a * a - b * b = n := by omega
  rw [← Nat.pow_two, ← Nat.pow_two] at hsq
  rw [← Nat.pow_two_sub_pow_two]
  exact hsq

/-- Brent advances precisely the specified number of polynomial iterates. -/
theorem brentBlock_iterates (n c x k y q : Nat) :
    (brentBlock n c x k y q).1 = rhoIterate n c k y := by
  induction k generalizing y q with
  | zero => rfl
  | succ k ih =>
    simpa only [brentBlock, rhoIterate] using
      (ih (rhoStep n c y) ((q * absDiff x (rhoStep n c y)) % n))

/-- The batched GCD input is exactly the product of the actual differences. -/
theorem brentBlock_product (n c x k y q : Nat) :
    (brentBlock n c x k y q).2 =
      (q * (batchDifferences n c x k y).prod) % n := by
  induction k generalizing y q with
  | zero => simp [brentBlock, batchDifferences]
  | succ k ih =>
    simp only [brentBlock, batchDifferences, List.prod_cons, ih]
    rw [Nat.mod_mul_mod, Nat.mul_assoc]

private theorem member_dvd_product {a : Nat} {xs : List Nat} (h : a ∈ xs) :
    a ∣ xs.prod := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with he | hmem
    · subst a
      exact Nat.dvd_mul_right x xs.prod
    · exact dvd_mul_of_dvd_right (ih hmem) x

/-- Batching preserves a collided divisor even after reducing its product modulo n. -/
theorem brent_collision_divides_gcd {p n c x k y q difference : Nat}
    (hpn : p ∣ n) (hmem : difference ∈ batchDifferences n c x k y)
    (hdiv : p ∣ difference) : p ∣ Nat.gcd (brentBlock n c x k y q).2 n := by
  rw [brentBlock_product]
  apply Nat.dvd_gcd _ hpn
  apply (Nat.dvd_mod_iff hpn).mpr
  exact dvd_mul_of_dvd_right (hdiv.trans (member_dvd_product hmem)) q

/-- Binary powering computes the mathematical modular power for every modulus. -/
theorem modPow_correct (base exponent modulus : Nat) :
    modPow base exponent modulus = base ^ exponent % modulus := by
  induction exponent using Nat.strong_induction_on generalizing base with
  | _ exponent ih =>
    by_cases hz : exponent = 0
    · simp [modPow, hz]
    · have hlt : exponent / 2 < exponent := by omega
      have hh := ih (exponent / 2) hlt ((base * base) % modulus)
      have he : exponent / 2 * 2 + exponent % 2 = exponent := Nat.div_add_mod' _ _
      have hm : exponent % 2 < 2 := Nat.mod_lt _ (by omega)
      by_cases hp : exponent % 2 = 0
      · have heven : exponent = exponent / 2 * 2 := by omega
        have power : base ^ exponent = (base * base) ^ (exponent / 2) := by
          calc
            base ^ exponent = base ^ (exponent / 2 * 2) := congrArg (base ^ ·) heven
            _ = (base ^ 2) ^ (exponent / 2) := Nat.pow_mul' _ _ _
            _ = (base * base) ^ (exponent / 2) := by rw [Nat.pow_two]
        rw [modPow, if_neg hz, hh, if_pos hp]
        rw [power]
        exact (Nat.pow_mod _ _ _).symm
      · have hodd : exponent % 2 = 1 := by omega
        have hoddexp : exponent = exponent / 2 * 2 + 1 := by omega
        have power : base ^ exponent = (base * base) ^ (exponent / 2) * base := by
          calc
            base ^ exponent = base ^ (exponent / 2 * 2 + 1) := congrArg (base ^ ·) hoddexp
            _ = (base * base) ^ (exponent / 2) * base := by
              rw [Nat.pow_add, Nat.pow_mul', Nat.pow_two, Nat.pow_one]
        rw [modPow, if_neg hz, hh, if_neg hp]
        rw [power]
        rw [← Nat.pow_mod, Nat.mul_mod_mod, Nat.mul_comm]

/-- Every stage-one prefix is powering by the product of its prime powers. -/
theorem powerSchedule_correct (n : Nat) (powers : List Nat) (base : Nat) :
    powerSchedule n powers base = base ^ powers.prod % n := by
  induction powers generalizing base with
  | nil => simp [powerSchedule]
  | cons exponent powers ih =>
    simp only [powerSchedule, List.prod_cons, ih, modPow_correct]
    rw [← Nat.pow_mod, ← Nat.pow_mul]

/-- The precise update invariant used at each Pollard p−1 stage-one step. -/
theorem pMinusOne_step_exponent (n base exponent power : Nat) :
    modPow (base ^ exponent % n) power n = base ^ (exponent * power) % n := by
  rw [modPow_correct, ← Nat.pow_mod, ← Nat.pow_mul]

theorem primePowerLoop_le_bound {p bound fuel q : Nat} (hq : q ≤ bound) :
    primePowerLoop p bound fuel q ≤ bound := by
  induction fuel generalizing q with
  | zero => exact hq
  | succ fuel ih =>
    simp only [primePowerLoop]
    split
    next hstep => exact ih hstep
    next => exact hq

/-- The stage-one exponent for a base prime never exceeds its smoothness bound. -/
theorem primePower_le_bound {p bound : Nat} (hp : p ≤ bound) :
    primePower p bound ≤ bound := primePowerLoop_le_bound hp

theorem primePowerLoop_maximal {p bound fuel q : Nat} (hp : 2 ≤ p)
    (hq : 0 < q) (hqb : q ≤ bound) (hf : bound < fuel + q) :
    bound < primePowerLoop p bound fuel q * p := by
  induction fuel generalizing q with
  | zero => omega
  | succ fuel ih =>
    simp only [primePowerLoop]
    split
    next hstep =>
      have hmul : q + q ≤ q * p := by
        simpa [Nat.mul_two] using Nat.mul_le_mul_left q hp
      exact ih (by omega) hstep (by omega)
    next hstep => omega

/-- Increasing the selected prime power once more exceeds the bound. -/
theorem primePower_maximal {p bound : Nat} (hp : 2 ≤ p) (hb : p ≤ bound) :
    bound < primePower p bound * p :=
  primePowerLoop_maximal hp (by omega) hb (by omega)

theorem primePowerLoop_is_power (p bound fuel exponent : Nat) :
    ∃ k, exponent ≤ k ∧ primePowerLoop p bound fuel (p ^ exponent) = p ^ k := by
  induction fuel generalizing exponent with
  | zero => exact ⟨exponent, le_refl _, rfl⟩
  | succ fuel ih =>
    simp only [primePowerLoop]
    split
    next =>
      have hh := ih (exponent + 1)
      rw [Nat.pow_succ] at hh
      obtain ⟨k, hk, he⟩ := hh
      exact ⟨k, by omega, he⟩
    next => exact ⟨exponent, le_refl _, rfl⟩

/-- Every selected stage-one exponent really is a positive power of its base. -/
theorem primePower_is_power (p bound : Nat) :
    ∃ k, 1 ≤ k ∧ primePower p bound = p ^ k := by
  simpa only [primePower, Nat.pow_one] using primePowerLoop_is_power p bound bound 1

end PrimeFactorLean.Search
