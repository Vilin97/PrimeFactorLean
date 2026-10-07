import PrimeFactorLean.Core

/-!
# Explicit trial division

The reference implementation tests every candidate below the input. The
optimized version tests only through the exact integer square root. These are
ordinary recursive Lean implementations, rather than aliases for mathlib's
factorization routine. Each unsuccessful square-root search also certifies
primality by the classical small-divisor theorem.
-/

namespace PrimeFactorLean

/-- Test consecutive divisor candidates, with an explicit iteration budget. -/
def trialSearchAux (n d : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    if 1 < d ∧ d < n ∧ d ∣ n then some d
    else trialSearchAux n (d + 1) fuel

theorem trialSearchAux_sound {n d fuel p : Nat}
    (h : trialSearchAux n d fuel = some p) : 1 < p ∧ p < n ∧ p ∣ n := by
  induction fuel generalizing d with
  | zero => simp [trialSearchAux] at h
  | succ fuel ih =>
    simp only [trialSearchAux] at h
    split_ifs at h with hd
    · have : d = p := Option.some.inj h
      exact this ▸ hd
    · exact ih h

/-- Exact completeness statement for the finite search interval. -/
theorem trialSearchAux_none_iff (n d fuel : Nat) :
    trialSearchAux n d fuel = none ↔
      ∀ p, d ≤ p → p < d + fuel → ¬(1 < p ∧ p < n ∧ p ∣ n) := by
  induction fuel generalizing d with
  | zero =>
    simp only [trialSearchAux, Nat.add_zero, true_iff]
    intro p hlow hhigh
    omega
  | succ fuel ih =>
    rw [trialSearchAux]
    by_cases hd : 1 < d ∧ d < n ∧ d ∣ n
    · rw [if_pos hd]
      simp only [Option.some_ne_none, false_iff]
      intro h
      exact h d le_rfl (by omega) hd
    · rw [if_neg hd, ih]
      constructor
      · intro h p hlow hhigh hp
        by_cases heq : p = d
        · subst p
          exact hd hp
        · exact h p (by omega) (by omega) hp
      · intro h p hlow hhigh
        exact h p (by omega) (by omega)

/-- Unoptimized reference: test 2, 3, ..., n - 1. -/
def trialSearchReference (n : Nat) : Option Nat :=
  trialSearchAux n 2 (n - 2)

/-- Square-root optimization: test 2, 3, ..., floor(sqrt n). -/
def trialSearch (n : Nat) : Option Nat :=
  trialSearchAux n 2 (Nat.sqrt n - 1)

theorem trialSearch_sound {n p : Nat} (h : trialSearch n = some p) :
    1 < p ∧ p < n ∧ p ∣ n := trialSearchAux_sound h

/-- Finding no divisor through sqrt(n) proves that n is prime. -/
theorem trialSearch_none_prime {n : Nat} (hn : 2 ≤ n)
    (h : trialSearch n = none) : Nat.Prime n := by
  apply Nat.prime_def_le_sqrt.mpr
  refine ⟨hn, ?_⟩
  have hnone := (trialSearchAux_none_iff n 2 (Nat.sqrt n - 1)).mp h
  intro p hp hpsqrt hdvd
  exact hnone p hp (by omega)
    ⟨by omega, lt_of_le_of_lt hpsqrt (Nat.sqrt_lt_self hn), hdvd⟩

def trialSplitterReference : Splitter := checkedSplitter trialSearchReference

def trialSplitter : Splitter := checkedSplitter trialSearch

def trialFactorReference (n : Nat) : Option (List Nat) := factorNat trialSplitterReference n

/-- Standalone square-root trial factorization. Unlike the generic engine,
this implementation needs no fallback: absence of a small divisor proves
primality directly. -/
def trialCore (n : Nat) : List Nat :=
  if _hn : n ≤ 1 then []
  else
    match hs : trialSearch n with
    | none => [n]
    | some d =>
      have _hd := trialSearch_sound hs
      trialCore d ++ trialCore (n / d)
termination_by n
decreasing_by
  · exact _hd.2.1
  · exact Nat.div_lt_self (by omega) _hd.1

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

def trialFactor (n : Nat) : Option (List Nat) :=
  if n = 0 then none else some (trialCore n)

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

/-- A 6-wheel tests d and d+2, then advances by 6. Starting at 5 visits
exactly 5, 7, 11, 13, ... and skips every multiple of 2 or 3. -/
def trialWheelAux (n d : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    if 1 < d ∧ d < n ∧ d ∣ n then some d
    else if 1 < d + 2 ∧ d + 2 < n ∧ d + 2 ∣ n then some (d + 2)
    else trialWheelAux n (d + 6) fuel

theorem trialWheelAux_sound {n d fuel p : Nat}
    (h : trialWheelAux n d fuel = some p) : 1 < p ∧ p < n ∧ p ∣ n := by
  induction fuel generalizing d with
  | zero => simp [trialWheelAux] at h
  | succ fuel ih =>
    rw [trialWheelAux] at h
    split_ifs at h with hd hd2
    · have heq := Option.some.inj h
      exact heq ▸ hd
    · have heq := Option.some.inj h
      exact heq ▸ hd2
    · exact ih h

theorem trialWheelAux_none_iff (n d fuel : Nat) :
    trialWheelAux n d fuel = none ↔
      ∀ i, i < fuel →
        ¬(1 < d + 6 * i ∧ d + 6 * i < n ∧ d + 6 * i ∣ n) ∧
        ¬(1 < d + 6 * i + 2 ∧ d + 6 * i + 2 < n ∧ d + 6 * i + 2 ∣ n) := by
  induction fuel generalizing d with
  | zero => simp [trialWheelAux]
  | succ fuel ih =>
    rw [trialWheelAux]
    by_cases hd : 1 < d ∧ d < n ∧ d ∣ n
    · rw [if_pos hd]
      simp only [Option.some_ne_none, false_iff]
      intro h
      have h0 := (h 0 (by omega)).1
      simpa using h0 hd
    · rw [if_neg hd]
      by_cases hd2 : 1 < d + 2 ∧ d + 2 < n ∧ d + 2 ∣ n
      · rw [if_pos hd2]
        simp only [Option.some_ne_none, false_iff]
        intro h
        have h0 := (h 0 (by omega)).2
        simpa using h0 hd2
      · rw [if_neg hd2, ih]
        constructor
        · intro h i hi
          cases i with
          | zero => simpa using And.intro hd hd2
          | succ i =>
            have heq : d + 6 * (i + 1) = (d + 6) + 6 * i := by omega
            simpa only [heq] using h i (by omega)
        · intro h i hi
          have heq : d + 6 * (i + 1) = (d + 6) + 6 * i := by omega
          simpa only [heq] using h (i + 1) (by omega)

/-- First handle 2 and 3, then examine only the two invertible residue classes
modulo 6, stopping after covering the integer square root. -/
def trialWheelSearch (n : Nat) : Option Nat :=
  if 1 < 2 ∧ 2 < n ∧ 2 ∣ n then some 2
  else if 1 < 3 ∧ 3 < n ∧ 3 ∣ n then some 3
  else trialWheelAux n 5 (Nat.sqrt n / 6 + 1)

theorem trialWheelSearch_sound {n p : Nat} (h : trialWheelSearch n = some p) :
    1 < p ∧ p < n ∧ p ∣ n := by
  unfold trialWheelSearch at h
  split_ifs at h with h2 h3
  · have heq := Option.some.inj h
    exact heq ▸ h2
  · have heq := Option.some.inj h
    exact heq ▸ h3
  · exact trialWheelAux_sound h

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
  rw [trialWheelSearch, if_neg h2', if_neg h3'] at h
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

def trialWheelSplitter : Splitter := checkedSplitter trialWheelSearch

/-- The optimized trial algorithm is independently total and exact. -/
def trialWheelCore (n : Nat) : List Nat :=
  if _hn : n ≤ 1 then []
  else
    match hs : trialWheelSearch n with
    | none => [n]
    | some d =>
      have _hd := trialWheelSearch_sound hs
      trialWheelCore d ++ trialWheelCore (n / d)
termination_by n
decreasing_by
  · exact _hd.2.1
  · exact Nat.div_lt_self (by omega) _hd.1

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

def trialWheelFactor (n : Nat) : Option (List Nat) :=
  if n = 0 then none else some (trialWheelCore n)

theorem trialWheelFactor_correct {n : Nat} {factors : List Nat}
    (h : trialWheelFactor n = some factors) : IsFactorization n factors := by
  unfold trialWheelFactor at h
  split_ifs at h with hn
  have heq := Option.some.inj h
  subst factors
  exact trialWheelCore_correct n hn

end PrimeFactorLean
