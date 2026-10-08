import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Bounded integer factor searches

These functions implement the search itself, using exact unbounded naturals.
They may exhaust their bounds; `none` never means that the input is prime.
The public factorization layer checks each successful split and supplies a
separately verified complete fallback.  Search invariants below describe the
actual modular exponentiation and batched rho computations.
-/

namespace PrimeFactorLean.Search

structure Config where
  fermatSteps : Nat := 10000
  rhoSteps : Nat := 50000
  rhoRestarts : Nat := 8
  brentBatch : Nat := 64
  pMinusOneBound : Nat := 1000
  ecmCurves : Nat := 12
  ecmBound : Nat := 200
  deriving Repr, Inhabited

def absDiff (a b : Nat) : Nat := if a < b then b - a else a - b

def properFactor (n d : Nat) : Bool := 1 < d && d < n && n % d == 0

def accept (n d : Nat) : Option Nat := if properFactor n d then some d else none

/-- A factor-valued result for the imperative Brent loop. Proof fields are
erased by compilation; every return path carries the divisibility invariant. -/
def acceptCertified (n d : Nat) : Option {d : Nat // 1 < d ∧ d < n ∧ d ∣ n} :=
  if h : properFactor n d then
    some ⟨d, by simpa [properFactor, Nat.dvd_iff_mod_eq_zero, and_assoc] using h⟩
  else none

def evenFactor (n : Nat) : Option Nat := if 2 < n && n % 2 == 0 then some 2 else none

/-- Deterministic restart enumeration, stopping at the first successful search. -/
def firstAttempt (search : Nat → Option Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, start =>
    match search start with
    | some d => some d
    | none => firstAttempt search fuel (start + 1)

/-! ## Fermat's difference of squares -/

def fermatLoop (n : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, a =>
    let b := Nat.sqrt (a * a - n)
    if b * b == a * a - n then
      match accept n (a - b) with
      | some d => some d
      | none => fermatLoop n fuel (a + 1)
    else fermatLoop n fuel (a + 1)

def fermat (n : Nat) (cfg : Config := {}) : Option Nat :=
  if n < 4 then none else
  match evenFactor n with
  | some d => some d
  | none =>
    let s := Nat.sqrt n
    let start := if s * s == n then s else s + 1
    fermatLoop n cfg.fermatSteps start

/-! ## Pollard rho with Floyd cycle detection -/

def rhoStep (n c x : Nat) : Nat := (x * x + c) % n

def floydStep (n c : Nat) (state : Nat × Nat) : Nat × Nat :=
  (rhoStep n c state.1, rhoStep n c (rhoStep n c state.2))

def rhoLoop (n c : Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, x, y =>
    let next := floydStep n c (x, y)
    let x' := next.1
    let y' := next.2
    let d := Nat.gcd (absDiff x' y') n
    if d == 1 then rhoLoop n c fuel x' y'
    else accept n d

def rho (n : Nat) (cfg : Config := {}) : Option Nat :=
  if n < 4 then none else
  match evenFactor n with
  | some d => some d
  | none => firstAttempt (fun attempt =>
      let seed := (attempt + 2) % n
      let c := (2 * attempt + 1) % n
      rhoLoop n c cfg.rhoSteps seed seed) cfg.rhoRestarts 0

/-! ## Brent's rho with batched GCD and individual recovery -/

def rhoIterate (n c : Nat) : Nat → Nat → Nat
  | 0, y => y
  | k + 1, y => rhoIterate n c k (rhoStep n c y)

def floydIterate (n c : Nat) : Nat → (Nat × Nat) → Nat × Nat
  | 0, state => state
  | k + 1, state => floydIterate n c k (floydStep n c state)

/-- The differences in one Brent block, in their actual execution order. -/
def batchDifferences (n c x : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, y =>
    let y' := rhoStep n c y
    absDiff x y' :: batchDifferences n c x k y'

/-- Advance a Brent block while accumulating the product of differences. -/
def brentBlock (n c x : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, y, q => (y, q % n)
  | k + 1, y, q =>
    let y' := rhoStep n c y
    brentBlock n c x k y' ((q * absDiff x y') % n)

def brentRecover (n c x : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | k + 1, y =>
    let y' := rhoStep n c y
    let d := Nat.gcd (absDiff x y') n
    if d == 1 then brentRecover n c x k y' else accept n d

def brentAttemptCertified (n c seed steps batch : Nat) :
    Option {d : Nat // 1 < d ∧ d < n ∧ d ∣ n} := Id.run do
  let m := max 1 batch
  let mut y := seed % n
  let mut r := 1
  let mut used := 0
  for _ in [:steps + 1] do
    if used + r > steps then return none
    let x := y
    y := rhoIterate n c r y
    used := used + r
    let blocks := (r + m - 1) / m
    for j in [:blocks] do
      let count := min m (r - j * m)
      if used + count > steps then return none
      let oldY := y
      let result := brentBlock n c x count y 1
      y := result.1
      used := used + count
      let d := Nat.gcd result.2 n
      if d != 1 then
        if d == n then
          match brentRecover n c x count oldY with
          | none => return none
          | some factor => return acceptCertified n factor
        else return acceptCertified n d
    r := 2 * r
  return none

def brentAttempt (n c seed steps batch : Nat) : Option Nat :=
  (brentAttemptCertified n c seed steps batch).map Subtype.val

def brent (n : Nat) (cfg : Config := {}) : Option Nat :=
  if n < 4 then none else
  match evenFactor n with
  | some d => some d
  | none => firstAttempt (fun attempt => brentAttempt n (2 * attempt + 1)
      (attempt + 2) cfg.rhoSteps cfg.brentBatch) cfg.rhoRestarts 0

/-! ## Binary modular exponentiation and Pollard p−1 stage 1 -/

/-- Binary powering, reducing after every multiplication. -/
def modPow (base exponent modulus : Nat) : Nat :=
  if exponent = 0 then 1 % modulus else
    let r := modPow ((base * base) % modulus) (exponent / 2) modulus
    if exponent % 2 = 0 then r else (base * r) % modulus
termination_by exponent
decreasing_by omega

/-- The largest power of `p` at most `bound`, with bounded recursion. -/
def primePowerLoop (p bound : Nat) : Nat → Nat → Nat
  | 0, q => q
  | fuel + 1, q =>
    if q * p ≤ bound then primePowerLoop p bound fuel (q * p) else q

def primePower (p bound : Nat) : Nat := primePowerLoop p bound bound p

/-- Small prime enumeration for smoothness bounds, unrelated to factoring `n`. -/
def smallPrimes (bound : Nat) : Array Nat := Id.run do
  let mut ps := #[]
  for p in [2:bound + 1] do
    let mut prime := true
    for q in ps do
      if q * q > p then break
      if p % q == 0 then
        prime := false
        break
    if prime then ps := ps.push p
  return ps

def pMinusOnePowers (bound : Nat) : List Nat :=
  (smallPrimes bound).toList.map fun p => primePower p bound

/-- Applying the stage-one powers without early factor extraction. -/
def powerSchedule (n : Nat) : List Nat → Nat → Nat
  | [], a => a % n
  | exponent :: exponents, a => powerSchedule n exponents (modPow a exponent n)

/-- The actual stage-one loop checks every prefix to avoid losing a factor when
both prime divisors become annihilated by a later, larger exponent. -/
def pMinusOneLoop (n : Nat) : List Nat → Nat → Option Nat
  | [], _ => none
  | exponent :: exponents, a =>
    let a' := modPow a exponent n
    let d := Nat.gcd (absDiff a' 1) n
    match accept n d with
    | some factor => some factor
    | none => if d == n then none else pMinusOneLoop n exponents a'

def pMinusOneAttemptWithPowers (n base : Nat) (powers : List Nat) : Option Nat :=
  match accept n (Nat.gcd base n) with
  | some d => some d
  | none => pMinusOneLoop n powers (base % n)

def pMinusOneAttempt (n base bound : Nat) : Option Nat :=
  pMinusOneAttemptWithPowers n base (pMinusOnePowers bound)

def pMinusOne (n : Nat) (cfg : Config := {}) : Option Nat :=
  if n < 4 then none else
  match evenFactor n with
  | some d => some d
  | none =>
    let powers := pMinusOnePowers cfg.pMinusOneBound
    firstAttempt (fun attempt => pMinusOneAttemptWithPowers n (attempt + 2) powers)
      cfg.rhoRestarts 0

/-! ## Execution invariants -/

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

theorem accept_sound {n candidate d : Nat} (h : accept n candidate = some d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  unfold accept at h
  split at h
  next hc =>
    simp only [Option.some.injEq] at h
    subst candidate
    simpa [properFactor, Nat.dvd_iff_mod_eq_zero, and_assoc] using hc
  next => simp at h

theorem evenFactor_sound {n d : Nat} (h : evenFactor n = some d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  unfold evenFactor at h
  split at h
  next hc =>
    simp only [Option.some.injEq] at h
    subst d
    have hh : 2 < n ∧ n % 2 = 0 := by simpa using hc
    exact ⟨by omega, hh.1, Nat.dvd_of_mod_eq_zero hh.2⟩
  next => simp at h

theorem firstAttempt_sound {P : Nat → Prop} {search : Nat → Option Nat}
    (hs : ∀ attempt d, search attempt = some d → P d)
    {fuel start d : Nat} (h : firstAttempt search fuel start = some d) : P d := by
  induction fuel generalizing start with
  | zero => simp [firstAttempt] at h
  | succ fuel ih =>
    cases he : search start with
    | none => exact ih (by simpa [firstAttempt, he] using h)
    | some factor =>
      have hd : factor = d := by simpa [firstAttempt, he] using h
      subst factor
      exact hs start d he

theorem fermatLoop_sound {n fuel a d : Nat} (h : fermatLoop n fuel a = some d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  induction fuel generalizing a with
  | zero => simp [fermatLoop] at h
  | succ fuel ih =>
    simp only [fermatLoop] at h
    split at h
    next =>
      cases ha : accept n (a - Nat.sqrt (a * a - n)) with
      | none => exact ih (by simpa [ha] using h)
      | some factor =>
        have hd : factor = d := by simpa [ha] using h
        subst factor
        exact accept_sound ha
    next => exact ih h

theorem fermat_sound {n d : Nat} {cfg : Config} (h : fermat n cfg = some d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  unfold fermat at h
  split at h
  next => simp at h
  next =>
    cases he : evenFactor n with
    | none => exact fermatLoop_sound (by simpa [he] using h)
    | some factor =>
      have hd : factor = d := by simpa [he] using h
      subst factor
      exact evenFactor_sound he

theorem rhoLoop_sound {n c fuel x y d : Nat} (h : rhoLoop n c fuel x y = some d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  induction fuel generalizing x y with
  | zero => simp [rhoLoop] at h
  | succ fuel ih =>
    simp only [rhoLoop] at h
    split at h
    next => exact ih h
    next => exact accept_sound h

theorem rho_sound {n d : Nat} {cfg : Config} (h : rho n cfg = some d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  unfold rho at h
  split at h
  next => simp at h
  next =>
    cases he : evenFactor n with
    | none =>
      apply firstAttempt_sound (fun _ _ hh => rhoLoop_sound hh)
      simpa [he] using h
    | some factor =>
      have hd : factor = d := by simpa [he] using h
      subst factor
      exact evenFactor_sound he

theorem brentRecover_sound {n c x fuel y d : Nat}
    (h : brentRecover n c x fuel y = some d) : 1 < d ∧ d < n ∧ d ∣ n := by
  induction fuel generalizing y with
  | zero => simp [brentRecover] at h
  | succ fuel ih =>
    simp only [brentRecover] at h
    split at h
    next => exact ih h
    next => exact accept_sound h

theorem brentAttempt_sound {n c seed steps batch d : Nat}
    (h : brentAttempt n c seed steps batch = some d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  unfold brentAttempt at h
  cases he : brentAttemptCertified n c seed steps batch with
  | none => simp [he] at h
  | some factor =>
    have hd : factor.val = d := by simpa [he] using h
    subst d
    exact factor.property

theorem brent_sound {n d : Nat} {cfg : Config} (h : brent n cfg = some d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  unfold brent at h
  split at h
  next => simp at h
  next =>
    cases he : evenFactor n with
    | none =>
      apply firstAttempt_sound (fun _ _ hh => brentAttempt_sound hh)
      simpa [he] using h
    | some factor =>
      have hd : factor = d := by simpa [he] using h
      subst factor
      exact evenFactor_sound he

theorem pMinusOneLoop_sound {n a d : Nat} {powers : List Nat}
    (h : pMinusOneLoop n powers a = some d) : 1 < d ∧ d < n ∧ d ∣ n := by
  induction powers generalizing a with
  | nil => simp [pMinusOneLoop] at h
  | cons exponent powers ih =>
    simp only [pMinusOneLoop] at h
    cases he : accept n (Nat.gcd (absDiff (modPow a exponent n) 1) n) with
    | some factor =>
      have hd : factor = d := by simpa [he] using h
      subst factor
      exact accept_sound he
    | none =>
      simp only [he] at h
      split at h
      next => simp at h
      next => exact ih h

theorem pMinusOneAttemptWithPowers_sound {n base d : Nat} {powers : List Nat}
    (h : pMinusOneAttemptWithPowers n base powers = some d) :
    1 < d ∧ d < n ∧ d ∣ n := by
  unfold pMinusOneAttemptWithPowers at h
  cases he : accept n (Nat.gcd base n) with
  | none => exact pMinusOneLoop_sound (by simpa [he] using h)
  | some factor =>
    have hd : factor = d := by simpa [he] using h
    subst factor
    exact accept_sound he

theorem pMinusOne_sound {n d : Nat} {cfg : Config}
    (h : pMinusOne n cfg = some d) : 1 < d ∧ d < n ∧ d ∣ n := by
  unfold pMinusOne at h
  split at h
  next => simp at h
  next =>
    cases he : evenFactor n with
    | none =>
      apply firstAttempt_sound (fun _ _ hh => pMinusOneAttemptWithPowers_sound hh)
      simpa [he] using h
    | some factor =>
      have hd : factor = d := by simpa [he] using h
      subst factor
      exact evenFactor_sound he

end PrimeFactorLean.Search
