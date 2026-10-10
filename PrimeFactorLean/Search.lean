import PrimeFactorLean.Core

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
    let b := isqrt (a * a - n)
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
    let s := isqrt n
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

/-! ## Soundness of every successful search -/

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
      cases ha : accept n (a - isqrt (a * a - n)) with
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
