import PrimeFactorLean.Trial

/-!
# Executable arithmetic shared by the factoring algorithms

Everything here runs on Lean's arbitrary-precision `Nat`/`Int` (GMP-backed).
Functions whose results are trusted by a proof come with a specification theorem
(`powMod_eq`, `invMod_spec`, `sqrtModPrime_spec`, `perfectPower_spec`,
`smallPrime_sound`). The remaining helpers (Jacobi symbols, the Eratosthenes
sieve, Miller–Rabin, Tonelli–Shanks candidates) only *guide* searches: no
correctness theorem depends on their answers.
-/

namespace PrimeFactorLean.Arith

/-! ## Modular exponentiation -/

/-- Right-to-left binary powering, tail recursive: `acc * base ^ exp % m`. -/
def powModAux (m base exp acc : Nat) : Nat :=
  if exp = 0 then acc % m
  else
    let acc' := if exp % 2 = 1 then acc * base % m else acc
    powModAux m (base * base % m) (exp / 2) acc'
termination_by exp
decreasing_by omega

/-- `(a % m) * (b % m)^k ≡ a * b^k (mod m)`. -/
theorem mod_mul_pow_mod (a b k m : Nat) : (a % m) * (b % m) ^ k % m = a * b ^ k % m := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod]

/-- `a * (b % m)^k ≡ a * b^k (mod m)`. -/
theorem mul_pow_mod (a b k m : Nat) : a * (b % m) ^ k % m = a * b ^ k % m := by
  rw [Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod]

theorem powModAux_eq (m base exp acc : Nat) :
    powModAux m base exp acc = acc * base ^ exp % m := by
  induction exp using Nat.strongRecOn generalizing base acc with
  | _ exp ih =>
    rw [powModAux]
    by_cases hz : exp = 0
    · subst hz; simp
    · rw [if_neg hz]
      have hlt : exp / 2 < exp := by omega
      rw [ih _ hlt]
      by_cases hodd : exp % 2 = 1
      · rw [if_pos hodd, mod_mul_pow_mod]
        have h2 : exp = 2 * (exp / 2) + 1 := by omega
        generalize exp / 2 = k at h2 ⊢
        subst h2
        rw [Nat.pow_succ, Nat.pow_mul, Nat.pow_two, Nat.mul_assoc, Nat.mul_comm base]
      · rw [if_neg hodd, mul_pow_mod]
        have h2 : exp = 2 * (exp / 2) := by omega
        generalize exp / 2 = k at h2 ⊢
        subst h2
        rw [Nat.pow_mul, Nat.pow_two]

/-- Modular powering `b ^ e % m` with `O(log e)` multiplications. -/
def powMod (b e m : Nat) : Nat := powModAux m (b % m) e 1

theorem powMod_eq (b e m : Nat) : powMod b e m = b ^ e % m := by
  rw [powMod, powModAux_eq, Nat.one_mul, ← Nat.pow_mod]

/-! ## Inverses -/

/-- Extended Euclid on integers: returns `(g, s, t)` with `s * a + t * b = g`.
The identity is not trusted; `invMod` checks its own result. -/
def gcdExtAux (r0 r1 s0 s1 t0 t1 : Int) : Nat → Int × Int × Int
  | 0 => (r0, s0, t0)
  | fuel + 1 =>
    if r1 = 0 then (r0, s0, t0)
    else
      let q := r0 / r1
      gcdExtAux r1 (r0 - q * r1) s1 (s0 - q * s1) t1 (t0 - q * t1) fuel

def gcdExt (a b : Int) : Int × Int × Int :=
  gcdExtAux a b 1 0 0 1 (2 * (a.natAbs.log2 + b.natAbs.log2) + 4)

/-- A checked modular inverse: `some x` only when `a * x ≡ 1 (mod m)`. -/
def invMod (a m : Nat) : Option Nat :=
  let x := ((gcdExt (a : Int) (m : Int)).2.1 % (m : Int)).toNat
  if a * x % m = 1 % m then some x else none

theorem invMod_spec {a m x : Nat} (h : invMod a m = some x) : a * x % m = 1 % m := by
  unfold invMod at h
  dsimp only at h
  split at h
  · cases h; assumption
  · contradiction

/-! ## Square roots modulo primes -/

/-- Jacobi symbol `(a / n)` for odd positive `n` (a search heuristic only). -/
def jacobi (a n : Nat) : Int := Id.run do
  let mut a := a % n
  let mut n := n
  let mut result : Int := 1
  let mut fuel := 2 * (n.log2 + a.log2 + 2)
  while a != 0 && fuel > 0 do
    fuel := fuel - 1
    while a % 2 == 0 && a > 0 do
      a := a / 2
      let r := n % 8
      if r == 3 || r == 5 then result := -result
    let t := a
    a := n
    n := t
    if a % 4 == 3 && n % 4 == 3 then result := -result
    a := a % n
  return if n == 1 then result else 0

/-- Tonelli–Shanks candidate square root of `a` modulo an odd prime `p`. -/
def tonelliShanks (a p : Nat) : Nat := Id.run do
  let a := a % p
  if a == 0 || p < 3 then return a
  if p % 4 == 3 then
    return powMod a ((p + 1) / 4) p
  -- Write p - 1 = q * 2^s with q odd.
  let mut q := p - 1
  let mut s := 0
  while q % 2 == 0 && q > 0 do
    q := q / 2
    s := s + 1
  -- Find a quadratic non-residue z.
  let mut z := 2
  while z < p && powMod z ((p - 1) / 2) p != p - 1 do
    z := z + 1
  let mut m := s
  let mut c := powMod z q p
  let mut t := powMod a q p
  let mut r := powMod a ((q + 1) / 2) p
  let mut fuel := s + 2
  while t != 1 && fuel > 0 do
    fuel := fuel - 1
    -- least i with t^(2^i) = 1
    let mut i := 0
    let mut tt := t
    while tt != 1 && i < m do
      tt := tt * tt % p
      i := i + 1
    if i == m then return 0
    let mut b := c
    for _ in [0:m - i - 1] do
      b := b * b % p
    m := i
    c := b * b % p
    t := t * c % p
    r := r * b % p
  return r

/-- A checked square root modulo `p`: `some r` only when `r² ≡ a (mod p)`. -/
def sqrtModPrime (a p : Nat) : Option Nat :=
  let r := tonelliShanks a p
  if r * r % p = a % p then some r else none

theorem sqrtModPrime_spec {a p r : Nat} (h : sqrtModPrime a p = some r) :
    r * r % p = a % p := by
  unfold sqrtModPrime at h
  dsimp only at h
  split at h
  · cases h; assumption
  · contradiction

/-! ## Integer roots and perfect powers -/

/-- `⌊n^(1/k)⌋` by Newton iteration from an overestimate (checked by callers). -/
def iroot (n k : Nat) : Nat := Id.run do
  if k ≤ 1 || n ≤ 1 then return n
  let mut x := 2 ^ (n.log2 / k + 1)
  let mut fuel := 2 * n.log2 + 64
  while fuel > 0 do
    fuel := fuel - 1
    let y := ((k - 1) * x + n / x ^ (k - 1)) / k
    if y ≥ x then break
    x := y
  let mut fuel2 := 64
  while x ^ k > n && fuel2 > 0 do
    x := x - 1
    fuel2 := fuel2 - 1
  while (x + 1) ^ k ≤ n && fuel2 > 0 do
    x := x + 1
    fuel2 := fuel2 - 1
  return x

/-- Search exponents `k, k+1, …` for an exact `r ^ k = n` with `r ≥ 2`. -/
def perfectPowerFrom (n : Nat) : Nat → Nat → Option (Nat × Nat)
  | 0, _ => none
  | fuel + 1, k =>
    let r := iroot n k
    if 2 ≤ r ∧ r ^ k = n then some (r, k) else perfectPowerFrom n fuel (k + 1)

/-- Detect `n = r ^ k` with `k ≥ 2`; the identity is checked. -/
def perfectPower (n : Nat) : Option (Nat × Nat) :=
  if n < 4 then none else perfectPowerFrom n n.log2 2

theorem perfectPowerFrom_spec {n fuel k r e : Nat}
    (h : perfectPowerFrom n fuel k = some (r, e)) : 2 ≤ r ∧ r ^ e = n := by
  induction fuel generalizing k with
  | zero => simp [perfectPowerFrom] at h
  | succ fuel ih =>
    simp only [perfectPowerFrom] at h
    split at h
    · cases h; assumption
    · exact ih h

theorem perfectPower_spec {n r k : Nat} (h : perfectPower n = some (r, k)) :
    2 ≤ r ∧ r ^ k = n := by
  unfold perfectPower at h
  split at h
  · contradiction
  · exact perfectPowerFrom_spec h

theorem perfectPowerFrom_exponent {n fuel k r e : Nat}
    (h : perfectPowerFrom n fuel k = some (r, e)) : k ≤ e := by
  induction fuel generalizing k with
  | zero => simp [perfectPowerFrom] at h
  | succ fuel ih =>
    simp only [perfectPowerFrom] at h
    split at h
    · cases h; exact Nat.le_refl _
    · exact Nat.le_of_succ_le (ih h)

/-- A perfect-power root is a proper divisor. -/
theorem perfectPower_proper {n r k : Nat} (h : perfectPower n = some (r, k)) :
    1 < r ∧ r < n ∧ r ∣ n := by
  obtain ⟨hr, hpow⟩ := perfectPower_spec h
  have hk : 2 ≤ k := by
    unfold perfectPower at h
    split at h
    · contradiction
    · exact perfectPowerFrom_exponent h
  refine ⟨by omega, ?_, ?_⟩
  · rw [← hpow]
    calc r = r ^ 1 := (Nat.pow_one r).symm
      _ < r ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
  · rw [← hpow]
    have := Nat.pow_dvd_pow r (show 1 ≤ k by omega)
    rwa [Nat.pow_one] at this

/-! ## Small-prime enumeration and probable-prime screening -/

/-- Sieve of Eratosthenes: the primes `≤ n` (search data only, never trusted). -/
def primesUpTo (n : Nat) : Array Nat := Id.run do
  if n < 2 then return #[]
  let mut composite : ByteArray := ByteArray.emptyWithCapacity (n + 1)
  for _ in [0:n + 1] do
    composite := composite.push 0
  let mut primes : Array Nat := #[]
  for i in [2:n + 1] do
    if composite.get! i == 0 then
      primes := primes.push i
      let mut j := i * i
      while j ≤ n do
        composite := composite.set! j 1
        j := j + i
  return primes

/-- One strong-probable-prime round to base `a` for odd `n > 2`. -/
def strongProbablePrime (n a : Nat) : Bool := Id.run do
  let mut d := n - 1
  let mut s := 0
  while d % 2 == 0 && d > 0 do
    d := d / 2
    s := s + 1
  let mut x := powMod a d n
  if x == 1 || x == n - 1 then return true
  for _ in [1:s] do
    x := x * x % n
    if x == n - 1 then return true
  return false

/-- Miller–Rabin with the first thirteen prime bases (deterministic below
`3.3 · 10^24`, and an excellent screen above). Never used as a proof. -/
def isProbablePrime (n : Nat) : Bool :=
  if n < 2 then false
  else
    let small := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
    if small.contains n then true
    else if small.any (fun p => n % p == 0) then false
    else small.all (fun a => strongProbablePrime n a)

/-! ## Verified small primality -/

/-- Exact primality for small inputs by the verified 6-wheel trial division. -/
def smallPrime (n : Nat) : Bool := 2 ≤ n && (trialWheelSearch n).isNone

end PrimeFactorLean.Arith
