import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.GCD.BigOperators
import PrimeFactorLean.Arith

/-!
# Pocklington–Lehmer primality certificates

Pratt certificates (`PrimeFactorLean.Primality`) need the *complete*
factorization of `n - 1`, recursively. Pocklington's criterion only needs a
factored part `F ∣ n - 1` with `F² > n`, which is far easier to find for large
primes. This file proves the criterion from scratch against mathlib's
`Nat.Prime` and gives a checker whose acceptance is proved sound.

**Theorem (Pocklington).** Let `n ≥ 2` and let `q₁,…,q_k` be distinct primes
with `q_i^{e_i} ∣ n - 1` and `F = ∏ q_i^{e_i}`, `F² > n`. If for every `i` there
is `a_i` with `a_i^{n-1} ≡ 1 (mod n)` and `gcd(a_i^{(n-1)/q_i} - 1, n) = 1`,
then `n` is prime.

*Proof.* Let `p` be any prime divisor of `n`. With `n - 1 = q^e k`, the element
`b = a^k` of `(ℤ/p)ˣ` has order exactly `q^e`, so `q^e ∣ p - 1`. The prime powers
are pairwise coprime, so `F ∣ p - 1` and `p > F > √n`. A composite `n` would
have a prime divisor `p ≤ √n`.

Certificates are produced by an untrusted generator that may call any
factoring routine; only `Step.check`/`Certificate.check` are trusted, and both
are proved sound below.
-/

namespace PrimeFactorLean.Pocklington

open Arith

/-- The order argument: a witness forces `q^e ∣ p - 1` for every prime `p ∣ n`. -/
theorem prime_pow_dvd_sub_one {p q e N a : Nat} (hp : p.Prime) (hq : q.Prime)
    (hqe : q ^ e ∣ N - 1)
    (hfull : (a : ZMod p) ^ (N - 1) = 1)
    (hpart : (a : ZMod p) ^ ((N - 1) / q) ≠ 1) : q ^ e ∣ p - 1 := by
  haveI := Fact.mk hp
  haveI := Fact.mk hq
  rcases e with _ | e
  · simp
  obtain ⟨k, hk⟩ := hqe
  set b : ZMod p := (a : ZMod p) ^ k with hb
  have hfin : b ^ q ^ (e + 1) = 1 := by
    rw [hb, ← pow_mul, mul_comm, ← hk]
    exact hfull
  have hnot : ¬ b ^ q ^ e = 1 := by
    intro h
    apply hpart
    have hdiv : (N - 1) / q = k * q ^ e := by
      rw [hk, pow_succ, show q ^ e * q * k = (k * q ^ e) * q by ring]
      exact Nat.mul_div_cancel _ hq.pos
    rw [hdiv, pow_mul]
    exact h
  have hord : orderOf b = q ^ (e + 1) := orderOf_eq_prime_pow hnot hfin
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_pos hq.pos _).ne'] at hfin
    exact zero_ne_one hfin
  rw [← hord]
  exact ZMod.orderOf_dvd_card_sub_one hb0

/-- Pairwise coprime divisors of `m` have a product dividing `m`. -/
theorem list_prod_dvd_of_coprime {l : List Nat} {m : Nat}
    (hco : l.Pairwise Nat.Coprime) (hd : ∀ x ∈ l, x ∣ m) : l.prod ∣ m := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.pairwise_cons] at hco
    rw [List.prod_cons]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · exact Nat.coprime_list_prod_right_iff.mpr hco.1
    · exact hd x (by simp)
    · exact ih hco.2 (fun y hy => hd y (by simp [hy]))

/-- The factored part of a certificate row: `∏ q^e` over its `(q, e, a)` triples. -/
def factoredPart (ws : List (Nat × Nat × Nat)) : Nat :=
  (ws.map fun t => t.1 ^ t.2.1).prod

/-- **Pocklington's criterion**, in the form used by the checker. -/
theorem pocklington {N : Nat} (hN : 2 ≤ N) (ws : List (Nat × Nat × Nat))
    (hprime : ∀ t ∈ ws, t.1.Prime)
    (hnodup : (ws.map Prod.fst).Nodup)
    (hdvd : ∀ t ∈ ws, t.1 ^ t.2.1 ∣ N - 1)
    (hbig : N < factoredPart ws ^ 2)
    (hwit : ∀ t ∈ ws, ∀ p, p.Prime → p ∣ N →
      (t.2.2 : ZMod p) ^ (N - 1) = 1 ∧ (t.2.2 : ZMod p) ^ ((N - 1) / t.1) ≠ 1) :
    N.Prime := by
  by_contra hnp
  have hp : N.minFac.Prime := Nat.minFac_prime (by omega)
  have hpN : N.minFac ∣ N := Nat.minFac_dvd N
  have hsq : N.minFac ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) hnp
  have hco : (ws.map fun t => t.1 ^ t.2.1).Pairwise Nat.Coprime := by
    rw [List.pairwise_map]
    have hne : ws.Pairwise (fun a b => a.1 ≠ b.1) := by
      have := hnodup
      rw [List.Nodup, List.pairwise_map] at this
      exact this
    refine List.Pairwise.imp_of_mem ?_ hne
    intro a b ha hb hab
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hprime a ha) (hprime b hb)).mpr hab)
  have hF : factoredPart ws ∣ N.minFac - 1 := by
    apply list_prod_dvd_of_coprime hco
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    obtain ⟨h1, h2⟩ := hwit t ht N.minFac hp hpN
    exact prime_pow_dvd_sub_one hp (hprime t ht) (hdvd t ht) h1 h2
  have h2 := hp.two_le
  have hFle : factoredPart ws ≤ N.minFac - 1 := Nat.le_of_dvd (by omega) hF
  have hlt : factoredPart ws ^ 2 < N.minFac ^ 2 :=
    Nat.pow_lt_pow_left (by omega) (by norm_num)
  omega

/-! ## Executable certificates -/

/-- One witness check: `a^(n-1) ≡ 1` and `gcd(a^((n-1)/q) - 1, n) = 1`. -/
def witnessOK (n q a : Nat) : Bool :=
  powMod a (n - 1) n == 1 % n &&
  Nat.gcd ((powMod a ((n - 1) / q) n + n - 1) % n) n == 1

/-- Translate a successful witness check into the hypotheses of `pocklington`. -/
theorem witnessOK_sound {n q a : Nat} (hn : 2 ≤ n) (h : witnessOK n q a = true)
    {p : Nat} (hp : p.Prime) (hpn : p ∣ n) :
    (a : ZMod p) ^ (n - 1) = 1 ∧ (a : ZMod p) ^ ((n - 1) / q) ≠ 1 := by
  simp only [witnessOK, Bool.and_eq_true, beq_iff_eq, powMod_eq] at h
  obtain ⟨hfull, hgcd⟩ := h
  constructor
  · have hmod : a ^ (n - 1) % p = 1 % p := Nat.ModEq.of_dvd hpn hfull
    have := (ZMod.natCast_eq_natCast_iff' (a ^ (n - 1)) 1 p).mpr hmod
    simpa using this
  · intro hone
    -- x = a^((n-1)/q) mod n is ≡ 1 mod p, so p divides the gcd argument.
    set x := a ^ ((n - 1) / q) % n with hx
    have hxp : (x : ZMod p) = 1 := by
      have hm : x % p = a ^ ((n - 1) / q) % p := Nat.mod_mod_of_dvd _ hpn
      have := (ZMod.natCast_eq_natCast_iff' x (a ^ ((n - 1) / q)) p).mpr hm
      rw [this]
      push_cast
      exact hone
    have htp : (((x + n - 1) % n : Nat) : ZMod p) = 0 := by
      have hm : (x + n - 1) % n % p = (x + n - 1) % p := Nat.mod_mod_of_dvd _ hpn
      rw [(ZMod.natCast_eq_natCast_iff' _ _ p).mpr hm]
      have hn0 : ((n : Nat) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hpn
      rw [Nat.cast_sub (by omega), Nat.cast_add, hxp, hn0]
      simp
    have hdvd1 : p ∣ (x + n - 1) % n := (ZMod.natCast_eq_zero_iff _ p).mp htp
    have : p ∣ Nat.gcd ((x + n - 1) % n) n := Nat.dvd_gcd hdvd1 hpn
    rw [hgcd] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- A Pocklington step: prove `n` prime from witnesses `(q, e, a)`. Each `q`
must be proved prime earlier in the certificate or be small enough for the
verified trial division. -/
structure Step where
  n : Nat
  witnesses : List (Nat × Nat × Nat)
  deriving Repr, Inhabited

/-- Bound below which a witness prime may be certified by exact trial division. -/
def smallBound : Nat := 2 ^ 32

/-- A factor-prime is acceptable if already proved or small and verified. -/
def knownPrime (known : List Nat) (q : Nat) : Bool :=
  known.contains q || (decide (q < smallBound) && smallPrime q)

theorem knownPrime_sound {known : List Nat} (hk : ∀ p ∈ known, p.Prime) {q : Nat}
    (h : knownPrime known q = true) : q.Prime := by
  simp only [knownPrime, Bool.or_eq_true, List.contains_iff_mem, Bool.and_eq_true,
    decide_eq_true_eq] at h
  rcases h with h | ⟨_, h⟩
  · exact hk q h
  · exact smallPrime_sound h

/-- The executable acceptance test for one step. -/
def Step.check (s : Step) (known : List Nat) : Bool :=
  decide (2 ≤ s.n) &&
  decide ((s.witnesses.map Prod.fst).Nodup) &&
  s.witnesses.all (fun t =>
    knownPrime known t.1 && (s.n - 1) % (t.1 ^ t.2.1) == 0 && witnessOK s.n t.1 t.2.2) &&
  decide (s.n < factoredPart s.witnesses ^ 2)

/-- Accepted steps prove primality, assuming only that earlier values were prime. -/
theorem Step.check_sound (s : Step) (known : List Nat) (hk : ∀ p ∈ known, p.Prime)
    (h : s.check known = true) : s.n.Prime := by
  simp only [Step.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at h
  obtain ⟨⟨⟨hn, hnodup⟩, hall⟩, hbig⟩ := h
  apply pocklington hn s.witnesses
  · intro t ht
    exact knownPrime_sound hk (hall t ht).1.1
  · exact hnodup
  · intro t ht
    exact Nat.dvd_of_mod_eq_zero (hall t ht).1.2
  · exact hbig
  · intro t ht p hp hpn
    exact witnessOK_sound hn (hall t ht).2 hp hpn

/-- Verify a dependency-ordered list of steps; the result lists proved primes. -/
def verifySteps : List Step → List Nat → Option (List Nat)
  | [], known => some known
  | s :: rest, known => if s.check known then verifySteps rest (s.n :: known) else none

theorem verifySteps_sound (steps : List Step) (known result : List Nat)
    (hk : ∀ p ∈ known, p.Prime) (h : verifySteps steps known = some result) :
    ∀ p ∈ result, p.Prime := by
  induction steps generalizing known with
  | nil =>
    simp only [verifySteps, Option.some.injEq] at h
    subst result
    exact hk
  | cons s rest ih =>
    simp only [verifySteps] at h
    split_ifs at h with hs
    apply ih (s.n :: known) ?_ h
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact s.check_sound known hk hs
    · exact hk p hp

/-- A certificate for `n`: small values are decided by verified trial division,
larger ones by Pocklington steps ending in `n`. -/
structure Certificate where
  n : Nat
  steps : List Step
  deriving Repr, Inhabited

def Certificate.check (c : Certificate) : Bool :=
  if c.n < smallBound then smallPrime c.n
  else match verifySteps c.steps [] with
    | none => false
    | some proved => proved.contains c.n

theorem Certificate.check_sound (c : Certificate) (h : c.check = true) : c.n.Prime := by
  unfold Certificate.check at h
  split_ifs at h
  · exact smallPrime_sound h
  · split at h
    · contradiction
    · rename_i proved hv
      exact verifySteps_sound c.steps [] proved (by simp) hv c.n
        (List.contains_iff_mem.mp h)

/-! ## Untrusted certificate generation -/

/-- Multiplicity of `q` in `m` (with fuel), and the cofactor. -/
def stripFactor (m q : Nat) : Nat × Nat := Id.run do
  let mut m := m
  let mut e := 0
  if q < 2 then return (m, 0)
  while m > 0 && m % q == 0 do
    m := m / q
    e := e + 1
  return (m, e)

/-- Find a witness `a` for `(n, q)` among small bases. -/
def findWitness (n q : Nat) (bound : Nat := 200) : Option Nat :=
  (List.range bound).find? (fun i => witnessOK n q (i + 2)) |>.map (· + 2)

/-- Partially factor `m = n - 1` until the factored part exceeds `√n`.
Returns prime candidates with multiplicities (unproved; the checker decides). -/
def partialFactor (split : Nat → Option Nat) (smallPrimes : Array Nat)
    (n : Nat) : Option (List (Nat × Nat)) := Id.run do
  let mut m := n - 1
  let mut found : List (Nat × Nat) := []
  let mut part := 1
  for p in smallPrimes do
    if m % p == 0 then
      let (m', e) := stripFactor m p
      m := m'
      found := (p, e) :: found
      part := part * p ^ e
    if m == 1 then break
  -- Peel larger prime factors from the cofactor until F² > n.
  let mut work : List Nat := if m > 1 then [m] else []
  let mut fuel := 64
  while part * part ≤ n && !work.isEmpty && fuel > 0 do
    fuel := fuel - 1
    match work with
    | [] => break
    | c :: rest =>
      work := rest
      if c ≤ 1 then continue
      if isProbablePrime c then
        let (m', e) := stripFactor m c
        if e > 0 then
          m := m'
          found := (c, e) :: found
          part := part * c ^ e
      else
        match split c with
        | some d =>
          if 1 < d && d < c && c % d == 0 then
            -- Prefer to handle the smaller piece first (cheaper certificates).
            let a := min d (c / d)
            let b := max d (c / d)
            work := a :: b :: work
          else continue
        | none => continue
  if part * part > n then return some found else return none

/-- Recursively build dependency-ordered Pocklington steps for `n`. -/
def generateSteps (split : Nat → Option Nat) (smallPrimes : Array Nat) :
    Nat → Nat → Option (List Step)
  | 0, _ => none
  | fuel + 1, n =>
    if n < smallBound then
      if smallPrime n then some [] else none
    else if !isProbablePrime n then none
    else do
      let found ← partialFactor split smallPrimes n
      -- Use the fewest large primes: sort by size and keep a prefix reaching √n.
      let sorted := found.mergeSort (fun a b => a.1 ≤ b.1)
      let mut chosen : List (Nat × Nat) := []
      let mut part := 1
      for (q, e) in sorted do
        if part * part > n then break
        chosen := (q, e) :: chosen
        part := part * q ^ e
      let mut steps : List Step := []
      let mut witnesses : List (Nat × Nat × Nat) := []
      for (q, e) in chosen.reverse do
        if q ≥ smallBound then
          let sub ← generateSteps split smallPrimes fuel q
          steps := steps ++ sub
        let a ← findWitness n q
        witnesses := witnesses ++ [(q, e, a)]
      return steps ++ [⟨n, witnesses⟩]

/-- Package steps as a certificate for `n`, accepting it only if it checks. -/
def checked (n : Nat) (steps : List Step) : Option Certificate :=
  let c : Certificate := ⟨n, steps⟩
  if c.check then some c else none

theorem checked_sound {n : Nat} {steps : List Step} {c : Certificate}
    (h : checked n steps = some c) : c.n = n ∧ c.n.Prime := by
  unfold checked at h
  dsimp only at h
  split_ifs at h with hc
  cases h
  exact ⟨rfl, Certificate.check_sound _ hc⟩

/-- Generate a certificate and check it before returning. -/
def generate (split : Nat → Option Nat) (n : Nat) (fuel : Nat := 64) : Option Certificate :=
  (if n < smallBound then some [] else generateSteps split (primesUpTo 65536) fuel n).bind
    (checked n)

theorem generate_sound {split : Nat → Option Nat} {n fuel : Nat} {c : Certificate}
    (h : generate split n fuel = some c) : c.n = n ∧ c.n.Prime := by
  unfold generate at h
  obtain ⟨steps, _, hc⟩ := Option.bind_eq_some_iff.mp h
  exact checked_sound hc

/-- A proof-producing primality oracle for the verified factorization engine. -/
def oracle (split : Nat → Option Nat) (fuel : Nat := 64) (n : Nat) :
    Option {_u : Unit // n.Prime} :=
  if n < smallBound then
    if h : smallPrime n = true then some ⟨(), smallPrime_sound h⟩ else none
  else if isProbablePrime n then
    match h : generate split n fuel with
    | none => none
    | some _ =>
      have hc := generate_sound h
      some ⟨(), hc.1 ▸ hc.2⟩
  else none

end PrimeFactorLean.Pocklington
