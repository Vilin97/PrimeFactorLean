import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.GCD.BigOperators
import PrimeFactorLean.Proofs.Arith
import PrimeFactorLean.Pocklington

/-! Proof layer: see the runtime module for documentation. -/

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

theorem factoredPart_eq (ws : List (Nat × Nat × Nat)) :
    factoredPart ws = (ws.map fun t => t.1 ^ t.2.1).prod := rfl

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

/-- Under the witness conditions every prime factor `p` of `N` has `F ∣ p - 1`. -/
theorem factoredPart_dvd_sub_one {N : Nat} (ws : List (Nat × Nat × Nat))
    (hprime : ∀ t ∈ ws, t.1.Prime) (hnodup : (ws.map Prod.fst).Nodup)
    (hdvd : ∀ t ∈ ws, t.1 ^ t.2.1 ∣ N - 1)
    (hwit : ∀ t ∈ ws, ∀ p, p.Prime → p ∣ N →
      (t.2.2 : ZMod p) ^ (N - 1) = 1 ∧ (t.2.2 : ZMod p) ^ ((N - 1) / t.1) ≠ 1)
    {p : Nat} (hp : p.Prime) (hpN : p ∣ N) : factoredPart ws ∣ p - 1 := by
  have hco : (ws.map fun t => t.1 ^ t.2.1).Pairwise Nat.Coprime := by
    rw [List.pairwise_map]
    have hne : ws.Pairwise (fun a b => a.1 ≠ b.1) := by
      have := hnodup
      rw [List.Nodup, List.pairwise_map] at this
      exact this
    refine List.Pairwise.imp_of_mem ?_ hne
    intro a b ha hb hab
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hprime a ha) (hprime b hb)).mpr hab)
  apply list_prod_dvd_of_coprime hco
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  obtain ⟨h1, h2⟩ := hwit t ht p hp hpN
  exact prime_pow_dvd_sub_one hp (hprime t ht) (hdvd t ht) h1 h2

/-- The factored part divides `N - 1`. -/
theorem factoredPart_dvd {N : Nat} (ws : List (Nat × Nat × Nat))
    (hprime : ∀ t ∈ ws, t.1.Prime) (hnodup : (ws.map Prod.fst).Nodup)
    (hdvd : ∀ t ∈ ws, t.1 ^ t.2.1 ∣ N - 1) : factoredPart ws ∣ N - 1 := by
  have hco : (ws.map fun t => t.1 ^ t.2.1).Pairwise Nat.Coprime := by
    rw [List.pairwise_map]
    have hne : ws.Pairwise (fun a b => a.1 ≠ b.1) := by
      have := hnodup
      rw [List.Nodup, List.pairwise_map] at this
      exact this
    refine List.Pairwise.imp_of_mem ?_ hne
    intro a b ha hb hab
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hprime a ha) (hprime b hb)).mpr hab)
  apply list_prod_dvd_of_coprime hco
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  exact hdvd t ht

/-- The integer square root of a perfect square. -/
theorem isqrt_mul_self (d : Nat) : isqrt (d * d) = d := by
  have h := isqrt_spec (d * d)
  apply le_antisymm
  · by_contra hc
    push_neg at hc
    have : (d + 1) * (d + 1) ≤ isqrt (d * d) * isqrt (d * d) := Nat.mul_self_le_mul_self hc
    nlinarith [h.1]
  · by_contra hc
    push_neg at hc
    have : (isqrt (d * d) + 1) * (isqrt (d * d) + 1) ≤ d * d := Nat.mul_self_le_mul_self hc
    nlinarith [h.2]

/-- The quadratic with roots `a` and `b` has a square discriminant. -/
theorem squareDiscriminant_sum_prod (a b : Nat) :
    squareDiscriminant (a + b) (a * b) = true := by
  set d := if b ≤ a then a - b else b - a with hd
  have hdd : (a + b) * (a + b) - 4 * (a * b) = d * d := by
    rw [hd]; split_ifs with h
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [show b + c - b = c by omega]
      ring_nf; omega
    · push_neg at h
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt h
      rw [show a + c + 1 - a = c + 1 by omega]
      ring_nf; omega
  have h4 : 4 * (a * b) ≤ (a + b) * (a + b) := by nlinarith [sq_nonneg ((a : Int) - b)]
  simp only [squareDiscriminant, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨h4, by rw [hdd, isqrt_mul_self]⟩

/-- **Brillhart–Lehmer–Selfridge** (1975, Theorem 5): a factored part `F` of
`N - 1` with `F³ > N` suffices, if the quadratic check `cubeTest` passes. -/
theorem pocklington_cube {N : Nat} (hN : 2 ≤ N) (ws : List (Nat × Nat × Nat))
    (hprime : ∀ t ∈ ws, t.1.Prime)
    (hnodup : (ws.map Prod.fst).Nodup)
    (hdvd : ∀ t ∈ ws, t.1 ^ t.2.1 ∣ N - 1)
    (hcube : N < factoredPart ws ^ 3)
    (htest : cubeTest N (factoredPart ws) = true)
    (hwit : ∀ t ∈ ws, ∀ p, p.Prime → p ∣ N →
      (t.2.2 : ZMod p) ^ (N - 1) = 1 ∧ (t.2.2 : ZMod p) ^ ((N - 1) / t.1) ≠ 1) :
    N.Prime := by
  set F := factoredPart ws with hFdef
  have hone : ∀ p, p.Prime → p ∣ N → F + 1 ≤ p ∧ F ∣ p - 1 := by
    intro p hp hpN
    have h := factoredPart_dvd_sub_one ws hprime hnodup hdvd hwit hp hpN
    have h2 := hp.two_le
    exact ⟨by have := Nat.le_of_dvd (by omega) h; omega, h⟩
  have hF2 : 2 ≤ F := by
    by_contra h
    push_neg at h
    have : F ^ 3 ≤ 1 := by
      rcases (show F = 0 ∨ F = 1 by omega) with h0 | h1
      · rw [h0]; norm_num
      · rw [h1]; norm_num
    omega
  by_contra hnp
  have hp : N.minFac.Prime := Nat.minFac_prime (by omega)
  have hsq : N.minFac ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) hnp
  obtain ⟨q, hq⟩ := Nat.minFac_dvd N
  set p := N.minFac with hpdef
  have hp2 := hp.two_le
  have hpq : p ≤ q := by
    by_contra h
    push_neg at h
    have : p * q < p * p := Nat.mul_lt_mul_of_pos_left h (by omega)
    nlinarith
  have hpF := (hone p hp ⟨q, hq⟩).1
  have hqprime : q.Prime := by
    by_contra hqn
    have hq2 : 2 ≤ q := le_trans hp2 hpq
    have hr : q.minFac.Prime := Nat.minFac_prime (by omega)
    have hr2 : q.minFac ^ 2 ≤ q := Nat.minFac_sq_le_self (by omega) hqn
    have hrN : q.minFac ∣ N := hq ▸ Dvd.dvd.mul_left (Nat.minFac_dvd q) p
    have hrF := (hone q.minFac hr hrN).1
    have h3 : (F + 1) ^ 3 ≤ N := by
      calc (F + 1) ^ 3 = (F + 1) * (F + 1) ^ 2 := by ring
        _ ≤ p * q.minFac ^ 2 := Nat.mul_le_mul hpF (Nat.pow_le_pow_left hrF 2)
        _ ≤ p * q := Nat.mul_le_mul_left p hr2
        _ = N := hq.symm
    have : F ^ 3 < (F + 1) ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)
    omega
  obtain ⟨a, ha⟩ := (hone p hp ⟨q, hq⟩).2
  obtain ⟨b, hb⟩ := (hone q hqprime ⟨p, by rw [hq, mul_comm]⟩).2
  have hq2 := hqprime.two_le
  have hp' : p = F * a + 1 := by omega
  have hq' : q = F * b + 1 := by omega
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h] at hp'; omega
    · exact h
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h] at hq'; omega
    · exact h
  have hN1 : N - 1 = F * (a * b * F + a + b) := by
    rw [hq, hp', hq']
    have : (F * a + 1) * (F * b + 1) = F * (a * b * F + a + b) + 1 := by ring
    omega
  have hR : (N - 1) / F = a * b * F + a + b := by
    rw [hN1, Nat.mul_div_cancel_left _ (by omega)]
  have hab : a * b < F := by
    by_contra h
    push_neg at h
    have : F * F * F ≤ F * F * (a * b) := Nat.mul_le_mul_left _ h
    have hN' : N = F * F * (a * b) + F * (a + b) + 1 := by rw [hq, hp', hq']; ring
    have : F ^ 3 = F * F * F := by ring
    omega
  have hsum : a + b ≤ F := by
    have : a + b ≤ a * b + 1 := by nlinarith
    omega
  unfold cubeTest at htest
  simp only [hR, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq] at htest
  rcases Nat.lt_or_ge (a + b) F with hlt | hge
  · have h1 : (a * b * F + a + b) / F = a * b := by
      rw [show a * b * F + a + b = (a + b) + F * (a * b) by ring,
        Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hlt, zero_add]
    have h2 : (a * b * F + a + b) % F = a + b := by
      rw [show a * b * F + a + b = (a + b) + F * (a * b) by ring, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hlt]
    rw [h1, h2, squareDiscriminant_sum_prod] at htest
    exact absurd htest.1 (by simp)
  · have heq : a + b = F := le_antisymm hsum hge
    have h1 : (a * b * F + a + b) / F = a * b + 1 := by
      rw [show a * b * F + a + b = 0 + F * (a * b + 1) by rw [← heq]; ring,
        Nat.add_mul_div_left _ _ (by omega), Nat.zero_div, zero_add]
    have h2 : (a * b * F + a + b) % F = 0 := by
      rw [show a * b * F + a + b = 0 + F * (a * b + 1) by rw [← heq]; ring,
        Nat.add_mul_mod_self_left, Nat.zero_mod]
    rw [h1, h2] at htest
    have h3 : squareDiscriminant (0 + F) (a * b + 1 - 1) = true := by
      rw [zero_add, Nat.add_sub_cancel, ← heq]
      exact squareDiscriminant_sum_prod a b
    rcases htest.2 with h | h
    · omega
    · rw [h3] at h; exact absurd h (by simp)

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

theorem knownPrime_sound {known : List Nat} (hk : ∀ p ∈ known, p.Prime) {q : Nat}
    (h : knownPrime known q = true) : q.Prime := by
  simp only [knownPrime, Bool.or_eq_true, List.contains_iff_mem, Bool.and_eq_true,
    decide_eq_true_eq] at h
  rcases h with h | ⟨_, h⟩
  · exact hk q h
  · exact smallPrime_sound h

/-- Accepted steps prove primality, assuming only that earlier values were prime. -/
theorem Step.check_sound (s : Step) (known : List Nat) (hk : ∀ p ∈ known, p.Prime)
    (h : s.check known = true) : s.n.Prime := by
  simp only [Step.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨hn, hnodup⟩, hall⟩, hbig⟩ := h
  have hprime : ∀ t ∈ s.witnesses, t.1.Prime := fun t ht => knownPrime_sound hk (hall t ht).1.1
  have hdvd : ∀ t ∈ s.witnesses, t.1 ^ t.2.1 ∣ s.n - 1 :=
    fun t ht => Nat.dvd_of_mod_eq_zero (hall t ht).1.2
  have hwit := fun t ht p hp hpn => witnessOK_sound hn (hall t ht).2 (p := p) hp hpn
  rcases hbig with hsq | ⟨hcube, htest⟩
  · exact pocklington hn s.witnesses hprime hnodup hdvd hsq hwit
  · exact pocklington_cube hn s.witnesses hprime hnodup hdvd hcube htest hwit

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

theorem Certificate.check_sound (c : Certificate) (h : c.check = true) : c.n.Prime := by
  unfold Certificate.check at h
  split_ifs at h
  · exact smallPrime_sound h
  · split at h
    · contradiction
    · rename_i proved hv
      exact verifySteps_sound c.steps [] proved (by simp) hv c.n
        (List.contains_iff_mem.mp h)

theorem checked_sound {n : Nat} {steps : List Step} {c : Certificate}
    (h : checked n steps = some c) : c.n = n ∧ c.n.Prime := by
  unfold checked at h
  dsimp only at h
  split_ifs at h with hc
  cases h
  exact ⟨rfl, Certificate.check_sound _ hc⟩

theorem generate_sound {split : Nat → Option Nat} {n fuel : Nat} {c : Certificate}
    (h : generate split n fuel = some c) : c.n = n ∧ c.n.Prime := by
  unfold generate at h
  obtain ⟨steps, _, hc⟩ := Option.bind_eq_some_iff.mp h
  exact checked_sound hc

/-- The Boolean primality checker of the factorization engine accepts only primes. -/
theorem oracle_sound {split : Nat → Option Nat} {fuel n : Nat}
    (h : oracle split fuel n = true) : n.Prime := by
  unfold oracle at h
  split at h
  · exact Arith.smallPrime_sound h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨_, hg⟩ := h
    cases hc : generate split n fuel with
    | none => simp [hc] at hg
    | some c =>
      have := generate_sound hc
      exact this.1 ▸ this.2

end PrimeFactorLean.Pocklington
