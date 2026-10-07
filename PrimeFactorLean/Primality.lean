import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.List.Prime
import Mathlib.Data.List.Dedup

/-!
# Executable Pratt primality certificates

A certificate is a sequence of Lucas tests in dependency order. Each step carries
the complete prime factorization of `n - 1`, with multiplicity, and a witness `a`.
The checker starts with the already proved prime 2. It accepts a step only when
every factor has been proved by an earlier step, their product is exactly `n - 1`,
and the Lucas modular-power tests hold. The complete certificate is accepted only
when its requested value occurs among the verified primes.

The producer is untrusted: all products, dependencies and modular powers are
rechecked in Lean. `PrimeCertificate.check_sound` relates every accepted
certificate to mathlib's standard `Nat.Prime`, for unrestricted natural numbers.
Modular powers use mathlib's proved binary-exponentiation compiler optimization
(`npowRec_eq_npowBinRec`), so verification has no trial-division primality calls.
-/

namespace PrimeFactorLean

/-- One Lucas/Pratt certificate step. Factors include their multiplicities. -/
structure LucasStep where
  value : Nat
  witness : Nat
  factors : List Nat
  deriving Repr, Inhabited

/-- Executable Lucas criterion against primes established by earlier steps. -/
def LucasStep.check (s : LucasStep) (known : List Nat) : Bool :=
  decide (2 ≤ s.value) &&
  decide (s.factors.prod = s.value - 1) &&
  s.factors.dedup.all (fun q => decide (q ∈ known)) &&
  decide ((s.witness : ZMod s.value) ^ (s.value - 1) = 1) &&
  s.factors.dedup.all (fun q =>
    decide ((s.witness : ZMod s.value) ^ ((s.value - 1) / q) ≠ 1))

/-- A successful step proves primality; no assumption about the producer is used. -/
theorem LucasStep.check_sound (s : LucasStep) (known : List Nat)
    (hk : ∀ p ∈ known, Nat.Prime p) (h : s.check known = true) :
    Nat.Prime s.value := by
  simp only [LucasStep.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  rcases h with ⟨⟨⟨⟨_, hprod⟩, hknown⟩, hpow⟩, hdiv⟩
  apply lucas_primality s.value (s.witness : ZMod s.value) hpow
  intro q hq hqd
  have hfactors : ∀ p ∈ s.factors, _root_.Prime p := by
    intro p hp
    exact (hk p (hknown p (List.mem_dedup.mpr hp))).prime
  have hqmem : q ∈ s.factors :=
    mem_list_primes_of_dvd_prod hq.prime hfactors (hprod.symm ▸ hqd)
  exact hdiv q (List.mem_dedup.mpr hqmem)

/-- Verify a dependency-ordered list of steps. An invalid step rejects everything. -/
def verifyLucasSteps : List LucasStep → List Nat → Option (List Nat)
  | [], known => some known
  | s :: rest, known =>
      if s.check known then verifyLucasSteps rest (s.value :: known) else none

/-- Every number returned by the verifier is prime if its initial seed is prime. -/
theorem verifyLucasSteps_sound (steps : List LucasStep) (known result : List Nat)
    (hk : ∀ p ∈ known, Nat.Prime p)
    (h : verifyLucasSteps steps known = some result) :
    ∀ p ∈ result, Nat.Prime p := by
  induction steps generalizing known with
  | nil =>
      simp only [verifyLucasSteps, Option.some.injEq] at h
      subst result
      exact hk
  | cons s rest ih =>
      by_cases hs : s.check known = true
      · simp only [verifyLucasSteps, hs, ↓reduceIte] at h
        apply ih (s.value :: known) ?_ h
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact s.check_sound known hk hs
        · exact hk p hp
      · simp only [verifyLucasSteps, hs] at h
        contradiction

/-- A shared-dependency Pratt certificate for an arbitrary natural number. -/
structure PrimeCertificate where
  value : Nat
  steps : List LucasStep
  deriving Repr, Inhabited

/-- Check a certificate using only 2 as the trusted, mathematically proved seed. -/
def PrimeCertificate.check (c : PrimeCertificate) : Bool :=
  match verifyLucasSteps c.steps [2] with
  | none => false
  | some verified => decide (c.value ∈ verified)

/-- Accepted executable certificates establish the standard definition of primality. -/
theorem PrimeCertificate.check_sound (c : PrimeCertificate) (h : c.check = true) :
    Nat.Prime c.value := by
  unfold PrimeCertificate.check at h
  cases hv : verifyLucasSteps c.steps [2] with
  | none => simp only [hv, Bool.false_eq_true] at h
  | some verified =>
      simp only [hv, decide_eq_true_eq] at h
      apply verifyLucasSteps_sound c.steps [2] verified ?_ hv c.value h
      intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      exact Nat.prime_two

/-- A cheap rejection-only filter. Passing this test is never used as a proof. -/
def fermatScreen (n : Nat) : Bool :=
  decide (2 ≤ n) &&
  [2, 3, 5, 7, 11, 13, 17].all (fun a =>
    (a % n == 0) || decide ((a : ZMod n) ^ (n - 1) = 1))

/-- Keep the first occurrence of each proved value, preserving dependency order.
This is a certificate-producer optimization; the final checker still checks it.
-/
def compactLucasSteps (steps : List LucasStep) : List LucasStep :=
  (steps.foldl (fun (acc : List LucasStep) s =>
    if acc.any (fun t => t.value == s.value) then acc else s :: acc) []).reverse

/-- Construct certificate steps using an arbitrary, untrusted factoring callback.

`fuel` limits recursive descent through factorizations of `n - 1`.
`witnessBound` bounds a deterministic search for a Lucas witness. A failure means
only that construction failed; it makes no mathematical claim about `n`.
-/
def generateLucasSteps (factor : Nat → List Nat) (witnessBound : Nat) :
    Nat → Nat → Option (List LucasStep)
  | 0, n => if n = 2 then some [] else none
  | fuel + 1, n => do
      if n = 2 then
        return []
      if !fermatScreen n then
        none
      else
        let factors := factor (n - 1)
        if factors.prod != n - 1 || factors.any (fun q => q < 2 || n ≤ q) then
          none
        else
          let children ← factors.dedup.mapM (generateLucasSteps factor witnessBound fuel)
          let steps := compactLucasSteps children.flatten
          let known := 2 :: steps.map LucasStep.value
          let witness ← (List.range witnessBound).find? (fun a =>
            (LucasStep.mk n a factors).check known)
          return steps ++ [⟨n, witness, factors⟩]

/-- Generate and then independently check a complete certificate.

No correctness assumption is imposed on the supplied factorization engine.
This final check keeps the certificate producer outside the trusted boundary.
-/
def generatePrimeCertificate (factor : Nat → List Nat) (n : Nat)
    (fuel : Nat := 64) (witnessBound : Nat := 256) : Option PrimeCertificate := do
  let steps ← generateLucasSteps factor witnessBound fuel n
  let certificate : PrimeCertificate := ⟨n, steps⟩
  if certificate.check then return certificate else none

/-- Every successfully generated certificate proves the requested value prime. -/
theorem generatePrimeCertificate_sound (factor : Nat → List Nat) (n fuel witnessBound : Nat)
    (certificate : PrimeCertificate)
    (h : generatePrimeCertificate factor n fuel witnessBound = some certificate) :
    Nat.Prime n := by
  unfold generatePrimeCertificate at h
  cases hs : generateLucasSteps factor witnessBound fuel n with
  | none =>
      simp only [hs, Option.bind_eq_bind, Option.bind_none] at h
      contradiction
  | some steps =>
      simp only [hs, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst certificate
        exact PrimeCertificate.check_sound ⟨n, steps⟩ hc
      · contradiction

/-- Proof-carrying prime oracle suitable for a certified factorization driver. -/
def prattOracle (factor : Nat → List Nat) (fuel : Nat := 64)
    (witnessBound : Nat := 256) (n : Nat) : Option {_u : Unit // Nat.Prime n} :=
  match h : generatePrimeCertificate factor n fuel witnessBound with
  | none => none
  | some certificate =>
      some ⟨(), generatePrimeCertificate_sound factor n fuel witnessBound certificate h⟩

end PrimeFactorLean
