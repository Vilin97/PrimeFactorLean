import PrimeFactorLean.Core
import PrimeFactorLean.Trial
import PrimeFactorLean.Search
import PrimeFactorLean.ECM
import PrimeFactorLean.QuadraticSieve
import PrimeFactorLean.Primality
import PrimeFactorLean.NumberFieldSieve
import PrimeFactorLean.CubicNumberFieldSieve

/-!
# Public algorithms and their exact specification

Probable-prime tests below only guide untrusted certificate construction.
Every prime leaf in `factor` is justified either by the kernel-proved Pratt
checker or by exact trial division. No probable-prime test is trusted.
-/
namespace PrimeFactorLean

inductive Algorithm where
  | trialReference | trial | wheel | fermat | rho | brent | pMinusOne | ecm | qs | mpqs | nfsQuadratic | nfsCubic | auto
  deriving Repr, Inhabited, DecidableEq

def Algorithm.name : Algorithm → String
  | .trialReference => "trial-reference"
  | .trial => "trial"
  | .wheel => "wheel"
  | .fermat => "fermat"
  | .rho => "rho"
  | .brent => "brent"
  | .pMinusOne => "pminusone"
  | .ecm => "ecm"
  | .qs => "qs"
  | .mpqs => "mpqs"
  | .nfsQuadratic => "nfs-quadratic"
  | .nfsCubic => "nfs-cubic"
  | .auto => "auto"

def Algorithm.parse : String → Option Algorithm
  | "trial-reference" => some .trialReference
  | "trial" => some .trial
  | "wheel" => some .wheel
  | "fermat" => some .fermat
  | "rho" => some .rho
  | "brent" => some .brent
  | "pminusone" => some .pMinusOne
  | "ecm" => some .ecm
  | "qs" => some .qs
  | "mpqs" => some .mpqs
  | "nfs-quadratic" => some .nfsQuadratic
  | "nfs-cubic" => some .nfsCubic
  | "auto" => some .auto
  | _ => none

/-- Remove powers of two; fuel is deliberately explicit. -/
def twoPart : Nat → Nat → Nat × Nat
  | 0, d => (d, 0)
  | fuel + 1, d =>
    if d > 0 && d % 2 == 0 then
      let r := twoPart fuel (d / 2)
      (r.1, r.2 + 1)
    else (d, 0)

def strongScreenLoop (n : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | k + 1, x =>
    let y := x * x % n
    if y == n - 1 then true else strongScreenLoop n k y

/-- A rejection/branching heuristic, never an assertion of primality. -/
def probablePrime (n : Nat) : Bool :=
  if n < 2 then false else
  if n == 2 || n == 3 then true else
  if n % 2 == 0 then false else
  let ds := twoPart 256 (n - 1)
  [2, 325, 9375, 28178, 450775, 9780504, 1795265022].all fun a =>
    if a % n == 0 then true else
      let x := Search.modPow a ds.1 n
      x == 1 || x == n - 1 || strongScreenLoop n (ds.2 - 1) x

/-- The automatic portfolio tries increasingly expensive bounded searches. -/
def portfolio (n : Nat) (cfg : Search.Config := {}) : Option Nat :=
  (trialSearchAux n 2 63).orElse fun _ =>
    (Search.fermat n {cfg with fermatSteps := min cfg.fermatSteps 128}).orElse fun _ =>
      (Search.brent n cfg).orElse fun _ =>
        (Search.pMinusOne n cfg).orElse fun _ =>
          (ECM.split n cfg.ecmBound cfg.ecmCurves).orElse fun _ =>
            QuadraticSieve.split n cfg.qsBound cfg.qsIntervals

def rawSearch (algorithm : Algorithm) (cfg : Search.Config := {}) : Nat → Option Nat :=
  match algorithm with
  | .trialReference => trialSearchReference
  | .trial => trialSearch
  | .wheel => trialWheelSearch
  | .fermat => fun n => Search.fermat n cfg
  | .rho => fun n => Search.rho n cfg
  | .brent => fun n => Search.brent n cfg
  | .pMinusOne => fun n => Search.pMinusOne n cfg
  | .ecm => fun n => ECM.split n cfg.ecmBound cfg.ecmCurves
  | .qs => fun n => QuadraticSieve.split n cfg.qsBound cfg.qsIntervals
  | .mpqs => fun n => QuadraticSieve.splitMPQS n
  | .nfsQuadratic => fun n => NumberFieldSieve.split n
  | .nfsCubic => fun n => CubicNumberFieldSieve.split n
  | .auto => fun n => portfolio n cfg

/-- Untrusted prime-factor candidates used solely by certificate generation.
It is safe to stop on a probable prime: the resulting certificate is checked.
-/
def candidateFactors (cfg : Search.Config) : Nat → Nat → List Nat
  | 0, n => if n ≤ 1 then [] else [n]
  | fuel + 1, n =>
    if n ≤ 1 then [] else
    if probablePrime n then [n] else
      match portfolio n cfg with
      | none => [n]
      | some d =>
        if 1 < d && d < n && n % d == 0 then
          candidateFactors cfg fuel d ++ candidateFactors cfg fuel (n / d)
        else [n]

def algorithmPrimeOracle (cfg : Search.Config := {}) : PrimeOracle := fun n =>
  if probablePrime n then
    prattOracle (candidateFactors cfg 64) 64 256 n
  else none

/-- All nonzero inputs receive a complete factorization. Searches may fall back.
The two trial implementations remain independent, certificate-free baselines.
-/
def factor (algorithm : Algorithm) (n : Nat) (cfg : Search.Config := {}) :
    Option (List Nat) :=
  if n = 0 then none else
    match algorithm with
    | .trialReference => some (factorCore trialSplitterReference n)
    | .trial => some (trialCore n)
    | .wheel => some (trialWheelCore n)
    | _ => some (factorCoreWith (algorithmPrimeOracle cfg) (checkedSplitter (rawSearch algorithm cfg)) n)

/-- The same universal theorem covers each named executable implementation. -/
theorem factor_correct (algorithm : Algorithm) (n : Nat) (cfg : Search.Config)
    (factors : List Nat) (h : factor algorithm n cfg = some factors) :
    IsFactorization n factors := by
  unfold factor at h
  split at h
  · contradiction
  · rename_i hn
    cases algorithm <;> simp only [Option.some.injEq] at h
    all_goals subst factors
    · exact factorCore_correct trialSplitterReference n hn
    · exact trialCore_correct n hn
    · exact trialWheelCore_correct n hn
    all_goals exact factorCoreWith_correct _ _ n hn

/-- Every positive input finishes with a complete prime factorization. -/
theorem factor_total_correct (algorithm : Algorithm) (n : Nat) (cfg : Search.Config)
    (hn : n ≠ 0) :
    ∃ ps, factor algorithm n cfg = some ps ∧ IsFactorization n ps := by
  cases hf : factor algorithm n cfg with
  | none => cases algorithm <;> simp [factor, hn] at hf
  | some ps => exact ⟨ps, rfl, factor_correct algorithm n cfg ps hf⟩

@[simp] theorem factor_zero (algorithm : Algorithm) (cfg : Search.Config) :
    factor algorithm 0 cfg = none := by simp [factor]

/-- Signed factorization with the same verified natural-number implementation. -/
def factorSigned (algorithm : Algorithm) (z : Int) (cfg : Search.Config := {}) :
    Option (Int × List Nat) :=
  (factor algorithm z.natAbs cfg).map fun ps => (z.sign, ps)

theorem factorSigned_correct (algorithm : Algorithm) (z : Int) (cfg : Search.Config)
    (sign : Int) (ps : List Nat)
    (h : factorSigned algorithm z cfg = some (sign, ps)) :
    IsIntFactorization z sign ps := by
  unfold factorSigned at h
  cases hf : factor algorithm z.natAbs cfg with
  | none => simp [hf] at h
  | some fs =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    have hc := factor_correct algorithm z.natAbs cfg fs hf
    cases h
    have hz : z ≠ 0 := by
      intro hz
      subst z
      simp [factor] at hf
    refine ⟨?_, hc.1, ?_⟩
    · by_cases hpos : 0 < z
      · exact Or.inl (Int.sign_eq_one_of_pos hpos)
      · exact Or.inr (Int.sign_eq_neg_one_of_neg (by omega))
    · rw [hc.2]
      exact Int.sign_mul_natAbs z

theorem factorSigned_total_correct (algorithm : Algorithm) (z : Int)
    (cfg : Search.Config) (hz : z ≠ 0) :
    ∃ sign ps, factorSigned algorithm z cfg = some (sign, ps) ∧
      IsIntFactorization z sign ps := by
  obtain ⟨ps, hf, _⟩ := factor_total_correct algorithm z.natAbs cfg
    (Int.natAbs_ne_zero.mpr hz)
  have hi : factorSigned algorithm z cfg = some (z.sign, ps) := by
    simp [factorSigned, hf]
  exact ⟨z.sign, ps, hi, factorSigned_correct algorithm z cfg z.sign ps hi⟩

end PrimeFactorLean
