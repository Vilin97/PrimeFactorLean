import PrimeFactorLean.Core
import PrimeFactorLean.Trial
import PrimeFactorLean.Search
import PrimeFactorLean.ECM
import PrimeFactorLean.ECMMontgomery
import PrimeFactorLean.QS
import PrimeFactorLean.GNFS
import PrimeFactorLean.SQUFOF
import PrimeFactorLean.CFRAC
import PrimeFactorLean.PMinusOne
import PrimeFactorLean.Primality
import PrimeFactorLean.Pocklington

/-!
# Public algorithms and their exact specification

Every algorithm is exposed as a *proof-carrying splitter*
`(n : Nat) → Option (ProperFactor n)`: a returned divisor comes with the proof
`1 < d ∧ d < n ∧ d ∣ n`, obtained from that algorithm's own soundness theorem
(never from a second runtime check). The verified engine `factorCoreWith`
recursively splits, certifies prime leaves with Pocklington certificates
(`Pocklington.oracle`, proved sound), and falls back to exact trial division
when a bounded search gives up. Hence `factor_total_correct` holds for every
algorithm, every configuration and every positive input.

Probable-prime tests and all factoring heuristics only guide the search; no
correctness theorem depends on them.
-/

namespace PrimeFactorLean

inductive Algorithm where
  | trialReference | trial | wheel | fermat | rho | brent | squfof | pMinusOne | pPlusOne
  | ecmAffine | ecm | cfrac | qs | mpqs | siqs | gnfs | auto
  deriving Repr, Inhabited, DecidableEq

def Algorithm.name : Algorithm → String
  | .trialReference => "trial-reference"
  | .trial => "trial"
  | .wheel => "wheel"
  | .fermat => "fermat"
  | .rho => "rho"
  | .brent => "brent"
  | .squfof => "squfof"
  | .pMinusOne => "pminusone"
  | .pPlusOne => "pplusone"
  | .ecmAffine => "ecm-affine"
  | .ecm => "ecm"
  | .cfrac => "cfrac"
  | .qs => "qs"
  | .mpqs => "mpqs"
  | .siqs => "siqs"
  | .gnfs => "gnfs"
  | .auto => "auto"

def Algorithm.all : List Algorithm :=
  [.trialReference, .trial, .wheel, .fermat, .rho, .brent, .squfof, .pMinusOne, .pPlusOne,
   .ecmAffine, .ecm, .cfrac, .qs, .mpqs, .siqs, .gnfs, .auto]

def Algorithm.parse (s : String) : Option Algorithm :=
  Algorithm.all.find? (·.name == s)

/-- Run-time configuration shared by all algorithms. -/
structure Config where
  search : Search.Config := {}
  /-- Parallel tasks used by ECM, the quadratic sieves and the number field sieve. -/
  threads : Nat := 8
  /-- Stage-one bound for `p - 1` and `p + 1`. -/
  pm1Bound : Nat := 100000
  /-- Fixed ECM `B1` (`0` selects the automatic schedule). -/
  ecmB1 : Nat := 0
  ecmCurves : Nat := 0
  deriving Inhabited

/-- Turn a raw search and its soundness theorem into a proof-carrying splitter. -/
def ofSound (search : Nat → Option Nat)
    (sound : ∀ n d, search n = some d → 1 < d ∧ d < n ∧ d ∣ n) : Splitter :=
  fun n => match h : search n with
    | some d => some ⟨d, sound n d h⟩
    | none => none

/-- Trial division by `2, …, bound` (proved by `trialSearchAux_sound`). -/
def smallSplitter (bound : Nat) : Splitter :=
  ofSound (fun n => trialSearchAux n 2 (bound - 1)) (fun _ _ h => trialSearchAux_sound h)

/-- Exact perfect powers `n = r^k`, `k ≥ 2`. -/
def powerSplitter : Splitter := fun n =>
  match h : Arith.perfectPower n with
  | some (r, _) => some ⟨r, Arith.perfectPower_proper h⟩
  | none => none

/-- `(B1, curves)` for an automatic ECM schedule, by size of `n` in digits. -/
def ecmSchedule (digits : Nat) : List (Nat × Nat) :=
  if digits ≤ 30 then [(2000, 8)]
  else if digits ≤ 45 then [(2000, 16), (11000, 32)]
  else if digits ≤ 60 then [(2000, 25), (11000, 90), (50000, 100)]
  else if digits ≤ 80 then [(2000, 25), (11000, 90), (50000, 300), (250000, 200)]
  else [(2000, 25), (11000, 90), (50000, 300), (250000, 700), (1000000, 500)]

/-- ECM over a list of `(B1, curves)` levels; the first factor wins. -/
def ecmLevels (threads : Nat) (levels : List (Nat × Nat)) : Splitter := fun n =>
  levels.foldl (fun acc (b1, curves) => acc.orElse fun _ =>
    ECMM.split n { b1 := b1, curves := curves, threads := threads }) none

/-- The automatic portfolio: cheap methods first, then ECM, then SIQS. -/
def autoSplitter (cfg : Config) : Splitter := fun n =>
  if n < 4 then none else
  (smallSplitter 4096 n).orElse fun _ =>
  (powerSplitter n).orElse fun _ =>
  (if n < 2 ^ 62 then SQUFOF.split n else none).orElse fun _ =>
  (ofSound (fun m => Search.brent m { cfg.search with rhoSteps := 20000, rhoRestarts := 2 })
    (fun _ _ h => Search.brent_sound h) n).orElse fun _ =>
  (PMinusOne.splitPMinusOne n 20000).orElse fun _ =>
  (ecmLevels cfg.threads (ecmSchedule (QS.decimalDigits n)) n).orElse fun _ =>
  QS.split n { variant := .siqs, threads := cfg.threads }

/-- The proof-carrying splitter of each algorithm. -/
def splitter (algorithm : Algorithm) (cfg : Config := {}) : Splitter :=
  match algorithm with
  | .trialReference => trialSplitterReference
  | .trial => trialSplitter
  | .wheel => trialWheelSplitter
  | .fermat => ofSound (fun n => Search.fermat n cfg.search) (fun _ _ h => Search.fermat_sound h)
  | .rho => ofSound (fun n => Search.rho n cfg.search) (fun _ _ h => Search.rho_sound h)
  | .brent => ofSound (fun n => Search.brent n cfg.search) (fun _ _ h => Search.brent_sound h)
  | .squfof => fun n => SQUFOF.split n
  | .pMinusOne => fun n => PMinusOne.splitPMinusOne n cfg.pm1Bound
  | .pPlusOne => fun n => PMinusOne.splitPPlusOne n cfg.pm1Bound
  | .ecmAffine => ofSound (fun n => ECM.split n cfg.search.ecmBound cfg.search.ecmCurves)
      (fun _ _ h => ECM.split_sound h)
  | .ecm => fun n =>
      if cfg.ecmB1 > 0 then
        ECMM.split n { b1 := cfg.ecmB1, curves := max 1 cfg.ecmCurves, threads := cfg.threads }
      else ecmLevels cfg.threads (ecmSchedule (QS.decimalDigits n)) n
  | .cfrac => fun n => CFRAC.split n
  | .qs => fun n => QS.split n { variant := .qs, threads := cfg.threads }
  | .mpqs => fun n => QS.split n { variant := .mpqs, threads := cfg.threads }
  | .siqs => fun n => QS.split n { variant := .siqs, threads := cfg.threads }
  | .gnfs => fun n => GNFS.split n { threads := cfg.threads }
  | .auto => autoSplitter cfg

/-- The raw divisor search (for benchmarks that must not count fallbacks). -/
def rawSearch (algorithm : Algorithm) (cfg : Config := {}) (n : Nat) : Option Nat :=
  (splitter algorithm cfg n).map Subtype.val

theorem rawSearch_sound {algorithm : Algorithm} {cfg : Config} {n d : Nat}
    (h : rawSearch algorithm cfg n = some d) : 1 < d ∧ d < n ∧ d ∣ n := by
  unfold rawSearch at h
  obtain ⟨f, _, rfl⟩ := Option.map_eq_some_iff.mp h
  exact f.property

/-- Prime leaves are certified by Pocklington certificates whose `n - 1`
factorizations are found with the automatic splitter (an untrusted helper). -/
def primeOracle (cfg : Config := {}) : PrimeOracle :=
  Pocklington.oracle (fun m => (autoSplitter cfg m).map Subtype.val)

/-- All nonzero inputs receive a complete factorization. Searches may fall back.
The trial algorithms remain independent, certificate-free baselines. -/
def factor (algorithm : Algorithm) (n : Nat) (cfg : Config := {}) : Option (List Nat) :=
  if n = 0 then none else
    match algorithm with
    | .trialReference => some (factorCore trialSplitterReference n)
    | .trial => some (trialCore n)
    | .wheel => some (trialWheelCore n)
    | _ => some (factorCoreWith (primeOracle cfg) (splitter algorithm cfg) n)

/-- The same universal theorem covers each named executable implementation. -/
theorem factor_correct (algorithm : Algorithm) (n : Nat) (cfg : Config)
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
theorem factor_total_correct (algorithm : Algorithm) (n : Nat) (cfg : Config)
    (hn : n ≠ 0) :
    ∃ ps, factor algorithm n cfg = some ps ∧ IsFactorization n ps := by
  cases hf : factor algorithm n cfg with
  | none => cases algorithm <;> simp [factor, hn] at hf
  | some ps => exact ⟨ps, rfl, factor_correct algorithm n cfg ps hf⟩

@[simp] theorem factor_zero (algorithm : Algorithm) (cfg : Config) :
    factor algorithm 0 cfg = none := by simp [factor]

/-- Signed factorization with the same verified natural-number implementation. -/
def factorSigned (algorithm : Algorithm) (z : Int) (cfg : Config := {}) :
    Option (Int × List Nat) :=
  (factor algorithm z.natAbs cfg).map fun ps => (z.sign, ps)

theorem factorSigned_correct (algorithm : Algorithm) (z : Int) (cfg : Config)
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
    (cfg : Config) (hz : z ≠ 0) :
    ∃ sign ps, factorSigned algorithm z cfg = some (sign, ps) ∧
      IsIntFactorization z sign ps := by
  obtain ⟨ps, hf, _⟩ := factor_total_correct algorithm z.natAbs cfg
    (Int.natAbs_ne_zero.mpr hz)
  have hi : factorSigned algorithm z cfg = some (z.sign, ps) := by
    simp [factorSigned, hf]
  exact ⟨z.sign, ps, hi, factorSigned_correct algorithm z cfg z.sign ps hi⟩

end PrimeFactorLean
