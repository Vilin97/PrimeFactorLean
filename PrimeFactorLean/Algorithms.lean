import PrimeFactorLean.Core
import PrimeFactorLean.Trial
import PrimeFactorLean.Search
import PrimeFactorLean.ECM
import PrimeFactorLean.ECMMontgomery
import PrimeFactorLean.ECMFast
import PrimeFactorLean.PMinusOneFast
import PrimeFactorLean.RhoFast
import PrimeFactorLean.QS
import PrimeFactorLean.SIQS
import PrimeFactorLean.GNFS
import PrimeFactorLean.SQUFOF
import PrimeFactorLean.CFRAC
import PrimeFactorLean.PMinusOne
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

/-- `(B1, curves)` of the automatic ECM pretest: GMP-ECM's t-levels (factors
of 15, 20, …, 40 digits) up to a target of `4/13` of the digits of `n` (the
default of YAFU's `factor()`); the level containing the target is run in
proportion. -/
def ecmSchedule (digits : Nat) : List (Nat × Nat) :=
  let levels : List (Nat × Nat × Nat) :=
    [(15, 2000, 25), (20, 11000, 90), (25, 50000, 300), (30, 250000, 700),
     (35, 1000000, 1800), (40, 3000000, 5100)]
  -- target in tenths of a digit
  let target := 40 * digits / 13
  levels.filterMap fun (t, b1, curves) =>
    let lo := 10 * t - 50
    if target ≤ lo then none
    else if target ≥ 10 * t then some (b1, curves)
    else some (b1, max 1 (curves * (target - lo) / 50))

/-- The full GMP-ECM schedule, levels for factors of 15, 20, …, 40 digits, up to
factors of about half the size of `n` (standalone ECM). -/
def ecmScheduleFull (digits : Nat) : List (Nat × Nat) :=
  let levels : List (Nat × Nat × Nat) :=
    [(15, 2000, 25), (20, 11000, 90), (25, 50000, 300), (30, 250000, 700),
     (35, 1000000, 1800), (40, 3000000, 5100)]
  (levels.filter fun l => l.1 ≤ max 15 (digits / 2 + 5)).map fun l => (l.2.1, l.2.2)

/-- ECM over a list of `(B1, curves)` levels; the first factor wins. -/
def ecmLevels (threads : Nat) (levels : List (Nat × Nat)) : Splitter := fun n =>
  levels.foldl (fun acc (b1, curves) => acc.orElse fun _ =>
    ECMF.split n { b1 := b1, curves := curves, threads := threads }) none

/-- The automatic portfolio: cheap methods first, then ECM, then SIQS. -/
def autoSplitter (cfg : Config) : Splitter := fun n =>
  if n < 4 then none else
  (smallSplitter 4096 n).orElse fun _ =>
  (powerSplitter n).orElse fun _ =>
  (if n < 2 ^ 62 then SQUFOF.split n else none).orElse fun _ =>
  (RhoF.split n 8000 1).orElse fun _ =>
  -- `p - 1` pays off only once the quadratic sieve is slow (from about 45 digits)
  (if n < 10 ^ 44 then none else PM1F.split n 20000).orElse fun _ =>
  (ecmLevels cfg.threads (ecmSchedule (QS.decimalDigits n)) n).orElse fun _ =>
  SIQS.split n { threads := cfg.threads }

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
        ECMF.split n { b1 := cfg.ecmB1, curves := max 1 cfg.ecmCurves, threads := cfg.threads }
      else ecmLevels cfg.threads (ecmScheduleFull (QS.decimalDigits n)) n
  | .cfrac => fun n => CFRAC.split n
  | .qs => fun n => QS.split n { variant := .qs, threads := cfg.threads }
  | .mpqs => fun n => QS.split n { variant := .mpqs, threads := cfg.threads }
  | .siqs => fun n => SIQS.split n { threads := cfg.threads }
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
factorizations are found with the automatic splitter (an untrusted helper).
Soundness: `Proofs.Pocklington.oracle_sound`. -/
def primeOracle (cfg : Config := {}) : Nat → Bool :=
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

end PrimeFactorLean
