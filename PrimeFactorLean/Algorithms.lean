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

/-- The divisors of `k` (by trial division up to `√k`). -/
def divisorsOf (k : Nat) : Array Nat := Id.run do
  let mut small : Array Nat := #[]
  let mut large : Array Nat := #[]
  let mut d := 1
  while d * d ≤ k do
    if k % d == 0 then
      small := small.push d
      if d * d != k then large := large.push (k / d)
    d := d + 1
  return small ++ large.reverse

/-- Algebraic factors of numbers dividing `b^k ± 1` (as YAFU's `factor()` does):
for small bases `b`, find the least `k` with `b^k ≡ ±1 (mod n)`; then
`n ∣ b^{2k} - 1 = ∏_{d ∣ 2k} Φ_d(b)`, and `gcd(n, b^d - 1)` for the divisors `d`
of `2k` split off its cyclotomic pieces. Every reported factor is a checked
proper divisor (`checkFactor`). -/
def algebraicSplitter : Splitter := fun n => Id.run do
  if n < 2 ^ 64 then return none
  for b in [2, 3, 5, 6, 7, 10, 11, 12] do
    if n % b == 0 then continue
    -- `k` up to about three times the exponent of `n` in base `b`
    let kmax := 3 * (n.log2 / Nat.log2 b) + 64
    let mut x := b % n
    let mut k := 1
    while k ≤ kmax do
      if x == 1 || x == n - 1 then
        for d in divisorsOf (2 * k) do
          if d == 2 * k then continue
          let g := Nat.gcd n ((Arith.powMod b d n + n - 1) % n)
          if 1 < g && g < n then return checkFactor n g
        break
      x := x * b % n
      k := k + 1
  return none

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

/-- Single-thread time (ms) of one curve with `B2 = 100 B1` on an 80-digit number
(ten limbs), measured at `f9b4a63`: the cost model of `ecmScheduleCost`. -/
def curveMs (b1 : Nat) : Float :=
  if b1 ≤ 2000 then 3.4 else if b1 ≤ 11000 then 11.9 else if b1 ≤ 50000 then 49.7
  else if b1 ≤ 250000 then 244.0 else if b1 ≤ 1000000 then 1000.0 else 3000.0

/-- Expected wall time (seconds, 16 threads) of the quadratic sieve on `d` digits:
7.0 s at 80 digits (`89e67d2`), doubling every 3.72 digits (`snfsCandidate`). -/
def qsSeconds (d : Nat) : Float := 7.0 * Float.exp2 ((d.toFloat - 80.0) / 3.72)

/-- Expected wall time (seconds, 16 threads) of the special number field sieve on a
`D`-digit `b^k ± 1` (`snfsCandidate`). -/
def snfsSeconds (D : Nat) : Float := 2.1 * Float.exp2 ((D.toFloat - 83.0) / 10.5)

/-- The levels of `ecmScheduleCost` from `levels` on (`prev` the previous level's
digits, `L` the limbs of `n`, `th` the threads, `T` the time ECM may save). A level
of `t` digits expects `k` curves for a factor of `t` digits; the factors it looks
for lie between `t - 5` and `t` digits, and a factor at the geometric middle of
that band needs about `k / √7.5` curves at its `B1` (expected curve counts grow
about 7.5 times per five digits): the rate used. -/
def ecmCostGo (T L th : Float) : List (Nat × Nat × Nat) → Nat → List (Nat × Nat)
  | [], _ => []
  | (t, b1, k) :: rest, prev =>
    let P := Float.log (t.toFloat / prev.toFloat)
    let c := curveMs b1 * (L / 10.0) * (L / 10.0) / th * 1.3 / 1000.0
    let ke := k.toFloat / 2.7386
    let r := P * 0.9 * T / (ke * c)
    let x := if r ≤ 1.0 then 0.0 else min k.toFloat (ke * Float.log r)
    if x < 0.05 * k.toFloat then [] else (b1, x.toUInt64.toNat) :: ecmCostGo T L th rest t

/-- `(B1, curves)` of the ECM levels for factors of 25 digits and more before a
method expected to take `T` seconds on the `d`-digit `n`, from a cost model (a
fixed share of the digits, YAFU's `4/13`, suits an ECM several times faster
relative to the sieves). For each level in turn (factors of `t` digits, `B1`, `k`
curves expected to find one), the number `x` of curves that maximizes the expected
saving `P w T (1 - e^{-x/k'})` minus the cost `c x`, that is
`x = k' ln(P w T/(k' c))`: `P = ln(t/t')` is the probability of a prime factor
between the previous level's `t'` and `t` digits (Mertens), `w = 0.9` the share of
`T` saved when one is found, `k' = k/√7.5` the curves for a factor in the middle
of that band (see `ecmCostGo`) and `c` the time of one curve on `threads` threads
(`curveMs` scaled by the square of the width of `n` and by 1.3 for the all-core
clock). The levels stop at the first one worth less than a twentieth of its
curves. -/
def ecmScheduleCost (d : Nat) (T : Float) (threads : Nat) : List (Nat × Nat) :=
  let L := ((d.toFloat * 3.3219 + 28.0) / 28.0).floor
  ecmCostGo T L (max 1 threads).toFloat
    [(25, 50000, 300), (30, 250000, 700), (35, 1000000, 1800), (40, 3000000, 5100)] 20

/-- The full GMP-ECM schedule, levels for factors of 15, 20, …, 40 digits, up to
factors of about half the size of `n` (standalone ECM). -/
def ecmScheduleFull (digits : Nat) : List (Nat × Nat) :=
  let levels : List (Nat × Nat × Nat) :=
    [(15, 2000, 25), (20, 11000, 90), (25, 50000, 300), (30, 250000, 700),
     (35, 1000000, 1800), (40, 3000000, 5100)]
  (levels.filter fun l => l.1 ≤ max 15 (digits / 2 + 5)).map fun l => (l.2.1, l.2.2)

/-- ECM over a list of `(B1, curves)` levels; the first factor wins. Each level
draws its own Suyama parameters (a level reusing the curves of the previous one
would retry group orders already known not to be smooth enough). The curves run
in batches of `threads`, so a level is rounded up to whole batches: the extra
curves take no extra time. -/
def ecmLevels (threads : Nat) (levels : List (Nat × Nat)) : Splitter := fun n =>
  let t := max 1 threads
  (levels.zip (List.range levels.length)).foldl (fun acc ((b1, curves), i) => acc.orElse fun _ =>
    ECMF.split n { b1 := b1, curves := (curves + t - 1) / t * t, threads := threads,
                   sigma := 11 + 100003 * i })
    none

/-- `(b, k, plus)` with `n ∣ b^k + 1` (`plus`) or `n ∣ b^k - 1` for a small base
`b`, `k` the least such exponent. -/
def specialForm (n : Nat) : Option (Nat × Nat × Bool) := Id.run do
  for b in [2, 3, 5, 6, 7, 10, 11, 12] do
    if n % b == 0 then continue
    let kmax := 3 * (n.log2 / Nat.log2 b) + 64
    let mut x := b % n
    let mut k := 1
    while k ≤ kmax do
      if x == n - 1 then return some (b, k, true)
      if x == 1 then return some (b, k, false)
      x := x * b % n
      k := k + 1
  return none

/-- The special number field sieve applies when `n` divides `b^k ± 1` and is
expected to be faster than the quadratic sieve: measured with 16 threads (the
huge tier at `4699f07`), the special sieve on `D` digits takes about
`2.1 s · 2^((D - 83)/10.5)` (83 to 98 digits) and the quadratic sieve on `d`
digits about `8.7 s · 2^((d - 80)/3.72)` (64 to 80 digits), which cross at
`d = 0.354 D + 43.0`. Returns `(b, k, plus, digits of b^k)`. -/
def snfsCandidate (n : Nat) : Option (Nat × Nat × Bool × Nat) :=
  let dn := QS.decimalDigits n
  if dn < 60 then none else
  match specialForm n with
  | some (b, k, plus) =>
    let D := QS.decimalDigits (b ^ k)
    if 354 * D + 43000 ≤ 1000 * dn && D ≤ 140 then some (b, k, plus, D) else none
  | none => none

/-- The ECM pretest of the automatic portfolio: `ecmScheduleCost` for the sieve
that follows (the special sieve on `D` digits for divisors of `b^k ± 1` where it
pays off, else the quadratic sieve). -/
def autoEcmLevels (threads : Nat) (n : Nat) (snfs : Option (Nat × Nat × Bool × Nat)) :
    List (Nat × Nat) :=
  let d := QS.decimalDigits n
  let pretest := match snfs with
    | some (_, _, _, D) => min d ((354 * D + 43000) / 1000)
    | none => d
  -- the cheap levels (factors of up to 20 digits) keep the fixed share of the
  -- digits; from 25 digits on, where that share would go, the cost model decides
  (ecmSchedule pretest).filter (·.1 ≤ 11000) ++
    if (ecmSchedule pretest).length ≤ 2 then [] else
    ecmScheduleCost d (match snfs with
      | some (_, _, _, D) => snfsSeconds D
      | none => qsSeconds d) threads

/-- The automatic portfolio: cheap methods first, then ECM (`autoEcmLevels`), then
the special number field sieve for divisors of `b^k ± 1` where it pays off, else
SIQS. -/
def autoSplitter (cfg : Config) : Splitter := fun n =>
  if n < 4 then none else
  (smallSplitter 4096 n).orElse fun _ =>
  (powerSplitter n).orElse fun _ =>
  (algebraicSplitter n).orElse fun _ =>
  (if n < 2 ^ 62 then SQUFOF.split n else none).orElse fun _ =>
  (RhoF.split n 8000 1).orElse fun _ =>
  -- `p - 1` pays off only once the quadratic sieve is slow (from about 45 digits)
  (if n < 10 ^ 44 then none else PM1F.split n 20000).orElse fun _ =>
  let snfs := snfsCandidate n
  (ecmLevels cfg.threads (autoEcmLevels cfg.threads n snfs) n).orElse fun _ =>
  match snfs with
  | some (b, k, plus, _) =>
    (GNFS.splitSNFS n b k plus { threads := cfg.threads }).orElse fun _ =>
      SIQS.split n { threads := cfg.threads }
  | none => SIQS.split n { threads := cfg.threads }

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

/-- Splitters for the partial factorizations of certificates, which give up
early: rho, `p - 1` and ECM at the given levels, the full splitter only below
`10^full` (where the quadratic sieve takes at most about a tenth of a second).
When one gives up on `n - 1` (say a product of two 36-digit primes), the
generator tries `n + 1`, and the full splitter comes last. -/
def certSplitter (cfg : Config) (levels : List (Nat × Nat)) (full : Nat) : Splitter := fun n =>
  if n < 10 ^ full then autoSplitter cfg n else
  (smallSplitter 4096 n).orElse fun _ =>
  (powerSplitter n).orElse fun _ =>
  (RhoF.split n 8000 1).orElse fun _ =>
  (PM1F.split n 20000).orElse fun _ =>
  ecmLevels cfg.threads levels n

/-- The cheap splitters of the certificates: ECM at 15 digits (full below 50
digits), then at 20 digits (full below 60 digits). -/
def certSplitters (cfg : Config) : List (Nat → Option Nat) :=
  [fun m => (certSplitter cfg [(2000, 25)] 50 m).map Subtype.val,
   fun m => (certSplitter cfg [(11000, 90)] 60 m).map Subtype.val]

/-- Prime leaves are certified by Pocklington certificates (on `n - 1` or
`n + 1`) whose partial factorizations are found with the splitters above, then
the automatic splitter (untrusted helpers). Soundness:
`Proofs.Pocklington.oracle_sound`. -/
def primeOracle (cfg : Config := {}) : Nat → Bool := fun n =>
  Pocklington.oracle (fun m => (autoSplitter cfg m).map Subtype.val) 64 n (certSplitters cfg)

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
