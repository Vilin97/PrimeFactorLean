# Algorithms, proofs, and trust boundaries

This document describes every implementation in the library, from trial
division to the general number field sieve, and states precisely what the
kernel-checked proofs establish about each one.

## The specification

```lean
def IsFactorization (n : Nat) (factors : List Nat) : Prop :=
  (∀ p ∈ factors, Nat.Prime p) ∧ factors.prod = n

theorem factor_total_correct (algorithm : Algorithm) (n : Nat) (cfg : Config)
    (hn : n ≠ 0) :
    ∃ ps, factor algorithm n cfg = some ps ∧ IsFactorization n ps
```

`Nat.Prime` is mathlib's definition. The theorem holds for every algorithm,
every configuration and every positive input. `factorSigned_total_correct`
extends it to nonzero integers with a sign. Zero has no factorization and
returns `none`.

## How the proofs are organized

Every algorithm is a **proof-carrying splitter**:

```lean
abbrev ProperFactor (n : Nat) := {d : Nat // 1 < d ∧ d < n ∧ d ∣ n}
abbrev Splitter := (n : Nat) → Option (ProperFactor n)
```

A splitter may fail (`none`), but whatever it returns carries a proof that it is
a proper divisor. That proof comes from the algorithm's own soundness argument,
never from a generic re-check in the driver. The verified engine
`factorCoreWith` (`Core.lean`) handles each node as follows:

1. It asks a **prime oracle** for a primality proof (Pocklington certificates;
   see below). If it gets one, the node is a prime leaf.
2. Otherwise it calls the splitter and recurses on `d` and `n / d`.
3. If the splitter gives up, it falls back to exact trial division
   (`Nat.minFac`).

The engine terminates by well-founded recursion on `n`, and
`factorCoreWith_correct` proves the specification for **any** oracle and **any**
splitter. Search failures therefore never cost correctness, only time.

The heuristic algorithms are written in the style of *certifying algorithms*.
Fast, untrusted search code (sieves, polynomial selection, the GF(2) solver,
the p-adic square-root search) produces an object. A cheap check, whose meaning
is proved, then validates it. Everything downstream of that check is proved.
For each algorithm the table below lists both what is proved and what is
checked at run time.

| Implementation | File | Proved | Checked at run time (then trusted via proof) |
|---|---|---|---|
| `trial-reference`, `trial`, `wheel` | `Trial.lean` | Soundness **and completeness**: `trialSearch_none_prime` and `trialWheelSearch_none_prime` show that no divisor up to √n means `Nat.Prime n`. The 6-wheel skips only multiples of 2 and 3 (`trialWheelAux_none_iff`). | nothing |
| `fermat` | `Search.lean` | `fermat_difference_identity`: `(a+b)(a-b) = n` from `b² = a² - n`; `fermat_sound` | the divisor test in `accept` |
| `rho`, `brent` | `Search.lean` | `rhoStep_congruent` (iteration respects every divisor's modulus), `floydIterate_correct`, `rho_collision_divides_gcd`; Brent's batched product is exactly the product of the actual differences (`brentBlock_product`) and keeps every collided divisor (`brent_collision_divides_gcd`) | `accept` / `acceptCertified` |
| `squfof` | `SQUFOF.lean` | `split_sound`; the divisor is a gcd, so it divides `n` by construction | nontriviality of the gcd |
| `pminusone`, `pplusone` | `PMinusOne.lean` | `applyPowers_mod` (stage 1 computes `x^E mod n` for the true exponent product), the Lucas-sequence ladder identities `lucas_double` and `lucas_double_add_one` in any commutative ring, soundness | nontriviality of the gcd |
| `ecm-affine` | `ECM.lean` | Chord and tangent formulas preserve the curve equation (`add_preserves_curve`), so do scalar multiplication and all of stage 1 (`stageOne_preserves_curve`); extended-Euclid inverses (`inverse_correct`) | `checkFactor` |
| `ecm` (Montgomery) | `ECMMontgomery.lean` | `xDBL_correct` and `xADD_correct`: the projective x-only formulas compute the affine Montgomery doubling and differential-addition x-coordinates over any field; divisors are gcds (`gcdFactor`) | nontriviality of the gcd |
| `cfrac`, `qs`, `mpqs`, `siqs` | `CFRAC.lean`, `QS.lean`, `Squares.lean` | Relations carry `x² ≡ ±s²·L·∏ fb[j]^e (mod n)`. Products (`Relation.mul`), large-prime pairing (`Relation.pair`), cycles (`Relation.absorb`), sorting/merging (`evalExps_perm`, `evalExps_mergeRuns`) and halving (`evalExps_half`) are proved, giving `X² ≡ Y² (mod n)` (`Relation.toSquares`). `SquareCongruence.factor_isSome` proves that every nontrivial congruence (`X ≢ ±Y`) splits `n`. | the relation congruence when a relation is created (`Relation.mk?`); evenness of the merged exponents of a dependency |
| `gnfs` | `GNFS.lean`, `NFS/*.lean` | Evaluation `ℤ[ω] → ℤ/n`, `ω ↦ r`, is multiplicative for the executable convolution-and-reduction product whenever `f(r) = 0` (`eval_mulZ`, `eval_prodTree`). `nfs_square` derives `φ(β)² = (φ(f')·c_d^k·Y₀)²` | `f(c_d·m) ≡ 0 (mod n)`; `β·β = γ` exactly in `ℤ[ω]`; `∏(a - b·m) = Y₀²` exactly; even relation count |
| prime leaves | `Pocklington.lean`, `Primality.lean` | **Pocklington's criterion** from scratch (`pocklington`, via `prime_pow_dvd_sub_one` and orders in `(ℤ/p)ˣ`); certificate checker soundness (`Step.check_sound`, `Certificate.check_sound`); Lucas/Pratt certificates (`PrimeCertificate.check_sound`) | the certificate (generated by untrusted code) |

`Tests/Audit.lean` prints the axioms of the central theorems and fails the
build if any project declaration depends on anything beyond `propext`,
`Classical.choice` and `Quot.sound`. `scripts/audit_sources.py` rejects the
escape-hatch keywords `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
`partial`, `implemented_by` and `extern` anywhere in the sources.

### What is *not* proved

- None of the theorems bounds a running time or the success probability of a
  heuristic search. Statements like "ECM finds 20-digit factors with these
  parameters" or "the sieve collects enough relations" are measured, not
  proved.
- The ECM lemmas establish the coordinate formulas. They do not formalize the
  group law of the elliptic curve over `ℤ/p` or the smooth-order argument.
- Linear algebra over GF(2) is untrusted. A wrong dependency fails the evenness
  check and is skipped.
- The GNFS proof does not show that the quadratic characters make `γ` a square;
  it only needs the checked equality `β·β = γ`.

## Implementations, simplest to most sophisticated

### Trial division (`trial-reference`, `trial`, `wheel`)
The reference implementation tests every `d < n`, `trial` stops at `⌊√n⌋`, and
`wheel` tests 2, 3 and then the residues `6k ± 1`. These are the only
algorithms whose *completeness* is proved, and they do not need the
fallback or a prime oracle: a failed search proves primality.

### Fermat's method (`fermat`)
Searches `a ≥ ⌈√n⌉` with `a² - n` a perfect square. It is fast only when the two
factors are close.

### Pollard rho (`rho`) and Brent's variant (`brent`)
These run the random walk `x ↦ x² + c mod n`. Floyd's version compares `x_i`
with `x_{2i}`. Brent's version uses power-of-two cycle blocks and batches 64
differences into one gcd, with recovery when the batched gcd is `n`. The
expected cost is `O(√p)` for the smallest prime `p`.

### SQUFOF (`squfof`)
This is Shanks' square forms factorization for `n < 2^62`. It races 16
multipliers, forward-cycles until it finds a square form, then
reverse-cycles to the factor. It needs `O(n^{1/4})` steps of single-word
arithmetic.

### Pollard `p - 1` and Williams `p + 1` (`pminusone`, `pplusone`)
Stage 1 raises to the maximal prime powers up to `B1`, with chunked gcds and
replay. Stage 2 covers the primes in `(B1, B2]` with prime-gap powers. Williams'
method uses Lucas sequences `V_k(P)` with six seeds that have independent
quadratic characters. These methods succeed when `p ∓ 1` is smooth.

### Elliptic curve method (`ecm-affine`, `ecm`)
`ecm-affine` is Lenstra's original formulation: affine Weierstrass curves with
modular inversions, stage 1 only. `ecm` is the modern form:

- Montgomery curves in Suyama's parametrization, whose group order is
  divisible by 12;
- projective x-only arithmetic, with no inversions;
- a Montgomery ladder over the maximal prime powers up to `B1`;
- a stage-2 standard continuation (baby steps / giant steps with
  `D = 2310` and one batched gcd);
- backtracking when stage 1 annihilates every prime factor at once
  (`gcd = n`): a replay with a gcd after each prime power;
- curves run in parallel tasks.

The automatic schedule follows GMP-ECM's recommended `(B1, curves)` pairs.

### Continued fraction method (`cfrac`)
Morrison–Brillhart was the first subexponential algorithm. It expands `√(kn)`
and collects the relations `A_{i-1}² ≡ (-1)^i Q_i (mod n)` over a factor base,
with single large primes. It then solves for a dependency over GF(2) and takes
the square root as above.

### Quadratic sieves (`qs`, `mpqs`, `siqs`)
All three variants sieve `Q(x) = (Ax + B)² - kn = A·(Ax² + 2Bx + C)` over
`[-M, M)` with logarithms in a byte array:

- `qs` uses the single polynomial (`A = 1`, shifted windows);
- `mpqs` uses Montgomery's `A = q²` with Hensel-lifted `B`;
- `siqs` chooses `A = q₁⋯q_s` from the factor base near `√(2kn)/M` and
  enumerates the `2^{s-1}` values of `B` in Gray-code order, so a new
  polynomial costs one addition per root.

All three use:

- a Knuth–Schroeppel multiplier;
- the small-prime variation;
- trial division of candidates by root position, never by big-number
  reduction;
- single and (optionally) double large primes, with union–find cycle counting
  and spanning-forest cycle extraction;
- parallel collection;
- structured Gaussian elimination (singleton removal, merging of weight-two
  columns) followed by GMP-bitset elimination.

### General number field sieve (`gnfs`)
The asymptotically fastest known general method, `L_n[1/3, (64/9)^{1/3}]`. Its
stages are:

- **Polynomial selection.** Degree 3–5 base-`m` polynomials. The leading
  coefficients are scanned up to `n^{1/(d+1)}`, and candidates are ranked by
  sampled log norms over the sieve region plus Murphy's `α`.
- **Factor bases.** Rational and algebraic. Algebraic roots modulo `p` are
  found with `gcd(x^p - x, f)` and Cantor–Zassenhaus. Projective ideals are
  included, as are 48 quadratic characters above the large-prime bound.
- **Sieving.** Line sieving for small inputs; Pollard's special-`q` lattice
  sieve (Gauss-reduced lattices, row sieving with incremental starts) from 35
  digits. One large prime per side.
- **Linear algebra.** Columns for the sign, the relation count, the
  characters, rational primes and algebraic ideals.
- **Square roots.** The algebraic square root of
  `γ = f'(ω)² ∏(c_d a - b ω)` comes from `p`-adic Newton iteration at an inert
  prime: Tonelli–Shanks in `𝔽_{p^d}`, then lifting the inverse square root.
  It is verified by exact multiplication in `ℤ[ω]`.

### Automatic portfolio (`auto`)
The portfolio tries, in order:

1. trial division to 4096;
2. perfect powers;
3. SQUFOF below `2^62`;
4. a short Brent rho;
5. `p - 1` with `B1 = 20000`;
6. ECM, with effort scaled to the input size;
7. SIQS.

### Primality certificates
The default prime oracle builds **Pocklington certificates**. It factors
`n - 1` only until the factored part `F` satisfies `F² > n`, using the
automatic splitter, which is untrusted. Each certificate step names primes `q`
that are proved earlier in the certificate or are below `2^32`, where they
are proved by verified trial division. For each `q` the step gives a witness
`a` with `a^{n-1} ≡ 1` and `gcd(a^{(n-1)/q} - 1, n) = 1`. The kernel-checked
theorem:

```lean
theorem pocklington {N : Nat} (hN : 2 ≤ N) (ws : List (Nat × Nat × Nat))
    (hprime : ∀ t ∈ ws, t.1.Prime) (hnodup : (ws.map Prod.fst).Nodup)
    (hdvd : ∀ t ∈ ws, t.1 ^ t.2.1 ∣ N - 1) (hbig : N < factoredPart ws ^ 2)
    (hwit : ∀ t ∈ ws, ∀ p, p.Prime → p ∣ N →
      (t.2.2 : ZMod p) ^ (N - 1) = 1 ∧ (t.2.2 : ZMod p) ^ ((N - 1) / t.1) ≠ 1) :
    N.Prime
```

The older Lucas–Pratt checker (full `n - 1` factorizations) is retained and
benchmarked against it.

## References

- J. M. Pollard, *A Monte Carlo method for factorization* (1975); R. P. Brent,
  *An improved Monte Carlo factorization algorithm* (1980).
- D. Shanks, *SQUFOF* (unpublished notes, 1975); J. Gower and S. Wagstaff,
  *Square form factorization*, Math. Comp. 77 (2008).
- J. M. Pollard, *Theorems on factorization and primality testing* (1974);
  H. C. Williams, *A p+1 method of factoring*, Math. Comp. 39 (1982).
- H. W. Lenstra Jr., *Factoring integers with elliptic curves*, Annals of Math.
  126 (1987); P. L. Montgomery, *Speeding the Pollard and elliptic curve
  methods of factorization*, Math. Comp. 48 (1987).
- M. A. Morrison and J. Brillhart, *A method of factoring and the factorization
  of F₇*, Math. Comp. 29 (1975).
- C. Pomerance, *The quadratic sieve factoring algorithm* (1985);
  R. D. Silverman, *The multiple polynomial quadratic sieve*, Math. Comp. 48
  (1987); S. Contini, *Factoring integers with the self-initializing quadratic
  sieve* (1997).
- A. K. Lenstra and H. W. Lenstra Jr. (eds.), *The development of the number
  field sieve*, LNM 1554 (1993); M. Briggs, *An introduction to the general
  number field sieve* (1998); B. A. Murphy, *Polynomial selection for the
  number field sieve* (thesis, 1999); J. M. Pollard, *The lattice sieve* (1993).
- H. C. Pocklington, *The determination of the prime or composite nature of
  large numbers by Fermat's theorem* (1914).
- The Cunningham Project, S. S. Wagstaff Jr.,
  <https://homes.cerias.purdue.edu/~ssw/cun/>.
