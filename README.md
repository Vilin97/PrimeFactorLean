# PrimeFactorLean

Native integer factorization in Lean 4, with kernel-checked correctness proofs,
exact arithmetic, independently generated test data, and measured optimizations.

**Status: substantial verified implementation, but the requested full goal is
not complete.** Modern high-degree general number field sieve (GNFS) is still
missing. The number-field implementations here are explicitly bounded research
prototypes; they are not competitive replacements for CADO-NFS.

## Run

Install Lean with [elan](https://github.com/leanprover/elan), then:

```sh
lake exe cache get
lake build factor factorTests factorBench
lake test
lake exe factor auto 1000036000099
lake exe factor brent -360
lake exe factor --split qs 300320077
lake exe factorBench results/optimization.json 19
```

The CLI returns JSON. Factors are positive prime numbers with multiplicity;
negative integers carry a separate sign. `1` has an empty factor list. `0`
returns `null`, because it has no finite prime factorization.

`--split` runs the selected search itself. A `null` divisor is a bounded search
failure, not a primality assertion. Ordinary factorization tries the selected
search, verifies prime leaves with Pratt certificates, and uses exact proved
trial division if necessary. `trial` and `wheel` have their own standalone
proved recursive factorization implementations.

## Implementations

| CLI name | Actual implementation | Main correctness evidence |
|---|---|---|
| `trial-reference` | Consecutive divisors below the input | Exact finite search interval; proper divisor bounds; complete recursive factorization |
| `trial` | Consecutive divisors through the integer square root | Search completeness; no small divisor implies `Nat.Prime`; standalone total factorization |
| `wheel` | Test 2, 3, then residues 1 and 5 modulo 6 | Exact wheel interval; excluded residues cannot divide; independent total factorization |
| `fermat` | Difference of squares, bounded increments | Square identity; direct raw divisor soundness |
| `rho` | Pollard rho with Floyd cycle detection | Modular polynomial congruence; one/two-iterate invariant; direct raw soundness |
| `brent` | Brent rho, power-of-two blocks, batched gcd, recovery | Actual iterate/product invariants; proof-carrying raw success paths |
| `pminusone` | Pollard p−1 stage one, maximal prime-power schedule | Binary modular powering; maximal prime powers; exponent schedule invariant; raw soundness |
| `ecm` | Affine elliptic curve stage one, exact gcd/inverse arithmetic, prime-power schedule | Seed/add/scalar/stage curve preservation; inverse/slope identities; raw soundness |
| `qs` | Modular-root block sieve, smooth relations, F₂ elimination | Exact relation reconstruction and modular congruence; even-exponent square reconstruction; raw soundness |
| `mpqs` | Multiple-polynomial QS with actual A/B selection, CRT roots, and Gray-code root updates | Exact polynomial and relation identities, A-factor reconstruction, independent raw output soundness |
| `nfs-quadratic` | Rational/algebraic relations for `X²+c`, parity dependencies, exact algebraic square roots | Algebraic ring/norm identities; evaluation homomorphism; actual square-root equality and congruence; raw soundness |
| `nfs-cubic` | Base-m cubic polynomial selection, prime-ideal columns, determinant norms, exact bounded algebraic root dictionary | Irreducibility certificates, coefficient multiplication/norm/evaluation identities, checked actual roots and proper divisors |
| `auto` | Small division, Fermat, Brent, p−1, ECM, QS portfolio | The same universal factorization theorem; every accepted split is a proper divisor |

All searches have explicit finite bounds. No third-party factoring executable is
called. The production factor library does not import the dataset or its answers.
See [the algorithm specification](docs/ALGORITHMS.md) for exact proof boundaries.

## Auditable theorem

For every named algorithm and every nonzero natural input, Lean proves that the
implementation returns a list consisting entirely of mathematical primes whose
product is the input:

```lean
factor_total_correct (algorithm : Algorithm) (n : Nat) (cfg : Search.Config)
  (hn : n ≠ 0) :
  ∃ ps, factor algorithm n cfg = some ps ∧
    (∀ p ∈ ps, Nat.Prime p) ∧ ps.prod = n
```

`factorSigned_total_correct` proves the corresponding statement for every
nonzero integer, including the unit sign. These theorems are independent of
heuristics, search success, and test results.

Pratt certificates are generated at runtime by untrusted candidate construction
and checked by a separately proved Lucas criterion. Miller–Rabin/Fermat screens
only guide construction; they never justify a prime output. Bad candidates,
invalid certificates, and exhausted search budgets trigger rejection or the
proved fallback. A full `n−1` factorization can be hard, so certificate generation
and fallback may be slow on difficult inputs.

No `sorry`, custom axioms, `native_decide`, unsafe definitions, foreign factoring
code, or unchecked implementation replacements occur in the project. The axiom
closure audit accepts only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`. CI rebuilds proofs and tests and runs the audit.

## Dataset and tests

[data/cases.json](data/cases.json) contains 220 exact cases:

- 168 routine cases, including all inputs 0 through 100, prime powers,
  pseudoprimes, seeded semiprimes, and small Cunningham numbers.
- 52 stress cases, including semiprimes, large prime leaves, and odd-exponent
  `2^n−1` Cunningham numbers through exponent 63.

The established source is the
[Cunningham Project's January 2026 table](https://homes.cerias.purdue.edu/~ssw/cun/pmain126.txt).
Its selected rows and source SHA-256 are recorded in
[data/provenance.json](data/provenance.json). Reference factors are constructed by
an independent Python implementation and checked for exact products. Generated
cases use seed `20261007`. RSA challenge inputs are much too large for routine
CI and are not silently treated as successfully factored tests.

```sh
python3 scripts/validate_dataset.py
python3 scripts/generate_dataset.py  # downloads the pinned Cunningham snapshot
python3 scripts/benchmark.py --tier core --algorithms trial wheel fermat rho brent pminusone ecm qs mpqs nfs-quadratic nfs-cubic auto
python3 scripts/benchmark.py --tier stress --algorithms auto brent
python3 scripts/split_benchmark.py --tier all
```

`lake test` also covers signed inputs, malicious split suggestions, certificate
tampering, hostile certificate producers, zero fuel, and actual raw splitter
successes. `Tests.Audit` exhaustively compares trial implementations on inputs
0 through 10000 (the slow reference through 500). All comparisons check prime
membership and exact products.

Complete driver benchmarks and raw-search benchmarks are separate. A complete
factorization passing is not evidence that its named search succeeded. Timeouts
and misses remain visible in the committed JSON reports. Detailed reports are
stored as `results/*.json.gz`; read them with `gzip -dc` or Python
`gzip.open`. Compression preserves the complete records. Stress budgets are
reported separately; the elementary trial algorithms are not expected to process
large prime leaves promptly.

Recorded verification results:

| Coverage | Result |
|---|---:|
| `lake test`: 12 drivers × 168 routine cases | 2016/2016 pass |
| Routine benchmark, including slow reference and both NFS prototypes | all 13 drivers pass all 168 cases |
| Full 220-case dataset: Fermat, rho, Brent, p−1, ECM, QS, MPQS, auto | all pass |
| Independent raw searches: rho / Brent / auto | 178/178 composite cases split |
| Independent raw searches: p−1 / ECM / QS / MPQS | 168 / 175 / 158 / 176 of 178 split |
| Independent raw searches: quadratic / cubic NFS prototypes | 87 / 14 of 178 split |
| Kernel axiom closure audit | all project declarations pass |

The raw-search misses are retained; in particular the NFS prototypes have low
coverage and are educational implementations. The complete driver results above
may use the proved fallback. The slow reference and trial methods are benchmarked
on the routine tier; large prime stress cases are deliberately outside their
practical timing budget.

## Optimization

The executable uses Lean's unbounded integer arithmetic. The implemented
optimizations preserve their mathematical specification:

- Square-root trial bounds, followed by a proved `6k±1` wheel.
- Binary modular exponentiation with a proof for every modulus.
- Brent batched gcd with exact iterate and product invariants.
- Shared p−1 prime-power schedules across restart bases.
- ECM maximal-prime-power schedules instead of the original factorial schedule;
  the old implementation remains available as `ECM.splitFactorial` for comparison.
- Exact residue-class sieving and F₂ bitset elimination for QS.
- Runtime Pratt certificates with shared dependency graphs instead of exhaustive
  primality division on large prime cofactors.

[results/optimization.json](results/optimization.json) records native in-process
comparisons and all raw outcomes. The harness interleaves configurations and
rotates their order. `@[noinline]` IO boundaries keep actual work between clock
reads; process startup is excluded from those measurements. These are workload
measurements, not proved complexity bounds or universal speed guarantees.

Measured median improvements on the committed workloads (19 interleaved rounds):

| Change | Measured speedup |
|---|---:|
| Brent batching versus Floyd rho | 1.40× |
| 6-wheel versus basic sqrt trial, prime inputs | 2.54× |
| 6-wheel versus basic sqrt trial, composite inputs | 3.10× |
| ECM prime-power versus factorial schedule, bound 100 | 1.89× |
| ECM prime-power versus factorial schedule, bound 200 | 3.25× |

Batch sizes 32 and 64 were within roughly 1.3% on this sample; the default remains
64. The benchmark retains bounded failures instead of timing only successes.

## Remaining work

The full user goal includes the best general-purpose classical methods. To reach
that goal, this project still needs modern high-degree GNFS: optimized polynomial
selection, prime-ideal/character relations, lattice sieving, scalable sparse
linear algebra, and an efficient algebraic square-root stage. A norm parity
condition alone does **not** establish an algebraic square; the current prototype
checks the actual square equality and can legitimately reject dependencies.

Further practical extensions include p−1/ECM stage two, stronger partial-factor
primality certificates, and large-prime relation variants. The current kernel
proofs establish output correctness and total fallback, and several execution
invariants; they do not prove heuristic success probabilities or competitive
GNFS complexity.

Pinned environment: Lean `4.24.0`, mathlib tag `v4.24.0`, with exact dependency
revisions in `lake-manifest.json`. Licensed under MIT; mathlib and Lean retain
their upstream licenses.
