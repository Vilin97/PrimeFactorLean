# PrimeFactorLean

Integer factorization in Lean 4, from trial division to the general number
field sieve, with kernel-checked proofs of correctness.

- **17 implementations**, from trial division through Fermat, Pollard rho,
  SQUFOF, `p ± 1`, ECM, CFRAC, the quadratic sieves (QS, MPQS, SIQS) and the
  general number field sieve (GNFS).
- **Proved correct**: for every algorithm and every nonzero input, the output
  is a list of primes whose product is the input. Prime leaves are certified
  by a Pocklington checker that is itself proved sound.
- **Tested** on all 609 fully factored Cunningham numbers `bⁿ − 1` up to 100
  digits, on balanced semiprimes up to 80 digits and more: 831 cases in total.
  Every algorithm passed every case in its domain. The two hardest numbers
  first needed dedicated runs (27.6 and 11.4 minutes); the current `auto`
  factors them in 12.7 s and 28 ms. No algorithm ever returned a wrong answer.
- **Optimized** with measured speedups. On 16 cores, SIQS splits an 80-digit
  balanced semiprime in 13 s, and the general number field sieve factors
  **RSA-100** in 6.1 minutes.
- **Compared** with [YAFU](https://github.com/bbuhrow/yafu) and
  [CADO-NFS](https://cado-nfs.gitlabpages.inria.fr/) on the same machine and
  inputs ([details](#comparison-with-yafu-and-cado-nfs)). The `auto` portfolio
  is faster than YAFU in total time on the core, medium and large tiers. It is
  slower in total on the 60–100-digit tier (179 s vs 137 s), although it wins
  171 of the 253 cases there. The number field sieve beats CADO-NFS on all 12
  balanced semiprimes of 60–80 digits. On RSA-100 it is still 2.2× slower than
  CADO-NFS and 2.1× slower than YAFU.

```text
$ lake exe factor --threads 16 auto 3533694129556768659166595001485837031654967793751237916243212402585239551
{"algorithm":"auto","factors":["22000409","160619474372352289412737508720216839225805656328990879953332340439"],...}
```

That input is 2²⁴¹ − 1. Its 66-digit factor comes with a Pocklington
primality certificate accepted by the proved checker.

## What is proved

For **every** algorithm, configuration and nonzero input, the result is a
list of primes (mathlib's `Nat.Prime`) whose product is the input:

```lean
theorem factor_total_correct (algorithm : Algorithm) (n : Nat) (cfg : Config)
    (hn : n ≠ 0) :
    ∃ ps, factor algorithm n cfg = some ps ∧ IsFactorization n ps
```

Each algorithm is a *proof-carrying splitter*:

```lean
(n : Nat) → Option {d // 1 < d ∧ d < n ∧ d ∣ n}
```

The divisibility proof comes from that algorithm's own soundness argument. A
verified engine recurses on the two parts and certifies prime leaves. If a
bounded search gives up, it falls back to exact trial division. The heuristic
methods are written as *certifying algorithms*: fast, untrusted search code
proposes; a cheap check validates; and the meaning of the check, plus
everything downstream, is proved.

- **CFRAC, QS, MPQS, SIQS.** Every relation carries the proof of
  `x² ≡ ±s²·L·∏ p^e (mod n)`, checked when the relation is created.
  The following steps are all proved to give `X² ≡ Y² (mod n)`:
  - multiplying relations;
  - pairing large primes and closing large-prime cycles;
  - sorting and merging exponents;
  - halving the exponents.

  `SquareCongruence.factor_isSome` proves the final gcd step succeeds whenever
  `X ≢ ±Y`.
- **GNFS.** A congruence of squares is accepted only after checking
  `X² ≡ Y² (mod n)` for `X = φ(β)·Y₁^k` and `Y = φ(f')·c_d^k·Z`, all modulo `n`
  (`SquareCongruence.ofCheck`), so no exact square in `ℤ[ω]` is formed.
  `nfs_square_lin` proves the check complete: it holds whenever
  `f(c_d·x₀) ≡ 0 (mod n)`, the algebraic square root satisfies `β·β = γ` in
  `ℤ[ω]`, and the rational product is `∏(Y₁a − m·b) = Z²`. That proof uses
  kernel-checked multiplicativity of evaluation modulo `n` (`eval_mulZ`,
  `eval_prodTree`).
- **Prime leaves.** Pocklington's criterion is proved from scratch
  (`Pocklington.pocklington`). Certificates come from untrusted code and are
  accepted only by the proved checker.
- **ECM.** The Montgomery x-only formulas are proved equal to the affine
  doubling and differential-addition formulas (`xDBL_correct`, `xADD_correct`).
  The affine version also has curve-preservation proofs.
- **Trial division.** Completeness is proved as well: no divisor up to `√n`
  implies `Nat.Prime n`.

**Two layers.** Every executed definition lives in a module that imports only
Lean's core library (plus `Std` hash maps), so the `factor` executable starts
in about a millisecond and never loads mathlib or the Lean frontend. Proof
obligations that runtime code needs (proper divisors, relation congruences,
the GNFS square identity, termination) are proved there with core tactics,
stating congruences as integer divisibility (`ModEq n a b := (n : ℤ) ∣ a - b`).
Everything that needs mathlib — `Nat.Prime`, Pocklington's theorem, the ECM
formulas, the final `factor_total_correct` — is proved in
`PrimeFactorLean/Proofs/` *about the same constants*. `scripts/audit_sources.py`
checks that the executable's import closure contains no mathlib or `Lean` module.

`Tests/Audit.lean` fails the build if any of the ~1,900 project declarations
depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`.
`scripts/audit_sources.py` rejects `sorry`, `admit`, `native_decide`, `unsafe`,
`partial`, `implemented_by` and `extern`.
[docs/ALGORITHMS.md](docs/ALGORITHMS.md) lists, for each algorithm, what is
proved and what is checked at run time, including what is *not* proved
(running times, success probabilities, the elliptic-curve group law).

## Comparison with YAFU and CADO-NFS

The CLI was timed against two mature native factoring programs on the same
machine (AMD Ryzen 9 9955HX, 16 cores), with the same inputs and thread budget:

- **YAFU** 3.1.9 (commit `8110dfbd8c6f`): AVX-512 and IFMA SIQS, GMP-ECM 7.0.6,
  GMP 6.3.0, run as `yafu -threads 16` on `factor(n)`;
- **CADO-NFS** (commit `692ecb7e62f0`): the reference GNFS implementation, run as
  `cado-nfs.py n -t 16`.

`scripts/baselines/build.sh` builds both from pinned sources: YAFU with its
AVX-512, IFMA and BMI2 code paths, CADO-NFS with `-O3 -march=native`. The C that
Lean generates is also compiled with `-march=native`.

`scripts/compare.py` times complete process runs of every tool on every case of
a tier, three times each, interleaved. A machine-wide lock serializes all timed
runs, these and every other benchmark job on the machine, so no two runs
overlap. A run counts only if it returns the exact reference factorization. The
tables use the median of the three runs. `factor` certifies every prime factor
(Pocklington); YAFU reports probable primes, and CADO-NFS reports the split.

Raw records are in `results/compare/109e943-*.jsonl`. Summaries:
`python3 scripts/compare_report.py FILE --ours TOOL --base TOOL [--cases]`.
These runs are at commit `109e943`.

**`factor auto` against YAFU `factor()`**, on every case of each tier:

| Tier | Cases | Both solved | `factor auto` total | YAFU total | Geometric mean of time ratios | `auto` faster on |
|---|---:|---:|---:|---:|---:|---:|
| core (≤ 8 digits and special values) | 204 | 204 | 0.54 s | 2.12 s | 0.25 | 204 |
| medium (< 2⁶⁴) | 102 | 102 | 0.31 s | 1.15 s | 0.26 | 101 |
| large (20–59 digits) | 271 | 271 | 7.84 s | 15.48 s | 0.47 | 225 |
| huge (60–100 digits) | 253 | 253 | 179 s | 137 s | 0.66 | 171 |

On the core and medium tiers both tools spend most of their time starting up:
a `factor` run takes about 3 ms, a YAFU run about 10 ms.

On the huge tier `auto` is faster on two thirds of the cases and in geometric
mean, but slower in total, for two reasons:

- **Balanced semiprimes (SIQS).** YAFU's AVX-512 SIQS is 1.3–2.6× faster: at 80
  digits, 5.0–5.3 s against 12.9 s.
- **Factors found by ECM.** On some Cunningham numbers YAFU's ECM pretest finds a
  factor at once, and `auto` needs more curves or a sieve. Examples: `2²⁹³ − 1`
  takes 8.15 s against 0.33 s, `3¹⁹⁹ − 1` 11.5 s against 2.6 s, and `2³¹⁷ − 1`
  6.5 s against 0.7 s.

**Number field sieve: `factor gnfs` against CADO-NFS**, on the balanced
semiprimes from 60 digits (median wall time):

| Case | Digits | `factor gnfs` | CADO-NFS |
|---|---:|---:|---:|
| balanced-60-0 | 60 | 2.35 s | 9.75 s |
| balanced-60-1 | 60 | 2.28 s | 9.78 s |
| balanced-64-0 | 64 | 4.16 s | 10.50 s |
| balanced-64-1 | 64 | 3.93 s | 10.50 s |
| balanced-68-0 | 68 | 5.80 s | 11.17 s |
| balanced-68-1 | 68 | 6.81 s | 11.21 s |
| balanced-72-0 | 71 | 7.51 s | 12.83 s |
| balanced-72-1 | 72 | 8.58 s | 12.94 s |
| balanced-76-0 | 76 | 16.09 s | 20.49 s |
| balanced-76-1 | 76 | 15.47 s | 21.61 s |
| balanced-80-0 | 80 | 25.80 s | 30.24 s |
| balanced-80-1 | 80 | 27.55 s | 30.23 s |

**RSA-100** (three runs each):

| Tool | Median | Runs |
|---|---:|---|
| `factor gnfs` | 366 s | 366, 370, 363 s |
| CADO-NFS | 166 s | 166, 166, 169 s |
| YAFU `factor()` | 175 s | 175, 174, 175 s |

**The goal is not met yet.** On RSA-100 the Lean number field sieve is 2.2×
slower than CADO-NFS and 2.1× slower than YAFU. Most of the gap is lattice
sieving:

| | Lean | CADO-NFS |
|---|---|---|
| Sieving (wall time) | about 300 s | 120 s, filtering included |
| Relations collected | 3.21M unique, special-q up to 1.32M | 3.13M unique (4.18M raw), special-q up to 0.87M |
| Time per special-q (one thread, q = 180000) | 37 ms | 21 ms |
| Relations per special-q (same q) | 77 | 86 |
| Linear algebra | 206K-row matrix, 34 s | 175K-row matrix, 21 s |

The work continues on the siever's per-q cost and yield, on linear algebra, and
on SIQS.

## Algorithms and dataset results

Every implementation was run on the slice of the dataset it is designed for,
by input size (`scripts/benchmark.py`). Inputs up to 59 digits used 12
concurrent jobs × 3 threads with a 300 s limit; 60–100 digits used 2 jobs ×
8 threads with 30 minutes each. A pass requires the exact reference
factorization. Reports: `results/dataset-core-medium-large.json.gz`,
`results/dataset-huge.json.gz`.

| CLI name | Method | In-domain inputs | Passed | Wrong |
|---|---|---|---:|---:|
| `trial-reference` | trial division by every `d < n` | ≤ 8 digits | 204 / 204 | 0 |
| `trial` | trial division to `⌊√n⌋` | ≤ 9 | 212 / 212 | 0 |
| `wheel` | 2, 3, then `6k ± 1` to `√n` | ≤ 9 | 212 / 212 | 0 |
| `fermat` | Fermat's difference of squares | ≤ 8 | 204 / 204 | 0 |
| `rho` | Pollard rho, Floyd cycle detection | ≤ 20 | 312 / 312 | 0 |
| `brent` | Brent's rho, batched gcds | ≤ 20 | 312 / 312 | 0 |
| `squfof` | Shanks' square forms, 16 racing multipliers | ≤ 19 | 306 / 306 | 0 |
| `pminusone` | Pollard `p − 1`, stages 1 and 2 | ≤ 8 | 204 / 204 | 0 |
| `pplusone` | Williams `p + 1`, Lucas sequences | ≤ 8 | 204 / 204 | 0 |
| `ecm-affine` | Lenstra's ECM, affine Weierstrass, stage 1 | ≤ 12 | 258 / 258 | 0 |
| `ecm` | ECM: Montgomery curves, x-only ladder, stage 2, parallel curves | ≤ 30 | 376 / 376 | 0 |
| `cfrac` | Morrison–Brillhart continued fractions | ≤ 40 | 445 / 445 | 0 |
| `qs` | quadratic sieve, single polynomial | ≤ 45 | 478 / 478 | 0 |
| `mpqs` | multiple-polynomial QS (`A = q²`) | ≤ 55 | 542 / 542 | 0 |
| `siqs` | self-initializing QS, Gray-code polynomials, large primes, parallel | ≤ 80 | 707 / 707 | 0 |
| `gnfs` | general number field sieve: Kleinjung polynomial selection, Franke–Kleinjung lattice sieve, block Lanczos, `p`-adic square root | ≤ 50 (scaling runs to 61) | 509 / 509 | 0 |
| `auto` | portfolio: small primes, perfect powers, algebraic factors of `bⁿ ± 1`, SQUFOF, rho, `p − 1`, ECM, special number field sieve, SIQS | ≤ 100 | 828 / 830 | 0 |

In that run `auto` finished 828 of the 830 cases up to 100 digits within the
30-minute limit. The other two are the hardest numbers in the dataset.
Dedicated runs without a time limit then factored both completely
(`results/hard-cases.json`):

- `10⁹⁷ − 1` = `3² · 12004721 · P36 · P54` took 27.6 minutes; SIQS split the
  90-digit `P36 · P54`.
- `5¹⁴¹ − 1` = `2² · 31 · P33 · P65` took 11.4 minutes with `ecm` at
  `B1 = 3·10⁶`.

The current `auto` factors both within the comparison runs' limits
([Comparison](#comparison-with-yafu-and-cado-nfs)): `10⁹⁷ − 1` in 12.7 s with the
special number field sieve, and `5¹⁴¹ − 1` in 28 ms from its algebraic factors.
Since then every number field sieve run has also passed: the 60–80-digit balanced
semiprimes and RSA-100.

**Every case in the dataset has been factored correctly.** That covers:

- 828 cases within the benchmark limits;
- the two cases above, in dedicated runs and in the comparison runs;
- the RSA-100 challenge, by SIQS in 6 h 35 min and by GNFS in 6.1 minutes (see
  [Dataset](#dataset)).

Plain `siqs` passed every case up to 80 digits: 577 up to 59 digits and 130
of 60–80 digits. The `p ± 1` methods are special-purpose: they succeed only
when `p ∓ 1` is smooth. Like every algorithm, they still return complete
factorizations because of the verified fallback.

### Raw splitters

A complete factorization can succeed through the verified trial-division
fallback even when the named algorithm's own search fails. So each algorithm's
splitter was also run alone on every composite in its domain
(`--split`; `results/raw-splitters.json.gz`):

| Algorithm | Composites in domain | Split by its own search | Misses (bounded search gave up) | Timeouts | Wrong |
|---|---:|---:|---:|---:|---:|
| `trial-reference` | 162 | 162 | 0 | 0 | 0 |
| `trial` | 170 | 170 | 0 | 0 | 0 |
| `wheel` | 170 | 170 | 0 | 0 | 0 |
| `fermat` | 162 | 159 | 3 | 0 | 0 |
| `rho` | 267 | 267 | 0 | 0 | 0 |
| `brent` | 267 | 267 | 0 | 0 | 0 |
| `squfof` | 261 | 257 | 4 | 0 | 0 |
| `pminusone` | 162 | 160 | 2 | 0 | 0 |
| `pplusone` | 162 | 162 | 0 | 0 | 0 |
| `ecm-affine` | 214 | 213 | 1 | 0 | 0 |
| `ecm` | 330 | 330 | 0 | 0 | 0 |
| `cfrac` | 397 | 311 | 86 | 0 | 0 |
| `qs` | 430 | 406 | 24 | 0 | 0 |
| `mpqs` | 494 | 470 | 24 | 0 | 0 |
| `siqs` | 529 | 505 | 24 | 0 | 0 |
| `gnfs` | 461 | 375 | 86 | 0 | 0 |
| `auto` | 529 | 529 | 0 | 0 | 0 |

Almost every miss is a documented limit, not an error:

- CFRAC, the quadratic sieves and GNFS decline inputs below 1000.
- SQUFOF declines inputs of `2⁶²` and above.
- Fermat targets close factors.
- `2047` and `265679` defeat `p − 1` because both of their primes `p` have
  the same largest prime in `p − 1`.

ECM's own search splits every composite in its domain. That needed stage-1
backtracking: with small factors, all prime orders can be annihilated at once,
giving `gcd = n`. Without backtracking, 43 inputs of 6–9 digits were missed.

### Scaling on balanced semiprimes

Raw splitters on the dataset's balanced semiprimes, the hardest inputs of their
size for these methods, using 16 threads (`results/scaling.json`;
`scripts/scaling.py`). This table predates the current SIQS and number field
sieve; for those, see the comparison below: 80 digits in 13 s (SIQS) and in 26–28 s
(GNFS).

| Digits | `cfrac` | `qs` | `mpqs` | `siqs` | `gnfs` |
|---:|---:|---:|---:|---:|---:|
| 20 | 4 ms | 8 ms | 13 ms | 21 ms | 220 ms |
| 24 | 6 ms | 10 ms | 21 ms | 32 ms | 233 ms |
| 28 | 17 ms | 9 ms | 15 ms | 75 ms | 431 ms |
| 32 | 70 ms | 18 ms | 22 ms | 23 ms | 517 ms |
| 36 | 239 ms | 41 ms | 28 ms | 30 ms | 1.3 s |
| 40 | 864 ms | 89 ms | 46 ms | 26 ms | 1.6 s |
| 44 |  | 452 ms | 178 ms | 63 ms | 5.5 s |
| 48 |  | 1.2 s | 745 ms | 80 ms | 15 s |
| 52 |  |  | 2.5 s | 271 ms | 35 s |
| 55 |  |  | 5.0 s | 516 ms | 39 s |
| 60 |  |  |  | 1.3 s | 150 s |
| 64 |  |  |  | 2.7 s |  |
| 68 |  |  |  | 9.7 s |  |
| 71 |  |  |  | 12 s |  |
| 76 |  |  |  | 32 s |  |
| 80 |  |  |  | 181 s |  |

SIQS is the fastest method below ~90 digits, as in every mature implementation.
GNFS shows the expected subexponential growth.

## Dataset

[data/cases.json](data/cases.json) holds 831 cases. Each has an exact
reference factorization built independently of Lean in pure Python
(`scripts/generate_dataset.py`) and validated by `scripts/validate_dataset.py`.

| Tier | Cases | Contents |
|---|---:|---|
| core | 204 | 0 … 100, primes, prime powers, Carmichael numbers, 40 seeded semiprimes, 48 Cunningham numbers below 10⁸ |
| medium | 102 | inputs below 2⁶⁴: pseudoprimes, close and seeded semiprimes, 68 Cunningham numbers |
| large | 271 | 20–59 digits: 250 Cunningham numbers, 21 balanced semiprimes |
| huge | 253 | 60–100 digits: 243 Cunningham numbers, 10 balanced semiprimes |
| challenge | 1 | RSA-100 |

**The Cunningham Project** (S. S. Wagstaff Jr.) is the classical, long-running
benchmark of integer factorization. The pinned main-table snapshot `pmain126.txt`
(January 2026, SHA-256 `ad0ca986…2a42`, recorded in `data/provenance.json`)
supplies **every** `bⁿ − 1` with `b ∈ {2, 3, 5, 6, 7, 10, 11, 12}`, `n` odd and
at most 100 digits — 609 numbers in all. Full factorizations are rebuilt from
the primitive parts of the cyclotomic factors `Φ_d(b)`, `d ∣ n`, including
Aurifeuillian L/M lines and implicit probable-prime cofactors, then checked by
exact multiplication. The hardest is `2²⁷⁷ − 1 = 1121297 · P38 · P40`.

**RSA-100**, the smallest number of the RSA Factoring Challenge (factored
in 1991), is the challenge tier. It is not part of the timed benchmark tiers.
The general number field sieve (`factor --threads 16 gnfs`) factors it in
**6.1 minutes** on 16 cores: 366 s, the median of three runs in the comparison
below. Both 50-digit prime factors carry Pocklington certificates. An earlier
dedicated SIQS run (`factor --threads 16 siqs`, a 64,000-prime factor base)
took 6 h 35 min with 1.3 GB of memory (`results/hard-cases.json`).

Seeded balanced semiprimes of 20 to 80 digits (seed `20261007`) are included as
well. They are the hardest inputs of their size for the general-purpose methods.

## Optimization

Each optimization was measured on the same machine before it was adopted;
measurements that showed no gain are recorded too. All changes stay inside the
verified interfaces, so the correctness theorems were unaffected. Wall times
below use 16 cores unless noted.

**Algorithmic upgrades.** These are measured by `factorBench`
(`results/optimization.json`); the configurations are interleaved over rounds
and every result is validated.

| Suite (inputs) | Baseline | Optimized | Speedup |
|---|---|---|---:|
| Pollard rho, 6 semiprimes of 40–60 bits | Floyd: 27.8 ms | Brent, batched gcd: 18.8 ms | 1.48× |
| Trial division, 5 primes ≤ 10⁶ | every `d < n`: 4.40 ms | 6-wheel to `√n`: < 0.01 ms | > 400× |
| Trial division, 3 composites | `√n` bound: 2.23 ms | 6-wheel: 0.63 ms | 3.5× |
| ECM stage 1 with `B1 = 200`, 4 inputs | factorial exponent: 3.57 ms | maximal prime powers: 1.05 ms | 3.4× |
| ECM, 200 curves, `B1 = 2000`, 1 thread (`2^101−1`, `2^103−1`, `2^109−1`, `2^149−1`) | affine Weierstrass: 17.9 s | Montgomery x-only + stage 2: 3.07 s | 5.8× |
| QS family, 30–40-digit balanced semiprimes, 1 thread | QS: 589 ms | MPQS 303 ms; SIQS 93 ms | 6.3× |
| SIQS, 50-digit balanced semiprime | 1 thread: 510 ms | 16 threads: 147 ms | 3.5× |
| GNFS, 50-digit balanced semiprime, 16 threads | line sieve: 28.1 s | special-`q` lattice sieve: 15.0 s | 1.9× |
| Prime certificates, 5 primes of 19–44 digits | Lucas–Pratt: 32.4 ms | Pocklington: 21.4 ms | 1.5× |

Every returned divisor or certificate was validated. Full rows, including all
Brent batch sizes, are in `results/optimization.json`.

**Engineering optimizations found by profiling.** Each was measured in
isolation (`Dev/` harnesses).

| Change | Effect |
|---|---|
| SIQS trial division tests primes dividing `kn` by their zero root, instead of reducing the 80-digit `kn` modulo each of 25,000 primes per candidate | candidate processing 189 ms → 21 ms per 400 polynomials (9×); 80-digit throughput 65 → 82 full relations/s |
| SIQS factor bases re-tuned (2–3× the classical sizes, affordable after the change above) | 80 digits: 454 s → 196 s |
| Sieve thresholds scanned block-wise with a fold over 1 KiB blocks, instead of byte by byte | sieve scan 0.25 → 0.10 ms per polynomial; 80 digits: 196 s → 173 s |
| Exponent merge of large dependencies made tail recursive (proof re-done) | fixes a stack overflow that blocked SIQS from 76 digits on |
| GNFS: Pollard's special-`q` lattice sieve instead of line sieving | 40 digits 3.1 → 1.4 s; 50 digits 28 → 13 s; 60 digits: line sieving collected only 5k of ~30k needed relations in 25k lines, the lattice sieve finished in 209 s |
| GNFS polynomial selection scores sampled norms over the sieve region and scans leading coefficients up to `n^{1/(d+1)}` | 40 digits (line sieve) 5.5 → 3.1 s |
| GNFS lattice points verified by row position instead of `Int` arithmetic per prime | 50 digits 9.3 → 8.0 s |
| Structured Gaussian elimination: merging weight-two columns | 50-digit GNFS matrix 56,636 → 11,019 rows before dense elimination (1.6 s) |
| Hidden quadratic copies removed (arrays extended while still shared: GF(2) occurrence lists, large-prime graph adjacency, the GNFS relation set) | merge step 16.8 s → 0.18 s; GNFS 61 digits 209 → 160 s |
| Parallel tasks for ECM curves, sieve polynomials and special-`q` | SIQS at 80 digits: 1 → 16 threads is 10.2× faster; SMT (32 threads) adds nothing |
| *Rejected:* double-large-prime variation at 80 digits | 249 s vs 196 s without it, so it is off by default and available as `dlpFactor` |
| *Rejected:* replacing `%` by a conditional subtraction in the Gray-code root update | 13% slower (boxed `Nat` comparisons cost more than one division), so it was reverted |
| *Neutral:* fusing root updates with sieving for primes beyond the interval | within measurement noise |

**Later rewrites**, each measured in isolation as above (details in the commit
messages):

| Change | Effect |
|---|---|
| SIQS: new sieve and candidate kernels, block Lanczos, retuned parameters; fixed-width Montgomery arithmetic (generated per limb count) for ECM, `p − 1` and rho | SIQS at 80 digits: 181 s → 12.9 s |
| GNFS: Kleinjung collision polynomial selection, Franke–Kleinjung lattice siever, singleton and clique removal, merge, block Lanczos, square root checked modulo `n` | 60 digits: 150 s → 2.3 s; RSA-100 in 6.1 minutes instead of 6 h 35 min with SIQS |
| Special number field sieve for divisors of `bⁿ ± 1`, chosen by measured cost | `10⁹⁷ − 1`: 27.6 minutes → 12.7 s |
| ECM stage 2 with normalized baby and giant steps and a prime-pair schedule shared by all curves | 80 digits, `B1 = 50000`: stage 2 29.1 → 14.6 ms per curve |
| Plans and tables built lazily instead of at program start | startup 20 ms → 4 ms |

## Running

Install Lean with [elan](https://github.com/leanprover/elan), then:

```sh
lake exe cache get
lake build factor factorTests factorBench
lake test                                   # dataset, raw splitters, certificates
lake exe factor auto 1000036000099
lake exe factor --threads 16 siqs 1156520139572037013687948284592862858389101127447023443743633
lake exe factor --split gnfs 42962805687576751187092496809409988591255346056409
lake exe factor --threads 16 --ecm-b1 3000000 --ecm-curves 3000 ecm 358732406867153170156474773322218529607747057120388037569809480675786517167580313980579376220703124
lake exe factorBench results/optimization.json 3
python3 scripts/benchmark.py --tiers core medium large --jobs 12 --threads 3
python3 scripts/benchmark.py --split --tiers core medium large --output results/raw-splitters.json
python3 scripts/scaling.py --threads 16 --max-digits cfrac=40 qs=48 mpqs=56 siqs=80 gnfs=61
```

The CLI prints JSON. Factors are positive primes with multiplicity, and
negative inputs carry a separate sign. `1` gives an empty list; `0` gives
`null`. `--split` runs only the named algorithm's search; a `null` divisor is a
bounded search failure, not a claim of primality. Reports in `results/` are
gzip-compressed JSON (`gzip -dc results/…json.gz`).

`--threads T` bounds the parallelism: for inputs of 45 digits and more the CLI
runs itself once more with `LEAN_NUM_THREADS=T`, so that at most `T` worker
threads of the Lean runtime compute at once, even in nested parallel phases.

## Repository layout

| Path | Contents |
|---|---|
| `PrimeFactorLean/Core.lean` | engine `factorCoreWith`, `ProperFactor`, `ModEq`, `isqrt`, `minFac`, signed factorization |
| `PrimeFactorLean/Proofs/*.lean` | mathlib-based correctness proofs of the runtime modules (`factor_total_correct`, Pocklington, ECM formulas, …) |
| `PrimeFactorLean/Trial.lean` | trial division (reference, `√n`, 6-wheel) with completeness proofs |
| `PrimeFactorLean/Search.lean` | Fermat, Pollard rho, Brent, original `p − 1` |
| `PrimeFactorLean/SQUFOF.lean`, `PMinusOne.lean` | SQUFOF; `p − 1` and Williams `p + 1` with stage 2 |
| `PrimeFactorLean/ECM.lean`, `ECMMontgomery.lean` | affine ECM; Montgomery-curve ECM with stage 2 |
| `PrimeFactorLean/Squares.lean`, `GF2.lean` | proof-carrying relations and congruences of squares; GF(2) solver |
| `PrimeFactorLean/CFRAC.lean`, `QS.lean` | continued fractions; QS, MPQS, SIQS |
| `PrimeFactorLean/NFS/*.lean`, `GNFS.lean` | number field sieve: `ℤ[ω]` arithmetic with proofs, `𝔽_p[x]` routines, square roots, selection, line and lattice sieving, driver |
| `PrimeFactorLean/Pocklington.lean`, `Primality.lean` | Pocklington and Lucas–Pratt certificates |
| `PrimeFactorLean/Algorithms.lean` | public API (`Proofs/Algorithms.lean`: main theorems) |
| `Tests/` | regression tests, adversarial certificate tests, axiom audit, generated dataset |
| `Bench.lean`, `scripts/` | in-process optimization benchmarks; dataset, raw-splitter and scaling benchmarks |
| `Dev/` | tuning harnesses (`lake exe dev`) |
| `data/`, `results/` | dataset with provenance; benchmark reports |

Pinned environment: Lean `4.24.0`, mathlib `v4.24.0` (exact revisions in
`lake-manifest.json`). Measurements were taken on an AMD Ryzen 9 9955HX
(16 cores). MIT license.
