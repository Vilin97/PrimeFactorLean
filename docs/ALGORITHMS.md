# Algorithms and what their proofs establish

The public specification is deliberately short:

```lean
IsFactorization n factors :=
  (∀ p ∈ factors, Nat.Prime p) ∧ factors.prod = n
```

`Algorithms.factor_correct` proves this specification for every selected
algorithm and every configuration whenever `factor` returns a list.
`factor_total_correct` additionally states that every positive input has such
a successful result. Zero returns
`none`; one returns the empty list. Signed inputs use positive prime factors and
a separate sign, with `factorSigned_correct` proving their product is the original
integer. Repeated prime factors are repeated list entries. The specification
does not require sorted output.

## Complete factorization and bounded searches

The search routines produce a **proper divisor**, rather than a complete prime
factorization. A successful split satisfies

```lean
1 < d ∧ d < n ∧ d ∣ n
```

The complete engine recursively factors `d` and `n / d`. Both arguments are
strictly smaller than `n`. A verified primality certificate can finish a prime
leaf immediately. If a bounded search gives up and no certificate is available,
the engine uses exact trial division through `Nat.minFac`. Consequently the
complete engine terminates mathematically on every positive input and its
correctness does not rely on random-walk or smoothness assumptions. This
fallback can be prohibitively slow on large inputs.

`none` from a **raw search** means its configured work budget was exhausted or
its attempted parameters failed. It does not mean that the input is prime. Raw
search success and complete factorization success should be reported separately
in benchmarks: a successful fallback is not evidence that rho, ECM, or a sieve
found the factor.

The probable-prime screen in `Algorithms.lean` guides candidate generation. It
does not justify a prime leaf. `PrimeCertificate.check_sound` and the Lucas/Pratt
checker establish primality before the certificate oracle accepts that leaf.

## Implemented searches

| Search | Actual computation | Mathematical invariants in the source |
| --- | --- | --- |
| Trial reference | Test successive candidate divisors with an explicit budget. | `trialSearchAux_sound` and `trialSearchAux_none_iff` describe the searched interval. |
| Square-root trial | Stop once the candidate exceeds the square root of the current input. | `trialSearch_sound`, `trialSearch_none_prime`, and `trialCore_correct`. |
| 6-wheel trial | Check 2 and 3 separately, then test the candidate pairs `6k − 1`, `6k + 1` through the square root. | `trialWheelAux_sound`, `trialWheelAux_none_iff`, the residue-class completeness argument, `trialWheelSearch_none_prime`, and `trialWheelCore_correct`. |
| Fermat | Starting at the ceiling of `sqrt n`, test whether `a² − n` is an integer square; try `a − b`. | `fermat_difference_identity` proves `(a + b)(a − b) = n` from the square equality. `fermatLoop_sound` and `fermat_sound` cover successful outputs. |
| Pollard rho, Floyd | Iterate `x ↦ x² + c mod n` with one walker advancing once and the other twice, taking gcds of their differences. Restart with deterministic seeds. | `rhoStep_congruent` proves compatibility with every divisor modulus. `floydIterate_correct` proves the one/two-walker schedule. `rho_collision_divides_gcd` connects a modular collision to the computed gcd. `rhoLoop_sound` and `rho_sound` cover successful outputs. |
| Pollard rho, Brent | Use doubling cycle blocks, modular products of differences, and one gcd per batch. Recover individual differences if a batch gcd is the whole input. | `brentBlock_iterates` and `brentBlock_product` give the exact executed orbit and product. `brent_collision_divides_gcd` proves that batching retains a collided divisor. The imperative loop returns proof-carrying factors; `brentAttempt_sound` and `brent_sound` establish its public result invariant. |
| Pollard p−1, stage one | Build maximal prime powers up to the bound, use binary modular powering, and check each prefix. Precompute the schedule once across restart bases. | `modPow_correct`, `primePower_is_power`, `primePower_le_bound`, `primePower_maximal`, `powerSchedule_correct`, and `pMinusOne_step_exponent` identify the actual arithmetic. `pMinusOneLoop_sound` and `pMinusOne_sound` cover successful outputs. |
| ECM, stage one | Seed affine Weierstrass curves with a known point. Compute inverses by extended Euclid; extract gcds from nonunit denominators or the discriminant. Use binary scalar multiplication and maximal prime powers. | `inverse_correct`, `seeded_point_on_curve`, `add_preserves_curve`, `multiply_preserves_curve`, and `stageOne_preserves_curve` prove actual modular arithmetic and curve-equation preservation. `split_sound` proves successful outputs are proper divisors. |
| Basic quadratic sieve | Exactly sieve positive values of `x² − n` at modular roots of the factor-base primes. Store smooth relations, eliminate parity rows over F₂, reconstruct square products, and try both gcd signs. | `stripPower_factorization`, `factorOverBase_factorization`, `smooth_relation_congruence`, and `even_powerProduct_is_square` prove the relation arithmetic and square reconstruction. `split_sound` proves proper-divisor output soundness. |
| Multiple-polynomial QS | Select products `A` of factor-base primes, assemble CRT roots `B`, and flip roots in Gray-code order. Sieve the quotient polynomial `Q(x) = ((Ax + B)² − n) / A`. Include the factors of `A` in every relation's exponents. | `mpqs_polynomial_identity` and `mpqs_relation_congruence` prove the exact quotient-polynomial arithmetic. `splitMPQS_sound` proves proper-divisor output soundness. The same smooth-relation and exponent-square invariants support reconstruction. |
| Quadratic number-field prototype | Select `X² + c` with `m² + c = n`; collect smooth rational values and algebraic norms, combine parity dependencies, and check an actual algebraic square root. | `selected_polynomial`, `polynomial_no_rational_root`, `norm_mul`, `evaluate_mul_mod`, `evaluate_product_mod`, and `square_roots_congruence` prove the number-field construction. Square-root results and successful factors carry proofs. |

Every search uses exact `Nat`/`Int` arithmetic. None relies on floating-point
rounding. ECM retains `splitFactorial` as a reference schedule for comparing the
prime-power optimization; both schedules have curve-preservation proofs.

## Limits of these theorems

The complete factorization theorem establishes the final mathematical answer.
The listed execution invariants explain more of the search than a final divisor
check alone, but their scope is precise:

- No theorem claims that a fixed rho, ECM, or sieve budget succeeds on every
  composite input.
- No expected-time, success-probability, or subexponential complexity bound is
  formalized.
- The ECM curve-preservation lemmas do not yet identify the executable scalar
  routine with abstract elliptic-curve group multiplication after reduction
  modulo a prime, nor prove the usual smooth-group-order success condition.
- The QS relation and square lemmas do not yet provide a whole-program theorem
  for the imperative F₂ elimination routine. Square reconstruction rejects odd
  exponent sums, and divisor certification protects the complete factorizer.
- The prime-power arithmetic is proved; enumeration of the small primes into
  the p−1 schedule does not yet have a completeness theorem.

## Number-field scope

The degree-two method is a small **number-field prototype**, not a production
GNFS implementation. Norm parity is only a prefilter: a square algebraic norm
does not imply that the algebraic element is square. The implementation checks
the two integer coefficients of the proposed algebraic root and rejects a
dependency without a valid root.

Production general number field sieve requires substantially more machinery:
higher-degree polynomial selection, prime-ideal and character columns, lattice
sieving, relation filtering, large sparse linear algebra, and an efficient
algebraic square-root algorithm. These components, the advanced production
SIQS features, ECM stage two, and Pollard p−1 stage two are not implemented
here. The prototype has no claim
to GNFS's asymptotic performance or ability to factor RSA challenge sizes.

## Primary references

- R. P. Brent, *An improved Monte Carlo factorization algorithm* (1980):
  [author's paper page](https://maths-people.anu.edu.au/~brent/pub/pub051.html).
- H. W. Lenstra, Jr., *Factoring integers with elliptic curves* (1987):
  [Annals of Mathematics](https://annals.math.princeton.edu/1987/126-3/p09).
- C. Pomerance, *A Tale of Two Sieves* (1996):
  [author's PDF](https://math.dartmouth.edu/~carlp/PDF/paper109.pdf).
- A. K. Lenstra and H. W. Lenstra, Jr., eds., *The Development of the Number
  Field Sieve* (1993):
  [Springer](https://link.springer.com/book/10.1007/BFb0091534).
- The CADO-NFS Development Team:
  [official implementation and phase description](https://cado-nfs.gitlabpages.inria.fr/).
- Mathlib's [Lucas primality theorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LucasPrimality.html).

## Cubic number-field prototype

`CubicNumberFieldSieve.split` selects a monic base-m cubic with a checked prime-field irreducibility certificate, collects rational and degree-one prime-ideal `(p,r)` relations, computes exact determinant norms, and searches a finite dictionary of actual algebraic squares. The executable norm is proved equal to the signed Sylvester resultant on linear elements. Multiplication, norm multiplicativity, reduction at the selected modular root, and the actual two-root square congruence are kernel proved. Raw `2479` returns `37` with factor base bound31; both37 and67 lie outside that base.

This is a bounded cubic educational implementation. It omits arbitrary-degree selection, character columns, lattice sieving, scalable sparse linear algebra, and a general efficient algebraic square-root algorithm. A dependency alone does not certify an algebraic square; the exact coefficient equality is checked. It does not complete the modern GNFS requirement. Primary reference: Matthew E. Briggs, [An Introduction to the General Number Field Sieve](https://intranet.math.vt.edu/people/brown/doc/briggs_gnfs_thesis.pdf), Virginia Tech,1998, Chapters2–4.
