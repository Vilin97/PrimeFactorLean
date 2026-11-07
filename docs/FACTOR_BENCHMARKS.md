# Cross-library integer-factor benchmarks

`scripts/benchmark_factorization.py` runs PrimeFactorLean and FLINT on one shared
set of exact integer inputs. The Hex families are copied from
`kim-em/hex-dev/bench/HexIntFactor/Bench.lean` at source revision `6134cc450`.
The manifest is `data/hex-int-factor-inputs.json`.

The comparable factorization families are table controls, balanced semiprimes,
smooth `p - 1` inputs, ECM inputs, power forms, and the fixed FLINT regression
cases. The manifest also records Hex's replay, order, sigma, and divisor targets.
Those are separate Hex APIs and are not silently substituted with an unrelated
PrimeFactorLean operation.

Install the optional FLINT adapter with `python3 -m pip install python-flint`,
then run a small paired sample with

```sh
python3 scripts/benchmark_factorization.py --family balanced --repeats 3
```

PrimeFactorLean outputs are accepted only when the returned factors are prime
and reconstruct the input exactly. The reported `wall_ns` includes the CLI
process, while `elapsed_ns` is the timing emitted inside the Lean executable.
FLINT timings are in-process `fmpz.factor()` timings.

FLINT's own near-power-of-two profile can be requested with
`--flint-profile`. It uses the exact source ladder of 1, 32, 64, 128, 192, and
224 bits with 1,000,000, 100,000, 10,000, 100, 30, and 10 repetitions. This
mode is intentionally opt-in because reproducing the complete million-call
rows is long and is not a substitute for the exact-factor correctness runs.
