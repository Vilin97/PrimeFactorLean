#!/usr/bin/env python3
"""Run FLINT/Hex/PrimeFactorLean integer-factor comparison cases.

Hex operands come from kim-em/hex-dev bench/HexIntFactor/Bench.lean. FLINT's
near-power-of-two p-factor profile is included as an optional exact ladder.
Every PrimeFactorLean and FLINT result is checked by reconstructing the input
from prime factors. Hex-only APIs are represented in the input manifest and
reported as unsupported rather than replaced by an unrelated operation.
"""
from __future__ import annotations
import argparse, json, math, pathlib, statistics, subprocess, time

ROOT = pathlib.Path(__file__).resolve().parents[1]
DEFAULT_INPUTS = ROOT / "data/hex-int-factor-inputs.json"


def is_prime(n: int) -> bool:
    # FLINT's primality predicate is used only to validate benchmark output,
    # never by PrimeFactorLean itself. It handles the large Hex factors without
    # the quadratic trial loop that would make the harness look like a factor.
    try:
        from flint import fmpz
        return bool(fmpz(n).is_prime())
    except ImportError:
        if n < 2: return False
        if n % 2 == 0: return n == 2
        d, s = n - 1, 0
        while d % 2 == 0: d, s = d // 2, s + 1
        for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
            if a >= n: continue
            x = pow(a, d, n)
            if x in (1, n - 1): continue
            for _ in range(s - 1):
                x = x * x % n
                if x == n - 1: break
            else: return False
        return True


def run_pfl(binary: pathlib.Path, n: int, algorithm: str, threads: int, timeout: float) -> dict:
    started = time.perf_counter_ns()
    try:
        proc = subprocess.run([str(binary), "--threads", str(threads), algorithm, str(n)],
                              capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"status": "timeout", "wall_ns": time.perf_counter_ns() - started}
    wall = time.perf_counter_ns() - started
    if proc.returncode:
        return {"status": "error", "wall_ns": wall, "stderr": proc.stderr[-1000:]}
    try:
        out = json.loads(proc.stdout)
        factors = sorted(int(x) for x in (out.get("factors") or []))
        valid = bool(factors) and math.prod(factors) == n and all(is_prime(x) for x in factors)
        return {"status": "pass" if valid else "wrong", "wall_ns": wall,
                "elapsed_ns": out.get("elapsedNs"), "factors": factors}
    except (ValueError, KeyError, json.JSONDecodeError) as exc:
        return {"status": "error", "wall_ns": wall, "stderr": str(exc)}


def run_flint(n: int) -> dict:
    try:
        from flint import fmpz
    except ImportError:
        return {"status": "unavailable", "error": "install python-flint"}
    started = time.perf_counter_ns()
    factors = []
    for p, exponent in fmpz(n).factor():
        factors.extend([int(p)] * int(exponent))
    wall = time.perf_counter_ns() - started
    factors.sort()
    valid = bool(factors) and math.prod(factors) == n and all(is_prime(x) for x in factors)
    return {"status": "pass" if valid else "wrong", "wall_ns": wall, "factors": factors}


def cases(data: dict, include_profile: bool) -> list[tuple[str, int]]:
    f = data["families"]
    out = []
    for i, n in enumerate(f["table"]): out.append((f"table-{i}", n))
    for bits, n in zip((32, 40, 48, 56, 64, 72, 80), f["balanced"]): out.append((f"balanced-{bits}", n))
    for bits, n in zip((32, 40, 48, 56, 64, 72, 76, 80), f["smooth"]): out.append((f"smooth-{bits}", n))
    for bits, n in zip((48, 56, 64, 72, 76, 80), f["ecm"]): out.append((f"ecm-{bits}", n))
    for e in f["power_exponents"]: out.append((f"power-2^{e}-1", 2 ** e - 1))
    for n in data["flint_regressions"]: out.append(("flint-regression", n))
    if include_profile:
        for bits, reps in zip(data["flint_profile"]["bits"], data["flint_profile"]["repetitions"]):
            for i in range(reps): out.append((f"flint-profile-{bits}", 2 ** max(0, bits - 1) + i))
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tool", choices=("pfl", "flint", "both"), default="both")
    ap.add_argument("--algorithm", default="auto")
    ap.add_argument("--binary", type=pathlib.Path, default=ROOT / ".lake/build/bin/factor")
    ap.add_argument("--inputs", type=pathlib.Path, default=DEFAULT_INPUTS)
    ap.add_argument("--family", action="append", help="substring filter, repeatable")
    ap.add_argument("--repeats", type=int, default=3)
    ap.add_argument("--threads", type=int, default=1)
    ap.add_argument("--timeout", type=float, default=120.0)
    ap.add_argument("--flint-profile", action="store_true", help="run FLINT's exact repetition ladder")
    ap.add_argument("--json", type=pathlib.Path, default=ROOT / "results/factorization-comparison.json")
    args = ap.parse_args()
    data = json.loads(args.inputs.read_text())
    selected = cases(data, args.flint_profile)
    if args.family:
        selected = [(label, n) for label, n in selected
                    if any(fragment in label for fragment in args.family)]
    records = []
    for label, n in selected:
        for repeat in range(args.repeats):
            rec = {"case": label, "n": str(n), "repeat": repeat}
            if args.tool in ("pfl", "both"):
                rec["pfl"] = run_pfl(args.binary, n, args.algorithm, args.threads, args.timeout)
            if args.tool in ("flint", "both"):
                rec["flint"] = run_flint(n)
            records.append(rec)
            print(json.dumps(rec, sort_keys=True), flush=True)
    args.json.parent.mkdir(parents=True, exist_ok=True)
    summary = {}
    for tool in ("pfl", "flint"):
        values = [r[tool]["wall_ns"] / 1e6 for r in records
                  if tool in r and r[tool].get("status") == "pass"]
        summary[tool] = {"pass": len(values), "median_ms": statistics.median(values) if values else None,
                         "total_ms": sum(values)}
    args.json.write_text(json.dumps({"inputs": str(args.inputs), "algorithm": args.algorithm,
                                     "repeats": args.repeats, "threads": args.threads,
                                     "summary": summary, "records": records}, indent=2) + "\n")
    print(json.dumps({"summary": summary}, sort_keys=True))


if __name__ == "__main__":
    main()
