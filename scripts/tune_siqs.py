#!/usr/bin/env python3
"""Grid search for the fast SIQS parameter table (`SIQS.paramTable`).

Runs `lake exe dev fastsiqsp N THREADS FB M LPMULT DLPDIV SPV SLACK` on balanced
semiprimes of the dataset, each run under the shared benchmark lock, and
prints/records wall times. Usage:

  python3 scripts/tune_siqs.py --digits 50 --fb 1000 1500 2000 --m 32768 65536 --out tune.jsonl
"""
import argparse, fcntl, itertools, json, pathlib, re, subprocess, time

ROOT = pathlib.Path(__file__).resolve().parents[1]
DEV = ROOT / '.lake/build/bin/dev'


def cases_for(digits):
    cases = json.loads((ROOT / 'data/cases.json').read_text())
    out = [c for c in cases if c['category'] == 'balanced-semiprime' and abs(c['digits'] - digits) <= 1]
    return out


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--digits', type=int, required=True)
    p.add_argument('--n', help='explicit input instead of dataset cases')
    p.add_argument('--fb', nargs='+', type=int, required=True)
    p.add_argument('--m', nargs='+', type=int, required=True)
    p.add_argument('--lp', nargs='+', type=int, default=[80])
    p.add_argument('--dlp', nargs='+', type=int, default=[0])
    p.add_argument('--spv', nargs='+', type=int, default=[20])
    p.add_argument('--slack', nargs='+', type=int, default=[3])
    p.add_argument('--threads', type=int, default=16)
    p.add_argument('--reps', type=int, default=1)
    p.add_argument('--out', type=pathlib.Path)
    a = p.parse_args()
    inputs = [a.n] if a.n else [c['n'] for c in cases_for(a.digits)][:2]
    lock = open('/tmp/vas-timed-benchmarks.lock', 'a')
    for fb, m, lp, dlp, spv, slack in itertools.product(a.fb, a.m, a.lp, a.dlp, a.spv, a.slack):
        times = []
        for n in inputs:
            for _ in range(a.reps):
                fcntl.flock(lock, fcntl.LOCK_EX)
                try:
                    t0 = time.perf_counter()
                    out = subprocess.run([str(DEV), 'fastsiqsp', n, str(a.threads), str(fb), str(m),
                                          str(lp), str(dlp), str(spv), str(slack)],
                                         capture_output=True, text=True, timeout=3600).stdout
                    dt = time.perf_counter() - t0
                finally:
                    fcntl.flock(lock, fcntl.LOCK_UN)
                ok = 'some' in out
                times.append(dt if ok else float('inf'))
        rec = dict(digits=a.digits, fb=fb, m=m, lp=lp, dlp=dlp, spv=spv, slack=slack,
                   threads=a.threads, times=times, total=sum(times))
        print(json.dumps(rec), flush=True)
        if a.out:
            with a.out.open('a') as f:
                f.write(json.dumps(rec) + '\n')


if __name__ == '__main__':
    main()
