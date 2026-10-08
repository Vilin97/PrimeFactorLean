#!/usr/bin/env python3
"""Time raw splitters on the dataset's balanced semiprimes, one run at a time.

Balanced semiprimes are the hardest inputs of their size for the general-purpose
methods (no small factor for ECM or rho to find). Every returned divisor is
checked against the reference factorization.
"""
import argparse, json, pathlib, platform, subprocess, time

ROOT = pathlib.Path(__file__).resolve().parents[1]


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--algorithms', nargs='+', default=['cfrac', 'qs', 'mpqs', 'siqs', 'gnfs'])
    p.add_argument('--max-digits', nargs='+', default=[], help='alg=digits limits, e.g. gnfs=60')
    p.add_argument('--threads', type=int, default=16)
    p.add_argument('--timeout', type=float, default=3600)
    p.add_argument('--variant', type=int, default=0, help='which of the two cases per size')
    p.add_argument('--output', type=pathlib.Path, default=ROOT / 'results/scaling.json')
    p.add_argument('--binary', type=pathlib.Path, default=ROOT / '.lake/build/bin/factor')
    a = p.parse_args()
    limits = dict(x.split('=') for x in a.max_digits)
    cases = [c for c in json.loads((ROOT / 'data/cases.json').read_text())
             if c['category'] == 'balanced-semiprime' and c['id'].endswith(f'-{a.variant}')]
    rows = []
    for alg in a.algorithms:
        for c in cases:
            if c['digits'] > int(limits.get(alg, 1000)):
                continue
            start = time.perf_counter()
            try:
                out = subprocess.run([str(a.binary), '--threads', str(a.threads), '--split', alg, c['n']],
                                     text=True, capture_output=True, timeout=a.timeout)
                res = json.loads(out.stdout)
                d = res['divisor']
                ok = d is not None and d in c['factors']
                row = dict(algorithm=alg, case=c['id'], digits=c['digits'],
                           status='split' if ok else ('miss' if d is None else 'wrong'),
                           seconds=res['elapsedNs'] / 1e9)
            except subprocess.TimeoutExpired:
                row = dict(algorithm=alg, case=c['id'], digits=c['digits'], status='timeout',
                           seconds=time.perf_counter() - start)
            rows.append(row)
            print(json.dumps(row), flush=True)
            if row['status'] != 'split':
                break
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(dict(threads=a.threads, platform=platform.platform(),
                                        processor=platform.processor(), rows=rows), indent=1) + '\n')


if __name__ == '__main__':
    main()
