#!/usr/bin/env python3
"""Run the compiled `factor` CLI on the dataset and compare with the oracle.

Each algorithm is run on the slice of the dataset it is designed for (its
*domain*, by input size; see DOMAINS). A row passes only if the complete
factorization equals the independently produced reference. Timeouts and
errors are recorded, never counted as passes. Wall time includes process
startup; `elapsedNs` is measured inside Lean.

Use --split to benchmark raw splitters instead: composite inputs only, a row
passes only if the algorithm itself returns a proper divisor (no prime
certificates, no fallback).
"""
import argparse, hashlib, json, pathlib, platform, statistics, subprocess, time
from concurrent.futures import ThreadPoolExecutor

ROOT = pathlib.Path(__file__).resolve().parents[1]

# Largest input (decimal digits) each algorithm is expected to finish promptly.
DOMAINS = {
    'trial-reference': 8, 'trial': 9, 'wheel': 9, 'fermat': 8, 'rho': 20, 'brent': 20,
    'squfof': 19, 'pminusone': 8, 'pplusone': 8, 'ecm-affine': 12, 'ecm': 30, 'cfrac': 40,
    'qs': 45, 'mpqs': 55, 'siqs': 100, 'gnfs': 50, 'auto': 100,
}
TIMEOUTS = {'core': 20, 'medium': 60, 'large': 300, 'huge': 1800, 'challenge': 86400}


def run_case(binary, alg, case, timeout, threads, split):
    n = case['n']
    args = [str(binary), '--threads', str(threads)]
    args += ['--split', alg, n] if split else [alg, n]
    record = dict(algorithm=alg, case=case['id'], n=n, digits=case['digits'], tier=case['tier'])
    start = time.perf_counter_ns()
    try:
        proc = subprocess.run(args, text=True, capture_output=True, timeout=timeout)
        record['wall_ns'] = time.perf_counter_ns() - start
        if proc.returncode != 0:
            record.update(status='error', stderr=proc.stderr[-1000:])
            return record
        out = json.loads(proc.stdout)
        record['elapsedNs'] = out.get('elapsedNs')
        if split:
            d = out['divisor']
            if d is None:
                record['status'] = 'miss'
            else:
                d, v = int(d), int(n)
                record['status'] = 'split' if 1 < d < v and v % d == 0 else 'wrong'
                record['divisor'] = str(d)
        else:
            actual = out.get('factors')
            actual = None if actual is None else sorted(map(int, actual))
            expected = None if case['factors'] is None else list(map(int, case['factors']))
            record['status'] = 'pass' if actual == expected else 'wrong'
            if record['status'] == 'wrong':
                record['output'] = out
    except subprocess.TimeoutExpired:
        record.update(status='timeout', wall_ns=time.perf_counter_ns() - start)
    return record


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--algorithms', nargs='+', default=list(DOMAINS))
    p.add_argument('--tiers', nargs='+', default=['core', 'medium', 'large'])
    p.add_argument('--max-digits', type=int, help='override every domain limit')
    p.add_argument('--domain', nargs='*', default=[], help='per-algorithm limits, e.g. siqs=80')
    p.add_argument('--jsonl', type=pathlib.Path, help='append each record here as it completes; '
                   'records already present are reused (resume)')
    p.add_argument('--timeout', type=float, help='override per-tier timeouts (seconds)')
    p.add_argument('--threads', type=int, default=8, help='Lean tasks per factorization')
    p.add_argument('--jobs', type=int, default=1, help='factorizations run concurrently')
    p.add_argument('--split', action='store_true', help='raw splitters on composites only')
    p.add_argument('--cases', nargs='*', help='restrict to these case ids')
    p.add_argument('--output', type=pathlib.Path, default=ROOT / 'results/benchmark.json')
    p.add_argument('--binary', type=pathlib.Path, default=ROOT / '.lake/build/bin/factor')
    a = p.parse_args()
    raw = (ROOT / 'data/cases.json').read_bytes()
    cases = [c for c in json.loads(raw) if c['tier'] in a.tiers]
    if a.cases:
        cases = [c for c in cases if c['id'] in a.cases]
    if a.split:
        cases = [c for c in cases if c['factors'] is not None and len(c['factors']) > 1]
    overrides = {k: int(v) for k, v in (x.split('=') for x in a.domain)}
    done = {}
    if a.jsonl and a.jsonl.exists():
        for line in a.jsonl.read_text().splitlines():
            r = json.loads(line)
            done[(r['algorithm'], r['case'])] = r
    jobs = []
    for alg in a.algorithms:
        limit = a.max_digits if a.max_digits is not None else overrides.get(alg, DOMAINS[alg])
        for c in cases:
            if c['digits'] <= limit:
                timeout = a.timeout if a.timeout is not None else TIMEOUTS[c['tier']]
                jobs.append((alg, c, timeout))
    import threading
    lock = threading.Lock()

    def work(j):
        key = (j[0], j[1]['id'])
        if key in done:
            return done[key]
        r = run_case(a.binary, j[0], j[1], j[2], a.threads, a.split)
        if a.jsonl:
            with lock, a.jsonl.open('a') as f:
                f.write(json.dumps(r) + '\n')
        return r

    with ThreadPoolExecutor(max_workers=a.jobs) as pool:
        records = list(pool.map(work, jobs))
    statuses = ['split', 'miss'] if a.split else ['pass']
    statuses += ['wrong', 'timeout', 'error']
    summary = {}
    for alg in a.algorithms:
        group = [r for r in records if r['algorithm'] == alg]
        if not group:
            continue
        ok = [r for r in group if r['status'] in ('pass', 'split')]
        summary[alg] = dict(total=len(group), **{s: sum(r['status'] == s for r in group) for s in statuses},
                            median_ms=statistics.median([r['elapsedNs'] / 1e6 for r in ok]) if ok else None,
                            max_digits_ok=max([r['digits'] for r in ok], default=None))
        print(json.dumps(dict(algorithm=alg, **summary[alg])), flush=True)
    domains = {alg: (a.max_digits if a.max_digits is not None else overrides.get(alg, DOMAINS[alg]))
               for alg in a.algorithms}
    report = dict(dataset_sha256=hashlib.sha256(raw).hexdigest(), tiers=a.tiers, split=a.split,
                  threads=a.threads, jobs=a.jobs, domains=domains, timeouts=TIMEOUTS,
                  platform=platform.platform(), processor=platform.processor(),
                  python=platform.python_version(), summary=summary, records=records,
                  note='Wall time includes process startup; elapsedNs is measured inside Lean. '
                       'A pass requires the exact reference factorization.')
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(report, indent=1) + '\n')
    if any(r['status'] in ('wrong', 'error') for r in records):
        raise SystemExit(1)


if __name__ == '__main__':
    main()
