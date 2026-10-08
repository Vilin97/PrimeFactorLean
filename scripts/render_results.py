#!/usr/bin/env python3
"""Render Markdown tables for the README from the benchmark reports in results/."""
import gzip, json, pathlib, statistics, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]


def load(name):
    for path in [ROOT / 'results' / name, ROOT / 'results' / (name + '.gz')]:
        if path.exists():
            opener = gzip.open if path.suffix == '.gz' else open
            with opener(path, 'rt') as f:
                return json.load(f)
    return None


def huge_rows():
    rep = load('dataset-huge.json')
    out = {}
    if rep:
        for alg, s in rep['summary'].items():
            out[alg] = (s['pass'], s['total'], s.get('timeout', 0), s['max_digits_ok'], rep['domains'][alg])
    return out


def raw_table():
    rep = load('raw-splitters.json')
    if not rep:
        return '(raw-splitter report missing)'
    lines = ['| Algorithm | Composites in domain | Split by its own search | Misses (bounded search gave up) | Timeouts | Wrong |',
             '|---|---:|---:|---:|---:|---:|']
    for alg, s in rep['summary'].items():
        lines.append(f"| `{alg}` | {s['total']} | {s['split']} | {s['miss']} | {s['timeout']} | {s['wrong']} |")
    return '\n'.join(lines)


def scaling_table():
    rep = load('scaling.json')
    if not rep:
        return '(scaling report missing)'
    algs = []
    for r in rep['rows']:
        if r['algorithm'] not in algs:
            algs.append(r['algorithm'])
    digits = sorted({r['digits'] for r in rep['rows']})
    cell = {(r['algorithm'], r['digits']): r for r in rep['rows']}
    head = '| Digits | ' + ' | '.join(f'`{a}`' for a in algs) + ' |'
    sep = '|---:|' + '---:|' * len(algs)
    lines = [head, sep]
    for d in digits:
        row = [str(d)]
        for a in algs:
            r = cell.get((a, d))
            if r is None:
                row.append('')
            elif r['status'] == 'split':
                sec = r['seconds']
                row.append(f'{sec * 1000:.0f} ms' if sec < 1 else
                           (f'{sec:.1f} s' if sec < 10 else f'{sec:.0f} s'))
            else:
                row.append(r['status'])
        lines.append('| ' + ' | '.join(row) + ' |')
    return '\n'.join(lines)


def bench_table():
    rep = load('optimization.json')
    if not rep:
        return '(optimization report missing)'
    lines = ['| Suite | Configuration | Inputs | Divisors / certificates returned | Median per round |',
             '|---|---|---:|---:|---:|']
    for row in rep['rows']:
        ms = row['medianRoundNs'] / 1e6
        t = f'{ms:.2f} ms' if ms < 1000 else f'{ms / 1000:.2f} s'
        lines.append(f"| {row['suite']} | `{row['algorithm']}` | {len(row['inputs'])} | "
                     f"{row['returnedDivisors']} / {row['calls']} | {t} |")
    return '\n'.join(lines)


if __name__ == '__main__':
    what = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if what in ('huge', 'all'):
        print(json.dumps(huge_rows()))
    if what in ('raw', 'all'):
        print(raw_table())
    if what in ('scaling', 'all'):
        print(scaling_table())
    if what in ('bench', 'all'):
        print(bench_table())
