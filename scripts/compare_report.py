#!/usr/bin/env python3
"""Aggregate scripts/compare.py JSONL records into per-tier comparison tables.

For every (tool, case) the median wall time over its repeats is used, and only
if every repeat returned the exact reference factorization; otherwise the case
counts as failed for that tool. A tier is summarized by the number of solved
cases, the sum of the per-case medians, and the per-case ratio against the
baseline tool (geometric mean, and how many cases each tool won).
"""
import argparse, collections, json, math, pathlib, statistics


def load(paths):
    recs = []
    for p in paths:
        for line in pathlib.Path(p).read_text().splitlines():
            if line.strip():
                recs.append(json.loads(line))
    return recs


def medians(recs):
    """(tool, case) -> (median seconds or None if any repeat failed, record)."""
    groups = collections.defaultdict(list)
    for r in recs:
        groups[(r['tool'], r['case'])].append(r)
    out = {}
    for key, rs in groups.items():
        ok = all(r['status'] == 'pass' for r in rs)
        med = statistics.median(r['wall_ns'] for r in rs) / 1e9 if ok else None
        out[key] = (med, rs[0], len(rs), [r['status'] for r in rs])
    return out


def fmt(sec):
    if sec is None:
        return '—'
    if sec < 1:
        return f'{sec * 1000:.0f} ms'
    if sec < 100:
        return f'{sec:.2f} s'
    return f'{sec:.0f} s'


def report(recs, ours, base):
    med = medians(recs)
    tiers = ['core', 'medium', 'large', 'huge', 'challenge']
    cases = collections.OrderedDict()
    for r in recs:
        cases.setdefault(r['case'], r)
    lines = [f'| Tier | Cases | `{ours}` solved | `{base}` solved | `{ours}` total | '
             f'`{base}` total | Geo-mean ratio ({ours}/{base}) | `{ours}` faster on |',
             '|---|---:|---:|---:|---:|---:|---:|---:|']
    summary = {}
    for tier in tiers:
        ids = [c for c, r in cases.items() if r['tier'] == tier
               and (ours, c) in med and (base, c) in med]
        if not ids:
            continue
        so = [c for c in ids if med[(ours, c)][0] is not None]
        sb = [c for c in ids if med[(base, c)][0] is not None]
        both = [c for c in ids if c in so and c in sb]
        to = sum(med[(ours, c)][0] for c in so)
        tb = sum(med[(base, c)][0] for c in sb)
        ratios = [med[(ours, c)][0] / med[(base, c)][0] for c in both]
        gm = math.exp(sum(map(math.log, ratios)) / len(ratios)) if ratios else None
        wins = sum(1 for x in ratios if x < 1)
        summary[tier] = dict(cases=len(ids), ours_solved=len(so), base_solved=len(sb),
                             ours_total_s=to, base_total_s=tb, geomean_ratio=gm,
                             ours_faster=wins, compared=len(both))
        lines.append(f'| {tier} | {len(ids)} | {len(so)} | {len(sb)} | {fmt(to)} | {fmt(tb)} | '
                     f'{gm:.2f} | {wins}/{len(both)} |' if gm is not None else
                     f'| {tier} | {len(ids)} | {len(so)} | {len(sb)} | {fmt(to)} | {fmt(tb)} | — | — |')
    return '\n'.join(lines), summary, med


def case_table(recs, tools, ids=None):
    med = medians(recs)
    cases = collections.OrderedDict()
    for r in recs:
        cases.setdefault(r['case'], r)
    lines = ['| Case | Digits | ' + ' | '.join(f'`{t}`' for t in tools) + ' |',
             '|---|---:|' + '---:|' * len(tools)]
    for c, r in cases.items():
        if ids and c not in ids:
            continue
        cells = []
        for t in tools:
            m = med.get((t, c))
            if m is None:
                cells.append('')
            elif m[0] is None:
                cells.append('/'.join(sorted(set(m[3]))))
            else:
                cells.append(fmt(m[0]))
        lines.append(f'| {c} | {r["digits"]} | ' + ' | '.join(cells) + ' |')
    return '\n'.join(lines)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('jsonl', nargs='+')
    p.add_argument('--ours', default='lean-auto')
    p.add_argument('--base', default='yafu')
    p.add_argument('--cases', action='store_true', help='also print the per-case table')
    p.add_argument('--json', type=pathlib.Path, help='write the summary here')
    a = p.parse_args()
    recs = load(a.jsonl)
    table, summary, _ = report(recs, a.ours, a.base)
    print(table)
    if a.cases:
        tools = sorted({r['tool'] for r in recs})
        print()
        print(case_table(recs, tools))
    if a.json:
        a.json.write_text(json.dumps(summary, indent=1) + '\n')
