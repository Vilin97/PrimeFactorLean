#!/usr/bin/env python3
"""Animated progress chart of the verified Lean CLI against YAFU and CADO-NFS.

Every plotted value is a recorded measurement from results/compare/*.jsonl.
Each file is one head-to-head comparison run (scripts/compare.py): all tools
timed end to end, interleaved, on the same machine with the same thread budget.
Files are grouped into runs by their prefix (a commit of the Lean code, or a
label such as `before`); runs are ordered by the time of their first record.

A panel's value for a tool in a run is the sum over the panel's cases of the
median wall time of that tool's runs of the case. A panel is drawn only when
every case of the panel has a passing record for the tool in that run;
otherwise the run is marked "not measured" there. Runs with a single
repetition are drawn with hollow markers. Competitor times are those measured
in the same run (they vary slightly between runs with the machine's state).

Writes docs/progress.gif (and progress-final.png, the last frame) and
results/progress/progress.json (every plotted value, the runs and their files).
Needs Pillow only.

Usage: python3 scripts/progress_gif.py
"""
import collections
import json
import os
import pathlib
import statistics
from PIL import Image, ImageDraw, ImageFont

ROOT = pathlib.Path(__file__).resolve().parents[1]
COMPARE = ROOT / 'results' / 'compare'
OUT_GIF = ROOT / 'docs' / 'progress.gif'
OUT_PNG = ROOT / 'docs' / 'progress-final.png'
OUT_JSON = ROOT / 'results' / 'progress' / 'progress.json'

# Runs whose label is not a commit of the repository: what the label means.
LABEL_NOTES = {
    'before': 'binary before a69f221 (file label "before")',
    'ecmfast': 'working tree between 5459c81 and d964516 (file label "ecmfast")',
    'baselines': 'YAFU and CADO-NFS only (no Lean run)',
}

# (key, title, record filter, tools)
PANELS = [
    ('core', 'Core tier (204 cases)', lambda r: r['tier'] == 'core', ['lean-auto', 'yafu']),
    ('medium', 'Medium tier (102 cases)', lambda r: r['tier'] == 'medium', ['lean-auto', 'yafu']),
    ('large', 'Large tier, 20-59 digits (271)', lambda r: r['tier'] == 'large', ['lean-auto', 'yafu']),
    ('huge', 'Huge tier, 60-100 digits (253)', lambda r: r['tier'] == 'huge', ['lean-auto', 'yafu']),
    ('huge-balanced', 'Huge: balanced semiprimes 64-80d (10)',
     lambda r: r['tier'] == 'huge' and r['category'] == 'balanced-semiprime', ['lean-auto', 'yafu']),
    ('huge-cunningham', 'Huge: Cunningham numbers (243)',
     lambda r: r['tier'] == 'huge' and r['category'] == 'cunningham', ['lean-auto', 'yafu']),
    ('gnfs', 'GNFS: balanced semiprimes 60-80d (12)', lambda r: True, ['lean-gnfs', 'cado']),
    ('rsa100', 'RSA-100 (100 digits), GNFS', lambda r: r['case'] == 'rsa-100',
     ['lean-gnfs', 'cado', 'yafu']),
]
# which record files feed which panels
FILE_PANELS = {
    'core-medium-large': ['core', 'medium', 'large'],
    'auto-core-medium-large': ['core', 'medium', 'large'],
    'large': ['large'],
    'huge': ['huge', 'huge-balanced', 'huge-cunningham'],
    'auto-huge': ['huge', 'huge-balanced', 'huge-cunningham'],
    'gnfs-balanced': ['gnfs'],
    'rsa100': ['rsa100'],
}
TOOL_NAMES = {'lean-auto': 'Lean (auto)', 'lean-gnfs': 'Lean (GNFS)', 'yafu': 'YAFU 3.1.9',
              'cado': 'CADO-NFS 692ecb7'}
TOOL_COLORS = {'lean': (31, 100, 180), 'yafu': (230, 120, 20), 'cado': (40, 150, 60)}


def tool_color(tool):
    return TOOL_COLORS['lean' if tool.startswith('lean') else tool]


def load_runs():
    groups = collections.defaultdict(list)
    for f in sorted(COMPARE.glob('*.jsonl')):
        prefix, _, kind = f.stem.partition('-')
        groups[prefix].append((kind, f))
    runs = []
    for prefix, files in groups.items():
        recs_by_panel = collections.defaultdict(list)
        first = None
        for kind, f in files:
            recs = [json.loads(line) for line in open(f) if line.strip()]
            for r in recs:
                first = r['time'] if first is None or r['time'] < first else first
            for key in FILE_PANELS.get(kind, []):
                recs_by_panel[key] += [(r, f.name) for r in recs]
        runs.append({'label': prefix, 'first': first, 'files': sorted(f.name for _, f in files),
                     'recs': recs_by_panel})
    runs.sort(key=lambda r: r['first'])
    return runs


def panel_values(run, panel):
    key, _, keep, tools = panel
    recs = [r for r, _ in run['recs'].get(key, []) if keep(r)]
    out = {}
    if not recs:
        return out
    cases = sorted({r['case'] for r in recs})
    for tool in tools:
        times = collections.defaultdict(list)
        for r in recs:
            if r['tool'] == tool and r['status'] == 'pass':
                times[r['case']].append(r['wall_ns'] / 1e9)
        if not times:
            continue
        missing = [c for c in cases if c not in times]
        reps = min(len(v) for v in times.values())
        threads = sorted({r['threads'] for r in recs if r['tool'] == tool})
        out[tool] = {
            'complete': not missing,
            'missing_cases': missing,
            'cases': len(cases),
            'reps': reps,
            'threads': threads,
            'total_s': sum(statistics.median(v) for v in times.values()) if not missing else None,
        }
    return out


def font(size, bold=False):
    names = ['DejaVuSans-Bold.ttf' if bold else 'DejaVuSans.ttf']
    for d in ['/usr/share/fonts/truetype/dejavu', '/usr/share/fonts/dejavu']:
        for n in names:
            p = os.path.join(d, n)
            if os.path.exists(p):
                return ImageFont.truetype(p, size)
    return ImageFont.load_default(size=size)


def nice_max(v):
    if v <= 0:
        return 1.0
    e = 10 ** int(f'{v:e}'.split('e')[1])
    for m in (1, 1.2, 1.5, 2, 2.5, 3, 4, 5, 6, 8, 10):
        if v <= m * e:
            return m * e
    return 10 * e


def fmt_s(v):
    return f'{v:.0f} s' if v >= 100 else (f'{v:.1f} s' if v >= 10 else f'{v:.2f} s')


W, H = 1600, 1040
COLS, ROWS = 4, 2
TOP, BOTTOM = 124, 150
LEFT, RIGHT = 20, 20


def draw_frame(runs, values, upto):
    img = Image.new('RGB', (W, H), (255, 255, 255))
    d = ImageDraw.Draw(img)
    f_title, f_sub = font(26, True), font(16)
    f_panel, f_tick, f_ann = font(16, True), font(13), font(14, True)
    cur = runs[upto]
    d.text((LEFT + 4, 10), 'PrimeFactorLean (verified, Lean 4) vs YAFU 3.1.9 and CADO-NFS: '
           'total wall time per benchmark panel', fill=(0, 0, 0), font=f_title)
    d.text((LEFT + 4, 44), 'Same machine (AMD Ryzen 9 9955HX laptop, 16 cores), 16 threads for every tool, '
           'same inputs. Each value: sum over the panel\'s cases of the median of 3 interleaved', fill=(60, 60, 60),
           font=f_sub)
    d.text((LEFT + 4, 64), 'end-to-end runs (hollow marker: 1 run). Lower is better; "Nx faster" = '
           'competitor time / Lean time in the same run.', fill=(60, 60, 60), font=f_sub)
    note = LABEL_NOTES.get(cur['label'], 'commit ' + cur['label'])
    d.text((LEFT + 4, 88), f'Comparison run {upto + 1} of {len(runs)}: {cur["label"]}  '
           f'({cur["first"][:16].replace("T", " ")} UTC; {note})', fill=(150, 20, 20), font=f_panel)
    pw = (W - LEFT - RIGHT) // COLS
    ph = (H - TOP - BOTTOM) // ROWS
    n = len(runs)
    for pi, panel in enumerate(PANELS):
        key, title, _, tools = panel
        px, py = LEFT + (pi % COLS) * pw, TOP + (pi // COLS) * ph
        # plot area
        x0, x1 = px + 62, px + pw - 14
        y0, y1 = py + 28, py + ph - 70
        d.text((px + 8, py + 4), title, fill=(0, 0, 0), font=f_panel)
        vals = [values[i][key] for i in range(n)]
        allv = [v[t]['total_s'] for v in vals for t in v if v[t]['total_s']]
        # the axis covers the values within 2.5x of the median; larger ones are
        # drawn as arrows at the top edge with their value
        med = statistics.median(allv) if allv else 1.0
        vmax = max([x for x in allv if x <= 2.5 * med] + [0])
        top = nice_max(vmax * 1.08)
        d.rectangle([x0, y0, x1, y1], outline=(160, 160, 160))
        for k in range(6):
            yv = top * k / 5
            yy = y1 - (y1 - y0) * k / 5
            d.line([x0, yy, x1, yy], fill=(232, 232, 232))
            d.text((x0 - 6, yy), fmt_s(yv) if k else '0', fill=(80, 80, 80), font=f_tick, anchor='rm')

        def xpos(i):
            return x0 + (x1 - x0) * (i + 0.5) / n

        # current run band, run numbers
        d.rectangle([xpos(upto) - (x1 - x0) / (2 * n), y0 + 1, xpos(upto) + (x1 - x0) / (2 * n), y1 - 1],
                    fill=(253, 238, 238))
        for i in range(n):
            d.text((xpos(i), y1 + 4), str(i + 1), fill=(0, 0, 0) if i == upto else (110, 110, 110),
                   font=f_tick, anchor='mt')
        for tool in tools:
            col = tool_color(tool)
            pts = []
            for i in range(upto + 1):
                v = vals[i].get(tool)
                if v and v['total_s'] is not None:
                    yy = y1 - (y1 - y0) * min(v['total_s'], top) / top
                    pts.append((xpos(i), yy, v['reps'] > 1))
                    if v['total_s'] > top:
                        xx = xpos(i)
                        d.polygon([(xx, y0 - 2), (xx - 6, y0 + 9), (xx + 6, y0 + 9)], fill=col)
                        d.text((xx + 8, y0 + 2 + 15 * (i % 2) + 30 * tools.index(tool)),
                               fmt_s(v['total_s']), fill=col, font=f_tick)
                else:
                    pts.append(None)
            seg = []
            for p in pts + [None]:
                if p is None:
                    if len(seg) > 1:
                        d.line([(a, b) for a, b, _ in seg], fill=col, width=3)
                    seg = []
                else:
                    seg.append(p)
            for p in pts:
                if p is None:
                    continue
                xx, yy, full = p
                r = 5
                shape = [xx - r, yy - r, xx + r, yy + r]
                if tool.startswith('lean'):
                    d.ellipse(shape, fill=col if full else (255, 255, 255), outline=col, width=2)
                elif tool == 'yafu':
                    d.rectangle(shape, fill=col if full else (255, 255, 255), outline=col, width=2)
                else:
                    d.polygon([(xx, yy - r - 1), (xx - r - 1, yy + r), (xx + r + 1, yy + r)],
                              fill=col if full else (255, 255, 255), outline=col)
        # not measured markers
        for i in range(upto + 1):
            if not any(vals[i].get(t) and vals[i][t]['total_s'] is not None for t in tools):
                xx = xpos(i)
                d.line([xx - 4, y1 - 14, xx + 4, y1 - 6], fill=(150, 150, 150), width=2)
                d.line([xx - 4, y1 - 6, xx + 4, y1 - 14], fill=(150, 150, 150), width=2)
        # annotation of the current run
        cv = vals[upto]
        lean = next((t for t in tools if t.startswith('lean')), None)
        lines = []
        if lean and cv.get(lean) and cv[lean]['total_s']:
            lt = cv[lean]['total_s']
            lines.append((f'Lean {fmt_s(lt)}', tool_color(lean)))
            for t in tools:
                if t == lean or not cv.get(t) or not cv[t]['total_s']:
                    continue
                ot = cv[t]['total_s']
                ratio = ot / lt
                verdict = f'{ratio:.2f}x faster' if ratio >= 1 else f'{1 / ratio:.2f}x slower'
                lines.append((f'{TOOL_NAMES[t].split()[0]} {fmt_s(ot)}: Lean {verdict}', tool_color(t)))
        else:
            lines.append(('not measured in this run', (150, 150, 150)))
        for k, (txt, col) in enumerate(lines):
            d.text((x0 + 2, y1 + 22 + 16 * k), txt, fill=col, font=f_ann)
    # legend and run key
    ly = H - BOTTOM + 8
    lx = LEFT + 8
    for tool, name in [('lean-auto', 'Lean CLI (auto: Lean panels 1-6, GNFS: 7-8)'),
                       ('yafu', 'YAFU 3.1.9 (factor)'), ('cado', 'CADO-NFS 692ecb7 (GNFS)')]:
        col = tool_color(tool)
        d.line([lx, ly + 9, lx + 30, ly + 9], fill=col, width=3)
        d.text((lx + 38, ly), name, fill=(0, 0, 0), font=f_sub)
        lx += 70 + int(d.textlength(name, font=f_sub))
    d.line([lx, ly + 5, lx + 8, ly + 13], fill=(150, 150, 150), width=2)
    d.line([lx, ly + 13, lx + 8, ly + 5], fill=(150, 150, 150), width=2)
    d.text((lx + 16, ly), 'not measured in that run;  ▲ value above the axis', fill=(120, 120, 120), font=f_sub)
    key_lines, line = [], ''
    for i, r in enumerate(runs):
        item = f'{i + 1} {r["label"]} ({r["first"][5:10]})'
        if d.textlength(line + '   ' + item, font=f_tick) > W - 2 * LEFT - 20:
            key_lines.append(line)
            line = item
        else:
            line = item if not line else line + '   ' + item
    key_lines.append(line)
    for k, txt in enumerate(key_lines):
        d.text((LEFT + 8, ly + 30 + 17 * k), ('Runs: ' if k == 0 else '      ') + txt,
               fill=(60, 60, 60), font=f_tick)
    d.text((LEFT + 8, H - 26), 'Data: results/compare/*.jsonl (raw records), results/progress/progress.json '
           '(plotted values); script: scripts/progress_gif.py', fill=(110, 110, 110), font=f_tick)
    return img


def main():
    runs = load_runs()
    values = [{p[0]: panel_values(r, p) for p in PANELS} for r in runs]
    # runs that feed no panel (e.g. competitor-only baselines) are left out
    keep = [i for i in range(len(runs)) if any(values[i][p[0]] for p in PANELS)]
    runs = [runs[i] for i in keep]
    values = [values[i] for i in keep]
    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    data = {
        'description': 'Sum over the cases of each panel of the median wall time (seconds) of each '
                       'tool, per comparison run; null when a case of the panel lacks a passing '
                       'record for the tool in that run.',
        'panels': [{'key': k, 'title': t, 'tools': tools} for k, t, _, tools in PANELS],
        'runs': [{'index': i + 1, 'label': r['label'], 'first_record': r['first'],
                  'note': LABEL_NOTES.get(r['label'], 'commit ' + r['label']), 'files': r['files'],
                  'panels': values[i]} for i, r in enumerate(runs)],
    }
    OUT_JSON.write_text(json.dumps(data, indent=1) + '\n')
    frames = [draw_frame(runs, values, k) for k in range(len(runs))]
    OUT_GIF.parent.mkdir(parents=True, exist_ok=True)
    pal = [f.convert('P', palette=Image.Palette.ADAPTIVE, colors=64) for f in frames]
    durations = [1400] * (len(pal) - 1) + [6000]
    pal[0].save(OUT_GIF, save_all=True, append_images=pal[1:], duration=durations, loop=0,
                optimize=True)
    frames[-1].save(OUT_PNG)
    print(f'{len(runs)} runs, {OUT_GIF} ({OUT_GIF.stat().st_size // 1024} KiB)')


if __name__ == '__main__':
    main()
