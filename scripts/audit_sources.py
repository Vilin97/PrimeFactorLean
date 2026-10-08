#!/usr/bin/env python3
"""Source hygiene complementing the kernel axiom-closure audit in Tests/Audit.lean.

Rejects proof escape hatches and unchecked implementation substitutions in every
Lean source of the project (comments and string literals are ignored).
"""
import pathlib, re

ROOT = pathlib.Path(__file__).resolve().parents[1]
BANNED = r'\b(?:sorry|admit|axiom|native_decide|unsafe|partial|implemented_by|extern)\b'


def uncomment(s: str) -> str:
    out = []
    i = 0
    depth = 0
    quoted = False
    while i < len(s):
        if depth:
            if s[i:i + 2] == '/-':
                depth += 1
                i += 2
            elif s[i:i + 2] == '-/':
                depth -= 1
                i += 2
            else:
                i += 1
        elif quoted:
            if s[i] == '\\':
                i += 2
            elif s[i] == '"':
                quoted = False
                i += 1
            else:
                i += 1
        elif s[i:i + 2] == '/-':
            depth = 1
            i += 2
        elif s[i:i + 2] == '--':
            j = s.find('\n', i)
            i = len(s) if j == -1 else j
        elif s[i] == '"':
            quoted = True
            i += 1
        else:
            out.append(s[i])
            i += 1
    return ''.join(out)


files = sorted(p for folder in ['PrimeFactorLean', 'Tests', 'Dev'] for p in (ROOT / folder).rglob('*.lean'))
files += [ROOT / name for name in ['PrimeFactorLean.lean', 'Main.lean', 'Bench.lean', 'lakefile.lean']]
for path in files:
    bad = re.findall(BANNED, uncomment(path.read_text()))
    if bad:
        raise SystemExit(f'{path}: prohibited escape hatches: {bad}')
print(f'PASS source hygiene: no proof escape hatches in {len(files)} Lean files.')
