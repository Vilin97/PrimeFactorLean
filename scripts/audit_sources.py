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


def import_closure(module):
    """Project modules reachable from `module`, and every external import they make."""
    seen, external, todo = set(), set(), [module]
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        path = ROOT / (m.replace('.', '/') + '.lean')
        for line in path.read_text().splitlines():
            mm = re.match(r'^import\s+(\S+)', line)
            if not mm:
                continue
            dep = mm.group(1)
            if dep.split('.')[0] in ('PrimeFactorLean', 'Dev'):
                todo.append(dep)
            else:
                external.add(dep)
    return seen, external


# Lean 4.24's compiler rewrites `0 - x` to `x` (for `Nat` and fixed-width integers);
# executed code must not contain the pattern (write `-x` for fixed-width negation).
ZERO_SUB = re.compile(r'(?<![\w.])0\s*-\s*[A-Za-z(]')
for path in sorted((ROOT / 'PrimeFactorLean').rglob('*.lean')):
    if 'Proofs' in path.parts:
        continue
    for lineno, line in enumerate(uncomment(path.read_text()).splitlines(), 1):
        if ZERO_SUB.search(line):
            raise SystemExit(f'{path}:{lineno}: `0 - x` is miscompiled by Lean 4.24: {line.strip()}')
print('PASS no `0 - x` in runtime code (miscompiled by Lean 4.24).')

# The factoring executable must not load mathlib or the Lean frontend: its import
# closure may use only Lean's core library (`Init`) and `Std` containers.
for exe in ['Main', 'Dev.Main']:
    mods, ext = import_closure(exe)
    bad = sorted(e for e in ext if e.split('.')[0] not in ('Init', 'Std'))
    if bad:
        raise SystemExit(f'{exe}: runtime import closure must avoid mathlib/Lean, found {bad}')
    print(f'PASS runtime closure of {exe}: {len(mods)} project modules, external imports {sorted(ext)}.')
