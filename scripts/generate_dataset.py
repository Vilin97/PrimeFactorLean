#!/usr/bin/env python3
"""Reproducible factorization dataset with independent reference factorizations.

Sources
-------
* The Cunningham Project main tables (pinned snapshot, SHA-256 recorded in
  data/provenance.json). Every b^n - 1 with b in {2,3,5,6,7,10,11,12}, n odd and
  at most 100 decimal digits whose table entry is completely factored is
  included. Full factorizations are rebuilt from the primitive parts of the
  cyclotomic factors Phi_d(b), d | n, as listed in the table (including
  Aurifeuillian L/M lines and implicit probable-prime cofactors), then checked
  by exact multiplication.
* RSA-100 from the RSA Factoring Challenge (factored in 1991), as a challenge.
* Edge cases, exhaustive small inputs, prime powers, pseudoprimes, and seeded
  balanced semiprimes (seed 20261007) for controlled sizes.

The data is an oracle for tests only; no Lean algorithm reads it. Primality of
reference factors is checked here with a strong probable-prime test to 25
bases (and the Lean side certifies primes independently with Pocklington
certificates).
"""
from __future__ import annotations
import argparse, hashlib, json, math, pathlib, random, re, urllib.request

ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCE = 'https://homes.cerias.purdue.edu/~ssw/cun/pmain126.txt'
SOURCE_SHA256 = 'ad0ca98600df26bc07bd682f7be479c520a7f0359adfc2987f09312377726a42'
SEED = 20261007
RSA100 = (
    1522605027922533360535618378132637429718068114961380688657908494580122963258952897654000350692006139,
    37975227936943673922808872755445627854565536638199,
    40094690950920881030683735292761468389214899724061)
BASES = [2, 3, 5, 6, 7, 10, 11, 12]
SMALL_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
                73, 79, 83, 89, 97]


def prime(n: int) -> bool:
    """Strong probable-prime test to 25 prime bases (deterministic below 3.3e24)."""
    if n < 2:
        return False
    for p in SMALL_PRIMES:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in SMALL_PRIMES:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def small_factors(n: int) -> list[int]:
    """Reference factorization for n < 2^64 by trial division and Pollard rho."""
    if n == 1:
        return []
    if prime(n):
        return [n]
    for p in SMALL_PRIMES:
        if n % p == 0:
            return sorted([p] + small_factors(n // p))
    for c in range(1, 200):
        x = y = 2
        d = 1
        while d == 1:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = math.gcd(abs(x - y), n)
        if d != n:
            return sorted(small_factors(d) + small_factors(n // d))
    raise RuntimeError(f'reference factorizer failed: {n}')


def next_prime(n: int) -> int:
    while not prime(n):
        n += 1
    return n


def random_prime(digits: int, rng: random.Random) -> int:
    return next_prime(rng.randrange(10 ** (digits - 1), 10 ** digits))


# --- Cunningham tables -----------------------------------------------------

def mobius(n: int) -> int:
    r, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return 0
            r = -r
        p += 1
    return -r if n > 1 else r


def cyclotomic_value(n: int, b: int) -> int:
    num = den = 1
    for d in range(1, n + 1):
        if n % d == 0:
            mu = mobius(n // d)
            if mu == 1:
                num *= b ** d - 1
            elif mu == -1:
                den *= b ** d - 1
    assert num % den == 0
    return num // den


def parse_tables(text: str) -> dict[str, dict[int, str]]:
    tables: dict[str, dict[int, str]] = {}
    current = None
    last = None
    for line in text.splitlines():
        m = re.match(r'\s*Table\s+(\S+)', line)
        if m:
            current = m.group(1)
            tables[current] = {}
            last = None
            continue
        if current is None:
            continue
        aur = re.match(r'^\s+([LM])\s+(.*)$', line)
        if aur and last is not None:
            tables[current][last] += ' ' + aur.group(2).strip()
            continue
        m = re.match(r'^\s{1,6}(\d+)\s+(.*)$', line)
        if m:
            last = int(m.group(1))
            tables[current][last] = m.group(2).strip()
            continue
        if last is not None and line.strip() and re.match(r'^\s{7,}\S', line):
            tables[current][last] += ' ' + line.strip()
    return tables


def primitive_tokens(entry: str) -> list[str]:
    body = re.sub(r'\([^)]*\)', '', entry).strip()
    return [t for t in re.split(r'[.\s]+', body) if t and t not in ('L', 'M')]


def cunningham_factorization(tables, b: int, n: int) -> list[int] | None:
    """Full factorization of b^n - 1 (n odd) from the primitive parts, or None."""
    table = tables[f'{b}-']
    factors: list[int] = []
    for d in range(1, n + 1):
        if n % d:
            continue
        if d == 1:
            factors += small_factors(b - 1)
            continue
        if d not in table:
            return None
        phi = cyclotomic_value(d, b)
        explicit = 1
        for tok in primitive_tokens(table[d]):
            tok = tok.rstrip('*')
            if tok.startswith('C'):
                return None
            if tok.startswith('P'):
                continue
            factors.append(int(tok))
            explicit *= int(tok)
        if phi % explicit:
            return None
        rest = phi // explicit
        if rest != 1:
            if not prime(rest):
                return None  # two implicit cofactors; not reconstructed here
            factors.append(rest)
    factors.sort()
    assert math.prod(factors) == b ** n - 1
    return factors


# --- Dataset -----------------------------------------------------------------

def tier_for(n: int) -> str:
    if n < 10 ** 8:
        return 'core'
    if n < 2 ** 64:
        return 'medium'
    if n < 10 ** 60:
        return 'large'
    return 'huge'


def generate(source_path: pathlib.Path | None = None) -> None:
    rows = []

    def add(name, n, kind, factors=None, source='generated', line=None, tier=None):
        if factors is None and n != 0:
            assert n < 2 ** 64
            factors = small_factors(n)
        if factors is not None:
            assert math.prod(factors) == n and all(prime(p) for p in factors), name
            factors = sorted(factors)
        rows.append(dict(id=name, n=str(n),
                         factors=None if factors is None else [str(p) for p in factors],
                         digits=len(str(n)), category=kind, tier=tier or tier_for(n),
                         source=source, source_line=line))

    add('zero', 0, 'edge', tier='core')
    add('one', 1, 'edge', tier='core')
    for n in range(2, 101):
        add(f'small-{n}', n, 'exhaustive-small')
    for n in [127, 257, 65537, 999983, 1000003, 15485863, 2147483647]:
        add(f'prime-{n}', n, 'prime')
    for p, e in [(2, 32), (3, 20), (5, 12), (7, 9), (97, 4), (1009, 3)]:
        add(f'power-{p}-{e}', p ** e, 'prime-power')
    for n in [561, 1105, 1729, 2465, 2821, 6601, 3215031751, 341550071728321]:
        add(f'pseudoprime-{n}', n, 'pseudoprime')
    for p, q in [(1009, 1013), (10007, 10009), (1000003, 1000033), (15485863, 15485917),
                 (2147483647, 2147483629), (65537, 1000000007), (257, 1000003)]:
        add(f'semiprime-{p}-{q}', p * q, 'close-semiprime' if q - p < 100 else 'semiprime')
    rng = random.Random(SEED)
    for i in range(40):
        p = next_prime(rng.randrange(100, 10000))
        q = next_prime(rng.randrange(100, 10000))
        add(f'seeded-core-{i}', p * q, 'seeded-semiprime')
    for i in range(20):
        p = next_prime(rng.randrange(10000, 1000000))
        q = next_prime(rng.randrange(10000, 1000000))
        add(f'seeded-medium-{i}', p * q, 'seeded-semiprime')
    # Balanced semiprimes of controlled size (two per size).
    for digits in range(20, 81, 4):
        for k in range(2):
            p = random_prime(digits // 2, rng)
            q = random_prime(digits - digits // 2, rng)
            add(f'balanced-{digits}-{k}', p * q, 'balanced-semiprime', [p, q])
    # Cunningham numbers.
    raw = source_path.read_bytes() if source_path else urllib.request.urlopen(SOURCE, timeout=60).read()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != SOURCE_SHA256:
        raise SystemExit(f'Cunningham snapshot hash mismatch: {digest}')
    tables = parse_tables(raw.decode())
    skipped = []
    for b in BASES:
        n = 3 if b == 2 else 1
        while len(str(b ** n - 1)) <= 100:
            factors = cunningham_factorization(tables, b, n)
            if factors is None:
                skipped.append(f'{b},{n}-')
            else:
                entry = tables[f'{b}-'].get(n)
                add(f'cunningham-{b}-{n}-minus', b ** n - 1, 'cunningham', factors, SOURCE,
                    None if entry is None else f'{n} {entry}')
            n += 2
    p, q = RSA100[1], RSA100[2]
    assert p * q == RSA100[0]
    add('rsa-100', RSA100[0], 'rsa-challenge', [p, q],
        'RSA Factoring Challenge (RSA Laboratories, 1991); factored by A. K. Lenstra and M. Manasse',
        tier='challenge')

    output = json.dumps(rows, indent=1) + '\n'
    (ROOT / 'data').mkdir(exist_ok=True)
    (ROOT / 'data/cases.json').write_text(output)
    tiers = {t: sum(r['tier'] == t for r in rows) for t in ['core', 'medium', 'large', 'huge', 'challenge']}
    provenance = dict(
        source_url=SOURCE, retrieved='2026-10-07', source_sha256=digest,
        tables=[f'{b}-' for b in BASES], seed=SEED,
        cunningham_rule='b^n - 1, b in {2,3,5,6,7,10,11,12}, n odd, at most 100 digits, '
                        'complete factorization reconstructable from the table',
        cunningham_skipped=skipped,
        rsa100='RSA-100 = 37975227936943673922808872755445627854565536638199 * '
               '40094690950920881030683735292761468389214899724061',
        reference='Pure Python exact arithmetic: Cunningham factorizations from the pinned '
                  'table and cyclotomic values; Pollard rho for small generated inputs; '
                  'strong probable-prime test to 25 bases for every reference factor.',
        tiers=tiers, cases_sha256=hashlib.sha256(output.encode()).hexdigest())
    (ROOT / 'data/provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')
    lean = ['-- Generated by scripts/generate_dataset.py; do not edit.', 'namespace Tests',
            'structure DatasetCase where', '  name : String', '  n : Nat',
            '  factors : Option (List Nat)', '  tier : String', '  deriving Repr', '']
    chunk = 50
    parts = []
    for start in range(0, len(rows), chunk):
        part = rows[start:start + chunk]
        name = f'dataset{start // chunk}'
        parts.append(name)
        lean.append(f'def {name} : List DatasetCase := [')
        for i, r in enumerate(part):
            fs = 'none' if r['factors'] is None else 'some [' + ', '.join(r['factors']) + ']'
            lean.append(f'  ⟨{json.dumps(r["id"])}, {r["n"]}, {fs}, {json.dumps(r["tier"])}⟩'
                        + (',' if i + 1 < len(part) else ''))
        lean += [']', '']
    lean += ['def dataset : List DatasetCase :=', '  ' + ' ++\n  '.join(parts), '', 'end Tests', '']
    (ROOT / 'Tests/Dataset.lean').write_text('\n'.join(lean))
    print(json.dumps({'rows': len(rows), **tiers, 'skipped': len(skipped),
                      'cases_sha256': provenance['cases_sha256']}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--source-file', type=pathlib.Path)
    generate(parser.parse_args().source_file)
