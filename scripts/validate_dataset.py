#!/usr/bin/env python3
import hashlib,json,math,pathlib
from generate_dataset import prime
ROOT=pathlib.Path(__file__).resolve().parents[1]
raw=(ROOT/'data/cases.json').read_bytes();cases=json.loads(raw);provenance=json.loads((ROOT/'data/provenance.json').read_text())
assert hashlib.sha256(raw).hexdigest()==provenance['cases_sha256']
assert len({r['id'] for r in cases})==len(cases)
for r in cases:
 n=int(r['n']);assert 0<=n<2**64
 fs=r['factors']
 if fs is None:assert n==0
 else:
  fs=list(map(int,fs));assert math.prod(fs)==n and fs==sorted(fs) and all(prime(p) for p in fs)
print(f'PASS {len(cases)} exact factorization oracles and dataset hash.')
