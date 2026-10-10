#!/usr/bin/env python3
"""Generate PrimeFactorLean/MontGen.lean: fixed-width Montgomery arithmetic.

For every limb count L in LIMBS, the generated module defines

* `N{L}`: a residue as L limbs of 28 bits held in `UInt64` fields (the
  structure is a constructor with unboxed scalar fields, so arithmetic compiles
  to straight-line `uint64_t` code and results reuse dead cells in place);
* `Mod{L}`: an odd modulus `n < 2^(28 L)` with its limbs and `-n⁻¹ mod 2^28`;
* Montgomery multiplication and squaring (finely integrated product scanning,
  radix 2^28: column sums stay below 2^61 for L ≤ 12, so a single machine word
  accumulates them), modular addition and subtraction, and conversions;
* an instance of `Mont.Arith` so that generic code (ECM, P-1) specializes to
  each width.

This is untrusted search arithmetic: every factor found with it is a gcd that
is checked against `n`.

Usage: python3 scripts/gen_mont.py > PrimeFactorLean/MontGen.lean
"""
LIMBS = range(1, 13)
M = '0xFFFFFFF'


def gen(L):
    out = []
    w = out.append
    fields = ' '.join(f'l{i}' for i in range(L))
    w(f'/-- A residue modulo a `Mod{L}` in Montgomery form: {L} limbs of 28 bits. -/')
    w(f'structure N{L} where')
    for i in range(L):
        w(f'  l{i} : UInt64')
    w('  deriving Inhabited')
    w('')
    w(f'/-- An odd modulus below `2^{28 * L}` with its limbs and `-n⁻¹ mod 2^28`. -/')
    w(f'structure Mod{L} where')
    w('  n : Nat')
    for i in range(L):
        w(f'  n{i} : UInt64')
    w('  ninv : UInt64')
    w('')
    # constructor of the modulus
    w(f'def Mod{L}.ofNat (n : Nat) : Mod{L} :=')
    w(f'  ⟨n, ' + ', '.join(f'(n >>> {28 * i} &&& {M}).toUInt64' for i in range(L))
      + ', negInv28 (n &&& {M}).toUInt64⟩'.replace('{M}', M))
    w('')
    # limbs of a natural number
    w(f'@[inline] def N{L}.ofLimbs (x : Nat) : N{L} :=')
    w('  ⟨' + ', '.join(f'(x >>> {28 * i} &&& {M}).toUInt64' for i in range(L)) + '⟩')
    w('')
    w(f'@[inline] def N{L}.limbNat (a : N{L}) : Nat :=')
    terms = [f'(a.l{i}.toNat <<< {28 * i})' for i in range(L)]
    w('  ' + ' ||| '.join(terms))
    w('')
    w(f'@[inline] def N{L}.isZero (a : N{L}) : Bool :=')
    w('  (' + ' ||| '.join(f'a.l{i}' for i in range(L)) + ') == 0')
    w('')
    # final conditional subtraction: u (limbs u0..), top carry c
    def final_sub(prefix, ulist, carry):
        lines = []
        b = '0'
        for i, u in enumerate(ulist):
            bt = '' if b == '0' else f' - {b}'
            lines.append(f'  let t{i} := {u} + 0x10000000 - m.n{i}{bt}')
            lines.append(f'  let d{i} := t{i} &&& {M}')
            lines.append(f'  let b{i + 1} := (1 : UInt64) - (t{i} >>> 28)')
            b = f'b{i + 1}'
        # use d when carry = 1 or no final borrow
        lines.append(f'  let s := ({carry} ||| ((1 : UInt64) - {b})) * {M}')
        res = ', '.join(f'{u} ^^^ (({u} ^^^ d{i}) &&& s)' for i, u in enumerate(ulist))
        lines.append(f'  ⟨{res}⟩')
        return lines
    # multiplication
    w(f'/-- Montgomery product `a b R⁻¹ mod n` (`R = 2^{28 * L}`), inputs and output in `[0, n)`. -/')
    w(f'@[inline] def N{L}.mul (m : Mod{L}) (a b : N{L}) : N{L} :=')
    w(f'  let msk : UInt64 := {M}')
    w('  let acc : UInt64 := 0')
    for i in range(L):
        terms = [f'a.l{j} * b.l{i - j}' for j in range(i + 1)] + [f'q{j} * m.n{i - j}' for j in range(i)]
        w(f'  let acc := acc + ' + ' + '.join(terms))
        w(f'  let q{i} := ((acc &&& msk) * m.ninv) &&& msk')
        w(f'  let acc := (acc + q{i} * m.n0) >>> 28')
    for i in range(L, 2 * L):
        js = range(i - L + 1, L)
        terms = [f'a.l{j} * b.l{i - j}' for j in js] + [f'q{j} * m.n{i - j}' for j in js]
        if terms:
            w(f'  let acc := acc + ' + ' + '.join(terms))
        w(f'  let u{i - L} := acc &&& msk')
        w('  let acc := acc >>> 28')
    for line in final_sub('', [f'u{i}' for i in range(L)], 'acc'):
        w(line)
    w('')
    # squaring
    w(f'/-- Montgomery square. -/')
    w(f'@[inline] def N{L}.sqr (m : Mod{L}) (a : N{L}) : N{L} :=')
    w(f'  let msk : UInt64 := {M}')
    w('  let acc : UInt64 := 0')
    def sq_terms(k):
        ts = []
        for i in range(L):
            j = k - i
            if j < i or j >= L:
                continue
            if i == j:
                ts.append(f'a.l{i} * a.l{i}')
            else:
                ts.append(f'((a.l{i} * a.l{j}) <<< 1)')
        return ts
    for i in range(L):
        terms = sq_terms(i) + [f'q{j} * m.n{i - j}' for j in range(i)]
        w(f'  let acc := acc + ' + ' + '.join(terms))
        w(f'  let q{i} := ((acc &&& msk) * m.ninv) &&& msk')
        w(f'  let acc := (acc + q{i} * m.n0) >>> 28')
    for i in range(L, 2 * L):
        js = range(i - L + 1, L)
        terms = sq_terms(i) + [f'q{j} * m.n{i - j}' for j in js]
        if terms:
            w(f'  let acc := acc + ' + ' + '.join(terms))
        w(f'  let u{i - L} := acc &&& msk')
        w('  let acc := acc >>> 28')
    for line in final_sub('', [f'u{i}' for i in range(L)], 'acc'):
        w(line)
    w('')
    # addition
    w(f'/-- `a + b mod n`. -/')
    w(f'@[inline] def N{L}.add (m : Mod{L}) (a b : N{L}) : N{L} :=')
    w(f'  let msk : UInt64 := {M}')
    c = '0'
    for i in range(L):
        ct = '' if c == '0' else f' + {c}'
        w(f'  let x{i} := a.l{i} + b.l{i}{ct}')
        w(f'  let c{i + 1} := x{i} >>> 28')
        w(f'  let v{i} := x{i} &&& msk')
        c = f'c{i + 1}'
    for line in final_sub('', [f'v{i}' for i in range(L)], c):
        w(line)
    w('')
    # subtraction
    w(f'/-- `a - b mod n`. -/')
    w(f'@[inline] def N{L}.sub (m : Mod{L}) (a b : N{L}) : N{L} :=')
    w(f'  let msk : UInt64 := {M}')
    b = '0'
    for i in range(L):
        bt = '' if b == '0' else f' - {b}'
        w(f'  let t{i} := a.l{i} + 0x10000000 - b.l{i}{bt}')
        w(f'  let d{i} := t{i} &&& msk')
        w(f'  let b{i + 1} := (1 : UInt64) - (t{i} >>> 28)')
        b = f'b{i + 1}'
    # add n back if borrow: masked limbs
    w(f'  let s := {b} * msk')
    c = '0'
    for i in range(L):
        ct = '' if c == '0' else f' + {c}'
        w(f'  let y{i} := d{i} + (m.n{i} &&& s){ct}')
        if i + 1 < L:
            w(f'  let e{i + 1} := y{i} >>> 28')
        c = f'e{i + 1}'
    w('  ⟨' + ', '.join(f'y{i} &&& msk' for i in range(L)) + '⟩')
    w('')
    w(f'instance : Arith N{L} Mod{L} where')
    w(f'  mul := N{L}.mul')
    w(f'  sqr := N{L}.sqr')
    w(f'  add := N{L}.add')
    w(f'  sub := N{L}.sub')
    w(f'  modulus := Mod{L}.n')
    w(f'  ofLimbs _ x := N{L}.ofLimbs x')
    w(f'  limbNat := N{L}.limbNat')
    w(f'  isZero := N{L}.isZero')
    w(f'  limbs := {L}')
    w('')
    return '\n'.join(out)


def main():
    print('''-- Generated by scripts/gen_mont.py; do not edit by hand.
import PrimeFactorLean.Mont

/-!
# Fixed-width Montgomery arithmetic (generated)

Residues modulo odd `n < 2^(28 L)` as `L` limbs of 28 bits in unboxed `UInt64`
fields, for `L = 1, …, 12`. See `scripts/gen_mont.py` and `PrimeFactorLean.Mont`.
-/

namespace PrimeFactorLean.Mont
''')
    for L in LIMBS:
        print(gen(L))
    print('end PrimeFactorLean.Mont')


if __name__ == '__main__':
    main()
