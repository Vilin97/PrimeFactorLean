import PrimeFactorLean.Arith

/-!
# Polynomials over `𝔽_p` (search helpers for the number field sieve)

Coefficient arrays, lowest degree first. These routines find roots of the
algebraic polynomial modulo factor-base primes (distinct-degree splitting by
`gcd(x^p - x, f)` followed by Cantor–Zassenhaus), detect *inert* primes (where
`f` stays irreducible), and take square roots in `𝔽_{p^d} = 𝔽_p[x]/(f)` by
Tonelli–Shanks.

Nothing here is trusted: factor-base roots only guide sieving and trial
division, and the algebraic square root is verified by exact multiplication in
`ℤ[ω]` before it is used (see `PrimeFactorLean.NFS.eval_mulZ`).
-/

namespace PrimeFactorLean.NFS.ModP

open Arith

abbrev Pol := Array Nat

/-- Remove trailing zero coefficients. -/
def trim (a : Pol) : Pol := Id.run do
  let mut a := a
  while a.size > 0 && a[a.size - 1]! == 0 do
    a := a.pop
  return a

def deg (a : Pol) : Nat := (trim a).size - 1

def ofInts (p : Nat) (xs : List Int) : Pol :=
  trim (xs.toArray.map fun c => (c % (p : Int)).toNat)

def add (p : Nat) (a b : Pol) : Pol := Id.run do
  let n := max a.size b.size
  let mut c : Pol := Array.replicate n 0
  for i in [0:n] do
    c := c.set! i ((a.getD i 0 + b.getD i 0) % p)
  return trim c

def sub (p : Nat) (a b : Pol) : Pol := Id.run do
  let n := max a.size b.size
  let mut c : Pol := Array.replicate n 0
  for i in [0:n] do
    c := c.set! i ((a.getD i 0 + p - b.getD i 0 % p) % p)
  return trim c

def mul (p : Nat) (a b : Pol) : Pol := Id.run do
  if a.size == 0 || b.size == 0 then return #[]
  let mut c : Pol := Array.replicate (a.size + b.size - 1) 0
  for i in [0:a.size] do
    let ai := a[i]!
    if ai == 0 then continue
    for j in [0:b.size] do
      c := c.set! (i + j) ((c[i + j]! + ai * b[j]!) % p)
  return trim c

/-- Quotient and remainder by `b` (leading coefficient invertible mod `p`). -/
def divMod (p : Nat) (a b : Pol) : Pol × Pol := Id.run do
  let b := trim b
  let mut r := trim a
  if b.size == 0 then return (#[], r)
  let lead := b[b.size - 1]!
  let some inv := invMod lead p | return (#[], r)
  if r.size < b.size then return (#[], r)
  let mut q : Pol := Array.replicate (r.size - b.size + 1) 0
  let mut fuel := r.size + 1
  while r.size ≥ b.size && fuel > 0 do
    fuel := fuel - 1
    let shift := r.size - b.size
    let c := r[r.size - 1]! * inv % p
    q := q.set! shift c
    for j in [0:b.size] do
      let idx := shift + j
      r := r.set! idx ((r[idx]! + p - c * b[j]! % p) % p)
    r := trim r
  return (trim q, r)

def rem (p : Nat) (a b : Pol) : Pol := (divMod p a b).2

def mulMod (p : Nat) (f a b : Pol) : Pol := rem p (mul p a b) f

def powMod (p : Nat) (f a : Pol) (e : Nat) : Pol := Id.run do
  let mut result : Pol := #[1]
  let mut base := rem p a f
  let mut e := e
  while e > 0 do
    if e % 2 == 1 then result := mulMod p f result base
    base := mulMod p f base base
    e := e / 2
  return rem p result f

/-- Monic gcd. -/
def gcd (p : Nat) (a b : Pol) : Pol := Id.run do
  let mut a := trim a
  let mut b := trim b
  let mut fuel := a.size + b.size + 2
  while b.size > 0 && fuel > 0 do
    fuel := fuel - 1
    let r := rem p a b
    a := b
    b := r
  if a.size == 0 then return a
  let lead := a[a.size - 1]!
  match invMod lead p with
  | some inv => return a.map (· * inv % p)
  | none => return a

def evalAt (p : Nat) (a : Pol) (x : Nat) : Nat := Id.run do
  let mut acc := 0
  for i' in [0:a.size] do
    let i := a.size - 1 - i'
    acc := (acc * x + a[i]!) % p
  return acc

/-- Split a squarefree product of distinct linear factors into its roots. -/
def splitLinear (p : Nat) : Nat → Pol → Array Nat
  | 0, _ => #[]
  | fuel + 1, h =>
    let h := trim h
    if h.size ≤ 1 then #[]
    else if h.size == 2 then
      match invMod h[1]! p with
      | some inv => #[(p - h[0]! * inv % p) % p]
      | none => #[]
    else Id.run do
      for delta in [1:200] do
        let t := powMod p h #[delta % p, 1] ((p - 1) / 2)
        let k := gcd p h (sub p t #[1])
        if 1 < k.size && k.size < h.size then
          let other := (divMod p h k).1
          return splitLinear p fuel k ++ splitLinear p fuel other
      return #[]

/-- All roots of `f` modulo the prime `p`. -/
def roots (p : Nat) (f : Pol) : Array Nat := Id.run do
  let f := trim (f.map (· % p))
  if f.size ≤ 1 then return #[]
  if p < 64 then
    let mut out := #[]
    for r in [0:p] do
      if evalAt p f r == 0 then out := out.push r
    return out
  -- h = gcd(x^p - x, f) is the product of the distinct linear factors.
  let xp := powMod p f #[0, 1] p
  let h := gcd p f (sub p xp #[0, 1])
  let rs := splitLinear p (2 * h.size + 2) h
  return (rs.filter fun r => evalAt p f r == 0).qsort (· < ·)

/-- `f` (of degree `d`, leading coefficient invertible) is irreducible over `𝔽_p`:
no factor of degree `i ≤ d/2`, i.e. `gcd(x^{p^i} - x, f) = 1`. -/
def isIrreducible (p : Nat) (f : Pol) : Bool := Id.run do
  let f := trim (f.map (· % p))
  if f.size < 2 then return false
  let d := f.size - 1
  if d == 1 then return true
  let mut xpi : Pol := #[0, 1]
  for _ in [0:d / 2] do
    xpi := powMod p f xpi p
    let g := gcd p f (sub p xpi #[0, 1])
    if g.size != 1 then return false
  return true

/-! ## The finite field `𝔽_p[x]/(f)` for an irreducible monic `f` -/

/-- Inverse by Fermat: `a^(q-2)` with `q = p^d`. -/
def fqInv (p : Nat) (f a : Pol) : Pol :=
  let d := (trim f).size - 1
  powMod p f a (p ^ d - 2)

/-- Tonelli–Shanks square root in `𝔽_{p^d}`; `none` for non-squares. -/
def fqSqrt (p : Nat) (f a : Pol) : Option Pol := Id.run do
  let f := trim f
  let d := f.size - 1
  let q := p ^ d
  let a := rem p a f
  if (trim a).size == 0 then return some #[]
  -- Euler's criterion.
  if trim (powMod p f a ((q - 1) / 2)) != #[1] then return none
  let mut t0 := q - 1
  let mut s := 0
  while t0 % 2 == 0 && t0 > 0 do
    t0 := t0 / 2
    s := s + 1
  -- A non-residue z.
  let mut z : Pol := #[]
  let mut found := false
  for i in [2:2000] do
    if found then break
    let cand : Pol := trim #[i % p, (i / p + 1) % p]
    if trim (powMod p f cand ((q - 1) / 2)) != #[1] then
      z := cand
      found := true
  if !found then return none
  let mut m := s
  let mut c := powMod p f z t0
  let mut t := powMod p f a t0
  let mut r := powMod p f a ((t0 + 1) / 2)
  let mut fuel := s + 2
  while trim t != #[1] && fuel > 0 do
    fuel := fuel - 1
    let mut i := 0
    let mut tt := t
    while trim tt != #[1] && i < m do
      tt := mulMod p f tt tt
      i := i + 1
    if i == m then return none
    let mut b := c
    for _ in [0:m - i - 1] do
      b := mulMod p f b b
    m := i
    c := mulMod p f b b
    t := mulMod p f t c
    r := mulMod p f r b
  if trim (mulMod p f r r) == trim a then return some r else return none

end PrimeFactorLean.NFS.ModP
