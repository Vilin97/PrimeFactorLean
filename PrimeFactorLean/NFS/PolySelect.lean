import PrimeFactorLean.NFS.Lattice

/-!
# Polynomial selection with a non-monic linear polynomial (Kleinjung)

For the number field sieve the polynomial pair `(F, Y₁ x - m)` only needs a
common root modulo `n` (resultant `± n`). Kleinjung's construction (Math. Comp.
75, 2006, Lemma 2.1; CADO-NFS `kleinjung.sage`, `lemme_21`): given the leading
coefficient `a_d`, a modulus `p` and `m` with `a_d m^d ≡ n (mod p)`, the digits

    r_d = n,   r_i = (r_{i+1} - a_{i+1} m^{i+1}) / p,
    a_i ≡ r_i m^{-i} (mod p), the representative nearest to r_i / m^i,

give `n = Σ a_i m^i p^{d-i}`, i.e. `F(m / p) p^d = n` with rational side `p x - m`.
When `m` is close to `m₀ = (n / a_d)^{1/d}`, `a_{d-1}` is small (at most about
`d a_d`). Choosing `p` as a product of small primes, each with `d` roots of
`a_d x^d ≡ n`, gives `d^ℓ` admissible `m` (by the Chinese remainder theorem);
the one whose polynomial has the smallest skewed `L²` norm plus Murphy's `α`
is kept, then small rotations `F + (u x + v)(p x - m)` (which keep the common
root) are tried to improve `α`.

Search code only: the GNFS checks the root equation exactly (`GNFS.mkSetup`).
-/

namespace PrimeFactorLean.NFS.PolySelect

open Arith

/-- Kleinjung's Lemma 2.1: the coefficients `a_0, …, a_d` with
`n = Σ a_i m^i p^{d-i}`, provided `a_d m^d ≡ n (mod p)` (checked: `none` otherwise). -/
def lemma21 (n d ad p m : Nat) : Option (Array Int) := Id.run do
  if p == 0 || m == 0 then return none
  let some minv := invMod (m % p) p | return none
  let mut a : Array Int := Array.replicate (d + 1) 0
  a := a.set! d (ad : Int)
  let mut r : Int := n
  -- powers of m
  let mut mm : Array Int := #[1]
  for _ in [0:d] do mm := mm.push (mm.back! * (m : Int))
  for i' in [0:d] do
    let i := d - 1 - i'
    let num := r - a[i + 1]! * mm[i + 1]!
    if num % (p : Int) != 0 then return none
    r := num / (p : Int)
    if i == 0 then
      a := a.set! 0 r
    else
      -- a_i ≡ r m^{-i} (mod p), nearest to r / m^i
      let aimod : Int := ((r % (p : Int)).toNat * powMod minv i p % p : Nat)
      -- k = (r / m^i - aimod) / p, rounded
      let q := r / mm[i]!
      let k := (q - aimod + (p : Int) / 2) / (p : Int)
      a := a.set! i ((p : Int) * k + aimod)
  -- verify n = Σ a_i m^i p^{d-i}
  let mut acc : Int := 0
  let mut pp : Int := 1
  for i' in [0:d + 1] do
    let i := d - i'
    acc := acc + a[i]! * mm[i]! * pp
    pp := pp * (p : Int)
  if acc != (n : Int) then return none
  return some a

/-- The roots of `a x^d ≡ n (mod q)` when there are `d` of them (else `#[]`):
`gcd(x^q - x, a x^d - n)` has degree `d` exactly then. -/
def rootsMod (a n d q : Nat) : Array Nat := Id.run do
  let f := ModP.ofInts q (((-(n : Int)) :: List.replicate (d - 1) 0) ++ [(a : Int)])
  if f.size != d + 1 then return #[]
  let xq := ModP.powMod q f #[0, 1] q
  let h := ModP.gcd q f (ModP.sub q xq #[0, 1])
  if h.size != d + 1 then return #[]
  let rs := ModP.splitLinear q (2 * d + 2) h
  return (rs.filter fun r => ModP.evalAt q f r == 0)

/-- `F(x) mod p` by Horner's rule on machine words (`p < 2^32`). -/
def hornerMod (red : Array Nat) (p x : UInt64) (d : Nat) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for i' in [0:d + 1] do
    v := (v * x + red[d - i']!.toUInt64) % p
  return v

/-- Murphy's `α` from the roots of `F` modulo the primes below 200 (in natural
logarithms), with the coefficients reduced modulo each prime first. -/
def alpha (cs : Array Int) : Float := Id.run do
  let d := cs.size - 1
  let mut a : Float := 0
  for p in ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
            79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163,
            167, 173, 179, 181, 191, 193, 197, 199] : List Nat) do
    let red : Array Nat := cs.map fun c => (c % (p : Int)).toNat
    let pu := p.toUInt64
    let mut roots := 0
    for x in [0:p] do
      roots := roots + (if hornerMod red pu x.toUInt64 d == 0 then 1 else 0)
    if red[d]! == 0 then roots := roots + 1
    let pf := p.toFloat
    a := a + (1.0 / (pf - 1.0) - roots.toFloat * pf / (pf * pf - 1.0)) * Float.log pf
  return a

/-- `s^d · ‖F‖²(s) = Σ_k w_k s^k` as a polynomial in the skewness `s` (unboxed
coefficients `w_0 … w_{2d}`; odd `k` vanish). -/
def normPoly (cs : Array Int) : FloatArray := Id.run do
  let d := cs.size - 1
  let mut w : FloatArray := FloatArray.emptyWithCapacity (2 * d + 1)
  for k in [0:2 * d + 1] do
    let mut c : Float := 0
    if k % 2 == 0 then
      for i in [0:d + 1] do
        if i ≤ k && k - i ≤ d then c := c + Float.ofInt cs[i]! * Float.ofInt cs[k - i]!
      c := c * 4.0 / ((k + 1).toFloat * (2 * d - k + 1).toFloat)
    w := w.push c
  return w

/-- `Σ_k w_k s^k` by Horner's rule. -/
def evalNormPoly (w : FloatArray) (s : Float) : Float := Id.run do
  let mut acc : Float := 0
  for k' in [0:w.size] do
    acc := acc * s + w.get! (w.size - 1 - k')
  return acc

/-- `log` of the `L²` norm at the optimal skewness, and that skewness
(golden-section search on `log s`). -/
def logNorm (cs : Array Int) : Float × Float := Id.run do
  let d := cs.size - 1
  let w := normPoly cs
  let f (t : Float) : Float := evalNormPoly w (Float.exp t) * Float.exp (-(d.toFloat) * t)
  let mut lo : Float := 0.0
  let mut hi : Float := 80.0
  let phi : Float := 0.6180339887498949
  for _ in [0:45] do
    let a := hi - phi * (hi - lo)
    let b := lo + phi * (hi - lo)
    if f a < f b then hi := b else lo := a
  let t := (lo + hi) / 2.0
  return (0.5 * Float.log (f t), Float.exp t)

/-- A candidate: coefficients, `m`, `p` and its score `log‖F‖ + α`. -/
structure Cand where
  cs : Array Int
  m : Nat
  p : Nat
  score : Float
  deriving Inhabited

/-- The best polynomials over leading coefficients `ad ∈ adStep · [1, adCount]`
and moduli `p` = products of `ell` primes from `[qlo, qhi)` with `d` roots each. -/
def search (n d : Nat) (adStep kFirst kStop ell qlo qhi keep : Nat) : Array Cand := Id.run do
  let mut best : Array Cand := #[]
  for k in [kFirst:kStop] do
    let ad := adStep * k
    -- primes with d roots of ad x^d ≡ n
    let mut good : Array (Nat × Array Nat) := #[]
    for q in [qlo:qhi] do
      if good.size ≥ 2 * ell then break
      if !isProbablePrime q || ad % q == 0 || n % q == 0 then continue
      let rs := rootsMod ad n d q
      if rs.size == d then good := good.push (q, rs)
    if good.size < ell then continue
    let ps := good.extract 0 ell
    let p := ps.foldl (fun acc e => acc * e.1) 1
    let m0 := iroot (n / ad) d
    -- CRT lifts of the roots
    let lifts : Array (Array Nat) := ps.map fun (q, rs) =>
      let c := p / q
      let ci := (invMod (c % q) q).getD 0
      rs.map fun x => x * ci % q * c % p
    -- all combinations
    let total := d ^ ell
    for idx in [0:total] do
      let mut mu := 0
      let mut t := idx
      for j in [0:ell] do
        mu := (mu + lifts[j]![t % d]!) % p
        t := t / d
      -- the representative of μ (mod p) nearest to m₀
      let off := (mu + p - m0 % p) % p
      let m := if 2 * off > p then m0 + off - p else m0 + off
      match lemma21 n d ad p m with
      | none => pure ()
      | some cs =>
        let (ln, _) := logNorm cs
        let c : Cand := { cs, m, p, score := ln }
        if best.size < keep then best := best.push c
        else
          -- replace the worst
          let mut wi := 0
          for i in [1:best.size] do
            if best[i]!.score > best[wi]!.score then wi := i
          if c.score < best[wi]!.score then best := best.set! wi c
  return best

/-- `F + (u x + v)(p x - m)`. -/
def rotate (cs : Array Int) (p m : Nat) (u v : Int) : Array Int :=
  let cs := cs.modify 0 (· - v * (m : Int))
  let cs := cs.modify 1 (· + v * (p : Int) - u * (m : Int))
  cs.modify 2 (· + u * (p : Int))

/-- Rotations with `|u| ≤ U`, `|v| ≤ V` minimizing `log‖F‖ + α`. -/
def bestRotation (c : Cand) (U V : Nat) : Cand := Id.run do
  let mut best := c
  let mut bestScore := (logNorm c.cs).1 + alpha c.cs
  for ui in [0:2 * U + 1] do
    let u : Int := (ui : Int) - (U : Int)
    for vi in [0:2 * V + 1] do
      let v : Int := (vi : Int) - (V : Int)
      let cs := rotate c.cs c.p c.m u v
      let s := (logNorm cs).1 + alpha cs
      if s < bestScore then
        bestScore := s
        best := { c with cs, score := s }
  return { best with score := bestScore }

/-- The `keep` best of `cs` by score. -/
def bestOf (cs : Array Cand) (keep : Nat) : Array Cand :=
  (cs.qsort (fun a b => a.score < b.score)).extract 0 keep

/-- A Kleinjung-style polynomial pair for `n` of degree `d`: the leading
coefficients `adStep · [1, adCount]` are split over `threads` tasks, and the
best candidates are rotated in parallel. -/
def select (n d : Nat) (adStep adCount ell qlo qhi : Nat) (rotU rotV : Nat) (threads : Nat := 1) :
    Option Selection := Id.run do
  let t := max 1 threads
  let per := (adCount + t - 1) / t
  let tasks := (List.range t).map fun i =>
    Task.spawn fun _ => search n d adStep (1 + i * per) (min (adCount + 1) (1 + (i + 1) * per))
      ell qlo qhi 8
  let cands := bestOf (tasks.foldl (fun acc tk => acc ++ tk.get) #[]) 8
  if cands.isEmpty then return none
  let rot := cands.toList.map fun c => Task.spawn fun _ => bestRotation c rotU rotV
  let mut best : Option Cand := none
  for tk in rot do
    let r := tk.get
    match best with
    | none => best := some r
    | some b => if r.score < b.score then best := some r
  match best with
  | none => return none
  | some b =>
    -- leading coefficient must be positive for the Selection convention
    if b.cs[d]! ≤ 0 then return none
    return some { coeffs := b.cs, m := b.m, y1 := b.p }

end PrimeFactorLean.NFS.PolySelect
