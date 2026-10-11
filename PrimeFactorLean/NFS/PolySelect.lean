import PrimeFactorLean.NFS.Lattice
import Std.Data.HashMap

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
    let pf := nf p
    a := a + (fc 1 / (pf - fc 1) - nf roots * pf / (pf * pf - fc 1)) * Float.log pf
  return a

/-- The binomial coefficient `C(n, k)`. -/
def binomial (n k : Nat) : Nat := Id.run do
  let mut c := 1
  for i in [0:k] do c := c * (n - i) / (i + 1)
  return c

/-- The weights of CADO-NFS's `L2` norm in degree `d`:
`π / (4^d (d+1)) · C(2d,d) C(d,k) / C(2d,2k)` for `k = 0 … d`. -/
def diskWeightsOf (d : Nat) : FloatArray := Id.run do
  let scale : Float := fc 314159265358979 / fc 100000000000000 /
    (Float.exp2 (nf (2 * d)) * nf (d + 1))
  let mut w : FloatArray := FloatArray.emptyWithCapacity (d + 1)
  for k in [0:d + 1] do
    w := w.push (nf (binomial (2 * d) d * binomial d k) / nf (binomial (2 * d) (2 * k)) * scale)
  return w

/-- `diskWeightsOf d` for `d ≤ 10`, computed once. -/
def diskWeights : Array FloatArray := (Array.range 11).map diskWeightsOf

/-- `Σ_{j=i}^{i+n-1} c_j c_{k-j}` added to `acc`. -/
def convGo (cf : FloatArray) (k i : Nat) (acc : Float) : Nat → Float
  | 0 => acc
  | n + 1 => convGo cf k (i + 1) (acc + cf.get! i * cf.get! (k - i)) n

/-- The coefficients `p_j = w_j Σ_{i+i'=2j} a_i a_{i'}` for `j` from `j` on. -/
def normPolyGo (cf wt : FloatArray) (d j : Nat) (out : FloatArray) : Nat → FloatArray
  | 0 => out
  | n + 1 =>
    let k := 2 * j
    let lo := k - min k d
    let c := convGo cf k lo 0 (min k d + 1 - lo)
    normPolyGo cf wt d (j + 1) (out.push (c * wt.get! j)) n

/-- `s^d ‖F‖²(s) = P(s²)` for CADO-NFS's `L2` norm (the integral of
`F(x √s, y / √s)²` over the unit disk), from float coefficients: the coefficients
of `P(x) = π / (4^d (d+1)) Σ_j C(2d,d) C(d,j) / C(2d,2j) (Σ_{i+i'=2j} a_i a_{i'}) x^j`. -/
def normPolyF (cf : FloatArray) : FloatArray :=
  let d := cf.size - 1
  let wt := if d < 11 then diskWeights[d]! else diskWeightsOf d
  normPolyGo cf wt d 0 (FloatArray.emptyWithCapacity (d + 1)) (d + 1)

/-- The coefficients as floats. -/
def toFloats (cs : Array Int) : FloatArray :=
  cs.foldl (fun a c => a.push (intF c)) (FloatArray.emptyWithCapacity cs.size)

/-- `normPolyF` of the integer coefficients. -/
def normPoly (cs : Array Int) : FloatArray := normPolyF (toFloats cs)

/-- `acc x^n + Σ_{i<n} q_i x^i` by Horner's rule. -/
def hornerGo (q : FloatArray) (x acc : Float) : Nat → Float
  | 0 => acc
  | i + 1 => hornerGo q x (acc * x + q.get! i) i

/-- `Σ_k q_k x^k`. -/
@[inline] def hornerF (q : FloatArray) (x : Float) : Float := hornerGo q x (fc 0) q.size

/-- `q(x) = Σ_j (2j - d) p_j x^j` (the numerator of the derivative of the norm in
the skewness, in `x = s²`), Horner from index `j - 1` down. -/
def qAtGo (p : FloatArray) (d : Nat) (x acc : Float) : Nat → Float
  | 0 => acc
  | j + 1 => qAtGo p d x (acc * x + (nf (2 * j) - nf d) * p.get! j) j

/-- `q'(x) = Σ_j j (2j - d) p_j x^(j-1)`, Horner from index `j` down to 1. -/
def qdAtGo (p : FloatArray) (d : Nat) (x acc : Float) : Nat → Float
  | 0 => acc
  | j + 1 => qdAtGo p d x (acc * x + nf (j + 1) * (nf (2 * j + 2) - nf d) * p.get! (j + 1)) j

/-- The sign changes of the nonzero `(2j - d) p_j` from `j` on (`sgn` the last sign). -/
def qChanges (p : FloatArray) (d j : Nat) (sgn : Float) (acc : Nat) : Nat → Nat
  | 0 => acc
  | n + 1 =>
    let c := (nf (2 * j) - nf d) * p.get! j
    if c == fc 0 then qChanges p d (j + 1) sgn acc n
    else if sgn != fc 0 && (c < fc 0) != (sgn < fc 0) then qChanges p d (j + 1) c (acc + 1) n
    else qChanges p d (j + 1) c acc n

/-- The first `y = x r^i` (`i ≥ 1`) with `q y ≥ 0` (`q x < 0`), or `0`. -/
def bracketUp (p : FloatArray) (d : Nat) (r x : Float) : Nat → Float
  | 0 => fc 0
  | n + 1 => let y := x * r
    if qAtGo p d y (fc 0) (d + 1) < fc 0 then bracketUp p d r y n else y

/-- The first `y = x / r^i` (`i ≥ 1`) with `q y < 0` (`q x ≥ 0`), or `0`. -/
def bracketDown (p : FloatArray) (d : Nat) (r x : Float) : Nat → Float
  | 0 => fc 0
  | n + 1 => let y := x / r
    if qAtGo p d y (fc 0) (d + 1) < fc 0 then y else bracketDown p d r y n

/-- Safeguarded Newton for the root of `q` in `[lo, hi]` (`q lo < 0 ≤ q hi`): a step
leaving the bracket is replaced by the bracket's geometric midpoint. -/
def skewNewton (p : FloatArray) (d : Nat) (lo hi x : Float) : Nat → Float
  | 0 => x
  | n + 1 =>
    let v := qAtGo p d x (fc 0) (d + 1)
    let lo := if v < fc 0 then x else lo
    let hi := if v < fc 0 then hi else x
    let dv := qdAtGo p d x (fc 0) d
    let xn := x - v / dv
    let xn := if dv > fc 0 && xn > lo && xn < hi then xn else Float.sqrt (lo * hi)
    if (xn - x).abs ≤ x / fc 10000000000 then xn else skewNewton p d lo hi xn n

/-- A lognorm and its skewness (unboxed). -/
structure LnSk where
  ln : Float
  sk : Float

/-- `log` of the `L²` norm at the optimal skewness, and that skewness. With
`x = s²`, `s^d ‖F‖²(s) = P(x)` and the optimum is at the positive root of
`q(x) = Σ_j (2j - d) p_j x^j` (CADO-NFS `L2_skewness`): found by safeguarded
Newton when the coefficients of `q` change sign once (a unique positive root)
or a skewness `hint > 0` (a neighbour's) is given (the local minimum next to
it), else by golden-section search on `log s`. From float coefficients. -/
def logNormS (cf : FloatArray) (hint : Float) : LnSk := Id.run do
  let d := cf.size - 1
  let p := normPolyF cf
  -- with a hint, the minimum next to it (the bracket always closes on a crossing
  -- of `q` from below, a local minimum of the norm)
  if hint > fc 0 || qChanges p d 0 (fc 0) 0 (d + 1) == 1 then
    -- bracket from the hint `s₀` (`x = s₀²`) by factors 2, else from 1 by factors 16
    let x0 := if hint > fc 0 then hint * hint else fc 1
    let r := if hint > fc 0 then fc 2 else fc 16
    let up := qAtGo p d x0 (fc 0) (d + 1) < fc 0
    let y := if up then bracketUp p d r x0 120 else bracketDown p d r x0 120
    if y > fc 0 then
      let lo := if up then y / r else y
      let hi := if up then y else y * r
      let x := skewNewton p d lo hi (Float.sqrt (lo * hi)) 60
      return ⟨fc 1 / fc 2 * (Float.log (hornerF p x) - nf d / fc 2 * Float.log x), Float.sqrt x⟩
  let dF := nf d
  let f (t : Float) : Float := hornerF p (Float.exp (fc 2 * t)) * Float.exp (Float.neg dF * t)
  let mut lo : Float := fc 0
  let mut hi : Float := fc 80
  let phi : Float := fc 6180339887498949 / fc 10000000000000000
  for _ in [0:45] do
    let a := hi - phi * (hi - lo)
    let b := lo + phi * (hi - lo)
    if f a < f b then hi := b else lo := a
  let t := (lo + hi) / fc 2
  return ⟨fc 1 / fc 2 * Float.log (f t), Float.exp t⟩

/-- `logNormS` as a pair. -/
@[inline] def logNormFH (cf : FloatArray) (hint : Float) : Float × Float :=
  let r := logNormS cf hint
  (r.ln, r.sk)

/-- `logNormFH` without a hint. -/
@[inline] def logNormF (cf : FloatArray) : Float × Float := logNormFH cf (fc 0)

/-- `logNormF` of the integer coefficients. -/
def logNorm (cs : Array Int) : Float × Float := logNormF (toFloats cs)

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

/-! ## Collision search (Kleinjung 2008, as in CADO-NFS `polyselect`)

With `Ñ = d^d a_d^{d-1} n` and `m₀ = ⌊Ñ^{1/d}⌋`, an integer `m̃` with
`m̃^d ≡ Ñ (mod ℓ²)` gives a pair `(F, ℓ x - m)` whose coefficients `a_{d-1}` and
`a_{d-2}` are both small: `a_{d-1} ≡ m̃ / ℓ (mod d a_d)` (centered),
`m = (m̃ - a_{d-1} ℓ) / (d a_d)`, and Lemma 2.1 with modulus `ℓ` for the others.
Here `ℓ = p₁ p₂ q` with `p₁, p₂ ∈ [P, 2P]` and a special-`q` part `q` (a product
of small primes, `m̃ ≡ m₀ + r_q (mod q²)`): writing `m̃ = m₀ + r_q + i q²`, each
root of `x^d ≡ Ñ (mod p²)` admits one residue class of `i` modulo `p²`, and two
primes whose classes share an `i` with `|i| ≤ (2P)²` (a *collision*, found by
hashing) give `ℓ`. The pairs are then size-optimized (local descent over
translations and rotations by `x^j (ℓ x - m)`, `j ≤ d - 2`), rotated by
`(u x + v)(ℓ x - m)` to improve `α`, and ranked by Murphy's `E`. -/

/-- `b^e mod m` on machine words (`m < 2^32`). -/
def powModW (b e m : UInt64) : UInt64 := go (b % m) e 1 64
where
  go (b e acc : UInt64) : Nat → UInt64
    | 0 => acc
    | fuel + 1 =>
      if e == 0 then acc
      else go (b * b % m) (e >>> 1) (if e &&& 1 == 1 then acc * b % m else acc) fuel

/-- `a⁻¹ mod m` for `m < 2^62` by extended Euclid on signed words (`0` if not
invertible). -/
def invModW (a m : UInt64) : UInt64 := Id.run do
  let mut r0 : Int64 := m.toInt64
  let mut r1 : Int64 := (a % m).toInt64
  let mut s0 : Int64 := 0
  let mut s1 : Int64 := 1
  for _ in [0:128] do
    if r1 == 0 then break
    let q := r0 / r1
    let r2 := r0 - q * r1
    let s2 := s0 - q * s1
    r0 := r1
    r1 := r2
    s0 := s1
    s1 := s2
  if r0 != 1 then return 0
  return (if s0 < 0 then s0 + m.toInt64 else s0).toUInt64

/-- A square root of the quadratic residue `a` modulo the odd prime `p < 2^31`
(Tonelli–Shanks). -/
def sqrtModW (a p : UInt64) : UInt64 := Id.run do
  let a := a % p
  if a == 0 then return 0
  if p % 4 == 3 then return powModW a ((p + 1) / 4) p
  -- p - 1 = q 2^e
  let mut q := p - 1
  let mut e : Nat := 0
  while q % 2 == 0 do
    q := q / 2
    e := e + 1
  -- a non-residue
  let mut z : UInt64 := 2
  while powModW z ((p - 1) / 2) p != p - 1 do z := z + 1
  let mut m := e
  let mut c := powModW z q p
  let mut t := powModW a q p
  let mut r := powModW a ((q + 1) / 2) p
  for _ in [0:64] do
    if t == 1 then break
    -- the least i with t^(2^i) = 1
    let mut i := 0
    let mut t2 := t
    while t2 != 1 && i < m do
      t2 := t2 * t2 % p
      i := i + 1
    if i == m then return 0
    let mut b := c
    for _ in [0:m - i - 1] do b := b * b % p
    m := i
    c := b * b % p
    t := t * c % p
    r := r * b % p
  return r

/-- The roots of `x^d ≡ c (mod p)` (`p` prime below `2^31`): there are `0` or
`g = gcd(d, p - 1)` of them, decided by `c^((p-1)/g)`. One root `r₀` is
`c^(d⁻¹ mod (p-1)/g)` when `d` is prime to `(p-1)/g`, two square roots for
`d = 4`; the others are `r₀ ζ^i` for a primitive `g`-th root of unity `ζ`.
The remaining cases fall back to the generic root finder. -/
def binomialRoots (d c p : Nat) : Array Nat := Id.run do
  let generic (_ : Unit) : Array Nat :=
    ModP.roots p (ModP.ofInts p (((-((c % p : Nat) : Int)) :: List.replicate (d - 1) (0 : Int)) ++ [1]))
  let pw := p.toUInt64
  let cw := (c % p).toUInt64
  if cw == 0 || p < 3 then return generic ()
  let g := Nat.gcd d (p - 1)
  let m := (p - 1) / g
  if g == 1 then
    return #[(powModW cw (invModW d.toUInt64 (p - 1).toUInt64) pw).toNat]
  if powModW cw m.toUInt64 pw != 1 then return #[]
  let r0 : UInt64 :=
    if Nat.gcd d m == 1 then powModW cw (invModW d.toUInt64 m.toUInt64) pw
    else if d == 4 then
      -- c = x₀⁴: s = ±x₀² and -s are both squares here (or p ≡ 3 mod 4: one is)
      let s := sqrtModW cw pw
      let s := if powModW s ((p - 1) / 2).toUInt64 pw == 1 then s else pw - s
      sqrtModW s pw
    else 0
  if r0 == 0 || powModW r0 d.toUInt64 pw != cw then return generic ()
  -- a primitive g-th root of unity (g ∈ {2, 3, 4, 5, 6} for d ≤ 6)
  let mut zeta : UInt64 := 0
  for h in [2:200] do
    let z := powModW h.toUInt64 m.toUInt64 pw
    -- order exactly g: z^(g/q) ≠ 1 for each prime q ∣ g
    let ok := (g % 2 != 0 || powModW z (g / 2).toUInt64 pw != 1) &&
      (g % 3 != 0 || powModW z (g / 3).toUInt64 pw != 1) &&
      (g % 5 != 0 || powModW z (g / 5).toUInt64 pw != 1)
    if ok then
      zeta := z
      break
  if zeta == 0 then return generic ()
  let mut out : Array Nat := #[]
  let mut r := r0
  for _ in [0:g] do
    out := out.push r.toNat
    r := r * zeta % pw
  return out

/-- The roots `r ≠ 0` of `x^d ≡ c (mod p)` lifted to roots modulo `p²` (Hensel),
returned as the residues of `r - m₀` modulo `p²`. -/
def liftedRoots (d c m0 p : Nat) : Array Nat := Id.run do
  let pp := p * p
  let cp := c % pp
  let mut out : Array Nat := #[]
  for r in binomialRoots d cp p do
    if r == 0 then continue
    let inv := (invModW (d * powMod r (d - 1) p % p).toUInt64 p.toUInt64).toNat
    if inv == 0 then continue
    let t := (cp + pp - powMod r d pp) % pp
    let rr := r + t / p * inv % p * p
    out := out.push ((rr + pp - m0 % pp) % pp)
  return out

/-- The special-`q` primes of CADO-NFS (`SPECIAL_Q`, whose first entry 2 its
`comp_sq_roots` skips). -/
def specialQPrimes : List Nat :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
   97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
   193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271]

/-- `x` with `x ≡ a (mod ma)`, `x ≡ b (mod mb)` (coprime moduli), in `[0, ma mb)`. -/
def crt2 (a ma b mb : Nat) : Nat :=
  let inv := if mb >>> 62 == 0 then (invModW (ma % mb).toUInt64 mb.toUInt64).toNat
    else (invMod (ma % mb) mb).getD 0
  a + ma * (((b + mb - a % mb) % mb) * inv % mb)

/-- The next `k`-subset of `[0, n)` in lexicographic order. -/
def nextComb (idx : Array Nat) (n : Nat) : Option (Array Nat) := Id.run do
  let k := idx.size
  for i' in [0:k] do
    let i := k - 1 - i'
    if idx[i]! < n - k + i then
      let mut out := idx.set! i (idx[i]! + 1)
      for j in [i + 1:k] do out := out.set! j (out[j - 1]! + 1)
      return some out
  return none

/-- CADO-NFS's order of the special-`q` primes (`polyselect_qroots_rearrange`): a
selection sort by decreasing number of roots that swaps (so it is not stable). -/
def rearrangeQ (sq : Array (Nat × Array Nat)) : Array (Nat × Array Nat) := Id.run do
  let mut a := sq
  for i in [0:a.size] do
    let mut mx := i
    for j in [i + 1:a.size] do
      if a[j]!.2.size > a[mx]!.2.size then mx := j
    a := a.swapIfInBounds i mx
  return a

/-- The number of root combinations over the `k`-subsets of the first `lq`
primes of `sq`: the elementary symmetric polynomial `e_k` of their root counts. -/
def numberComb (sq : Array (Nat × Array Nat)) (k lq : Nat) : Nat := Id.run do
  let mut e : Array Nat := (Array.replicate (k + 1) 0).set! 0 1
  for i in [0:min lq sq.size] do
    let a := sq[i]!.2.size
    for j' in [0:k] do
      let j := k - j'
      e := e.set! j (e[j]! + a * e[j - 1]!)
  return e[k]!

/-- The special-`q` primes in CADO-NFS's order and the number `k` of factors of a
special-`q` (`find_suitable_lq`): `k` grows while `d^k < nq` and the product of
the first `k` primes stays below `lim = m₀ / (2P)⁴`; the special-`q` are drawn
from the least number `lq` of leading primes whose `k`-subsets carry at least
`nq` root combinations. -/
def suitableQ (sq0 : Array (Nat × Array Nat)) (d nq : Nat) (lim : Float) (cado : Bool := true) :
    Array (Nat × Array Nat) × Nat := Id.run do
  let sq := if cado then rearrangeQ sq0 else sq0
  let mut k0 := 0
  let mut prod := 1
  let mut sqv : Float := fc 1
  for (q, _) in sq do
    if prod ≥ nq then break
    if sqv * q.toFloat ≥ lim then break
    prod := prod * d
    sqv := sqv * q.toFloat
    k0 := k0 + 1
  let k := max 1 (min k0 8)
  if !cado then return (sq, k)
  let mut lq := k
  while lq < sq.size && numberComb sq k lq < nq do lq := lq + 1
  return (sq.extract 0 lq, k)

/-- Up to `nq` special-`q`: products `Q` of `k` primes of `sq` (lexicographic
subsets, also returned as their indices) and every combination of their roots,
combined modulo `Q²`. -/
def specialQList (sq : Array (Nat × Array Nat)) (k nq : Nat) :
    Array (Nat × Array Nat × Array Nat) := Id.run do
  let mut out : Array (Nat × Array Nat × Array Nat) := #[]
  if sq.size < k || k == 0 then return out
  let mut idx : Array Nat := (Array.range k)
  let mut total := 0
  for _ in [0:100000] do
    -- all root combinations for this subset, combined modulo `Q²` one prime at a
    -- time: every partial combination has the same modulus, so one inverse per
    -- prime serves them all (`crt2` would invert once per combination)
    let mut rsQ : Array Nat := #[0]
    let mut QQ := 1
    for i in idx do
      let (q, rs) := sq[i]!
      let qq := q * q
      let inv := (invModW (QQ % qq).toUInt64 qq.toUInt64).toNat
      rsQ := rsQ.foldl (fun acc r => rs.foldl (fun acc rq =>
        acc.push (r + QQ * (((rq + qq - r % qq) % qq) * inv % qq))) acc)
        (Array.mkEmpty (rsQ.size * rs.size))
      QQ := QQ * qq
    let Q := idx.foldl (fun acc i => acc * sq[i]!.1) 1
    let take := min rsQ.size (nq - total)
    out := out.push (Q, rsQ.extract 0 take, idx)
    total := total + take
    if total ≥ nq then break
    match nextComb idx sq.size with
    | some idx' => idx := idx'
    | none => break
  return out

/-- Collisions for one special-`q` `(Q, r_Q)`: triples `(i, p₁, p₂)` with
`m₀ + r_Q + i Q²` a root of `x^d ≡ Ñ` modulo `p₁²` and `p₂²`, `|i| ≤ M`
(`prs`: the primes with their shifted lifted roots, `invs`: `Q⁻² mod p²`). -/
def collide (prs : Array (Nat × Array Nat)) (invs : Array Nat) (rQ M : Nat) :
    Array (Int × Nat × Nat) := Id.run do
  let mut h : Std.HashMap Int Nat := Std.HashMap.emptyWithCapacity 4096
  let mut out : Array (Int × Nat × Nat) := #[]
  for k in [0:prs.size] do
    let (p, rs) := prs[k]!
    let inv := invs[k]!
    if inv == 0 then continue
    let pp := p * p
    let rq := rQ % pp
    for rp in rs do
      let u := (rp + pp - rq) % pp * inv % pp
      let mut i : Int := ((M + u) % pp : Nat) - (M : Int)
      for _ in [0:2 * M / pp + 2] do
        if i > (M : Int) then break
        match h.get? i with
        | some p' => if p' != p then out := out.push (i, p', p)
        | none => h := h.insert i p
        i := i + (pp : Int)
  return out

/-- The slot of `key` in an open-addressing table, or the first slot without a
current entry (`gen` tags the current entries): tail recursive, no allocation. -/
def findSlot (t : Array Nat) (mask g key h : UInt64) : Nat → UInt64
  | 0 => h
  | fuel + 1 =>
    let e := t[h.toNat]!.toUInt64
    if e >>> 44 != g || (e >>> 14) &&& 1073741823 == key then h
    else findSlot t mask g key ((h + 1) &&& mask) fuel

/-- The keys `key, key + pp, … ≤ top` of the prime with index `k`: each is
inserted, or reported with the prime already stored under it. -/
def collideKeys (prs : Array (Nat × Array Nat)) (t : Array Nat) (out : Array (Int × Nat × Nat))
    (mask g top ppw M p k : UInt64) (key : UInt64) : Nat → Array Nat × Array (Int × Nat × Nat)
  | 0 => (t, out)
  | fuel + 1 =>
    if key > top then (t, out)
    else
      let h := findSlot t mask g key (((key * 2654435761) >>> 16) &&& mask) t.size
      let e := t[h.toNat]!.toUInt64
      if e >>> 44 == g then
        let p' := prs[(e &&& 16383).toNat]!.1
        let out := if p'.toUInt64 != p then
            out.push ((key.toNat : Int) - (M.toNat : Int), p', p.toNat) else out
        collideKeys prs t out mask g top ppw M p k (key + ppw) fuel
      else
        collideKeys prs (t.set! h.toNat ((g <<< 44) ||| (key <<< 14) ||| k).toNat) out mask g top
          ppw M p k (key + ppw) fuel

/-- `collide` with an open-addressing table (`2^14` slots, reused across calls):
an entry is `gen <<< 44 ||| (i + M) <<< 14 ||| k` (`k` the prime's index), so a
slot from an earlier call (another `gen`) counts as empty and the table is never
cleared. Requires `2 M < 2^30` and fewer than `2^14` primes. -/
def collideTab (prs : Array (Nat × Array Nat)) (invs : Array Nat) (rQ M : Nat) (tbl : Array Nat)
    (gen : Nat) : Array (Int × Nat × Nat) × Array Nat := Id.run do
  let mask := (tbl.size - 1).toUInt64
  let g := gen.toUInt64
  let top := (2 * M).toUInt64
  let mut t := tbl
  let mut out : Array (Int × Nat × Nat) := #[]
  for k in [0:prs.size] do
    let (p, rs) := prs[k]!
    let inv := invs[k]!
    if inv == 0 then continue
    let pp := p * p
    let rq := rQ % pp
    for rp in rs do
      let u := (rp + pp - rq) % pp * inv % pp
      let (t', out') := collideKeys prs t out mask g top pp.toUInt64 M.toUInt64 p.toUInt64 k.toUInt64
        ((M + u) % pp).toUInt64 (2 * M / pp + 2)
      t := t'
      out := out'
  return (out, t)

/-- The pair of `m̃` and `ℓ` (Lemma 2.1 with modulus `ℓ` after fixing
`a_d = ad` and the centered `a_{d-1} ≡ m̃ / ℓ (mod d a_d)`): the coefficients and
`m`, with `n = Σ a_j m^j ℓ^{d-j}` checked. `m` may be negative (`m̃ < 0` for
collisions far below `m₀`), as in CADO-NFS. -/
def fromCollision (n d ad : Nat) (mt : Int) (l : Nat) : Option (Array Int × Int) := Id.run do
  let dad := d * ad
  if l == 0 || dad == 0 then return none
  let some linv := invMod (l % dad) dad | return none
  let a1n := (mt % (dad : Int)).toNat * linv % dad
  let a1 : Int := if 2 * a1n ≥ dad then (a1n : Int) - (dad : Int) else a1n
  let num := mt - a1 * (l : Int)
  if num % (dad : Int) != 0 then return none
  let mI := num / (dad : Int)
  if mI == 0 then return none
  let li : Int := l
  let mut cs : Array Int := Array.replicate (d + 1) 0
  cs := cs.set! d (ad : Int)
  cs := cs.set! (d - 1) a1
  let mut t : Int := (n : Int) - (ad : Int) * mI ^ d
  if t % li != 0 then return none
  t := t / li - a1 * mI ^ (d - 1)
  for j' in [0:d - 2] do
    let j := d - 2 - j'
    if t % li != 0 then return none
    t := t / li
    let mj := mI ^ j
    let a0 := t.fdiv mj  -- floor (as CADO-NFS; `m` may be negative)
    let some mjinv := invMod (mj % li).toNat l | return none
    let k0 := ((t % li).toNat * mjinv % l + l - (a0 % li).toNat) % l
    let k : Int := if 2 * k0 ≥ l then (k0 : Int) - li else k0
    let a := a0 + k
    cs := cs.set! j a
    t := t - a * mj
  if t % li != 0 then return none
  cs := cs.set! 0 (t / li)
  let mut acc : Int := 0
  let mut lp : Int := 1
  for i' in [0:d + 1] do
    let i := d - i'
    acc := acc + cs[i]! * mI ^ i * lp
    lp := lp * li
  if acc != (n : Int) then return none
  return some (cs, mI)

/-- `f(x + k)` (Taylor shift). -/
def translate (cs : Array Int) (k : Int) : Array Int := Id.run do
  let d := cs.size - 1
  let mut c := cs
  for i in [0:d] do
    for j' in [0:d - i] do
      let j := d - 1 - j'
      c := c.set! j (c[j]! + k * c[j + 1]!)
  return c

/-- `f + λ x^j (ℓ x - m)`. -/
def rotJ (cs : Array Int) (l m lam : Int) (j : Nat) : Array Int :=
  (cs.modify (j + 1) (· + lam * l)).modify j (· - lam * m)

/-- Size optimization by local descent (CADO-NFS `sopt_local_descent`):
translations `x ↦ x + k` and rotations by `x^j (ℓ x - m)`, `j ≤ d - 2`, with
step sizes doubled on success and halved on failure. Returns the polynomial,
the new `m` (translation changes `ℓ x - m` to `ℓ x - (m - ℓ k)`) and the lognorm. -/
def sizeOpt (cs0 : Array Int) (l m0 : Int) (maxIter : Nat := 300) (rot : Bool := true) :
    Array Int × Int × Float := Id.run do
  let d := cs0.size - 1
  let ln (c : Array Int) : Float := (logNorm c).1
  let guard : Float := fc 1 / fc 1000
  let nrot := if rot then d - 1 else 0
  let base := ln cs0
  let mut steps : Array Int := #[]
  for j in [0:nrot] do
    let mut k : Int := 1
    for _ in [0:80] do
      if ln (rotJ cs0 l m0 k j) > base + guard && ln (rotJ cs0 l m0 (-k) j) > base + guard then break
      k := 2 * k
    steps := steps.push k
  let mut kt : Int := 1
  for _ in [0:80] do
    if ln (translate cs0 kt) > base + guard && ln (translate cs0 (-kt)) > base + guard then break
    kt := 2 * kt
  let mut cs := cs0
  let mut m := m0
  let mut best := base
  for _ in [0:maxIter] do
    let mut changedT := false
    let c1 := translate cs kt
    let v1 := ln c1
    if v1 < best then
      cs := c1
      m := m - l * kt
      best := v1
      changedT := true
    else
      let c2 := translate cs (-kt)
      let v2 := ln c2
      if v2 < best then
        cs := c2
        m := m + l * kt
        best := v2
        changedT := true
    let mut changed : Array Bool := Array.replicate nrot false
    for j in [0:nrot] do
      let k := steps[j]!
      let r1 := rotJ cs l m k j
      let w1 := ln r1
      if w1 < best then
        cs := r1
        best := w1
        changed := changed.set! j true
      else
        let r2 := rotJ cs l m (-k) j
        let w2 := ln r2
        if w2 < best then
          cs := r2
          best := w2
          changed := changed.set! j true
    let mut finished := !changedT && kt == 1
    for j in [0:nrot] do
      if changed[j]! || steps[j]! != 1 then finished := false
    if finished then break
    kt := if changedT then 2 * kt else if kt > 1 then kt / 2 else kt
    for j in [0:nrot] do
      let k := steps[j]!
      steps := steps.set! j (if changed[j]! then 2 * k else if k > 1 then k / 2 else k)
  return (cs, m, best)

/-- `f(x + k)` on float coefficients. -/
def translateF (cf : FloatArray) (k : Float) : FloatArray := Id.run do
  let d := cf.size - 1
  let mut c := cf
  for i in [0:d] do
    for j' in [0:d - i] do
      let j := d - 1 - j'
      c := c.set! j (c.get! j + k * c.get! (j + 1))
  return c

/-- `f + λ x^j (ℓ x - m)` on float coefficients. -/
@[inline] def rotJF (cf : FloatArray) (l m lam : Float) (j : Nat) : FloatArray :=
  let cf := cf.set! (j + 1) (cf.get! (j + 1) + lam * l)
  cf.set! j (cf.get! j - lam * m)

/-- `sizeOpt` with the trial polynomials in floating point (no big-integer
arithmetic per trial): the accepted moves (`0` a translation, `j + 1` a rotation
by `x^j g`) are replayed exactly at the end. -/
def sizeOptF (cs0 : Array Int) (l m0 : Int) (maxIter : Nat := 300) (rot : Bool := true) :
    Array Int × Int × Float := Id.run do
  let d := cs0.size - 1
  let f0 := toFloats cs0
  let r0 := logNormS f0 (fc 0)
  let base := r0.ln
  let sk0 := r0.sk
  -- trial polynomials are near the current one: its skewness seeds their search
  let ln (c : FloatArray) : Float := (logNormS c sk0).ln
  let guard : Float := fc 1 / fc 1000
  let nrot := if rot then d - 1 else 0
  let lf := intF l
  let mut steps : Array Int := #[]
  for j in [0:nrot] do
    let mut k : Int := 1
    for _ in [0:80] do
      let kf := intF k
      if ln (rotJF f0 lf (intF m0) kf j) > base + guard &&
          ln (rotJF f0 lf (intF m0) (Float.neg kf) j) > base + guard then break
      k := 2 * k
    steps := steps.push k
  let mut kt : Int := 1
  for _ in [0:80] do
    let kf := intF kt
    if ln (translateF f0 kf) > base + guard && ln (translateF f0 (Float.neg kf)) > base + guard then break
    kt := 2 * kt
  let mut cf := f0
  let mut m := m0
  let mut best := base
  let mut sk := sk0
  let mut moves : Array (Nat × Int) := #[]
  for _ in [0:maxIter] do
    let mut changedT := false
    let c1 := translateF cf (intF kt)
    let e1 := logNormS c1 sk
    let v1 := e1.ln
    if v1 < best then
      cf := c1
      m := m - l * kt
      best := v1
      sk := e1.sk
      changedT := true
      moves := moves.push (0, kt)
    else
      let c2 := translateF cf (intF (-kt))
      let e2 := logNormS c2 sk
      let v2 := e2.ln
      if v2 < best then
        cf := c2
        m := m + l * kt
        best := v2
        sk := e2.sk
        changedT := true
        moves := moves.push (0, -kt)
    let mut changed : Array Bool := Array.replicate nrot false
    let mf := intF m
    for j in [0:nrot] do
      let k := steps[j]!
      let r1 := rotJF cf lf mf (intF k) j
      let e1 := logNormS r1 sk
      let w1 := e1.ln
      if w1 < best then
        cf := r1
        best := w1
        sk := e1.sk
        changed := changed.set! j true
        moves := moves.push (j + 1, k)
      else
        let r2 := rotJF cf lf mf (intF (-k)) j
        let e2 := logNormS r2 sk
        let w2 := e2.ln
        if w2 < best then
          cf := r2
          best := w2
          sk := e2.sk
          changed := changed.set! j true
          moves := moves.push (j + 1, -k)
    let mut finished := !changedT && kt == 1
    for j in [0:nrot] do
      if changed[j]! || steps[j]! != 1 then finished := false
    if finished then break
    kt := if changedT then 2 * kt else if kt > 1 then kt / 2 else kt
    for j in [0:nrot] do
      let k := steps[j]!
      steps := steps.set! j (if changed[j]! then 2 * k else if k > 1 then k / 2 else k)
  -- replay the moves exactly (a rotation uses the `m` of its time)
  let mut cs := cs0
  let mut mm := m0
  for (op, k) in moves do
    if op == 0 then
      cs := translate cs k
      mm := mm - l * k
    else cs := rotJ cs l mm k (op - 1)
  return (cs, mm, (logNorm cs).1)

/-- Murphy's `α` over the primes below `B` (simple and projective roots). -/
def alphaB (cs : Array Int) (B : Nat) : Float := Id.run do
  let d := cs.size - 1
  let mut a : Float := 0
  for p in primesUpTo B do
    let red : Array Nat := cs.map fun c => (c % (p : Int)).toNat
    let pu := p.toUInt64
    let mut roots := 0
    for x in [0:p] do
      roots := roots + (if hornerMod red pu x.toUInt64 d == 0 then 1 else 0)
    if red[d]! == 0 then roots := roots + 1
    let pf := nf p
    a := a + (fc 1 / (pf - fc 1) - nf roots * pf / (pf * pf - fc 1)) * Float.log pf
  return a

/-- `F(x, 1) mod q` for `x < q ≤ 2^16` (Horner on machine words). -/
def evalModQ (red : Array UInt64) (q x : UInt64) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for i' in [0:red.size] do
    v := (v * x + red[red.size - 1 - i']!) % q
  return v

/-- The number of distinct roots modulo the prime `p` of `f` (reduced, nonzero
of degree at least one): `deg gcd(f, x^p - x)`. -/
def numRootsModP (p : Nat) (f : ModP.Pol) : Nat :=
  let xp := ModP.powMod p f #[0, 1] p
  (ModP.gcd p f (ModP.sub p xp #[0, 1])).size - 1

/-- `alphaExact` of a linear `ℓ x - m` with `gcd(ℓ, m) = 1`: one root on
`ℙ¹(ℤ/p^k)` at every level. -/
def alphaLinear (B : Nat) : Float := Id.run do
  let mut a : Float := 0
  for p in primesUpTo B do
    let pf := nf p
    let mut ev : Float := 0
    let mut q := p
    for _ in [0:13] do
      ev := ev + fc 1 / (nf q + nf (q / p))
      if q * p > 4096 then break
      q := q * p
    a := a + (fc 1 / (pf - fc 1) - ev) * Float.log pf
  return a

/-- Murphy's `α` over the primes below `B`, with the expected valuation
`Σ_k N_k / (p^k + p^{k-1})` (`N_k`: the roots of `F` on `ℙ¹(ℤ/p^k)`) counted
exactly for `p^k ≤ 4096`, which covers multiple roots modulo small primes. -/
def alphaExact (cs : Array Int) (B : Nat) : Float := Id.run do
  let d := cs.size - 1
  let mut a : Float := 0
  for p in primesUpTo B do
    let pf := nf p
    let lp := Float.log pf
    if p * p > 4096 then
      -- one level: the distinct roots modulo `p` (`deg gcd(f, x^p - x)`), and the
      -- root at infinity when `p ∣ a_d` (every point when `p` divides `f`)
      let red : Array Nat := cs.map fun c => (c % (p : Int)).toNat
      let f := ModP.trim red
      let n := if f.size == 0 then p + 1
        else (if f.size ≤ 1 then 0 else numRootsModP p f) + (if red[d]! == 0 then 1 else 0)
      a := a + (fc 1 / (pf - fc 1) - nf n / (pf + fc 1)) * lp
      continue
    let mut ev : Float := 0
    let mut q := p
    let mut level := 0
    while q ≤ 4096 || level == 0 do
      level := level + 1
      let qi : Int := q
      let red : Array UInt64 := cs.map fun c => (c % qi).toNat.toUInt64
      -- projective: F(1, y) with p | y, i.e. the reversed coefficients at y
      let rev : Array UInt64 := red.reverse
      let mut n := 0
      for x in [0:q] do
        if evalModQ red q.toUInt64 x.toUInt64 == 0 then n := n + 1
      for y' in [0:q / p] do
        let y := y' * p
        if evalModQ rev q.toUInt64 y.toUInt64 == 0 then n := n + 1
      ev := ev + nf n / (nf q + (nf (q / p)))
      if q > 4096 then break
      q := q * p
      if q > 4096 then break
    -- the remaining levels for simple roots (geometric tail): ignored beyond 4096
    let _ := d
    a := a + (fc 1 / (pf - fc 1) - ev) * lp
  return a

/-- `α` of `f + (u x + v)(ℓ x - m)` for `v ∈ [vlo, vlo + len)` (index `v - vlo`),
up to a constant, sieved over the prime powers `p^k ≤ 1024` and the primes below
200: for `x` with `p ∤ g(x)`, `x` is a root modulo `p^k` exactly when
`v ≡ -f(x)/g(x) - u x (mod p^k)`, and each root modulo `p^k` adds
`1/(p^k + p^{k-1})` to the expected valuation of `p`. Roots with `p ∣ g(x)` and
projective roots (which do not depend on `v`) are left out. -/
def alphaSieve (cs : Array Int) (l m u : Int) (vlo : Int) (len : Nat) : FloatArray := Id.run do
  let mut arr : FloatArray := ⟨Array.replicate len (fc 0)⟩
  let mut const : Float := fc 0
  for p in primesUpTo 200 do
    let pf := nf p
    let lp := Float.log pf
    let constW := lp / (pf - fc 1)
    let mut q := p
    for _ in [0:12] do
      let qi : Int := q
      let w := lp / (nf q + (nf (q / p)))
      let red : Array UInt64 := cs.map fun c => (c % qi).toNat.toUInt64
      let lm := (l % qi).toNat
      let mm := (m % qi).toNat
      let um := (u % qi).toNat
      let vl := (vlo % qi).toNat
      let mut cnt : Array Nat := Array.replicate q 0
      for x in [0:q] do
        let gx := (lm * x + q - mm) % q
        if gx % p == 0 then continue
        let fx := (evalModQ red q.toUInt64 x.toUInt64).toNat
        let gi := (invMod gx q).getD 0
        let vr := (2 * q - fx * gi % q - um * x % q) % q
        cnt := cnt.set! vr (cnt[vr]! + 1)
      for r in [0:q] do
        let c := cnt[r]!
        if c == 0 then continue
        let wr := nf c * w
        let mut t := (r + q - vl) % q
        for _ in [0:len / q + 1] do
          if t ≥ len then break
          arr := arr.set! t (arr.get! t - wr)
          t := t + q
      if q * p > 1024 then break
      q := q * p
    const := const + constW
  -- the constant part (the same for every `v`)
  for t in [0:len] do arr := arr.set! t (arr.get! t + const)
  return arr

/-- The lognorm at a fixed skewness `s`. -/
def lognormAt (cs : Array Int) (s : Float) : Float :=
  let d := cs.size - 1
  fc 1 / fc 2 * Float.log (hornerF (normPoly cs) (s * s) * Float.pow s (-((nf d))))

/-- The range `[kmin, kmax]` of rotations `k x^i (ℓ x - m)` keeping the lognorm
at skewness `s` at most `maxLog` (CADO-NFS `expected_growth`: doubling, then
bisection). -/
def rotRange (cs : Array Int) (l m : Int) (i : Nat) (maxLog s : Float) (reopt : Bool := false) :
    Int × Int := Id.run do
  let ok (k : Int) : Bool :=
    (if reopt then (logNorm (rotJ cs l m k i)).1 else lognormAt (rotJ cs l m k i) s) ≤ maxLog
  let mut kmin : Int := -1
  for _ in [0:80] do
    if !ok kmin then break
    kmin := 2 * kmin
  -- bisection between kmin (bad) and kmin / 2 (good)
  let mut bad := kmin
  let mut good := kmin / 2
  for _ in [0:80] do
    let mid := (bad + good) / 2
    if mid == bad || mid == good then break
    if ok mid then good := mid else bad := mid
  let lo := good
  let mut kmax : Int := 1
  for _ in [0:80] do
    if !ok kmax then break
    kmax := 2 * kmax
  bad := kmax
  good := kmax / 2
  for _ in [0:80] do
    let mid := (bad + good) / 2
    if mid == bad || mid == good then break
    if ok mid then good := mid else bad := mid
  return (lo, good)

/-- The expected minimum of `α` over `K = e^logK` rotations (CADO-NFS
`expected_alpha`: `α` is roughly normal with deviation `0.824`). -/
def expectedAlpha (logK : Float) : Float :=
  if logK < fc 999 / fc 1000 then fc 0
  else
    let t := Float.sqrt (fc 2 * logK)
    Float.neg ((fc 824 / fc 1000) * (t - (Float.log logK + fc 13766 / fc 10000) / (fc 2 * t)))

/-- The projective part of `α`: the primes dividing the leading coefficient
(one simple root at infinity each). -/
def projAlpha (cs : Array Int) : Float := Id.run do
  let ad := cs.back!.natAbs
  let mut a : Float := 0
  for p in primesUpTo 100 do
    if ad % p == 0 then
      let pf := nf p
      a := a - pf / (pf * pf - fc 1) * Float.log pf
  return a

/-- The expected `α` after root optimization (CADO-NFS `expected_rotation_gain`):
the projective `α`, the expected minimum over the rotations `x^i g` (`2i < d`)
that keep the lognorm within `0.2`, and `0.1` per nontrivial rotation degree. -/
def expectedRotationGain (cs : Array Int) (l m : Int) : Float := Id.run do
  let d := cs.size - 1
  let (n, s) := logNorm cs
  let mut S : Float := fc 1
  let mut incr : Float := fc 0
  for i in [0:d] do
    if 2 * i < d then
      let (kmin, kmax) := rotRange cs l m i (n + fc 2 / fc 10) s
      let sz := intF (kmax - kmin + 1)
      S := S * sz
      if sz ≥ fc 2 then incr := incr + fc 1 / fc 10
  return projAlpha cs + expectedAlpha (Float.log S) + incr

/-- Dickman's `ρ` on `[0, 32]` at step `1/64` (trapezoidal rule on
`ρ'(u) = -ρ(u - 1)/u`, `ρ = 1` on `[0, 1]`). -/
def dickmanTable : FloatArray := Id.run do
  let h : Float := fc 1 / fc 64
  let n := 32 * 64
  let mut t : FloatArray := ⟨Array.replicate (n + 1) (fc 1)⟩
  for i in [65:n + 1] do
    let u0 := (nf (i - 1)) * h
    let u1 := nf i * h
    let a := t.get! (i - 1 - 64) / u0
    let b := t.get! (i - 64) / u1
    t := t.set! i (t.get! (i - 1) - h * (a + b) / fc 2)
  return t

/-- `ρ(u)` by linear interpolation in `dickmanTable`. -/
def dickman (tbl : FloatArray) (u : Float) : Float :=
  if u ≤ fc 1 then fc 1
  else if u ≥ fc 32 then fc 0
  else
    let x := u * fc 64
    let i := x.floor.toUInt64.toNat
    let f := x - (nf i)
    tbl.get! i * (fc 1 - f) + tbl.get! (i + 1) * f

/-- Murphy's `E` (CADO-NFS `MurphyE`, `K` sample points on the skewed ellipse
of area `area`; smoothness bounds `bf`, `bg`). -/
def murphyE (tbl : FloatArray) (cs : Array Int) (l m : Int) (s bf bg area : Float) (B : Nat := 2000)
    (K : Nat := 200) : Float := Id.run do
  let af := alphaExact cs B
  let ag := if Nat.gcd l.natAbs m.natAbs == 1 then alphaLinear B else alphaExact #[-m, l] B
  let x0 := Float.sqrt (area * s)
  let y0 := Float.sqrt (area / s)
  let csF : Array Float := cs.map intF
  let lf := intF l
  let mf := intF m
  let pi : Float := fc 314159265358979 / fc 100000000000000
  let mut e : Float := 0
  for i in [0:K] do
    let ti := pi / nf K * (nf i + fc 1 / fc 2)
    let xi := x0 * Float.cos ti
    let yi := y0 * Float.sin ti
    -- F(x, y) by Horner in x / y
    let mut acc : Float := csF[cs.size - 1]!
    let mut yp : Float := fc 1
    for j' in [0:cs.size - 1] do
      let j := cs.size - 2 - j'
      yp := yp * yi
      acc := acc * xi + csF[j]! * yp
    let vf := (Float.log acc.abs + af) / Float.log bf
    let vg := (Float.log (lf * xi - mf * yi).abs + ag) / Float.log bg
    e := e + dickman tbl vf * dickman tbl vg
  return e / (nf K)

/-! ### Size optimization with lattice reduction (CADO-NFS `size_optimization`)

The local descent alone stops far from the best sizes (on the raw polynomials of
CADO-NFS's RSA-100 search: mean lognorm 33.8 against its 31.1). CADO-NFS first
tries translations that make the coefficients of degree 2 and 3 small together
(roots of their resultant), and for each reduces the lattice spanned by
`f(x + k)` and the rotations `x^i g(x + k)` (`i ≤ d - 2`), with the coordinates
weighted by powers of a skewness: its short vectors of degree `d` are
polynomials `a f + λ g`, which keep the root of `g` modulo `n`. -/

/-- `x` rounded to an integer (saturating beyond `2^63`). -/
def roundInt (x : Float) : Int :=
  let r := x.round
  if r ≥ fc 0 then (r.toUInt64.toNat : Int) else -(((Float.neg r).toUInt64.toNat : Nat) : Int)

/-- The real roots of `a x² + b x + c` (`a` may vanish). -/
def quadRoots (a b c : Float) : Array Float :=
  if a == fc 0 then (if b == fc 0 then #[] else #[Float.neg c / b])
  else
    let disc := b * b - fc 4 * a * c
    if disc < fc 0 then #[]
    else
      let sq := Float.sqrt disc
      #[(Float.neg b + sq) / (fc 2 * a), (Float.neg b - sq) / (fc 2 * a)]

/-- `Σ_{i<n} a_i b_i` from index `i` on, added to `acc`. -/
def dotGo (a b : FloatArray) (i : Nat) (acc : Float) : Nat → Float
  | 0 => acc
  | n + 1 => dotGo a b (i + 1) (acc + a.get! i * b.get! i) n

/-- `a - c b` (entrywise). -/
def axpyGo (a b : FloatArray) (c : Float) (i : Nat) : Nat → FloatArray
  | 0 => a
  | n + 1 => axpyGo (a.set! i (a.get! i - c * b.get! i)) b c (i + 1) n

/-- LLL reduction (`δ = 0.99`) of the integer rows `b`: floating-point
Gram–Schmidt of the rows `0 … k` recomputed at every step (the dimension is at
most six) from float copies of the rows, refreshed when a row changes. -/
def lll (b0 : Array (Array Int)) : Array (Array Int) := Id.run do
  let n := b0.size
  if n ≤ 1 then return b0
  let dim := b0[0]!.size
  let delta : Float := fc 99 / fc 100
  let mut b := b0
  let mut bf : Array FloatArray := b0.map toFloats
  let mut k := 1
  let mut iters := 0
  while k < n && iters < 5000 do
    iters := iters + 1
    -- Gram–Schmidt of the rows `0..k`
    let mut bs : Array FloatArray := #[]
    let mut Bn : FloatArray := FloatArray.emptyWithCapacity (k + 1)
    let mut mu : Array FloatArray := #[]
    for i in [0:k + 1] do
      let bi := bf[i]!
      let mut v := bi
      let mut row : FloatArray := FloatArray.emptyWithCapacity (k + 1)
      for j in [0:i] do
        let c := if Bn.get! j == fc 0 then fc 0 else dotGo bi bs[j]! 0 (fc 0) dim / Bn.get! j
        row := row.push c
        v := axpyGo v bs[j]! c 0 dim
      bs := bs.push v
      Bn := Bn.push (dotGo v v 0 (fc 0) dim)
      mu := mu.push row
    -- size reduction of row `k`
    let mut changed := false
    let mut muk := mu[k]!
    for j' in [0:k] do
      let j := k - 1 - j'
      let c := muk.get! j
      if c.abs > fc 51 / fc 100 then
        let q := roundInt c
        b := b.set! k (Array.zipWith (fun x y => x - q * y) b[k]! b[j]!)
        let qf := intF q
        for i in [0:j] do muk := muk.set! i (muk.get! i - qf * mu[j]!.get! i)
        muk := muk.set! j (c - qf)
        changed := true
    if changed then
      bf := bf.set! k (toFloats b[k]!)
      continue
    let c := muk.get! (k - 1)
    if Bn.get! k ≥ (delta - c * c) * Bn.get! (k - 1) then k := k + 1
    else
      let t := b[k]!
      b := (b.set! k b[k - 1]!).set! (k - 1) t
      let tf := bf[k]!
      bf := (bf.set! k bf[k - 1]!).set! (k - 1) tf
      k := max 1 (k - 1)
  return b

/-- The shortest polynomial of degree `d` in the reduced lattice of `f(x + k)`
and `x^i g(x + k)` (`i ≤ maxRot`, `g = ℓ x - m`), weighted by `skew`: the
polynomial, the translated `m` and its weighted squared norm. -/
def bestNorm (cs : Array Int) (l m skew k : Int) (maxRot : Nat) : Option (Array Int × Int × Float) :=
  Id.run do
  let d := cs.size - 1
  let ft := translate cs k
  let mt := m - l * k
  let pw : Array Int := (Array.range (d + 1)).map fun j => skew ^ j
  let mut rows : Array (Array Int) := #[(Array.range (d + 1)).map fun j => ft[j]! * pw[j]!]
  for i in [0:maxRot + 1] do
    rows := rows.push ((Array.range (d + 1)).map fun j =>
      if j == i then -mt * pw[j]! else if j == i + 1 then l * pw[j]! else 0)
  let red := lll rows
  let mut best : Option (Array Int × Int × Float) := none
  for r in red do
    if r[d]! == 0 then continue
    let nrm := (r.map fun x => let f := intF x; f * f).foldl (· + ·) (fc 0)
    match best with
    | some (_, _, b) => if nrm ≥ b then continue
    | none => pure ()
    best := some ((Array.range (d + 1)).map fun j => r[j]! / pw[j]!, mt, nrm)
  return best

/-- `bestNorm` iterated over the translations that cancel the coefficient of
degree `d - 2` (CADO-NFS `best_norm2`, at most `depth` levels). -/
def bestNorm2 (cs : Array Int) (l m skew k : Int) (maxRot : Nat) (minNorm : Float) :
    Nat → Option (Array Int × Int × Float)
  | 0 => none
  | depth + 1 => Id.run do
    let d := cs.size - 1
    let some (ft, mt, nrm) := bestNorm cs l m skew k maxRot | return none
    if nrm ≥ minNorm then return none
    let mut best := (ft, mt, nrm)
    let eq2 := nf (d * (d - 1) / 2) * intF ft[d]!
    let eq1 := nf (d - 1) * intF ft[d - 1]!
    let eq0 := intF ft[d - 2]!
    -- `ft` is `f` translated by `k` (and rotated): its own translations add to `k`
    for r in quadRoots eq2 eq1 eq0 do
      let k2 := k + roundInt r
      if k2 == k then continue
      if let some c := bestNorm2 cs l m skew k2 maxRot best.2.2 depth then
        if c.2.2 < best.2.2 then best := c
    return some best

/-- Translations `k` for which `(f + q₂ x² g)(x + k)` has vanishing coefficients
of degree 2 and 3 for some `q₂` (CADO-NFS `sopt_find_translations_deg5`), with
rational approximations of `q₂` of denominator at most 100. -/
def translationsDeg5 (cs : Array Int) (l m : Int) : Array Int := Id.run do
  let a5 := intF cs[5]!
  let a4 := intF cs[4]!
  let a3 := intF cs[3]!
  let a2 := intF cs[2]!
  let g1 := intF l
  let g0 := intF (-m)
  let r2 := (fc 5 * a5 * g0 - a4 * g1) * (fc 5 * a5 * g0 - a4 * g1)
  let r1 := fc 8 * a4 * a4 * a4 * g0 - fc 30 * a3 * a4 * a5 * g0 + fc 50 * a2 * a5 * a5 * g0 -
    fc 2 * a3 * a4 * a4 * g1 + fc 10 * a3 * a3 * a5 * g1 - fc 10 * a2 * a4 * a5 * g1
  let r0 := Float.neg (fc 3) * a3 * a3 * a4 * a4 + fc 8 * a2 * a4 * a4 * a4 + fc 10 * a3 * a3 * a3 * a5 -
    fc 30 * a2 * a3 * a4 * a5 + fc 25 * a2 * a2 * a5 * a5
  let mut out : Array Int := #[]
  for q in quadRoots r2 r1 r0 do
    if q.abs > fc 10000000000 then continue
    -- rational approximations with denominators up to 100 (16 at most)
    let mut bestE : Float := fc 2
    let mut approx : Array Float := #[]
    for den in [1:101] do
      if approx.size ≥ 16 then break
      let dF := nf den
      let num := (dF * q).round
      let e := (q - num / dF).abs
      if e < bestE then
        bestE := e
        approx := approx.push (num / dF)
    for qr in approx do
      for k in quadRoots (fc 10 * a5) (fc 4 * a4) (g1 * qr + a3) do
        out := out.push (roundInt k)
  return out

/-- Size optimization as CADO-NFS: translations `0` and `translationsDeg5`
(degree 5), each through `bestNorm2` and the local descent `sizeOpt`, scored by
lognorm plus the expected rotation gain. Returns the polynomial, `m` and the
lognorm. -/
def sizeOpt2 (cs0 : Array Int) (l m0 : Int) : Array Int × Int × Float := Id.run do
  let d := cs0.size - 1
  let (c0, mm0, ln0) := sizeOptF cs0 l m0
  let mut best := (c0, mm0, ln0)
  let mut bestScore := ln0 + expectedRotationGain c0 l mm0
  let skew0 := Float.pow ((intF m0).abs / (intF cs0[d]!).abs) (fc 1 / nf d)
  let skew := max 1 (roundInt skew0)
  let ks : Array Int := (if d == 5 then translationsDeg5 cs0 l m0 else #[]).push 0
  let mut seen : Array Int := #[]
  for k in ks do
    if seen.contains k then continue
    seen := seen.push k
    let some (ft, mt, _) := bestNorm2 cs0 l m0 skew k (d - 2) (fc 1 / fc 0) 8 | continue
    let (f2, m2, ln2) := sizeOptF ft l mt
    let sc := ln2 + expectedRotationGain f2 l m2
    if sc < bestScore then
      bestScore := sc
      best := (f2, m2, ln2)
  return best

/-- `Π_{i ∈ idx} t[i np + j] mod pps[j]` for every `j < np` (`idx` nonempty). -/
def invsOf (t pps idx : Array Nat) (np : Nat) : Array Nat := Id.run do
  let mut out := t.extract (idx[0]! * np) (idx[0]! * np + np)
  for i in idx.extract 1 idx.size do
    for j in [0:np] do
      out := out.set! j (out[j]! * t[i * np + j]! % pps[j]!)
  return out

/-- A collision candidate after size optimization. -/
structure CCand where
  cs : Array Int
  l : Nat
  m : Int
  score : Float
  deriving Inhabited

/-- The best size-optimized collision polynomials (by lognorm + `α`) for the
leading coefficients `ad ∈ [adLo, adHi)` stepping by `incr`. -/
def collisionSearch (n d P nq incr adLo adHi keep : Nat) (lllSopt : Bool := false)
    (cadoQ : Bool := true) : Array CCand :=
  Id.run do
  let mut best : Array CCand := #[]
  let primesP := (primesUpTo (2 * P)).filter (· ≥ P)
  let M := 4 * P * P
  let useTab := 2 * M < 1073741824 && primesP.size < 16384
  let mut tbl : Array Nat := Array.replicate 16384 0
  let mut gen := 0
  let mut ad := (adLo + incr - 1) / incr * incr
  if ad == 0 then ad := incr
  while ad < adHi do
    let ntilde := d ^ d * ad ^ (d - 1) * n
    let m0 := iroot ntilde d
    let prs : Array (Nat × Array Nat) := primesP.filterMap fun p =>
      if (d * ad) % p == 0 || n % p == 0 then none
      else
        let rs := liftedRoots d ntilde m0 p
        if rs.isEmpty then none else some (p, rs)
    -- special-q primes with roots, and the number k of factors
    let sq : Array (Nat × Array Nat) := specialQPrimes.toArray.filterMap fun q =>
      if (d * ad) % q == 0 || n % q == 0 then none
      else
        let rs := liftedRoots d ntilde m0 q
        if rs.isEmpty then none else some (q, rs)
    let p2 := (2 * P).toFloat
    let (sq, k) := suitableQ sq d nq (m0.toFloat / (p2 * p2 * p2 * p2)) cadoQ
    -- `1/Q² mod p²` as the product of the `1/q² mod p²` of the factors of `Q`
    let np := prs.size
    let pps : Array Nat := prs.map fun (p, _) => p * p
    let invQ : Array Nat := sq.foldl (fun acc (q, _) => pps.foldl (fun acc pp =>
      acc.push (invModW ((q * q) % pp).toUInt64 pp.toUInt64).toNat) acc) #[]
    for (Q, rsQ, idx) in specialQList sq k nq do
      let QQ := Q * Q
      let invs := invsOf invQ pps idx np
      for rQ in rsQ do
        gen := gen + 1
        if gen ≥ 524288 then
          tbl := Array.replicate 16384 0
          gen := 1
        let (cols, t) := if useTab then collideTab prs invs rQ M tbl gen
          else (collide prs invs rQ M, tbl)
        tbl := t
        for (i, p1, p2) in cols do
          let mt : Int := (m0 : Int) + (rQ : Int) + i * (QQ : Int)
          let l := p1 * p2 * Q
          match fromCollision n d ad mt l with
          | none => pure ()
          | some (cs, m) =>
            -- CADO discards a_d a_{d-2} > 0 (size optimization works badly)
            if cs[d]! * cs[d - 2]! > 0 then continue
            let (cs', m', ln) := if lllSopt then sizeOpt2 cs l m else sizeOptF cs l m
            -- the same pair up to signs: `m > 0` by `x ↦ -x`, `c_d > 0` by `f ↦ -f`
            -- (discarding them lost about half of the candidates)
            let (cs', m') := if m' < 0 then
                ((cs'.mapIdx fun i c => if i % 2 == 1 then -c else c), -m')
              else (cs', m')
            let cs' := if cs'[d]! < 0 then cs'.map (- ·) else cs'
            if m' == 0 || cs'[d]! == 0 then continue
            -- CADO also discards a_{d-1} a_{d-3} > 0 after size optimization
            if d ≥ 3 && cs'[d - 1]! * cs'[d - 3]! > 0 then continue
            let c : CCand := { cs := cs', l, m := m', score := ln + expectedRotationGain cs' l m' }
            if best.size < keep then best := best.push c
            else
              let mut wi := 0
              for j in [1:best.size] do
                if best[j]!.score > best[wi]!.score then wi := j
              if c.score < best[wi]!.score then best := best.set! wi c
    ad := ad + incr
  return best

/-- The raw collision polynomials of `collisionSearch` for the leading
coefficients `[adLo, adHi)`, before any filter: `(a_d, ℓ, m, coefficients)`
(a development aid for comparisons with CADO-NFS). -/
def collisionRaw (n d P nq incr adLo adHi : Nat) : Array (Nat × Nat × Int × Array Int) := Id.run do
  let mut out : Array (Nat × Nat × Int × Array Int) := #[]
  let primesP := (primesUpTo (2 * P)).filter (· ≥ P)
  let M := 4 * P * P
  let mut ad := (adLo + incr - 1) / incr * incr
  if ad == 0 then ad := incr
  while ad < adHi do
    let ntilde := d ^ d * ad ^ (d - 1) * n
    let m0 := iroot ntilde d
    let prs : Array (Nat × Array Nat) := primesP.filterMap fun p =>
      if (d * ad) % p == 0 || n % p == 0 then none
      else
        let rs := liftedRoots d ntilde m0 p
        if rs.isEmpty then none else some (p, rs)
    let sq : Array (Nat × Array Nat) := specialQPrimes.toArray.filterMap fun q =>
      if (d * ad) % q == 0 || n % q == 0 then none
      else
        let rs := liftedRoots d ntilde m0 q
        if rs.isEmpty then none else some (q, rs)
    let p2 := (2 * P).toFloat
    let (sq, k) := suitableQ sq d nq (m0.toFloat / (p2 * p2 * p2 * p2))
    for (Q, rsQ, _) in specialQList sq k nq do
      let QQ := Q * Q
      let invs := prs.map fun (p, _) => (invModW (QQ % (p * p)).toUInt64 (p * p).toUInt64).toNat
      for rQ in rsQ do
        for (i, p1, p2) in collide prs invs rQ M do
          let mt : Int := (m0 : Int) + (rQ : Int) + i * (QQ : Int)
          let l := p1 * p2 * Q
          if let some (cs, m) := fromCollision n d ad mt l then out := out.push (ad, l, m, cs)
    ad := ad + incr
  return out

/-- Root optimization: rotations `(u x + v)(ℓ x - m)` within the lognorm margin
`margin` (at most `maxU` values of `u`, `maxV` of `v`, centered). The `top`
best sieved `α` of each `u` are scored by lognorm + sieved `α`, and the 16 best
of these are re-scored with the exact `α` (`alphaExact`). -/
def rootOpt (c : CCand) (margin : Float) (maxU maxV top : Nat) (reopt : Bool := false) : CCand :=
  Id.run do
  let (n, s) := logNorm c.cs
  -- quadratic rotations `w x² g` too for degree five and more (at most 9 of them)
  let (wlo, whi) : Int × Int := if c.cs.size ≥ 6 then
      let (a, b) := rotRange c.cs c.l c.m 2 (n + margin) s
      (max a (-4), min b 4)
    else (0, 0)
  let mut short : Array (Float × Array Int) := #[]
  for wi in [0:(whi - wlo + 1).toNat] do
    let w : Int := wlo + wi
    let cw := rotJ c.cs c.l c.m w 2
    let (ulo0, uhi0) := rotRange cw c.l c.m 1 (n + margin) s reopt
    let ulo := max ulo0 (-((maxU / 2 : Nat) : Int))
    let uhi := min uhi0 ((maxU / 2 : Nat) : Int)
    for ui in [0:(uhi - ulo + 1).toNat] do
      let u : Int := ulo + ui
      let base := rotJ cw c.l c.m u 1
      let (vlo0, vhi0) := rotRange base c.l c.m 0 (n + margin) s reopt
      let vlo := max vlo0 (-((maxV / 2 : Nat) : Int))
      let vhi := min vhi0 ((maxV / 2 : Nat) : Int)
      if vhi < vlo then continue
      let len := (vhi - vlo + 1).toNat
      let arr := alphaSieve cw c.l c.m u vlo len
      let idx := ((Array.range arr.size).qsort fun a b => arr.get! a < arr.get! b).extract 0 top
      for t in idx do
        let cs := rotJ base c.l c.m (vlo + (t : Int)) 0
        short := short.push ((logNorm cs).1 + arr.get! t, cs)
  let mut best := c
  let mut bestScore := n + alphaExact c.cs 200
  for (_, cs) in (short.qsort fun a b => a.1 < b.1).extract 0 16 do
    let sc := (logNorm cs).1 + alphaExact cs 200
    if sc < bestScore then
      bestScore := sc
      best := { c with cs, score := sc }
  return { best with score := bestScore }

/-! ### Root optimization as CADO-NFS (`ropt_linear`, degrees 4 and 5)

The rotations `f + (u x + v) g` are bounded as in CADO-NFS: `u` and `v` grow by
powers of two while the rotated polynomial, re-optimized by translation, keeps
`lognorm + expectedRotationGain` within `0.5%` of the original's. Each `u` gets
a sieve of `α` over `v` (primes below 200); the best `v` of each `u` are
translation-optimized and ranked by lognorm plus their sieved `α`, and the best
of those by Murphy's `E`. -/

/-- `lognorm + expectedRotationGain` of `f + k x^j g` re-optimized by translation. -/
def rotScore (cs : Array Int) (l m k : Int) (j : Nat) : Float :=
  let (f, m', ln) := sizeOptF (rotJ cs l m k j) l m 300 false
  ln + expectedRotationGain f l m'

/-- The first powers of two `-2^a`, `2^b` for which `f + k x^j g` re-optimized by
translation scores above `bound` (CADO-NFS `rotate_bounds_U_lu`, `_V_mpz`). -/
def rotBounds (cs : Array Int) (l m : Int) (j : Nat) (bound : Float) (maxI : Nat) :
    Int × Int := Id.run do
  let mut hi : Int := 1
  for _ in [0:maxI] do
    if rotScore cs l m hi j > bound then break
    hi := 2 * hi
  let mut lo : Int := -1
  for _ in [0:maxI] do
    if rotScore cs l m lo j > bound then break
    lo := 2 * lo
  return (lo, hi)

/-- One prime power of the `α` sieve: `q = p^k`, the weight `log p / (q + q/p)` of
a root modulo `q`, and for each `x` with `p ∤ g(x)` the residue `-f(x)/g(x)`: `x`
is a root of `f + (u x + v) g` modulo `q` exactly when `v ≡ -f(x)/g(x) - u x`. -/
structure AlphaTab where
  q : Nat
  w : Float
  xs : Array Nat
  rs : Array Nat

/-- The `α` sieve tables of `f` for the prime powers `p^k ≤ 1024`, `p < 200`, and
the constant part `Σ log p / (p - 1)`. -/
def alphaTabs (cs : Array Int) (l m : Int) : Array AlphaTab × Float := Id.run do
  let mut out : Array AlphaTab := #[]
  let mut const : Float := fc 0
  for p in primesUpTo 200 do
    let pf := nf p
    let lp := Float.log pf
    const := const + lp / (pf - fc 1)
    let mut q := p
    for _ in [0:12] do
      let qi : Int := q
      let red : Array UInt64 := cs.map fun c => (c % qi).toNat.toUInt64
      let lm := (l % qi).toNat
      let mm := (m % qi).toNat
      let mut xs : Array Nat := #[]
      let mut rs : Array Nat := #[]
      for x in [0:q] do
        let gx := (lm * x + q - mm) % q
        if gx % p == 0 then continue
        let fx := (evalModQ red q.toUInt64 x.toUInt64).toNat
        let gi := (invMod gx q).getD 0
        xs := xs.push x
        rs := rs.push ((q - fx * gi % q) % q)
      out := out.push { q, w := lp / (nf q + nf (q / p)), xs, rs }
      if q * p > 1024 then break
      q := q * p
  return (out, const)

/-- Subtract `wr` at `s, s + q, …` below `len`. -/
def sieveSub (arr : FloatArray) (s q len : Nat) (wr : Float) : Nat → FloatArray
  | 0 => arr
  | n + 1 => if s < len then sieveSub (arr.set! s (arr.get! s - wr)) (s + q) q len wr n else arr

/-- `α` (primes below 200, affine roots) of `f + (u x + v) g` for `v ∈ [vlo, vlo + len)`
from the tables of `alphaTabs`. -/
def alphaSieveTab (tabs : Array AlphaTab) (const : Float) (u vlo : Int) (len : Nat) :
    FloatArray := Id.run do
  let mut arr : FloatArray := FloatArray.emptyWithCapacity len
  for _ in [0:len] do arr := arr.push const
  for t in tabs do
    let q := t.q
    let qi : Int := q
    let um := (u % qi).toNat
    let vl := (vlo % qi).toNat
    let mut cnt : Array Nat := Array.replicate q 0
    for i in [0:t.xs.size] do
      let vr := (t.rs[i]! + q - um * t.xs[i]! % q) % q
      cnt := cnt.set! vr (cnt[vr]! + 1)
    for r in [0:q] do
      let c := cnt[r]!
      if c != 0 then arr := sieveSub arr ((r + q - vl) % q) q len (nf c * t.w) (len / q + 1)
  return arr

/-- The index of the largest first component. -/
def worstIdx (best : Array (Float × Nat)) : Nat := Id.run do
  let mut wi := 0
  for j in [1:best.size] do
    if best[j]!.1 > best[wi]!.1 then wi := j
  return wi

/-- The `T` smallest entries of `arr` from index `i` on, as `(value, index)`. -/
def topGo (arr : FloatArray) (T : Nat) (best : Array (Float × Nat)) (wi i : Nat) :
    Nat → Array (Float × Nat)
  | 0 => best
  | n + 1 =>
    let v := arr.get! i
    if best.size < T then
      let best := best.push (v, i)
      topGo arr T best (worstIdx best) (i + 1) n
    else if v < best[wi]!.1 then
      let best := best.set! wi (v, i)
      topGo arr T best (worstIdx best) (i + 1) n
    else topGo arr T best wi (i + 1) n

/-- Root optimization of a candidate of degree 4 or 5 as CADO-NFS's `ropt_linear`: the
best pair by Murphy's `E` (bounds `bf`, `bg`, `area`), with that `E`. `uMul`,
`vMul` scale the rotation bounds, `uCap` and `maxLen` cap `|u|` and the sieved
`v` per `u` (CADO-NFS restricts wide ranges to sublattices instead); the `T`
best `v` of each `u` by `α` are translation-optimized, and the `F` best of
those by lognorm plus `α` are ranked by `E`. -/
def rootOpt2 (tbl : FloatArray) (c : CCand) (bf bg area : Float)
    (uMul vMul uCap maxLen T F : Nat) : CCand × Float := Id.run do
  let cs := c.cs
  let l : Int := c.l
  let m := c.m
  let (n0, _) := logNorm cs
  let bound := (n0 + expectedRotationGain cs l m) * (fc 1005 / fc 1000)
  let (ulo0, uhi0) := rotBounds cs l m 1 bound 62
  let (vlo0, vhi0) := rotBounds cs l m 0 bound 150
  let ulo := max (ulo0 * uMul) (-(uCap : Int))
  let uhi := min (uhi0 * uMul) (uCap : Int)
  let half : Int := (maxLen / 2 : Nat)
  let vlo := max (vlo0 * vMul) (-half)
  let vhi := min (vhi0 * vMul) half
  let len := (vhi - vlo + 1).toNat
  let (tabs, const) := alphaTabs cs l m
  let mut short : Array (Float × Array Int × Int) := #[]
  for ui in [0:(uhi - ulo + 1).toNat] do
    let u := ulo + ui
    let arr := alphaSieveTab tabs const u vlo len
    let base := rotJ cs l m u 1
    for (a, t) in topGo arr T #[] 0 0 len do
      let (f, m', ln) := sizeOptF (rotJ base l m (vlo + t) 0) l m 300 false
      short := short.push (ln + a, f, m')
  let mut best := c
  let s0 := (logNorm cs).2
  let mut bestE := murphyE tbl cs l m s0 bf bg area
  for (_, f, m') in (short.qsort fun a b => a.1 < b.1).extract 0 F do
    -- the same pair up to signs: `m > 0` by `x ↦ -x`, `c_d > 0` by `f ↦ -f`
    let (f, m') := if m' < 0 then ((f.mapIdx fun i c => if i % 2 == 1 then -c else c), -m')
      else (f, m')
    let f := if f.back! < 0 then f.map (- ·) else f
    let e := murphyE tbl f l m' (logNorm f).2 bf bg area
    if e > bestE then
      bestE := e
      best := { c with cs := f, m := m' }
  return (best, bestE)

/-- A polynomial pair by collision search, size and root optimization, ranked
by Murphy's `E` with bounds `2^lpbA`, `2^lpbR` over `area`. -/
def selectCollision (n d P nq incr admax keep : Nat) (U V : Nat) (lpbR lpbA : Nat) (area : Float)
    (threads : Nat := 1) : Option Selection := Id.run do
  let t := max 1 threads
  let count := (admax + incr - 1) / incr
  -- about four tasks per thread: leading coefficients cost unequal times, and
  -- the task pool balances many small tasks (one per thread left threads idle)
  let per := (count + 4 * t - 1) / (4 * t)
  -- CADO-NFS's root optimization in degrees 4 and 5; in degree 5 also its
  -- special-q order and size optimization with lattice reduction (on RSA-100
  -- they reach CADO-NFS's polynomial; in degree 4 its special-q order picked
  -- worse polynomials at 80 digits)
  let tasks := (List.range ((count + per - 1) / per)).map fun i =>
    Task.spawn fun _ => collisionSearch n d P nq incr (1 + i * per * incr)
      (min (admax + 1) (1 + (i + 1) * per * incr)) keep (d == 5) (d == 5)
  let mut cands : Array CCand := tasks.foldl (fun acc tk => acc ++ tk.get) #[]
  cands := (cands.qsort fun a b => a.score < b.score).extract 0 keep
  if cands.isEmpty then return none
  let tbl := dickmanTable
  let bf := Float.exp2 lpbA.toFloat
  let bg := Float.exp2 lpbR.toFloat
  let rot := cands.toList.map fun c => Task.spawn fun _ =>
    if d == 4 || d == 5 then rootOpt2 tbl c bf bg area 2 8 16 262144 16 16
    else
      let r := rootOpt c (fc 1) U V 32
      (r, murphyE tbl r.cs r.l r.m (logNorm r.cs).2 bf bg area)
  let mut best : Option (Float × CCand) := none
  for tk in rot do
    let (c, e) := tk.get
    if c.m ≤ 0 || c.cs[d]! ≤ 0 then continue
    match best with
    | none => best := some (e, c)
    | some (e0, _) => if e > e0 then best := some (e, c)
  match best with
  | none => return none
  | some (_, c) => return some { coeffs := c.cs, m := c.m.toNat, y1 := c.l }

end PrimeFactorLean.NFS.PolySelect
