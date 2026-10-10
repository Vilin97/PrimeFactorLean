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

/-- `s^d · ‖F‖²(s) = Σ_k w_k s^k` as a polynomial in the skewness `s` (unboxed
coefficients `w_0 … w_{2d}`; odd `k` vanish). -/
def normPoly (cs : Array Int) : FloatArray := Id.run do
  let d := cs.size - 1
  let mut w : FloatArray := FloatArray.emptyWithCapacity (2 * d + 1)
  for k in [0:2 * d + 1] do
    let mut c : Float := 0
    if k % 2 == 0 then
      for i in [0:d + 1] do
        if i ≤ k && k - i ≤ d then c := c + intF cs[i]! * intF cs[k - i]!
      c := c * fc 4 / ((nf (k + 1)) * (nf (2 * d - k + 1)))
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
  let dF := nf d
  let f (t : Float) : Float := evalNormPoly w (Float.exp t) * Float.exp (-dF * t)
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

/-- The roots `r ≠ 0` of `x^d ≡ c (mod p)` lifted to roots modulo `p²` (Hensel),
returned as the residues of `r - m₀` modulo `p²`. -/
def liftedRoots (d c m0 p : Nat) : Array Nat := Id.run do
  let pp := p * p
  let cp := c % pp
  let f := ModP.ofInts p (((-((cp % p : Nat) : Int)) :: List.replicate (d - 1) (0 : Int)) ++ [1])
  let mut out : Array Nat := #[]
  for r in ModP.roots p f do
    if r == 0 then continue
    let some inv := invMod (d * powMod r (d - 1) p % p) p | continue
    let t := (cp + pp - powMod r d pp) % pp
    let rr := r + t / p * inv % p * p
    out := out.push ((rr + pp - m0 % pp) % pp)
  return out

/-- The special-`q` primes of CADO-NFS (`SPECIAL_Q`). -/
def specialQPrimes : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
   97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
   193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271]

/-- `x` with `x ≡ a (mod ma)`, `x ≡ b (mod mb)` (coprime moduli), in `[0, ma mb)`. -/
def crt2 (a ma b mb : Nat) : Nat :=
  let inv := (invMod (ma % mb) mb).getD 0
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

/-- Up to `nq` special-`q`: products `Q` of `k` primes of `sq` (lexicographic
subsets) and every combination of their roots, combined modulo `Q²`. -/
def specialQList (sq : Array (Nat × Array Nat)) (k nq : Nat) : Array (Nat × Array Nat) := Id.run do
  let mut out : Array (Nat × Array Nat) := #[]
  if sq.size < k || k == 0 then return out
  let mut idx : Array Nat := (Array.range k)
  let mut total := 0
  for _ in [0:100000] do
    -- all root combinations for this subset
    let mut combos : Array (Nat × Nat) := #[(1, 0)]   -- (Q², r mod Q²) partial products
    for i in idx do
      let (q, rs) := sq[i]!
      let qq := q * q
      combos := combos.foldl (fun acc (QQ, r) => acc ++ rs.map fun rq => (QQ * qq, crt2 r QQ rq qq)) #[]
    let Q := idx.foldl (fun acc i => acc * sq[i]!.1) 1
    let rsQ := combos.map (·.2)
    let take := min rsQ.size (nq - total)
    out := out.push (Q, rsQ.extract 0 take)
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

/-- The pair of `m̃` and `ℓ` (Lemma 2.1 with modulus `ℓ` after fixing
`a_d = ad` and the centered `a_{d-1} ≡ m̃ / ℓ (mod d a_d)`): the coefficients and
`m`, with `n = Σ a_j m^j ℓ^{d-j}` checked. -/
def fromCollision (n d ad : Nat) (mt : Int) (l : Nat) : Option (Array Int × Nat) := Id.run do
  let dad := d * ad
  if l == 0 || dad == 0 then return none
  let some linv := invMod (l % dad) dad | return none
  let a1n := (mt % (dad : Int)).toNat * linv % dad
  let a1 : Int := if 2 * a1n ≥ dad then (a1n : Int) - (dad : Int) else a1n
  let num := mt - a1 * (l : Int)
  if num % (dad : Int) != 0 then return none
  let mI := num / (dad : Int)
  if mI ≤ 0 then return none
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
    let a0 := t / mj
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
  return some (cs, mI.toNat)

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
def sizeOpt (cs0 : Array Int) (l m0 : Int) (maxIter : Nat := 300) : Array Int × Int × Float := Id.run do
  let d := cs0.size - 1
  let ln (c : Array Int) : Float := (logNorm c).1
  let guard : Float := fc 1 / fc 1000
  let nrot := d - 1
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

/-- Murphy's `α` over the primes below `B`, with the expected valuation
`Σ_k N_k / (p^k + p^{k-1})` (`N_k`: the roots of `F` on `ℙ¹(ℤ/p^k)`) counted
exactly for `p^k ≤ 4096`, which covers multiple roots modulo small primes. -/
def alphaExact (cs : Array Int) (B : Nat) : Float := Id.run do
  let d := cs.size - 1
  let mut a : Float := 0
  for p in primesUpTo B do
    let pf := nf p
    let lp := Float.log pf
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
    -- the constant part
    for t in [0:len] do arr := arr.set! t (arr.get! t + constW)
  return arr

/-- The lognorm at a fixed skewness `s`. -/
def lognormAt (cs : Array Int) (s : Float) : Float :=
  let d := cs.size - 1
  fc 1 / fc 2 * Float.log (evalNormPoly (normPoly cs) s * Float.pow s (-((nf d))))

/-- The range `[kmin, kmax]` of rotations `k x^i (ℓ x - m)` keeping the lognorm
at skewness `s` at most `maxLog` (CADO-NFS `expected_growth`: doubling, then
bisection). -/
def rotRange (cs : Array Int) (l m : Int) (i : Nat) (maxLog s : Float) : Int × Int := Id.run do
  let ok (k : Int) : Bool := lognormAt (rotJ cs l m k i) s ≤ maxLog
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
  let ag := alphaExact #[-m, l] B
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

/-- A collision candidate after size optimization. -/
structure CCand where
  cs : Array Int
  l : Nat
  m : Int
  score : Float
  deriving Inhabited

/-- The best size-optimized collision polynomials (by lognorm + `α`) for the
leading coefficients `ad ∈ [adLo, adHi)` stepping by `incr`. -/
def collisionSearch (n d P nq incr adLo adHi keep : Nat) : Array CCand := Id.run do
  let mut best : Array CCand := #[]
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
    -- special-q primes with roots, and the number k of factors
    let sq : Array (Nat × Array Nat) := specialQPrimes.toArray.filterMap fun q =>
      if (d * ad) % q == 0 || n % q == 0 then none
      else
        let rs := liftedRoots d ntilde m0 q
        if rs.isEmpty then none else some (q, rs)
    let p2 := (2 * P).toFloat
    let lim := m0.toFloat / (p2 * p2 * p2 * p2)
    let mut k := 0
    let mut prod := 1
    let mut sqv : Float := fc 1
    for (q, _) in sq do
      if prod ≥ nq then break
      if sqv * q.toFloat ≥ lim then break
      prod := prod * d
      sqv := sqv * q.toFloat
      k := k + 1
    for (Q, rsQ) in specialQList sq (max 1 (min k 8)) nq do
      let QQ := Q * Q
      let invs := prs.map fun (p, _) => (invMod (QQ % (p * p)) (p * p)).getD 0
      for rQ in rsQ do
        for (i, p1, p2) in collide prs invs rQ M do
          let mt : Int := (m0 : Int) + (rQ : Int) + i * (QQ : Int)
          let l := p1 * p2 * Q
          match fromCollision n d ad mt l with
          | none => pure ()
          | some (cs, m) =>
            -- CADO discards a_d a_{d-2} > 0 (size optimization works badly)
            if cs[d]! * cs[d - 2]! > 0 then continue
            let (cs', m', ln) := sizeOpt cs l m
            if m' ≤ 0 || cs'[d]! ≤ 0 then continue
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

/-- Root optimization: rotations `(u x + v)(ℓ x - m)` within the lognorm margin
`margin` (at most `maxU` values of `u`, `maxV` of `v`, centered). The `top`
best sieved `α` of each `u` are scored by lognorm + sieved `α`, and the 16 best
of these are re-scored with the exact `α` (`alphaExact`). -/
def rootOpt (c : CCand) (margin : Float) (maxU maxV top : Nat) : CCand := Id.run do
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
    let (ulo0, uhi0) := rotRange cw c.l c.m 1 (n + margin) s
    let ulo := max ulo0 (-((maxU / 2 : Nat) : Int))
    let uhi := min uhi0 ((maxU / 2 : Nat) : Int)
    for ui in [0:(uhi - ulo + 1).toNat] do
      let u : Int := ulo + ui
      let base := rotJ cw c.l c.m u 1
      let (vlo0, vhi0) := rotRange base c.l c.m 0 (n + margin) s
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

/-- A polynomial pair by collision search, size and root optimization, ranked
by Murphy's `E` with bounds `2^lpbA`, `2^lpbR` over `area`. -/
def selectCollision (n d P nq incr admax keep : Nat) (U V : Nat) (lpbR lpbA : Nat) (area : Float)
    (threads : Nat := 1) : Option Selection := Id.run do
  let t := max 1 threads
  let count := (admax + incr - 1) / incr
  let per := (count + t - 1) / t
  let tasks := (List.range t).map fun i =>
    Task.spawn fun _ => collisionSearch n d P nq incr (1 + i * per * incr)
      (min (admax + 1) (1 + (i + 1) * per * incr)) keep
  let mut cands : Array CCand := tasks.foldl (fun acc tk => acc ++ tk.get) #[]
  cands := (cands.qsort fun a b => a.score < b.score).extract 0 keep
  if cands.isEmpty then return none
  let rot := cands.toList.map fun c => Task.spawn fun _ => rootOpt c (fc 1) U V 32
  let tbl := dickmanTable
  let bf := Float.exp2 lpbA.toFloat
  let bg := Float.exp2 lpbR.toFloat
  let mut best : Option (Float × CCand) := none
  for tk in rot do
    let c := tk.get
    if c.m ≤ 0 || c.cs[d]! ≤ 0 then continue
    let s := (logNorm c.cs).2
    let e := murphyE tbl c.cs c.l c.m s bf bg area
    match best with
    | none => best := some (e, c)
    | some (e0, _) => if e > e0 then best := some (e, c)
  match best with
  | none => return none
  | some (_, c) => return some { coeffs := c.cs, m := c.m.toNat, y1 := c.l }

end PrimeFactorLean.NFS.PolySelect
