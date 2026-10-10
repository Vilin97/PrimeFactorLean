import PrimeFactorLean.QS
import PrimeFactorLean.Lanczos

/-!
# A fast self-initializing quadratic sieve

The same mathematics as `QS.siqsBatch` (Alford–Pomerance, Peralta, Contini),
re-engineered for speed:

* Roots, primes and Gray-code deltas live in `Array UInt32` (unboxed scalars),
  and the sieve is a `ByteArray`; the hot loops are tail-recursive functions on
  `USize` positions whose bounds are discharged once per call, so the compiled
  code has no `Nat` arithmetic and no allocation per update.
* Every polynomial switch is one fused pass over the factor base: both roots
  move by `±δ (mod p)` and the prime is sieved over the whole interval
  (`2M ≤ 2^19` bytes stays in the L2 cache), so primes beyond the interval cost
  one comparison per root.
* The sieve starts at a bias such that a position is a candidate exactly when
  its byte reaches `128`; candidate blocks are found by an `OR` fold over the
  bytes, which the C compiler vectorizes.
* Trial division tests divisibility by comparing the candidate's position with
  each prime's two roots, so the large residue is divided only by primes that
  divide it.
* Optionally, cofactors below `dlpBound` are split into two large primes
  (double large prime variation); partial relations become cycles of the
  large-prime graph exactly as in `QS.collect`.

Relations are `Squares.Relation`s (checked when created), so the proved
pipeline `Relation.toSquares`/`SquareCongruence.factor` is unchanged and the
result is a `ProperFactor n`. Everything in this file is untrusted search code.
-/

namespace PrimeFactorLean.SIQS

open Arith Squares QS

/-! ## Sieve kernels -/

theorem size_uset (s : ByteArray) (j : USize) (v : UInt8) (h : j.toNat < s.size) :
    (s.uset j v h).size = s.size := by
  cases s; simp [ByteArray.uset, ByteArray.size]

theorem numBits_ge : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide

theorem toNat_add_small (j p : USize) (hj : j.toNat < 2 ^ 31) (hp : p.toNat < 2 ^ 31) :
    (j + p).toNat = j.toNat + p.toNat := by
  rw [USize.toNat_add]
  apply Nat.mod_eq_of_lt
  have := numBits_ge
  omega

/-! Per-prime data is kept compact so that a thread's working set (the sieve plus
one pass over the factor base) fits in its L2 cache: primes and Gray-code
deltas are little-endian 32-bit words in `ByteArray`s, and the two roots of a
prime are packed into one machine-word `Nat` (`r₁ + 2³² r₂`, both `< 2³¹`). -/

/-- The 32-bit little-endian word `i` of `b`. -/
@[inline] def u32 (b : ByteArray) (i : Nat) (h : 4 * i + 4 ≤ b.size) : UInt32 :=
  (b.get (4 * i) (by omega)).toUInt32 |||
  ((b.get (4 * i + 1) (by omega)).toUInt32 <<< 8) |||
  ((b.get (4 * i + 2) (by omega)).toUInt32 <<< 16) |||
  ((b.get (4 * i + 3) (by omega)).toUInt32 <<< 24)

/-- Little-endian 32-bit words. -/
def packU32 (xs : Array UInt32) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (4 * xs.size)
  for x in xs do
    b := (((b.push x.toUInt8).push (x >>> 8).toUInt8).push (x >>> 16).toUInt8).push
      (x >>> 24).toUInt8
  return b

/-- Checked read of word `i` (`0` out of range). -/
def u32Get (b : ByteArray) (i : Nat) : UInt32 :=
  if h : 4 * i + 4 ≤ b.size then u32 b i h else 0

@[inline] def packRoots (a b : UInt32) : Nat := (a.toUInt64 ||| (b.toUInt64 <<< 32)).toNat
@[inline] def root1 (w : Nat) : UInt32 := w.toUInt64.toUInt32
@[inline] def root2 (w : Nat) : UInt32 := (w.toUInt64 >>> 32).toUInt32

/-- `r ± δ (mod p)` for residues `r, δ < p < 2^31`, without branches (the
comparison is random, so a branch would be mispredicted half of the time).
The masks are written `-b` rather than `0 - b`: Lean 4.24's compiler rewrites
`0 - x` to `x` (for `Nat` and the fixed-width types alike). -/
@[inline] def moveRoot (add : Bool) (r d p : UInt32) : UInt32 :=
  if add then
    let x := r + d
    x - (p &&& -(decide (x ≥ p)).toUInt32)
  else
    let x := r - d
    x + (p &&& -(decide (r < d)).toUInt32)

/-! The sieve buffer has one extra byte at index `len` (the interval length):
positions beyond the interval are clamped onto it, so every update is
unconditional and branch-free. -/

theorem uget_bound {s : ByteArray} {k len : USize} (hk : k ≤ len) (h : len.toNat < s.size) :
    k.toNat < s.size := by
  have := USize.le_iff_toNat_le.mp hk
  omega

/-- Add `lg` at `min a len` (the trash byte when `a` is outside the interval). -/
@[inline] def hitClamp (s : ByteArray) (len a : USize) (lg : UInt8) (h : len.toNat < s.size) :
    ByteArray :=
  let k := if a ≤ len then a else len
  have hk : k ≤ len := by
    show (if a ≤ len then a else len) ≤ len
    split
    · assumption
    · exact USize.le_refl len
  s.uset k (s.uget k (uget_bound hk h) + lg) (uget_bound hk h)

theorem size_hitClamp (s : ByteArray) (len a : USize) (lg : UInt8) (h : len.toNat < s.size) :
    (hitClamp s len a lg h).size = s.size := by
  simp [hitClamp, size_uset]

/-- Exactly `count` updates at `j, j + p, …`, each clamped onto the trash byte:
for a run of primes with the same `count = ⌈len / p⌉` the loop exit is
predictable. -/
def strideN (s : ByteArray) (len j p : USize) (lg : UInt8) (h : len.toNat < s.size) :
    Nat → ByteArray
  | 0 => s
  | count + 1 =>
    strideN (hitClamp s len j lg h) len (j + p) p lg (by rw [size_hitClamp]; exact h) count

theorem size_strideN (s : ByteArray) (len j p : USize) (lg : UInt8) (h : len.toNat < s.size)
    (c : Nat) : (strideN s len j p lg h c).size = s.size := by
  induction c generalizing s j with
  | zero => rfl
  | succ c ih => simp only [strideN]; rw [ih, size_hitClamp]

/-- Sieve the primes with index in `[i, stop)` (below the interval length) at
their current roots: the first polynomial of an `A`. -/
def sieveFrom (primeB : ByteArray) (roots : Array Nat) (logp : ByteArray) (s : ByteArray)
    (len : USize) (hs : len.toNat < s.size) (i stop : Nat) (h1 : 4 * stop ≤ primeB.size)
    (h2 : stop ≤ roots.size) (h3 : stop ≤ logp.size) : ByteArray :=
  if hi : i < stop then
    let p := u32 primeB i (by omega)
    let w := roots[i]
    let lg := logp.get i (by omega)
    let count := ((len.toUInt32 + p - 1) / p).toNat
    let t := strideN s len (root1 w).toUSize p.toUSize lg hs count
    let t := strideN t len (root2 w).toUSize p.toUSize lg (by rw [size_strideN]; exact hs) count
    sieveFrom primeB roots logp t len (by rw [size_strideN, size_strideN]; exact hs) (i + 1) stop
      h1 h2 h3
  else s
termination_by stop - i

/-- Sieve primes beyond the interval at their current roots (one clamped update
per root). -/
def sieveLarge (roots : Array Nat) (logp : ByteArray) (s : ByteArray) (len : USize)
    (hs : len.toNat < s.size) (i stop : Nat) (h2 : stop ≤ roots.size) (h3 : stop ≤ logp.size) :
    ByteArray :=
  if hi : i < stop then
    let w := roots[i]
    let lg := logp.get i (by omega)
    let t := hitClamp s len (root1 w).toUSize lg hs
    let t := hitClamp t len (root2 w).toUSize lg (by rw [size_hitClamp]; exact hs)
    sieveLarge roots logp t len (by rw [size_hitClamp, size_hitClamp]; exact hs) (i + 1) stop h2 h3
  else s
termination_by stop - i

/-- Gray-code switch for the primes in `[i, stop)` below the interval length:
both roots move by `±δ`, then the prime is sieved at the new roots. -/
def switchMedium (primeB deltaB logp : ByteArray) (add : Bool) (roots : Array Nat)
    (s : ByteArray) (len : USize) (hs : len.toNat < s.size) (i stop : Nat)
    (h1 : 4 * stop ≤ primeB.size) (h2 : 4 * stop ≤ deltaB.size) (h3 : stop ≤ logp.size)
    (h4 : stop ≤ roots.size) : Array Nat × ByteArray :=
  if hi : i < stop then
    let p := u32 primeB i (by omega)
    let d := u32 deltaB i (by omega)
    let w := roots[i]
    let a := moveRoot add (root1 w) d p
    let b := moveRoot add (root2 w) d p
    let lg := logp.get i (by omega)
    let count := ((len.toUInt32 + p - 1) / p).toNat
    let t := strideN s len a.toUSize p.toUSize lg hs count
    let t := strideN t len b.toUSize p.toUSize lg (by rw [size_strideN]; exact hs) count
    let roots' := roots.set i (packRoots a b) (by omega)
    switchMedium primeB deltaB logp add roots' t len
      (by rw [size_strideN, size_strideN]; exact hs) (i + 1) stop h1 h2 h3 (by simp [roots']; omega)
  else (roots, s)
termination_by stop - i

/-- Gray-code switch for primes beyond the interval: one clamped update per root. -/
def switchLarge (primeB deltaB logp : ByteArray) (add : Bool) (roots : Array Nat)
    (s : ByteArray) (len : USize) (hs : len.toNat < s.size) (i stop : Nat)
    (h1 : 4 * stop ≤ primeB.size) (h2 : 4 * stop ≤ deltaB.size) (h3 : stop ≤ logp.size)
    (h4 : stop ≤ roots.size) : Array Nat × ByteArray :=
  if hi : i < stop then
    let p := u32 primeB i (by omega)
    let d := u32 deltaB i (by omega)
    let w := roots[i]
    let a := moveRoot add (root1 w) d p
    let b := moveRoot add (root2 w) d p
    let lg := logp.get i (by omega)
    let t := hitClamp s len a.toUSize lg hs
    let t := hitClamp t len b.toUSize lg (by rw [size_hitClamp]; exact hs)
    let roots' := roots.set i (packRoots a b) (by omega)
    switchLarge primeB deltaB logp add roots' t len
      (by rw [size_hitClamp, size_hitClamp]; exact hs) (i + 1) stop h1 h2 h3 (by simp [roots']; omega)
  else (roots, s)
termination_by stop - i

/-- Positions whose byte reached `128` (bit 7 set). Blocks are first tested by
an `OR` fold, which compiles to vectorized code. -/
def scan (s : ByteArray) (len : Nat) : Array Nat := Id.run do
  let block := 4096
  let size := min len s.size
  let mut out : Array Nat := #[]
  let mut b := 0
  while b < size do
    let e := min size (b + block)
    if s.foldl (fun acc x => acc ||| x) 0 b e ≥ 128 then
      for j in [b:e] do
        if s.get! j ≥ 128 then out := out.push j
    b := e
  return out

/-! ## Context -/

structure Params where
  fbSize : Nat
  /-- Half width: positions `j ∈ [0, 2M)` stand for `x = j - M`. -/
  M : Nat
  lpMult : Nat
  /-- Double large primes: cofactors below `lpBound² / dlpDiv` are split
  (`0` disables the variation). -/
  dlpDiv : Nat := 0
  /-- Primes with index below `spv` are not sieved (small prime variation). -/
  spv : Nat := 20
  /-- Threshold slack, in bits. -/
  slack : Nat := 0
  extra : Nat := 64
  deriving Repr, Inhabited

/-- `(digits, factor-base size, M, large-prime multiplier, dlpDiv)`, measured with
16 threads (double large primes from 60 digits: cofactors below `lp²/16`). -/
def paramTable : List (Nat × Nat × Nat × Nat × Nat) :=
  [(20, 60, 2048, 20, 0), (25, 100, 4096, 30, 0), (30, 160, 8192, 30, 0),
   (35, 250, 16384, 40, 0), (40, 400, 16384, 50, 0), (45, 600, 32768, 50, 0),
   (50, 1000, 32768, 60, 0), (55, 1600, 65536, 70, 0), (60, 2400, 65536, 80, 16),
   (65, 3500, 65536, 80, 16), (70, 5500, 98304, 90, 16), (75, 9000, 131072, 100, 16),
   (80, 16000, 196608, 100, 16), (85, 22000, 196608, 110, 16), (90, 30000, 196608, 120, 16),
   (95, 40000, 262144, 120, 16), (100, 50000, 262144, 150, 16), (110, 70000, 262144, 150, 16)]

def chooseParams (digits : Nat) : Params :=
  let e := (paramTable.find? fun e => digits ≤ e.1).getD
    (paramTable.getLast?.getD (110, 70000, 262144, 150, 0))
  { fbSize := e.2.1, M := e.2.2.1, lpMult := e.2.2.2.1, dlpDiv := e.2.2.2.2 }

/-- `p⁻¹ mod 2^32` for odd `p` (Newton's iteration; `p = 2` gives garbage, unused). -/
def inv32 (p : UInt32) : UInt32 := Id.run do
  let mut x : UInt32 := p
  for _ in [0:5] do x := x * (2 - p * x)
  return x

structure Ctx where
  n : Nat
  k : Nat
  N : Nat
  fb : Array Nat
  prime : Array UInt32
  /-- The primes as little-endian 32-bit words (for the sieve kernels). -/
  primeB : ByteArray
  sqrtN : Array UInt32
  logp : ByteArray
  M : Nat
  /-- Sieve length `2M`. -/
  size : Nat
  mmod : Array UInt32
  /-- `p⁻¹ mod 2^32` and `⌊(2^32 - 1)/p⌋`: `p ∣ x` iff `x · p⁻¹ ≤ lim (mod 2^32)`. -/
  pinv : Array UInt32
  lim : Array UInt32
  spv : Nat
  /-- First index whose prime exceeds the interval (`p ≥ 2M`). -/
  medEnd : Nat
  /-- First index resieved (smaller primes are tested per candidate). -/
  resieveStart : Nat
  bias : UInt8
  lpBound : Nat
  dlpBound : Nat
  template : ByteArray

/-- Factor base, logarithms and threshold; `.inr p` reports a small factor. -/
def mkCtx (n : Nat) (params : Params) : Ctx ⊕ Nat := Id.run do
  let primes := primesUpTo (max 1000 (params.fbSize * 30))
  let k := chooseMultiplier n primes
  let N := k * n
  let (fb, roots, found) := buildFactorBase n N params.fbSize primes
  if let some p := found then return .inr p
  let M := params.M
  let size := 2 * M
  let pmax := fb[fb.size - 1]!
  let lpBound := pmax * params.lpMult
  let dlpBound := if params.dlpDiv == 0 then 0 else lpBound * lpBound / params.dlpDiv
  -- Threshold: log2 of the typical |v(x)| minus the large-prime allowance and
  -- the expected contribution of the unsieved small primes.
  let spv := min params.spv (fb.size - 1)
  let mut small : Float := 0
  for i in [1:spv] do
    let p := fb[i]!.toFloat
    small := small + 2.0 * Float.log2 p / (p - 1.0)
  let target := Float.log2 M.toFloat + (N.log2.toFloat + 1.0) / 2.0 - 0.5
  let allowance := if dlpBound > 0 then Float.log2 dlpBound.toFloat else Float.log2 lpBound.toFloat
  let thr := target - allowance - small - params.slack.toFloat
  -- Scale logarithms so that the threshold fits below 128.
  let scale := if thr > 110.0 then thr / 110.0 else 1.0
  let logp := ByteArray.mk (fb.map fun p => (Float.round (Float.log2 p.toFloat / scale)).toUInt8)
  let t := thr / scale
  let t := if t < 10.0 then 10.0 else t
  let bias := (128.0 - t).toUInt8
  -- one extra (trash) byte for clamped updates
  let template := ByteArray.mk (Array.replicate (size + 1) bias)
  let mut medEnd := spv
  while medEnd < fb.size && fb[medEnd]! < size do medEnd := medEnd + 1
  let mut resieveStart := spv
  while resieveStart < medEnd && fb[resieveStart]! < 4096 do resieveStart := resieveStart + 1
  let prime := fb.map (·.toUInt32)
  return .inl { n := n, k := k, N := N, fb := fb, prime := prime, primeB := packU32 prime,
                sqrtN := roots.map (·.toUInt32), logp := logp, M := M, size := size,
                mmod := fb.map fun p => (M % p).toUInt32, pinv := prime.map inv32,
                lim := prime.map fun p => if p == 0 then 0 else (0xFFFFFFFF : UInt32) / p,
                spv := spv, medEnd := medEnd, resieveStart := resieveStart, bias := bias,
                lpBound := lpBound, dlpBound := dlpBound, template := template }

/-! ## Polynomials -/

/-- Extended Euclid on machine words with signed coefficients: invariant
`r₀ ≡ s₀ a`, `r₁ ≡ s₁ a (mod p)`, `|s| ≤ p`. -/
def invLoop (r0 r1 : UInt64) (s0 s1 : Int64) : Nat → Int64
  | 0 => 0
  | fuel + 1 =>
    if r1 == 0 then (if r0 == 1 then s0 else 0)
    else
      let q := r0 / r1
      invLoop r1 (r0 - q * r1) s1 (s0 - q.toInt64 * s1) fuel

/-- `a⁻¹ mod p` for `0 < a < p < 2^32` (`0` if `a` is not invertible). -/
def invModU (a p : UInt64) : UInt64 :=
  let s := invLoop p a 0 1 64
  if s < 0 then (s + p.toInt64).toUInt64 else s.toUInt64

/-- Choose the factors of `A`: `s - 1` random factor-base primes near
`q = target^{1/s}`, then the prime closest to the remaining quotient, so that
`A` is within a fraction of a percent of `target = √(2N)/M` (a larger `A`
inflates `|v(x)|` and lowers the yield). Retries with fresh random choices. -/
def chooseQs (fb : Array Nat) (N seed target : Nat) : Option (Array Nat) := Id.run do
  let bits := target.log2
  let qbits := if bits > 100 then 11 else if bits > 60 then 10 else if bits > 36 then 8
    else if bits > 18 then 6 else 4
  let s := max 1 ((bits + qbits / 2) / qbits)
  let q := 2 ^ (bits / s)
  -- index window of primes in [0.8 q, 1.25 q] (widened for small bases)
  let mut lo := 1
  while lo < fb.size && fb[lo]! * 5 < q * 4 do lo := lo + 1
  let mut hi := lo
  while hi < fb.size && fb[hi]! * 4 < q * 5 do hi := hi + 1
  while hi - lo < 2 * s + 4 && (lo > 1 || hi < fb.size) do
    if lo > 1 then lo := lo - 1
    if hi < fb.size then hi := hi + 1
  if hi ≤ lo + s then return none
  let mut rng := seed * 2654435761 + 12345
  for _ in [0:50] do
    let mut chosen : Array Nat := #[]
    let mut prod := 1
    let mut fuel := 100 * s + 100
    while chosen.size + 1 < s && fuel > 0 do
      fuel := fuel - 1
      rng := nextRand rng
      let i := lo + rng % (hi - lo)
      if chosen.contains i || N % fb[i]! == 0 then continue
      chosen := chosen.push i
      prod := prod * fb[i]!
    if chosen.size + 1 < s then continue
    let want := target / max 1 prod
    if want < 3 then continue
    -- closest admissible prime to `want` (binary search, then a local scan)
    let mut a := 1
    let mut b := fb.size
    while a + 1 < b do
      let m := (a + b) / 2
      if fb[m]! ≤ want then a := m else b := m
    let mut best := 0
    let mut bestDist := want + 1
    for i in [a - min a 8:min fb.size (a + 9)] do
      if i == 0 || chosen.contains i || N % fb[i]! == 0 then continue
      let p := fb[i]!
      let d := if p ≤ want then want - p else p - want
      if d < bestDist then
        best := i
        bestDist := d
    if best == 0 then continue
    return some (chosen.push best)
  return none

/-- One `A = q₁ ⋯ q_s` with its Gray-code data. -/
structure APoly where
  A : Nat
  qs : Array Nat
  Bl : Array Nat
  /-- Row `l`: `δ_l = 2 B_l A⁻¹ mod p` for every factor-base prime (32-bit words). -/
  delta : Array ByteArray
  /-- Packed roots of the first polynomial `B = ∑ B_l`. -/
  roots : Array Nat
  /-- Logarithms with the primes of `A` (and those of `kN`) zeroed. -/
  logp : ByteArray

/-- Build an `A`, the `B_l`, the deltas and the first roots. -/
def mkAPoly (ctx : Ctx) (seed : Nat) : Option APoly := Id.run do
  let target := isqrt (2 * ctx.N) / ctx.M
  let some qs := chooseQs ctx.fb ctx.N seed target | return none
  let A := qs.foldl (fun acc i => acc * ctx.fb[i]!) 1
  let mut Bl : Array Nat := #[]
  for l in [0:qs.size] do
    let q := ctx.fb[qs[l]!]!
    let t := ctx.sqrtN[qs[l]!]!.toNat
    let aq := A / q
    match Arith.invMod (aq % q) q with
    | none => return none
    | some inv =>
      let mut gamma := t * inv % q
      if 2 * gamma > q then gamma := q - gamma
      Bl := Bl.push (aq * gamma)
  let B := Bl.foldl (· + ·) 0
  if (B * B) % A != ctx.N % A then return none
  let F := ctx.fb.size
  let mut delta : Array (Array UInt32) := Array.replicate qs.size (Array.replicate F 0)
  let mut roots : Array Nat := Array.replicate F 0
  let mut logp := ctx.logp
  for i in [1:F] do
    let p := ctx.fb[i]!
    let pu := p.toUInt64
    let am := (A % p).toUInt64
    if am == 0 || ctx.sqrtN[i]! == 0 then
      -- primes of `A` and of `kN`: not sieved (trial divided directly)
      logp := logp.set! i 0
      continue
    let ainv := invModU am pu
    let t := ctx.sqrtN[i]!.toUInt64
    let bm := (B % p).toUInt64
    let mm := ctx.mmod[i]!.toUInt64
    -- positions j = x + M of the roots x = A⁻¹ (±t - B)
    let x1 := ainv * ((t + pu - bm) % pu) % pu
    let x2 := ainv * ((pu - t + pu - bm) % pu) % pu
    roots := roots.set! i (packRoots ((x1 + mm) % pu).toUInt32 ((x2 + mm) % pu).toUInt32)
    for l in [0:qs.size] do
      let blm := (Bl[l]! % p).toUInt64
      delta := delta.modify l fun row => row.set! i ((2 * blm % pu) * ainv % pu).toUInt32
  logp := logp.set! 0 0
  return some { A := A, qs := qs, Bl := Bl, delta := delta.map packU32, roots := roots,
                logp := logp }

/-! ## Cofactors below `2^50`

Double-large-prime cofactors fit in 50 bits, where `a · b mod m` can be computed
with machine words: the quotient is estimated in floating point (53-bit
mantissa, so it is off by at most one) and the remainder is corrected in
wrapping 64-bit arithmetic. -/

/-- `a · b mod m` for `a, b < m < 2^52`, with `minv ≈ 1/m`: `a`, `b` are exact
doubles, the product and the quotient carry relative errors of a few `2^-53`,
so the estimated quotient is off by at most two, which the corrections absorb
(the true remainder lies in `(-2m, 3m)`, well inside 64 bits). -/
@[inline] def mulmod50 (a b m : UInt64) (minv : Float) : UInt64 :=
  let q := ((a.toFloat * b.toFloat) * minv).toUInt64
  let r := a * b - q * m
  -- the true remainder lies in (-2m, 3m); the sign is the top bit. (A repeated
  -- 64-bit literal here would trigger a Lean 4.24 code-generation bug.)
  let r := if r >>> 63 != 0 then r + m else r
  let r := if r >>> 63 != 0 then r + m else r
  let r := if r ≥ m then r - m else r
  if r ≥ m then r - m else r

/-- `b^e mod m` for `b < m < 2^50`. -/
def powmod50 (b e m : UInt64) (mf : Float) : UInt64 := Id.run do
  -- `mf` is `1/m`
  let mut result : UInt64 := 1
  let mut base := b
  let mut e := e
  while e != 0 do
    if e &&& 1 == 1 then result := mulmod50 result base m mf
    base := mulmod50 base base m mf
    e := e >>> 1
  return result

/-- Strong probable prime to base 2, for odd `3 < m < 2^50` (a screen only:
large-prime classification never affects correctness). -/
def sprp2 (m : UInt64) : Bool := Id.run do
  let mf := 1.0 / m.toFloat
  let mut d := m - 1
  let mut s := 0
  while d &&& 1 == 0 do
    d := d >>> 1
    s := s + 1
  let mut x := powmod50 2 d m mf
  if x == 1 || x == m - 1 then return true
  for _ in [1:s] do
    x := mulmod50 x x m mf
    if x == m - 1 then return true
  return false

/-- Binary gcd of machine words (no divisions). -/
def gcd64 (a b : UInt64) : UInt64 := Id.run do
  if a == 0 then return b
  if b == 0 then return a
  let mut a := a
  let mut b := b
  let mut shift : UInt64 := 0
  while (a ||| b) &&& 1 == 0 do
    a := a >>> 1
    b := b >>> 1
    shift := shift + 1
  while a &&& 1 == 0 do a := a >>> 1
  let mut fuel := 400
  while b != 0 && fuel > 0 do
    fuel := fuel - 1
    while b &&& 1 == 0 do b := b >>> 1
    if a > b then
      let t := a
      a := b
      b := t
    b := b - a
  return a <<< shift

/-- One rho step `y ↦ y² + c (mod m)`. -/
@[inline] def rhoF (y c m : UInt64) (mf : Float) : UInt64 :=
  let z := mulmod50 y y m mf + c
  if z ≥ m then z - m else z

/-- `k` rho steps. -/
def rhoIter (y c m : UInt64) (mf : Float) : Nat → UInt64
  | 0 => y
  | k + 1 => rhoIter (rhoF y c m mf) c m mf k

/-- `k` rho steps from `y`, multiplying `q` by `|x - y|` after each. -/
def rhoBatch (x y q c m : UInt64) (mf : Float) : Nat → UInt64 × UInt64
  | 0 => (y, q)
  | k + 1 =>
    let y := rhoF y c m mf
    let d := if x ≥ y then x - y else y - x
    rhoBatch x y (mulmod50 q d m mf) c m mf k

/-- Single steps from `ys` until `gcd(|x - y|, m) ≠ 1` (after a batch overshot). -/
def rhoSingle (x ys c m : UInt64) (mf : Float) : Nat → UInt64
  | 0 => 1
  | k + 1 =>
    let ys := rhoF ys c m mf
    let g := gcd64 (if x ≥ ys then x - ys else ys - x) m
    if g != 1 then g else rhoSingle x ys c m mf k

/-- Brent's variant of Pollard's rho for `m < 2^50`, with the gcd batched over
`256` steps; `0` if no factor was found within about `iters` steps. -/
def rho50 (m c iters : UInt64) : UInt64 := Id.run do
  let mf := 1.0 / m.toFloat
  let mut y : UInt64 := 2
  let mut r : UInt64 := 1
  let mut q : UInt64 := 1
  let mut x : UInt64 := 2
  let mut ys : UInt64 := 2
  let mut g : UInt64 := 1
  let mut steps : UInt64 := 0
  while g == 1 && steps < iters do
    x := y
    y := rhoIter y c m mf r.toNat
    let mut k : UInt64 := 0
    while k < r && g == 1 do
      ys := y
      let lim := min 256 (r - k)
      let (y', q') := rhoBatch x y q c m mf lim.toNat
      y := y'
      q := q'
      g := gcd64 q m
      k := k + lim
    steps := steps + r
    r := 2 * r
  if g == m then g := rhoSingle x ys c m mf 100000
  return if g == m || g == 1 then 0 else g

/-- SQUFOF as a last resort (kept in a single call site so that it is only
evaluated when needed). -/
@[noinline] def squfofFactor (u : Nat) : Nat := ((SQUFOF.race u).map (·.val)).getD 0

/-- A factor of a composite `u` (`0` if none was found): rho for `u < 2^50`. -/
def cofactorFactor (u : Nat) : Nat :=
  let g := if u < 2 ^ 52 then
      let g := rho50 u.toUInt64 1 200000
      if g != 0 then g else rho50 u.toUInt64 3 200000
    else 0
  if g != 0 then g.toNat else squfofFactor u

/-- Split a double-large-prime cofactor `u` into two primes below `lp` (a base-2
probable-prime screen first). -/
def splitCofactor (u lp : Nat) : Option (Nat × Nat) :=
  if u < 2 ^ 52 && u % 2 == 1 && sprp2 u.toUInt64 then none
  else
    let d := cofactorFactor u
    if d ≤ 1 then none else
    let a := min d (u / d)
    let b := max d (u / d)
    if a < lp && b < lp && a * b == u && a != b then some (a, b) else none

/-! ## Trial division of candidates -/

/-- Exponent of `p` in `u` and the cofactor. -/
@[inline] def strip (u p : Nat) : Nat × Nat := QS.stripPrime u p

/-- `p ∣ (j - r)` for a root `r < p`, by multiplication with `p⁻¹ (mod 2^32)`
(Granlund–Montgomery); `j < r` cannot be a hit since `0 < r - j < p`. -/
@[inline] def rootHit (j r q l : UInt32) : Bool := j ≥ r && (j - r) * q ≤ l

/-- Divide `u` by every factor-base prime in `[i, stop)` that divides `v(x)` at
position `j`: primes of `A` and `kN` (zero logarithm) are tested on `u`
directly, the others by comparing `j` with their roots. -/
def tdivFrom (ctx : Ctx) (logp : ByteArray) (roots : Array Nat) (j : UInt32)
    (i stop : Nat) (u : Nat) (exps : List (Nat × Nat)) : Nat × List (Nat × Nat) :=
  if i < stop then
    let hit :=
      if logp.get! i == 0 then u % ctx.fb[i]! == 0
      else
        let q := ctx.pinv[i]!
        let l := ctx.lim[i]!
        let w := roots[i]!
        rootHit j (root1 w) q l || rootHit j (root2 w) q l
    if hit then
      let (u', e) := strip u ctx.fb[i]!
      tdivFrom ctx logp roots j (i + 1) stop u' (if e > 0 then (i, e) :: exps else exps)
    else tdivFrom ctx logp roots j (i + 1) stop u exps
  else (u, exps)
termination_by stop - i

/-- The large primes (index in `[i, stop)`, beyond the interval) whose current
roots land on a candidate (a byte `≥ 128`): one read-only pass for all the
candidates of a polynomial. Returns `(position, index)` pairs. -/
def largeHits (roots : Array Nat) (buf : ByteArray) (len i stop : Nat)
    (acc : Array (Nat × Nat)) : Array (Nat × Nat) :=
  if i < stop then
    let w := roots[i]!
    let a := (root1 w).toNat
    let b := (root2 w).toNat
    let acc := if a < len && buf.get! a ≥ 128 then acc.push (a, i) else acc
    let acc := if b < len && buf.get! b ≥ 128 then acc.push (b, i) else acc
    largeHits roots buf len (i + 1) stop acc
  else acc
termination_by stop - i

/-- Divide `u` by the large primes listed for position `j`. -/
def divideLarge (fb : Array Nat) (hits : Array (Nat × Nat)) (j : Nat) (u : Nat)
    (exps : List (Nat × Nat)) : Nat × List (Nat × Nat) := Id.run do
  let mut u := u
  let mut exps := exps
  for (pos, i) in hits do
    if pos == j then
      let (u', e) := strip u fb[i]!
      if e > 0 then
        u := u'
        exps := (i, e) :: exps
  return (u, exps)

/-- Factor `v(x)` for the candidate at position `j` and build a relation. -/
def candidate (ctx : Ctx) (ap : APoly) (B : Int) (C : Int) (roots : Array Nat)
    (hits : Array (Nat × Nat)) (j : Nat) : Option (Found ctx.n ctx.fb) := Id.run do
  let x : Int := (j : Int) - (ctx.M : Int)
  let A : Int := ap.A
  let v : Int := (A * x + 2 * B) * x + C
  if v == 0 then return none
  let (u, e2) := strip v.natAbs 2
  let exps0 : List (Nat × Nat) := ap.qs.toList.map fun i => (i, 1)
  let exps0 := if e2 > 0 then (0, e2) :: exps0 else exps0
  let (u, exps) := tdivFrom ctx ap.logp roots j.toUInt32 1 ctx.medEnd u exps0
  let (u, exps) := divideLarge ctx.fb hits j u exps
  -- cofactor: full, one large prime, or two
  let lp : Option (Nat × Nat) :=
    if u == 1 then some (1, 1)
    else if u < ctx.lpBound then some (1, u)
    else if ctx.dlpBound > 0 && u < ctx.dlpBound && !isProbablePrime u then
      match SQUFOF.split u with
      | some d =>
        let a := min d.val (u / d.val)
        let b := max d.val (u / d.val)
        if a < ctx.lpBound && b < ctx.lpBound && a * b == u && a != b then some (a, b) else none
      | none => none
    else none
  let some (l1, l2) := lp | return none
  let X := ((A * x + B) % (ctx.n : Int)).toNat
  match Relation.mk? ctx.n ctx.fb X 1 u (decide (v < 0)) exps with
  | some r => return some ⟨r, l1, l2⟩
  | none => return none

/-! ## Resieving

When a polynomial has many candidates, their factor-base primes are found in one
pass that walks the same arithmetic progressions as the sieve: the bytes of the
candidates are relabelled `128 + c` (`c` the candidate's index; `255` beyond 126
candidates), so a step that lands on a labelled byte records its prime for that
candidate. -/

/-- Relabel the candidates; the trash byte is cleared so it never looks like one. -/
def labelCandidates (buf : ByteArray) (cands : Array Nat) (len : Nat) : ByteArray := Id.run do
  let mut b := buf.set! len 0
  for ci in [0:cands.size] do
    b := b.set! cands[ci]! (if ci < 127 then (128 + ci).toUInt8 else 255)
  return b

/-- Record `i` for every labelled candidate at `j, j + p, …` (`count` clamped steps). -/
def resieveN (buf : ByteArray) (len j p : USize) (i : Nat) (h : len.toNat < buf.size)
    (acc : Array (Array Nat)) : Nat → Array (Array Nat)
  | 0 => acc
  | count + 1 =>
    let k := if j ≤ len then j else len
    have hk : k ≤ len := by
      show (if j ≤ len then j else len) ≤ len
      split
      · assumption
      · exact USize.le_refl len
    let b := buf.uget k (uget_bound hk h)
    let acc := if b ≥ 128 && b != 255 then acc.modify (b - 128).toNat (·.push i) else acc
    resieveN buf len (j + p) p i h acc count

/-- Resieve the primes with index in `[i, stop)` (below the interval length). -/
def resieveFrom (primeB : ByteArray) (roots : Array Nat) (buf : ByteArray) (len : USize)
    (h : len.toNat < buf.size) (i stop : Nat) (h1 : 4 * stop ≤ primeB.size)
    (h2 : stop ≤ roots.size) (acc : Array (Array Nat)) : Array (Array Nat) :=
  if hi : i < stop then
    let p := u32 primeB i (by omega)
    let w := roots[i]
    let count := ((len.toUInt32 + p - 1) / p).toNat
    let acc := resieveN buf len (root1 w).toUSize p.toUSize i h acc count
    let acc := resieveN buf len (root2 w).toUSize p.toUSize i h acc count
    resieveFrom primeB roots buf len h (i + 1) stop h1 h2 acc
  else acc
termination_by stop - i

/-- Primes beyond the interval whose roots land on a labelled candidate. -/
def labelLarge (roots : Array Nat) (buf : ByteArray) (len i stop : Nat)
    (acc : Array (Array Nat)) : Array (Array Nat) :=
  if i < stop then
    let w := roots[i]!
    let a := (root1 w).toNat
    let b := (root2 w).toNat
    let ba := if a < len then buf.get! a else 0
    let bb := if b < len then buf.get! b else 0
    let acc := if ba ≥ 128 && ba != 255 then acc.modify (ba - 128).toNat (·.push i) else acc
    let acc := if bb ≥ 128 && bb != 255 then acc.modify (bb - 128).toNat (·.push i) else acc
    labelLarge roots buf len (i + 1) stop acc
  else acc
termination_by stop - i

/-- Factor `v(x)` at position `j`: small primes (index `< smallEnd`, including
those of `A` and `kN`) are tested here, the other factor-base primes dividing
`v(x)` are given in `listed`. -/
def factorCandidate (ctx : Ctx) (ap : APoly) (B C : Int) (roots : Array Nat) (smallEnd : Nat)
    (listed : Array Nat) (j : Nat) : Option (Found ctx.n ctx.fb) := Id.run do
  let x : Int := (j : Int) - (ctx.M : Int)
  let A : Int := ap.A
  let v : Int := (A * x + 2 * B) * x + C
  if v == 0 then return none
  let (u, e2) := strip v.natAbs 2
  let exps0 : List (Nat × Nat) := ap.qs.toList.map fun i => (i, 1)
  let exps0 := if e2 > 0 then (0, e2) :: exps0 else exps0
  let (u, exps) := tdivFrom ctx ap.logp roots j.toUInt32 1 smallEnd u exps0
  let mut u := u
  let mut exps := exps
  for i in listed do
    let (u', e) := strip u ctx.fb[i]!
    if e > 0 then
      u := u'
      exps := (i, e) :: exps
  let lp : Option (Nat × Nat) :=
    if u == 1 then some (1, 1)
    else if u < ctx.lpBound then some (1, u)
    else if ctx.dlpBound > 0 && u < ctx.dlpBound then splitCofactor u ctx.lpBound
    else none
  let some (l1, l2) := lp | return none
  let X := ((A * x + B) % (ctx.n : Int)).toNat
  -- sorted by index, so that products of relations can merge exponent lists
  let sorted := exps.mergeSort (fun a b => a.1 ≤ b.1)
  match Relation.mk? ctx.n ctx.fb X 1 u (decide (v < 0)) sorted with
  | some r => return some ⟨r, l1, l2⟩
  | none => return none

/-- All relations from the candidates of one polynomial: by resieving when there
are many, by per-candidate tests otherwise. -/
def processCandidates (ctx : Ctx) (ap : APoly) (B C : Int) (roots : Array Nat)
    (buf : ByteArray) (cands : Array Nat) (rels : Array (Found ctx.n ctx.fb)) :
    Array (Found ctx.n ctx.fb) := Id.run do
  let mut rels := rels
  let F := ctx.fb.size
  if cands.size ≥ 6 then
    let buf := labelCandidates buf cands ctx.size
    let len : USize := ctx.size.toUSize
    let mut lists : Array (Array Nat) := Array.replicate (min 127 cands.size) #[]
    if h : len.toNat < buf.size ∧ 4 * ctx.medEnd ≤ ctx.primeB.size ∧ ctx.medEnd ≤ roots.size then
      lists := resieveFrom ctx.primeB roots buf len h.1 ctx.resieveStart ctx.medEnd h.2.1 h.2.2 lists
    lists := labelLarge roots buf ctx.size ctx.medEnd F lists
    for ci in [0:cands.size] do
      let j := cands[ci]!
      let found := if ci < 127 then
          factorCandidate ctx ap B C roots ctx.resieveStart lists[ci]! j
        else
          -- beyond the labels: test every prime below the interval directly
          let hits := (largeHits roots buf ctx.size ctx.medEnd F #[]).filterMap fun (pos, i) =>
            if pos == j then some i else none
          factorCandidate ctx ap B C roots ctx.medEnd hits j
      if let some r := found then rels := rels.push r
  else
    let hits := largeHits roots buf ctx.size ctx.medEnd F #[]
    for j in cands do
      let listed := hits.filterMap fun (pos, i) => if pos == j then some i else none
      if let some r := factorCandidate ctx ap B C roots ctx.medEnd listed j then
        rels := rels.push r
  return rels

/-! ## One `A`: all of its Gray-code polynomials -/

/-- Sieve every polynomial of the `A` chosen by `seed`. -/
def processA (ctx : Ctx) (seed : Nat) : Array (Found ctx.n ctx.fb) := Id.run do
  let some ap := mkAPoly ctx seed | return #[]
  let F := ctx.fb.size
  let s := ap.qs.size
  let len : USize := ctx.size.toUSize
  let mut rels : Array (Found ctx.n ctx.fb) := #[]
  let mut B : Int := (ap.Bl.foldl (· + ·) 0 : Nat)
  let A : Int := ap.A
  let mut roots := ap.roots
  let mut buf := ctx.template.copySlice 0 ByteArray.empty 0 ctx.template.size
  -- first polynomial: sieve at the initial roots
  if h : len.toNat < buf.size ∧ 4 * ctx.medEnd ≤ ctx.primeB.size ∧ ctx.medEnd ≤ roots.size ∧
      ctx.medEnd ≤ ap.logp.size then
    buf := sieveFrom ctx.primeB roots ap.logp buf len h.1 ctx.spv ctx.medEnd h.2.1 h.2.2.1 h.2.2.2
  if h : len.toNat < buf.size ∧ F ≤ roots.size ∧ F ≤ ap.logp.size then
    buf := sieveLarge roots ap.logp buf len h.1 ctx.medEnd F h.2.1 h.2.2
  let cands := scan buf ctx.size
  if !cands.isEmpty then
    rels := processCandidates ctx ap B ((B * B - (ctx.N : Int)) / A) roots buf cands rels
  for g in [1:2 ^ (s - 1)] do
    -- Gray code: bit v flips between g - 1 and g
    let v := (g &&& (2 ^ 64 - g)).log2
    let gray := g ^^^ (g >>> 1)
    let negate := gray.testBit v
    let bv : Int := (ap.Bl[v]! : Int)
    B := if negate then B - 2 * bv else B + 2 * bv
    buf := ctx.template.copySlice 0 buf 0 ctx.template.size
    let drow := ap.delta[v]!
    -- B decreases by 2B_v: roots A⁻¹(±t - B) increase by δ_v, and conversely
    if h : len.toNat < buf.size ∧ 4 * ctx.medEnd ≤ ctx.primeB.size ∧
        4 * ctx.medEnd ≤ drow.size ∧ ctx.medEnd ≤ ap.logp.size ∧ ctx.medEnd ≤ roots.size then
      let (roots', buf') := switchMedium ctx.primeB drow ap.logp negate roots buf len h.1 ctx.spv
        ctx.medEnd h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      roots := roots'
      buf := buf'
    if h : len.toNat < buf.size ∧ 4 * F ≤ ctx.primeB.size ∧ 4 * F ≤ drow.size ∧
        F ≤ ap.logp.size ∧ F ≤ roots.size then
      let (roots', buf') := switchLarge ctx.primeB drow ap.logp negate roots buf len h.1
        ctx.medEnd F h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      roots := roots'
      buf := buf'
    -- primes below the small prime bound are not sieved, but their roots move
    for i in [1:ctx.spv] do
      if ap.logp.get! i != 0 then
        let p := ctx.prime[i]!
        let d := u32Get drow i
        let w := roots[i]!
        roots := roots.set! i (packRoots (moveRoot negate (root1 w) d p)
          (moveRoot negate (root2 w) d p))
    let C := (B * B - (ctx.N : Int)) / A
    let cands := scan buf ctx.size
    if !cands.isEmpty then
      rels := processCandidates ctx ap B C roots buf cands rels
  return rels

/-! ## Driver -/

/-- Collect relations on parallel tasks until enough full relations and cycles
exist, then combine every cycle into a full relation (as in `QS.collect`). -/
def collect (ctx : Ctx) (needed threads maxRounds : Nat) : Array (Relation ctx.n ctx.fb) := Id.run do
  let mut fulls : Array (Relation ctx.n ctx.fb) := #[]
  let mut edges : Array (Found ctx.n ctx.fb) := #[]
  let mut uf : UnionFind := {}
  let mut cycles := 0
  let mut seen : Std.HashSet Nat := {}
  let mut round := 0
  -- give up after many rounds without a single relation (e.g. no usable `A`)
  let mut idle := 0
  while fulls.size + cycles < needed && round < maxRounds && idle < 50 do
    let base := round * threads
    let tasks := (List.range threads).map fun t =>
      Task.spawn fun _ => processA ctx (base + t)
    let before := fulls.size + edges.size
    for task in tasks do
      for f in task.get do
        if seen.contains f.rel.x then continue
        seen := seen.insert f.rel.x
        if f.l1 == 1 && f.l2 == 1 then
          fulls := fulls.push f.rel
        else
          edges := edges.push f
          let (uf', closed) := uf.union f.l1 f.l2
          uf := uf'
          if closed then cycles := cycles + 1
    idle := if fulls.size + edges.size == before then idle + 1 else 0
    round := round + 1
  for ids in graphCycles (edges.map fun f => (f.l1, f.l2)) do
    if let some r := combineCycle edges ids then fulls := fulls.push r
  return fulls

/-- Linear algebra (block Lanczos, falling back to elimination) and square
roots: try each dependency until one splits `n`. -/
def extract (ctx : Ctx) (rels : Array (Relation ctx.n ctx.fb)) (threads : Nat := 8) :
    Option (ProperFactor ctx.n) := Id.run do
  let rows := rels.map parityColumns
  let tryDeps (deps : Array (Array Nat)) : Option (ProperFactor ctx.n) := Id.run do
    for dep in deps do
      if dep.isEmpty then continue
      let rs := dep.map fun i => rels[i]!
      match (Relation.prodTree rs 0 rs.size).toSquares with
      | none => continue
      | some sc =>
        match sc.factor with
        | some d => return some d
        | none => continue
    return none
  match tryDeps (Lanczos.dependencies (ctx.fb.size + 1) rows 64 threads) with
  | some d => return some d
  | none => return tryDeps (GF2.dependencies (ctx.fb.size + 1) rows 64)

structure Config where
  threads : Nat := 8
  maxRounds : Nat := 1000000
  params : Option Params := none
  deriving Inhabited

/-- Split an odd composite `n` that is not a perfect power. -/
def splitCore (n : Nat) (cfg : Config := {}) : Option (ProperFactor n) :=
  if n < 1000 then none else
  let params := cfg.params.getD (chooseParams (decimalDigits n))
  match mkCtx n params with
  | .inr p => checkFactor n p
  | .inl ctx =>
    let needed := ctx.fb.size + 1 + params.extra
    let rels := collect ctx needed (max 1 cfg.threads) cfg.maxRounds
    if h : ctx.n = n then h ▸ extract ctx rels (max 1 cfg.threads) else none

/-- The public splitter: even numbers and perfect powers are handled first;
inputs below 20 digits use the simpler SIQS of `QS` (no suitable `A` with the
fast parameters). -/
def split (n : Nat) (cfg : Config := {}) : Option (ProperFactor n) :=
  if n < 4 then none
  else if n % 2 = 0 then checkFactor n 2
  else if decimalDigits n < 20 then QS.split n { variant := .siqs, threads := cfg.threads }
  else match perfectPower n with
    | some (r, _) => checkFactor n r
    | none => splitCore n cfg

/-- Every factor returned by the fast SIQS is a proper divisor. -/
theorem split_sound {n : Nat} {cfg : Config} {d : ProperFactor n}
    (_h : split n cfg = some d) : 1 < d.val ∧ d.val < n ∧ d.val ∣ n := d.property

end PrimeFactorLean.SIQS
