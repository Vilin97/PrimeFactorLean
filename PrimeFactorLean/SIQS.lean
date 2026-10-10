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

/-- Add `lg` at `a` when `a < len`. -/
@[inline] def hitIf (s : ByteArray) (len a : USize) (lg : UInt8) (h : len.toNat < s.size) :
    ByteArray :=
  if hlt : a < len then
    have hk : a ≤ len := USize.le_of_lt hlt
    s.uset a (s.uget a (uget_bound hk h) + lg) (uget_bound hk h)
  else s

theorem size_hitIf (s : ByteArray) (len a : USize) (lg : UInt8) (h : len.toNat < s.size) :
    (hitIf s len a lg h).size = s.size := by
  unfold hitIf
  split
  · simp [size_uset]
  · rfl

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

/-- Positions in `[j, e)` whose byte is `≥ 128`, appended to `acc`. -/
def scanBytes (s : ByteArray) (j e : Nat) (acc : Array Nat) : Array Nat :=
  if h : j < e ∧ j < s.size then
    scanBytes s (j + 1) e (if s.get j h.2 ≥ 128 then acc.push j else acc)
  else acc
termination_by e - j

/-- Positions whose byte reached `128` (bit 7 set). Blocks of 4096 bytes, then
chunks of 64, are first tested by an `OR` fold (vectorized by the C compiler);
only chunks containing a candidate are scanned byte by byte. -/
def scan (s : ByteArray) (len : Nat) : Array Nat := Id.run do
  let size := min len s.size
  let mut out : Array Nat := #[]
  let mut b := 0
  while b < size do
    let e := min size (b + 4096)
    if s.foldl (fun acc x => acc ||| x) 0 b e ≥ 128 then
      let mut c := b
      while c < e do
        let ce := min e (c + 64)
        if s.foldl (fun acc x => acc ||| x) 0 c ce ≥ 128 then out := scanBytes s c ce out
        c := ce
    b := e
  return out

/-! ### Kernels on unboxed per-prime arrays

The kernels below read primes, Gray-code deltas and the per-prime counts
`⌈len / p⌉` from `Array UInt32` (unboxed scalars), and sieve both roots of a
prime in one loop. -/

theorem usize_pred_lt (c : USize) (h : c ≠ 0) : (c - 1).toNat < c.toNat := by
  have h0 : c.toNat ≠ 0 := by
    intro h0
    apply h
    exact USize.toNat_inj.mp (by simpa using h0)
  have h1 : (1 : USize) ≤ c := by
    rw [USize.le_iff_toNat_le]
    simp
    omega
  rw [USize.toNat_sub_of_le _ _ h1]
  simp
  omega

/-- `count` clamped updates at `a, a + p, …` and `b, b + p, …` (both roots per step;
a machine-word counter). -/
def stride2 (s : ByteArray) (len a b p : USize) (lg : UInt8) (h : len.toNat < s.size)
    (count : USize) : ByteArray :=
  if hc : count = 0 then s
  else
    let t := hitClamp s len a lg h
    let t := hitClamp t len b lg (by rw [size_hitClamp]; exact h)
    stride2 t len (a + p) (b + p) p lg (by rw [size_hitClamp, size_hitClamp]; exact h) (count - 1)
termination_by count.toNat
decreasing_by exact usize_pred_lt count hc

theorem size_stride2 (s : ByteArray) (len a b p : USize) (lg : UInt8) (h : len.toNat < s.size)
    (c : USize) : (stride2 s len a b p lg h c).size = s.size := by
  fun_induction stride2 s len a b p lg h c with
  | case1 => rfl
  | case2 s a b h c hc t1 t2 ih => rw [ih]; simp only [t1, t2, size_hitClamp]

/-- Sieve the primes with index in `[i, stop)` (below the interval length) at their
current roots: the first polynomial of an `A`. -/
def sieveMed (prime cnt : Array UInt32) (roots : Array Nat) (logp : ByteArray) (s : ByteArray)
    (len : USize) (hs : len.toNat < s.size) (i stop : Nat) (h1 : stop ≤ prime.size)
    (h2 : stop ≤ cnt.size) (h3 : stop ≤ roots.size) (h4 : stop ≤ logp.size) : ByteArray :=
  if hi : i < stop then
    let w := roots[i]
    let t := stride2 s len (root1 w).toUSize (root2 w).toUSize prime[i].toUSize
      (logp.get i (by omega)) hs cnt[i].toUSize
    sieveMed prime cnt roots logp t len (by rw [size_stride2]; exact hs) (i + 1) stop h1 h2 h3 h4
  else s
termination_by stop - i

/-- Gray-code switch for the primes in `[i, stop)` below the interval length:
both roots move by `±δ`, then the prime is sieved at the new roots. -/
def switchMed (prime delta cnt : Array UInt32) (logp : ByteArray) (add : Bool)
    (roots : Array Nat) (s : ByteArray) (len : USize) (hs : len.toNat < s.size) (i stop : Nat)
    (h1 : stop ≤ prime.size) (h2 : stop ≤ delta.size) (h3 : stop ≤ cnt.size)
    (h4 : stop ≤ logp.size) (h5 : stop ≤ roots.size) : Array Nat × ByteArray :=
  if hi : i < stop then
    let p := prime[i]
    let d := delta[i]
    let w := roots[i]
    let a := moveRoot add (root1 w) d p
    let b := moveRoot add (root2 w) d p
    let t := stride2 s len a.toUSize b.toUSize p.toUSize (logp.get i (by omega)) hs cnt[i].toUSize
    let roots' := roots.set i (packRoots a b) (by omega)
    switchMed prime delta cnt logp add roots' t len (by rw [size_stride2]; exact hs) (i + 1) stop
      h1 h2 h3 h4 (by simp [roots']; omega)
  else (roots, s)
termination_by stop - i

/-- Gray-code switch for primes beyond the interval: one clamped update per root. -/
def switchBig (prime delta : Array UInt32) (logp : ByteArray) (add : Bool) (roots : Array Nat)
    (s : ByteArray) (len : USize) (hs : len.toNat < s.size) (i stop : Nat)
    (h1 : stop ≤ prime.size) (h2 : stop ≤ delta.size) (h4 : stop ≤ logp.size)
    (h5 : stop ≤ roots.size) : Array Nat × ByteArray :=
  if hi : i < stop then
    let p := prime[i]
    let d := delta[i]
    let w := roots[i]
    let a := moveRoot add (root1 w) d p
    let b := moveRoot add (root2 w) d p
    let lg := logp.get i (by omega)
    -- a root beyond the interval is skipped (a branch rather than an update of
    -- the trash byte: those updates would form one chain through memory)
    let t := hitIf s len a.toUSize lg hs
    let t := hitIf t len b.toUSize lg (by rw [size_hitIf]; exact hs)
    let roots' := roots.set i (packRoots a b) (by omega)
    switchBig prime delta logp add roots' t len (by rw [size_hitIf, size_hitIf]; exact hs)
      (i + 1) stop h1 h2 h4 (by simp [roots']; omega)
  else (roots, s)
termination_by stop - i

/-- Roots of the unsieved small primes `[i, stop)` move without sieving. -/
def moveTiny (prime delta : Array UInt32) (add : Bool) (roots : Array Nat) (i stop : Nat)
    (h1 : stop ≤ prime.size) (h2 : stop ≤ delta.size) (h5 : stop ≤ roots.size) : Array Nat :=
  if hi : i < stop then
    let p := prime[i]
    let d := delta[i]
    let w := roots[i]
    let roots' := roots.set i (packRoots (moveRoot add (root1 w) d p) (moveRoot add (root2 w) d p))
      (by omega)
    moveTiny prime delta add roots' (i + 1) stop h1 h2 (by simp [roots']; omega)
  else roots
termination_by stop - i

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
  /-- Sieve threshold slack, in bits (more candidates, which the filter rejects cheaply). -/
  slack : Nat := 0
  extra : Nat := 64
  /-- Factor-base primes below this bound are tested per candidate against their
  roots; larger primes are found by walking their progressions once per polynomial. -/
  smallBound : Nat := 8192
  /-- Candidate filter slack in bits: a candidate is factored exactly when its
  unexplained part is below the cofactor bound times `2^filterSlack`. -/
  filterSlack : Nat := 4
  /-- Slack in bits of the first filter (sieve byte, tiny primes and the power of 2). -/
  preSlack : Nat := 6
  deriving Repr, Inhabited

/-- `(digits, factor-base size, M, large-prime multiplier, dlpDiv, slack)`, measured with
16 threads on the balanced semiprimes of the dataset (`scripts/tune_siqs.py`). -/
def paramTable : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  [(20, 60, 2048, 20, 0, 10), (25, 100, 4096, 30, 0, 10), (30, 150, 8192, 30, 0, 10),
   (35, 220, 16384, 40, 0, 10), (40, 300, 32768, 60, 0, 8), (44, 500, 32768, 60, 0, 14),
   (48, 800, 16384, 60, 0, 10), (52, 1200, 32768, 60, 0, 10), (56, 1800, 65536, 60, 0, 10),
   (60, 2400, 32768, 80, 0, 12), (64, 5500, 65536, 80, 0, 14), (68, 5500, 65536, 80, 0, 16),
   (72, 6000, 65536, 80, 16, 12), (76, 7000, 65536, 80, 16, 12), (80, 12000, 131072, 90, 16, 10),
   (85, 17000, 131072, 100, 16, 10), (90, 22000, 196608, 110, 16, 10),
   (95, 30000, 196608, 120, 16, 10), (100, 40000, 262144, 150, 16, 10),
   (110, 60000, 262144, 150, 16, 10)]

def chooseParams (digits : Nat) : Params :=
  let e := (paramTable.find? fun e => digits ≤ e.1).getD
    (paramTable.getLast?.getD (110, 70000, 262144, 150, 16, 12))
  { fbSize := e.2.1, M := e.2.2.1, lpMult := e.2.2.2.1, dlpDiv := e.2.2.2.2.1,
    slack := e.2.2.2.2.2, spv := 30, filterSlack := 6, preSlack := 6, smallBound := 16384 }

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
  /-- `⌈size / p⌉`: the number of steps of a root's progression over the interval. -/
  cnt : Array UInt32
  sqrtN : Array UInt32
  logp : ByteArray
  /-- `round(8 log₂ p)`, for the candidate filter. -/
  log8 : ByteArray
  M : Nat
  /-- Sieve length `2M`. -/
  size : Nat
  mmod : Array UInt32
  /-- `p⁻¹ mod 2^32` and `⌊(2^32 - 1)/p⌋`: `p ∣ x` iff `x · p⁻¹ ≤ lim (mod 2^32)`. -/
  pinv : Array UInt32
  lim : Array UInt32
  spv : Nat
  /-- First index whose prime is tested by walking its progression (not by roots). -/
  smallEnd : Nat
  /-- First index whose prime exceeds the interval (`p ≥ 2M`). -/
  medEnd : Nat
  bias : UInt8
  lpBound : Nat
  dlpBound : Nat
  template : ByteArray
  /-- `⌊√(2N)⌋ / M`: the size of `A` that balances `|v(x)|` over the interval. -/
  target : Nat
  /-- Indices of the factor-base primes dividing `kN` (one root, not sieved). -/
  special : Array Nat
  /-- The filter bound in eighths of a bit. -/
  allow8 : Nat
  /-- Bits per unit of the sieve logarithms (`logp` holds `log₂ p / scale`). -/
  scale : Float
  /-- The first (cheap) filter bound in eighths of a bit. -/
  pre8 : Nat
  /-- `kN ≡ 1 (mod 8)`: the polynomials are `(2Ax + B)² - kN = 4A v(x)` with `B` odd and
  `v(x) = Ax² + Bx + C` (values half as large); otherwise `(Ax + B)² - kN = A v(x)` with
  `v(x) = Ax² + 2Bx + C`. -/
  q2 : Bool

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
  let q2 := N % 8 == 1
  -- log₂ max |v(x)|: `M √(kN/2)` (halved for `Q2` polynomials, which are also
  -- always even: about two more bits of the unsieved prime 2)
  let target := Float.log2 M.toFloat + (N.log2.toFloat + 1.0) / 2.0 - 0.5 -
    (if q2 then 2.0 else 0.0)
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
  let mut smallEnd := spv
  while smallEnd < medEnd && fb[smallEnd]! < params.smallBound do smallEnd := smallEnd + 1
  let prime := fb.map (·.toUInt32)
  let special := (Array.range fb.size).filter fun i => i ≥ 1 && roots[i]! == 0
  let allow8 := (8.0 * (allowance + params.filterSlack.toFloat)).toUInt64.toNat
  let pre8 := (8.0 * (allowance + params.preSlack.toFloat)).toUInt64.toNat
  return .inl { n := n, k := k, N := N, fb := fb, prime := prime,
                cnt := prime.map fun p => if p == 0 then 0 else (size.toUInt32 + p - 1) / p,
                sqrtN := roots.map (·.toUInt32), logp := logp,
                log8 := ByteArray.mk (fb.map fun p => (Float.round (8.0 * Float.log2 p.toFloat)).toUInt8),
                M := M, size := size,
                mmod := fb.map fun p => (M % p).toUInt32, pinv := prime.map inv32,
                lim := prime.map fun p => if p == 0 then 0 else (0xFFFFFFFF : UInt32) / p,
                spv := spv, smallEnd := smallEnd, medEnd := medEnd, bias := bias,
                lpBound := lpBound, dlpBound := dlpBound, template := template,
                target := if q2 then isqrt (2 * N) / (2 * M) else isqrt (2 * N) / M,
                special := special, allow8 := allow8, pre8 := pre8, scale := scale, q2 := q2 }

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
  /-- Row `l`: `δ_l = 2 B_l A⁻¹ mod p` for every factor-base prime. -/
  delta : Array (Array UInt32)
  /-- Packed roots of the first polynomial `B = ∑ B_l`. -/
  roots : Array Nat
  /-- Logarithms with the primes of `A` (and those of `kN`) zeroed. -/
  logp : ByteArray

/-- Build an `A`, the `B_l`, the deltas and the first roots. The residues of `A`
and of the `B_l = (A/q_l) γ_l` modulo each factor-base prime are computed with
machine words from the `q_l mod p` (prefix and suffix products), not by dividing
the big numbers. -/
def mkAPoly (ctx : Ctx) (seed : Nat) : Option APoly := Id.run do
  let some qs := chooseQs ctx.fb ctx.N seed ctx.target | return none
  let s := qs.size
  let A := qs.foldl (fun acc i => acc * ctx.fb[i]!) 1
  let mut Bl : Array Nat := #[]
  let mut gam : Array Nat := #[]
  for l in [0:s] do
    let q := ctx.fb[qs[l]!]!
    let t := ctx.sqrtN[qs[l]!]!.toNat
    let aq := A / q
    match Arith.invMod (aq % q) q with
    | none => return none
    | some inv =>
      let mut gamma := t * inv % q
      if ctx.q2 then
        -- `B` must be odd: `B_{s-1}` (never flipped) odd, the other `B_l` even
        if (gamma % 2 == 1) != (l + 1 == s) then gamma := q - gamma
      else if 2 * gamma > q then gamma := q - gamma
      Bl := Bl.push (aq * gamma)
      gam := gam.push gamma
  let B := Bl.foldl (· + ·) 0
  if (B * B) % A != ctx.N % A then return none
  if ctx.q2 && (B % 2 == 0 || (B * B) % (4 * A) != ctx.N % (4 * A)) then return none
  let qv : Array UInt64 := qs.map fun i => ctx.fb[i]!.toUInt64
  let F := ctx.fb.size
  let mut delta : Array (Array UInt32) := Array.replicate s (Array.replicate F 0)
  let mut roots : Array Nat := Array.replicate F 0
  let mut logp := ctx.logp
  let mut pre : Array Nat := Array.replicate (s + 1) 1
  for i in [1:F] do
    if ctx.sqrtN[i]! == 0 then
      -- primes of `kN`: not sieved (trial divided directly)
      logp := logp.set! i 0
      continue
    let pu := ctx.fb[i]!.toUInt64
    -- prefix products of the `q_l mod p`
    let mut acc : UInt64 := 1
    for l in [0:s] do
      pre := pre.set! l acc.toNat
      acc := acc * (qv[l]! % pu) % pu
    if acc == 0 then
      -- primes of `A`: not sieved
      logp := logp.set! i 0
      continue
    let ainv0 := invModU acc pu
    -- the roots solve `A x + B ≡ ±t` (or `2A x + B ≡ ±t` for `Q2`)
    let ainv := if ctx.q2 then ainv0 * ((pu + 1) / 2) % pu else ainv0
    let mut suf : UInt64 := 1
    let mut bm : UInt64 := 0
    for l' in [0:s] do
      let l := s - 1 - l'
      let bl := pre[l]!.toUInt64 * suf % pu * (gam[l]!.toUInt64 % pu) % pu
      bm := (bm + bl) % pu
      -- flipping `B_l` moves `B` by `2 B_l` and the roots by `2 B_l / A` (or `B_l / A`)
      delta := delta.modify l fun row => row.set! i ((2 * bl % pu) * ainv % pu).toUInt32
      suf := suf * (qv[l]! % pu) % pu
    let t := ctx.sqrtN[i]!.toUInt64
    let mm := ctx.mmod[i]!.toUInt64
    -- positions j = x + M of the roots x = A⁻¹ (±t - B)
    let x1 := ainv * ((t + pu - bm) % pu) % pu
    let x2 := ainv * ((pu - t + pu - bm) % pu) % pu
    roots := roots.set! i (packRoots ((x1 + mm) % pu).toUInt32 ((x2 + mm) % pu).toUInt32)
  logp := logp.set! 0 0
  return some { A := A, qs := qs, Bl := Bl, delta := delta, roots := roots, logp := logp }

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
def powmod50 (b e m : UInt64) (mf : Float) : UInt64 := go b e 1 64
where
  /-- Right-to-left binary powering (tail recursive: no loop state to allocate). -/
  go (base e result : UInt64) : Nat → UInt64
    | 0 => result
    | fuel + 1 =>
      if e == 0 then result
      else go (mulmod50 base base m mf) (e >>> 1)
        (if e &&& 1 == 1 then mulmod50 result base m mf else result) fuel

/-- Strong probable prime to base 2, for odd `3 < m < 2^50` (a screen only:
large-prime classification never affects correctness). -/
def sprp2 (m : UInt64) : Bool :=
  let mf := 1.0 / m.toFloat
  -- m - 1 = 2^tz · d with d odd
  let tz := ((m - 1) &&& (-(m - 1))).toNat.log2
  let d := (m - 1) >>> tz.toUInt64
  let x := powmod50 2 d m mf
  x == 1 || x == m - 1 || squares x mf tz
where
  /-- `x² , x⁴, …` (`k - 1` squarings): does one of them reach `-1`? -/
  squares (x : UInt64) (mf : Float) : Nat → Bool
    | 0 => false
    | 1 => false
    | k + 1 =>
      let x := mulmod50 x x m mf
      x == m - 1 || squares x mf k

/-- Binary gcd of machine words (no divisions). -/
def gcd64 (a b : UInt64) : UInt64 :=
  if a == 0 then b
  else if b == 0 then a
  else
    -- common power of two, then Stein's loop on odd `a`
    let shift := ((a ||| b) &&& (-(a ||| b))).toNat.log2
    let a := a >>> (a &&& (-a)).toNat.log2.toUInt64
    (loop a b 200) <<< shift.toUInt64
where
  /-- Stein's algorithm with `a` odd (tail recursive). -/
  loop (a b : UInt64) : Nat → UInt64
    | 0 => a
    | fuel + 1 =>
      if b == 0 then a
      else
        let b := b >>> (b &&& (-b)).toNat.log2.toUInt64
        if a > b then loop b (a - b) fuel else loop a (b - a) fuel

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
  -- Brent's rho finds a factor `p ≤ u^(1/2)` after about `1.25 √p ≤ 1.25 u^(1/4)`
  -- steps: a budget of `8 u^(1/4)` (and at least 2000) rarely gives up early
  let iters := (max 2000 (8 * iroot u 4)).toUInt64
  -- `u >>> 52 == 0` rather than `u < 2 ^ 52`: `Nat` literals above `2^32` are
  -- parsed from their digits at every use
  let g := if u >>> 52 == 0 then
      let g := rho50 u.toUInt64 1 iters
      if g != 0 then g else rho50 u.toUInt64 3 iters
    else 0
  if g != 0 then g.toNat else squfofFactor u

/-- Split a double-large-prime cofactor `u` into two primes below `lp` (a base-2
probable-prime screen first). -/
def splitCofactor (u lp : Nat) : Option (Nat × Nat) :=
  if u >>> 52 == 0 && u % 2 == 1 && sprp2 u.toUInt64 then none
  else
    let d := cofactorFactor u
    if d ≤ 1 then none else
    let a := min d (u / d)
    let b := max d (u / d)
    if a < lp && b < lp && a * b == u && a != b then some (a, b) else none

/-! ## Candidates

A candidate's factor-base primes are found without touching big numbers:

* primes below `smallEnd` by comparing the candidate's position with their roots;
* larger primes below the interval by walking their progressions once per
  polynomial and recording the steps that land on a candidate (a byte `≥ 128`,
  which only candidates have after the scan);
* primes beyond the interval by looking at their two roots.

The logarithms of these primes are compared with `log₂ |v(x)|`: only candidates
whose unexplained part is within the cofactor bound (plus a slack for prime
powers and the unsieved primes) are factored exactly, with big numbers. -/

/-- Exponent of `p` in `u` and the cofactor. -/
@[inline] def strip (u p : Nat) : Nat × Nat := QS.stripPrime u p

/-- `p ∣ (j - r)` for a root `r < p`, by multiplication with `p⁻¹ (mod 2^32)`
(Granlund–Montgomery); `j < r` cannot be a hit since `0 < r - j < p`. -/
@[inline] def rootHit (j r q l : UInt32) : Bool := j ≥ r && (j - r) * q ≤ l

/-- Primes `[i, stop)` dividing `v(x)` at position `j`, by their roots (primes
with zero sieve logarithm, those of `A` and `kN`, are skipped: they are tested
exactly later). Accumulates the indices and their `log8`. -/
def smallTest (logp log8 : ByteArray) (pinv lim : Array UInt32) (roots : Array Nat) (j : UInt32)
    (i stop : Nat) (h1 : stop ≤ logp.size) (h2 : stop ≤ log8.size) (h3 : stop ≤ pinv.size)
    (h4 : stop ≤ lim.size) (h5 : stop ≤ roots.size) (hits : List Nat) (l : Nat) : List Nat × Nat :=
  if hi : i < stop then
    if logp.get i (by omega) == 0 then
      smallTest logp log8 pinv lim roots j (i + 1) stop h1 h2 h3 h4 h5 hits l
    else
      let w := roots[i]
      let q := pinv[i]
      let lm := lim[i]
      if rootHit j (root1 w) q lm || rootHit j (root2 w) q lm then
        smallTest logp log8 pinv lim roots j (i + 1) stop h1 h2 h3 h4 h5 (i :: hits)
          (l + (log8.get i (by omega)).toNat)
      else smallTest logp log8 pinv lim roots j (i + 1) stop h1 h2 h3 h4 h5 hits l
  else (hits, l)
termination_by stop - i

/-- `count` clamped steps of the progressions `a, b (+ p)`: record
`pos <<< 24 ||| tag` for every position whose byte is `≥ 128`. The trash byte at
`len` (where clamped positions land) is zero during candidate processing, so a
clamped step never records anything. -/
def walk2 (buf : ByteArray) (len a b p : USize) (tag : Nat) (h : len.toNat < buf.size)
    (acc : Array Nat) (count : USize) : Array Nat :=
  if hc : count = 0 then acc
  else
    let ka := if a ≤ len then a else len
    have hka : ka ≤ len := by
      show (if a ≤ len then a else len) ≤ len
      split
      · assumption
      · exact USize.le_refl len
    let kb := if b ≤ len then b else len
    have hkb : kb ≤ len := by
      show (if b ≤ len then b else len) ≤ len
      split
      · assumption
      · exact USize.le_refl len
    let va := buf.uget ka (uget_bound hka h)
    let vb := buf.uget kb (uget_bound hkb h)
    if (va ||| vb) ≥ 128 then
      let acc := if va ≥ 128 then acc.push ((ka.toNat <<< 24) ||| tag) else acc
      let acc := if vb ≥ 128 then acc.push ((kb.toNat <<< 24) ||| tag) else acc
      walk2 buf len (a + p) (b + p) p tag h acc (count - 1)
    else walk2 buf len (a + p) (b + p) p tag h acc (count - 1)
termination_by count.toNat
decreasing_by all_goals exact usize_pred_lt count hc

/-- Walk the primes `[i, stop)` below the interval (skipping zero logarithms). -/
def walkMed (prime cnt : Array UInt32) (logp : ByteArray) (roots : Array Nat) (buf : ByteArray)
    (len : USize) (h : len.toNat < buf.size) (i stop : Nat) (h1 : stop ≤ prime.size)
    (h2 : stop ≤ cnt.size) (h3 : stop ≤ logp.size) (h4 : stop ≤ roots.size) (acc : Array Nat) :
    Array Nat :=
  if hi : i < stop then
    if logp.get i (by omega) == 0 then walkMed prime cnt logp roots buf len h (i + 1) stop h1 h2 h3 h4 acc
    else
      let w := roots[i]
      let acc := walk2 buf len (root1 w).toUSize (root2 w).toUSize prime[i].toUSize i h acc
        cnt[i].toUSize
      walkMed prime cnt logp roots buf len h (i + 1) stop h1 h2 h3 h4 acc
  else acc
termination_by stop - i

/-- Primes `[i, stop)` beyond the interval: one look at each root. -/
def checkBig (logp : ByteArray) (roots : Array Nat) (buf : ByteArray) (len : USize)
    (h : len.toNat < buf.size) (i stop : Nat) (h3 : stop ≤ logp.size) (h4 : stop ≤ roots.size)
    (acc : Array Nat) : Array Nat :=
  if hi : i < stop then
    if logp.get i (by omega) == 0 then checkBig logp roots buf len h (i + 1) stop h3 h4 acc
    else
      let w := roots[i]
      checkBig logp roots buf len h (i + 1) stop h3 h4
        (walk2 buf len (root1 w).toUSize (root2 w).toUSize 0 i h acc 1)
  else acc
termination_by stop - i

/-- Index of `pos` in the increasing array `cands` (`cands.size` if absent). -/
def findCand (cands : Array Nat) (pos : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := cands.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if cands[mid]! < pos then lo := mid + 1 else hi := mid
  return if lo < cands.size && cands[lo]! == pos then lo else cands.size

/-- Factor `v(x)` at position `j` exactly, given the factor-base primes found to
divide it (the primes of `A` and `kN` are tested here), and build a checked
relation: full, or with one or two large primes. -/
def exactRelation (ctx : Ctx) (ap : APoly) (B C : Int) (j : Nat) (found : List Nat) :
    Option (Found ctx.n ctx.fb) := Id.run do
  let x : Int := (j : Int) - (ctx.M : Int)
  let A : Int := ap.A
  let v : Int := if ctx.q2 then (A * x + B) * x + C else (A * x + 2 * B) * x + C
  if v == 0 then return none
  let (u, e2) := strip v.natAbs 2
  let mut exps : List (Nat × Nat) := ap.qs.toList.map fun i => (i, 1)
  if e2 > 0 then exps := (0, e2) :: exps
  let mut u := u
  for i in found do
    let (u', e) := strip u ctx.fb[i]!
    if e > 0 then
      u := u'
      exps := (i, e) :: exps
  for i in ap.qs do
    let (u', e) := strip u ctx.fb[i]!
    if e > 0 then
      u := u'
      exps := (i, e) :: exps
  for i in ctx.special do
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
  let X := ((if ctx.q2 then 2 * A * x + B else A * x + B) % (ctx.n : Int)).toNat
  -- sorted by index, so that products of relations can merge exponent lists
  let sorted := exps.mergeSort (fun a b => a.1 ≤ b.1)
  -- `X² = 4 A v(x)` for `Q2` polynomials: the square factor 2² goes into `sq`
  match Relation.mk? ctx.n ctx.fb X (if ctx.q2 then 2 else 1) u (decide (v < 0)) sorted with
  | some r => return some ⟨r, l1, l2⟩
  | none => return none

/-- All relations from the candidates of one polynomial. -/
def processCands (ctx : Ctx) (ap : APoly) (B C : Int) (roots : Array Nat) (buf : ByteArray)
    (cands : Array Nat) (rels : Array (Found ctx.n ctx.fb)) : Array (Found ctx.n ctx.fb) := Id.run do
  let F := ctx.fb.size
  let len : USize := ctx.size.toUSize
  let mut recs : Array Nat := #[]
  if h : len.toNat < buf.size ∧ ctx.medEnd ≤ ctx.prime.size ∧ ctx.medEnd ≤ ctx.cnt.size ∧
      ctx.medEnd ≤ ap.logp.size ∧ ctx.medEnd ≤ roots.size then
    recs := walkMed ctx.prime ctx.cnt ap.logp roots buf len h.1 ctx.smallEnd ctx.medEnd h.2.1 h.2.2.1
      h.2.2.2.1 h.2.2.2.2 recs
  if h : len.toNat < buf.size ∧ F ≤ ap.logp.size ∧ F ≤ roots.size then
    recs := checkBig ap.logp roots buf len h.1 ctx.medEnd F h.2.1 h.2.2 recs
  let mut lists : Array (List Nat) := Array.replicate cands.size []
  for r in recs do
    let c := findCand cands (r >>> 24)
    if c < cands.size then lists := lists.modify c ((r &&& 0xFFFFFF) :: ·)
  let Af := nf ap.A
  let Bf := intF B
  let Cf := intF C
  let Mf := nf ctx.M
  -- `v(x) mod 2^64` gives the exact power of 2 in `v(x)` (2 is not sieved)
  let w64 : Int := 18446744073709551616
  let A64 := (ap.A % 18446744073709551616).toUInt64
  let B64 := ((if ctx.q2 then B else 2 * B) % w64).toNat.toUInt64
  let C64 := (C % w64).toNat.toUInt64
  let M64 := ctx.M.toUInt64
  let mut rels := rels
  let biasF := nf ctx.bias.toNat
  let B2f := if ctx.q2 then Bf else fc 2 * Bf
  let pre8F := nf ctx.pre8
  for c in [0:cands.size] do
    let j := cands[c]!
    let x := nf j - Mf
    let vf := ((Af * x + B2f) * x + Cf).abs
    let l8v := if vf < fc 2 then fc 0 else fc 8 * Float.log2 vf
    let x64 := j.toUInt64 - M64
    let v64 := (A64 * x64 + B64) * x64 + C64
    let e2 : Nat := if v64 == 0 then 64 else (v64 &&& (-v64)).toNat.log2
    -- first filter: the power of 2, the unsieved primes (index < spv) by their
    -- roots and the sieved ones through the sieve byte (rounded logarithms, each
    -- prime once), with four bits for rounding and prime powers
    let (tiny, lt) :=
      if h : ctx.spv ≤ ap.logp.size ∧ ctx.spv ≤ ctx.log8.size ∧ ctx.spv ≤ ctx.pinv.size ∧
          ctx.spv ≤ ctx.lim.size ∧ ctx.spv ≤ roots.size then
        smallTest ap.logp ctx.log8 ctx.pinv ctx.lim roots j.toUInt32 1 ctx.spv h.1 h.2.1 h.2.2.1
          h.2.2.2.1 h.2.2.2.2 [] (8 * e2)
      else ([], 8 * e2)
    let sieved := ((buf.get! j).toUInt64.toFloat - biasF) * ctx.scale * fc 8
    if l8v > nf lt + sieved + pre8F then continue
    let (hits, l8) :=
      if h : ctx.smallEnd ≤ ap.logp.size ∧ ctx.smallEnd ≤ ctx.log8.size ∧ ctx.smallEnd ≤ ctx.pinv.size ∧
          ctx.smallEnd ≤ ctx.lim.size ∧ ctx.smallEnd ≤ roots.size then
        smallTest ap.logp ctx.log8 ctx.pinv ctx.lim roots j.toUInt32 ctx.spv ctx.smallEnd h.1 h.2.1
          h.2.2.1 h.2.2.2.1 h.2.2.2.2 tiny lt
      else (tiny, lt)
    let mut l8 := l8
    let mut found := hits
    for i in lists[c]! do
      l8 := l8 + (ctx.log8.get! i).toNat
      found := i :: found
    if l8v ≤ (nf (l8 + ctx.allow8)) then
      if let some r := exactRelation ctx ap B C j found then rels := rels.push r
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
  if h : len.toNat < buf.size ∧ ctx.medEnd ≤ ctx.prime.size ∧ ctx.medEnd ≤ ctx.cnt.size ∧
      ctx.medEnd ≤ roots.size ∧ ctx.medEnd ≤ ap.logp.size then
    buf := sieveMed ctx.prime ctx.cnt roots ap.logp buf len h.1 ctx.spv ctx.medEnd h.2.1 h.2.2.1
      h.2.2.2.1 h.2.2.2.2
  if h : len.toNat < buf.size ∧ F ≤ roots.size ∧ F ≤ ap.logp.size then
    buf := sieveLarge roots ap.logp buf len h.1 ctx.medEnd F h.2.1 h.2.2
  -- clamped updates land on the trash byte; clear it for candidate processing
  buf := buf.set! ctx.size 0
  let cands := scan buf ctx.size
  if !cands.isEmpty then
    rels := processCands ctx ap B ((B * B - (ctx.N : Int)) / (if ctx.q2 then 4 * A else A)) roots buf
      cands rels
  for g in [1:2 ^ (s - 1)] do
    -- Gray code: bit v (the lowest set bit of g) flips between g - 1 and g;
    -- machine words (`2 ^ 64 - g` would be a big number)
    let v := (g.toUInt64 &&& (-g.toUInt64)).toNat.log2
    let gray := g ^^^ (g >>> 1)
    let negate := gray.testBit v
    let bv : Int := (ap.Bl[v]! : Int)
    B := if negate then B - 2 * bv else B + 2 * bv
    buf := ctx.template.copySlice 0 buf 0 ctx.template.size
    let drow := ap.delta[v]!
    -- B decreases by 2B_v: roots A⁻¹(±t - B) increase by δ_v, and conversely
    if h : len.toNat < buf.size ∧ F ≤ ctx.prime.size ∧ F ≤ drow.size ∧ F ≤ ctx.cnt.size ∧
        F ≤ ap.logp.size ∧ F ≤ roots.size ∧ ctx.medEnd ≤ F ∧ ctx.spv ≤ F then
      let (roots', buf') := switchMed ctx.prime drow ctx.cnt ap.logp negate roots buf len h.1
        ctx.spv ctx.medEnd (by omega) (by omega) (by omega) (by omega) (by omega)
      roots := roots'
      buf := buf'
    if h : len.toNat < buf.size ∧ F ≤ ctx.prime.size ∧ F ≤ drow.size ∧ F ≤ ap.logp.size ∧
        F ≤ roots.size then
      let (roots', buf') := switchBig ctx.prime drow ap.logp negate roots buf len h.1 ctx.medEnd F
        h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
      roots := roots'
      buf := buf'
    -- primes below the small prime bound are not sieved, but their roots move
    if h : ctx.spv ≤ ctx.prime.size ∧ ctx.spv ≤ drow.size ∧ ctx.spv ≤ roots.size then
      roots := moveTiny ctx.prime drow negate roots 1 ctx.spv h.1 h.2.1 h.2.2
    let C := (B * B - (ctx.N : Int)) / (if ctx.q2 then 4 * A else A)
    buf := buf.set! ctx.size 0
    let cands := scan buf ctx.size
    if !cands.isEmpty then
      rels := processCands ctx ap B C roots buf cands rels
  return rels

/-! ## Driver -/

/-- The relations of the `A`s with seeds `first, first + 1, …` (`count` of them). -/
def processAs (ctx : Ctx) (first count : Nat) : Array (Found ctx.n ctx.fb) := Id.run do
  let mut out : Array (Found ctx.n ctx.fb) := #[]
  for k in [0:count] do out := out ++ processA ctx (first + k)
  return out

/-- Collect relations on parallel tasks until enough full relations and cycles
exist, then combine every cycle into a full relation (as in `QS.collect`).
After a pilot round (one `A` per task), each task processes several `A`s, as
many as the measured yield suggests for most of the remaining need: fewer,
longer rounds keep the threads busy (a round waits for its slowest task). -/
def collect (ctx : Ctx) (needed threads maxRounds : Nat) : Array (Relation ctx.n ctx.fb) := Id.run do
  let mut fulls : Array (Relation ctx.n ctx.fb) := #[]
  let mut edges : Array (Found ctx.n ctx.fb) := #[]
  let mut uf : UnionFind := {}
  let mut cycles := 0
  let mut seen : Std.HashSet Nat := {}
  let mut round := 0
  let mut nextSeed := 0
  let mut perTask := 1
  let mut processed := 0
  -- give up after many rounds without a single relation (e.g. no usable `A`)
  let mut idle := 0
  while fulls.size + cycles < needed && round < maxRounds && idle < 50 do
    let base := nextSeed
    let k := perTask
    let tasks := (List.range threads).map fun t =>
      Task.spawn fun _ => processAs ctx (base + t * k) k
    nextSeed := nextSeed + threads * k
    processed := processed + threads * k
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
    -- the yield per `A` so far underestimates the future rate (cycles grow
    -- faster than linearly), so aiming at 60% of the estimate rarely overshoots
    let got := fulls.size + cycles
    if got > 0 && got < needed then
      let estA := (needed - got) * processed / got
      perTask := max 1 (min 32 (estA * 6 / 10 / threads))
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
