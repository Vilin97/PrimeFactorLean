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

theorem usize_succ_of_lt (i n : USize) (h : i < n) : (i + 1).toNat = i.toNat + 1 := by
  have h1 := USize.lt_iff_toNat_lt.mp h
  have h2 : n.toNat < 2 ^ System.Platform.numBits := n.toNat_lt_size
  rw [USize.toNat_add]
  have h3 : (1 : USize).toNat = 1 := by
    show (USize.ofNat 1).toNat = 1
    have : (USize.ofNat 1).toNat = 1 % 2 ^ System.Platform.numBits := rfl
    rw [this]
    apply Nat.mod_eq_of_lt
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
  rw [h3]
  exact Nat.mod_eq_of_lt (by omega)

theorem toUSize_toNat_of_lt (n : Nat) (h : n < 2 ^ 32) : n.toUSize.toNat = n := by
  show (USize.ofNat n).toNat = n
  have : (USize.ofNat n).toNat = n % 2 ^ System.Platform.numBits := rfl
  rw [this]
  have := numBits_ge
  exact Nat.mod_eq_of_lt (by omega)

/-- `a` inside the interval, else one of the 64 trash bytes `len + (a mod 64)`
after it: no branch, and misses do not form one dependency chain through a
single trash byte. -/
@[inline] def spreadPos (len a : USize) : USize :=
  if a < len then a else len + (a &&& 63)

theorem spreadPos_lt (len a : USize) (hl : len.toNat < 2 ^ 31) :
    (spreadPos len a).toNat < len.toNat + 64 := by
  unfold spreadPos
  split
  · have := USize.lt_iff_toNat_lt.mp ‹a < len›
    omega
  · have h63 : (a &&& 63).toNat ≤ 63 := by
      rw [USize.toNat_and]
      exact Nat.le_trans Nat.and_le_right (by simp)
    rw [toNat_add_small len (a &&& 63) hl (by omega)]
    omega

/-- Add `lg` at `spreadPos len a`. -/
@[inline] def hitSpread (s : ByteArray) (len a : USize) (lg : UInt8) (hl : len.toNat < 2 ^ 31)
    (h : len.toNat + 64 ≤ s.size) : ByteArray :=
  have hk : (spreadPos len a).toNat < s.size := by
    have := spreadPos_lt len a hl
    omega
  s.uset (spreadPos len a) (s.uget (spreadPos len a) hk + lg) hk

theorem size_hitSpread (s : ByteArray) (len a : USize) (lg : UInt8) (hl : len.toNat < 2 ^ 31)
    (h : len.toNat + 64 ≤ s.size) : (hitSpread s len a lg hl h).size = s.size := by
  simp [hitSpread, size_uset]

/-- Sieve primes beyond the interval at their current roots (one update per root,
misses spread over the trash bytes). -/
def sieveLarge (roots : Array Nat) (logp : ByteArray) (s : ByteArray) (len : USize)
    (hl : len.toNat < 2 ^ 31) (hs : len.toNat + 64 ≤ s.size) (i stop : USize)
    (h2 : stop.toNat ≤ roots.size) (h3 : stop.toNat ≤ logp.size) : ByteArray :=
  if hi : i < stop then
    have hlt := USize.lt_iff_toNat_lt.mp hi
    let w := roots.uget i (by omega)
    let lg := logp.uget i (by omega)
    let t := hitSpread s len (root1 w).toUSize lg hl hs
    let t := hitSpread t len (root2 w).toUSize lg hl (by rw [size_hitSpread]; exact hs)
    sieveLarge roots logp t len hl (by rw [size_hitSpread, size_hitSpread]; exact hs) (i + 1) stop
      h2 h3
  else s
termination_by stop.toNat - i.toNat
decreasing_by rw [usize_succ_of_lt i stop hi]; omega

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

/-- The chunks of 64 bytes from `c` to `e` whose `OR` fold has bit 7 set,
scanned byte by byte (tail recursive: a `while` loop with several mutable
variables allocates its state every iteration). -/
def scanChunks (s : ByteArray) (c e : Nat) (acc : Array Nat) : Nat → Array Nat
  | 0 => acc
  | fuel + 1 =>
    if c < e then
      let ce := min e (c + 64)
      let acc := if s.foldl (fun acc x => acc ||| x) 0 c ce ≥ 128 then scanBytes s c ce acc else acc
      scanChunks s ce e acc fuel
    else acc

/-- The blocks of 4096 bytes from `b` to `size` whose `OR` fold has bit 7 set,
then their chunks. -/
def scanBlocks (s : ByteArray) (b size : Nat) (acc : Array Nat) : Nat → Array Nat
  | 0 => acc
  | fuel + 1 =>
    if b < size then
      let e := min size (b + 4096)
      let acc := if s.foldl (fun acc x => acc ||| x) 0 b e ≥ 128 then scanChunks s b e acc 65
        else acc
      scanBlocks s e size acc fuel
    else acc

/-- Positions whose byte reached `128` (bit 7 set). Blocks of 4096 bytes, then
chunks of 64, are first tested by an `OR` fold (vectorized by the C compiler);
only chunks containing a candidate are scanned byte by byte. -/
def scan (s : ByteArray) (len : Nat) : Array Nat :=
  let size := min len s.size
  scanBlocks s 0 size #[] (size / 4096 + 1)

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
    (len : USize) (hs : len.toNat < s.size) (i stop : USize) (h1 : stop.toNat ≤ prime.size)
    (h2 : stop.toNat ≤ cnt.size) (h3 : stop.toNat ≤ roots.size) (h4 : stop.toNat ≤ logp.size) :
    ByteArray :=
  if hi : i < stop then
    have hlt := USize.lt_iff_toNat_lt.mp hi
    let w := roots.uget i (by omega)
    let t := stride2 s len (root1 w).toUSize (root2 w).toUSize (prime.uget i (by omega)).toUSize
      (logp.uget i (by omega)) hs (cnt.uget i (by omega)).toUSize
    sieveMed prime cnt roots logp t len (by rw [size_stride2]; exact hs) (i + 1) stop h1 h2 h3 h4
  else s
termination_by stop.toNat - i.toNat
decreasing_by rw [usize_succ_of_lt i stop hi]; omega

/-- Gray-code switch for the primes in `[i, stop)` below the interval length:
both roots move by `±δ`, then the prime is sieved at the new roots. -/
def switchMed (pdc : Array Nat) (logp : ByteArray) (add : Bool)
    (roots : Array Nat) (s : ByteArray) (len : USize) (hs : len.toNat < s.size) (i stop : USize)
    (h1 : stop.toNat ≤ pdc.size) (h4 : stop.toNat ≤ logp.size) (h5 : stop.toNat ≤ roots.size) :
    Array Nat × ByteArray :=
  if hi : i < stop then
    have hlt := USize.lt_iff_toNat_lt.mp hi
    let c := (pdc.uget i (by omega)).toUInt64
    let p := (c &&& 0x1FFFFF).toUInt32
    let d := ((c >>> 21) &&& 0x1FFFFF).toUInt32
    let w := roots.uget i (by omega)
    let a := moveRoot add (root1 w) d p
    let b := moveRoot add (root2 w) d p
    let t := stride2 s len a.toUSize b.toUSize p.toUSize (logp.uget i (by omega)) hs
      (c >>> 42).toUSize
    let roots' := roots.uset i (packRoots a b) (by omega)
    switchMed pdc logp add roots' t len (by rw [size_stride2]; exact hs) (i + 1) stop
      h1 h4 (by simp [roots']; omega)
  else (roots, s)
termination_by stop.toNat - i.toNat
decreasing_by rw [usize_succ_of_lt i stop hi]; omega

/-- Gray-code switch for primes beyond the interval: one update per root, misses
spread over the trash bytes (a branch on `a < len` mispredicts for primes not
much larger than the interval: 6.6 ns per prime at 80 digits). -/
def switchBig (pdc : Array Nat) (logp : ByteArray) (add : Bool) (roots : Array Nat)
    (s : ByteArray) (len : USize) (hl : len.toNat < 2 ^ 31) (hs : len.toNat + 64 ≤ s.size)
    (i stop : USize) (h1 : stop.toNat ≤ pdc.size)
    (h4 : stop.toNat ≤ logp.size) (h5 : stop.toNat ≤ roots.size) : Array Nat × ByteArray :=
  if hi : i < stop then
    have hlt := USize.lt_iff_toNat_lt.mp hi
    let c := (pdc.uget i (by omega)).toUInt64
    let p := (c &&& 0x1FFFFF).toUInt32
    let d := ((c >>> 21) &&& 0x1FFFFF).toUInt32
    let w := roots.uget i (by omega)
    let a := moveRoot add (root1 w) d p
    let b := moveRoot add (root2 w) d p
    let lg := logp.uget i (by omega)
    let t := hitSpread s len a.toUSize lg hl hs
    let t := hitSpread t len b.toUSize lg hl (by rw [size_hitSpread]; exact hs)
    let roots' := roots.uset i (packRoots a b) (by omega)
    switchBig pdc logp add roots' t len hl (by rw [size_hitSpread, size_hitSpread]; exact hs)
      (i + 1) stop h1 h4 (by simp [roots']; omega)
  else (roots, s)
termination_by stop.toNat - i.toNat
decreasing_by rw [usize_succ_of_lt i stop hi]; omega

/-- Roots of the unsieved small primes `[i, stop)` move without sieving. -/
def moveTiny (pdc : Array Nat) (add : Bool) (roots : Array Nat) (i stop : USize)
    (h1 : stop.toNat ≤ pdc.size) (h5 : stop.toNat ≤ roots.size) : Array Nat :=
  if hi : i < stop then
    have hlt := USize.lt_iff_toNat_lt.mp hi
    let c := (pdc.uget i (by omega)).toUInt64
    let p := (c &&& 0x1FFFFF).toUInt32
    let d := ((c >>> 21) &&& 0x1FFFFF).toUInt32
    let w := roots.uget i (by omega)
    let roots' := roots.uset i (packRoots (moveRoot add (root1 w) d p) (moveRoot add (root2 w) d p))
      (by omega)
    moveTiny pdc add roots' (i + 1) stop h1 (by simp [roots']; omega)
  else roots
termination_by stop.toNat - i.toNat
decreasing_by rw [usize_succ_of_lt i stop hi]; omega

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
16 threads on the balanced semiprimes of the dataset (`scripts/tune_siqs.py`). Re-tuned at
68-80 digits once relations were collected from a task queue (590f68c), on the two dataset
semiprimes and eight fresh ones per size (one run each, totals in seconds): 68 digits
5500/65536 10.60, 7000/65536 9.88, 7000/98304 9.56; 72 digits 6000/65536 20.53 (larger
bases no better); 76 digits 7000/65536 54.08, 10000/98304 46.71; 80 digits (six numbers)
12000/131072 57.68, 20000/196608 52.88. Times vary up to twofold between numbers of one
size, so two numbers do not decide. -/
def paramTable : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  [(20, 60, 2048, 20, 0, 10), (25, 100, 4096, 30, 0, 10), (30, 150, 8192, 30, 0, 10),
   (35, 220, 16384, 40, 0, 10), (40, 300, 32768, 60, 0, 8), (44, 500, 32768, 60, 0, 14),
   (48, 800, 16384, 60, 0, 10), (52, 1200, 32768, 60, 0, 10), (56, 1800, 65536, 60, 0, 10),
   (60, 2400, 32768, 80, 0, 12), (64, 5500, 65536, 80, 0, 14), (68, 7000, 98304, 80, 0, 16),
   (72, 6000, 65536, 80, 16, 12), (76, 10000, 98304, 80, 16, 12), (80, 20000, 196608, 90, 16, 10),
   (85, 17000, 131072, 100, 16, 10), (90, 22000, 196608, 110, 16, 10),
   (95, 30000, 196608, 120, 16, 10), (100, 40000, 262144, 150, 16, 10),
   (110, 60000, 262144, 150, 16, 10)]

def chooseParams (digits : Nat) : Params :=
  let e := (paramTable.find? fun e => digits ≤ e.1).getD
    (paramTable.getLast?.getD (110, 70000, 262144, 150, 16, 12))
  -- from 61 to 80 digits the first 45 factor-base primes are not sieved (one more
  -- bit of slack): balanced semiprimes of 64, 68, 72, 76 and 80 digits, three
  -- interleaved pairs each, 4-12% faster than with 30; no gain at 52-60 digits
  let wide := 61 ≤ digits && digits ≤ 80
  { fbSize := e.2.1, M := e.2.2.1, lpMult := e.2.2.2.1, dlpDiv := e.2.2.2.2.1,
    slack := e.2.2.2.2.2 + (if wide then 1 else 0), spv := if wide then 45 else 30,
    filterSlack := 6, preSlack := 6, smallBound := 16384 }

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
  /-- `lim + 2^31 pinv` (both fit: `lim < 2^31` for `p ≥ 3`), one read per prime. -/
  pl : Array Nat
  /-- `2^64 mod p`, for Montgomery arithmetic modulo `p` with `R = 2^32`. -/
  r2 : Array Nat
  /-- `p + 2^42 ⌈size / p⌉`: the word of a prime with zero delta (see `APoly.pdc`). -/
  pc : Array Nat
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
  -- primes, deltas and counts are packed into 21-bit fields (`APoly.pdc`)
  let keep := (fb.takeWhile (· < 2097152)).size
  let fb := fb.extract 0 keep
  let roots := roots.extract 0 keep
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
  -- trash bytes for clamped updates (the first) and spread misses (all 64)
  let template := ByteArray.mk (Array.replicate (size + 64) bias)
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
                pl := prime.map fun p =>
                  if p < 3 then 0 else ((0xFFFFFFFF : UInt32) / p).toNat + (inv32 p).toNat * 2147483648,
                r2 := fb.map fun p => if p < 3 then 0 else 18446744073709551616 % p,
                pc := fb.map fun p => if p == 0 then 0 else p + ((size + p - 1) / p) * 4398046511104,
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
  /-- Row `l`: for every factor-base prime, `p + 2^21 δ_l + 2^42 ⌈size / p⌉` with
  `δ_l = 2 B_l A⁻¹ mod p` (`B_l A⁻¹` for `Q2` polynomials): the root move of a
  Gray-code step flipping `B_l`, read with the prime and its count in one word
  (`p, δ < 2^21`, `⌈size/p⌉ < 2^21`). Zero delta for the primes of `A` and `kN`. -/
  pdc : Array (Array Nat)
  /-- Packed roots of the first polynomial `B = ∑ B_l`. -/
  roots : Array Nat
  /-- Logarithms with the primes of `A` (and those of `kN`) zeroed. -/
  logp : ByteArray

/-- Montgomery reduction modulo an odd `p < 2^21` with `R = 2^32`: `T R⁻¹ mod p`
for `T < 2^32 p`, `np = -p⁻¹ mod 2^32`. -/
@[inline] def redc32 (T p np : UInt64) : UInt64 :=
  let t := (T + ((T * np) &&& 0xFFFFFFFF) * p) >>> 32
  if t ≥ p then t - p else t

/-- `q mod p` for `q, p < 2^21` (no division when `q < p`). -/
@[inline] def modSmall (q p : UInt64) : UInt64 := if q < p then q else q % p

/-- `sc[k] ← ∏_{j<k} q_j` for `k < s` and `sc[s] ← ∏_{j<s} q_j` (Montgomery form
modulo `p`, `P` the running product). -/
def prefixLoop (qv : Array Nat) (p np r2 : UInt64) (k s : Nat) (P : UInt64) (sc : Array Nat) :
    Array Nat :=
  if k < s then
    let q := redc32 (modSmall qv[k]!.toUInt64 p * r2) p np
    prefixLoop qv p np r2 (k + 1) s (redc32 (P * q) p np) (sc.set! k P.toNat)
  else sc.set! s P.toNat
termination_by s - k

/-- From `k - 1` down to `0`: `sc[j] ← q_j⁻¹` (Montgomery form) from `sc[j] = ∏_{i<j} q_i`
and `inv = (∏_{i<k} q_i)⁻¹` (batch inversion). -/
def backLoop (qv : Array Nat) (p np r2 : UInt64) : Nat → UInt64 → Array Nat → Array Nat
  | 0, _, sc => sc
  | k + 1, inv, sc =>
    let q := redc32 (modSmall qv[k]!.toUInt64 p * r2) p np
    backLoop qv p np r2 k (redc32 (inv * q) p np)
      (sc.set! k (redc32 (inv * sc[k]!.toUInt64) p np).toNat)

/-- The packed rows of one prime and `B A⁻¹ mod p`. -/
structure RowsOut where
  pdc : Array (Array Nat)
  bq : UInt64

/-- For `k < s`: `γ_k q_k⁻¹ mod p` from `sc[k] = q_k⁻¹` (Montgomery form), summed
into `bq` (`= B A⁻¹`, since `B_k A⁻¹ = γ_k q_k⁻¹`), and the delta `2 γ_k q_k⁻¹`
(`γ_k q_k⁻¹` for `Q2`) written into row `k` at index `i` with `base = p + 2^42 cnt`. -/
def rowsLoop (gam sc : Array Nat) (p np base : UInt64) (q2 : Bool) (i : Nat) (k s : Nat)
    (pdc : Array (Array Nat)) (bq : UInt64) : RowsOut :=
  if k < s then
    let b := redc32 (modSmall gam[k]!.toUInt64 p * sc[k]!.toUInt64) p np
    let d := if q2 then b else (let d := 2 * b; if d ≥ p then d - p else d)
    let pdc := pdc.modify k fun row => row.set! i (base ||| (d <<< 21)).toNat
    let bq := bq + b
    rowsLoop gam sc p np base q2 i (k + 1) s pdc (if bq ≥ p then bq - p else bq)
  else ⟨pdc, bq⟩
termination_by s - k

/-- The packed rows and first roots of a new `A`. -/
structure PolyRows where
  pdc : Array (Array Nat)
  roots : Array Nat
  logp : ByteArray

/-- Deltas and first roots of the factor-base primes `i, …, F - 1` for the `A` with
factors `qv` (multipliers `gam`), in Montgomery arithmetic modulo each prime
(one inverse per prime by Euclid; no division otherwise). The roots solve
`A x + B ≡ ±t` (`2 A x + B ≡ ±t` for `Q2`): `x = ±t A⁻¹ - B A⁻¹` (halved for `Q2`). -/
def primeLoop (ctx : Ctx) (qv gam : Array Nat) (s : Nat) (i F : Nat) (sc : Array Nat)
    (acc : PolyRows) : PolyRows :=
  if i < F then
    let t := ctx.sqrtN[i]!.toUInt64
    if t == 0 then
      -- primes of `kN`: not sieved (trial divided directly)
      primeLoop ctx qv gam s (i + 1) F sc { acc with logp := acc.logp.set! i 0 }
    else
      let p := ctx.fb[i]!.toUInt64
      let np := (-(ctx.pinv[i]!)).toUInt64
      let r2 := ctx.r2[i]!.toUInt64
      let sc := prefixLoop qv p np r2 0 s (redc32 r2 p np) sc
      let a := redc32 sc[s]!.toUInt64 p np
      if a == 0 then
        -- primes of `A`: not sieved
        primeLoop ctx qv gam s (i + 1) F sc { acc with logp := acc.logp.set! i 0 }
      else
        let ainv := invModU a p
        let sc := backLoop qv p np r2 s (redc32 (ainv * r2) p np) sc
        let out := rowsLoop gam sc p np ctx.pc[i]!.toUInt64 ctx.q2 i 0 s acc.pdc 0
        let ta := ainv * t % p
        let bq := out.bq
        let x1 := ta + p - bq
        let x1 := if x1 ≥ p then x1 - p else x1
        let x2 := 2 * p - ta - bq
        let x2 := if x2 ≥ p then x2 - p else x2
        let x2 := if x2 ≥ p then x2 - p else x2
        -- `Q2`: halve modulo `p`
        let x1 := if ctx.q2 then (x1 + (x1 &&& 1) * p) >>> 1 else x1
        let x2 := if ctx.q2 then (x2 + (x2 &&& 1) * p) >>> 1 else x2
        let mm := ctx.mmod[i]!.toUInt64
        let j1 := x1 + mm
        let j2 := x2 + mm
        let r := packRoots (if j1 ≥ p then j1 - p else j1).toUInt32 (if j2 ≥ p then j2 - p else j2).toUInt32
        primeLoop ctx qv gam s (i + 1) F sc
          { pdc := out.pdc, roots := acc.roots.set! i r, logp := acc.logp }
  else acc
termination_by F - i

/-- Build an `A`, the `B_l`, the deltas and the first roots. Everything modulo the
factor-base primes is computed with machine words from the `q_l` and the `γ_l`
(`B_l = (A/q_l) γ_l`, so `B_l A⁻¹ = γ_l q_l⁻¹`), not from the big numbers. -/
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
  let qv : Array Nat := qs.map fun i => ctx.fb[i]!
  let F := ctx.fb.size
  let rows := primeLoop ctx qv gam s 1 F (Array.replicate (s + 1) 0)
    { pdc := Array.replicate s ctx.pc, roots := Array.replicate F 0, logp := ctx.logp }
  return some { A := A, qs := qs, Bl := Bl, pdc := rows.pdc, roots := rows.roots,
                logp := rows.logp.set! 0 0 }

/-! ## Cofactors below `2^51`

Double-large-prime cofactors fit in 51 bits, where `a · b mod m` can be computed
with machine words: the quotient is estimated in floating point (53-bit
mantissa, so it is off by at most one) and the remainder is corrected in
wrapping 64-bit arithmetic. -/

/-- `a · b mod m` for `a, b < m ≤ 2^51`, with `minv ≈ 1/m`: `a`, `b` are exact
doubles, and the three roundings of the estimated quotient (product, `1/m`,
quotient), of relative error `2^-53` each, leave it within `3 · 2^-53 · ab/m < 1`
of `ab/m < 2^51`. So it is off by at most one, and the true remainder lies in
`[-m, 2m)`: one correction each way, by masks rather than branches (they are
taken at random; the branches cost a third of `uecm`'s time). -/
@[inline] def mulmod50 (a b m : UInt64) (minv : Float) : UInt64 :=
  let q := ((a.toFloat * b.toFloat) * minv).toUInt64
  let r := a * b - q * m
  -- the sign is the top bit
  let r := r + (m &&& -(r >>> 63))
  let t := r - m
  t + (m &&& -(t >>> 63))

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

/-! ### ECM for double-large-prime cofactors

Splitting a cofactor of 40 to 52 bits into two primes above the factor-base
bound, rho's steps form one dependency chain (a modular square of some 30
cycles each), while the operations of an elliptic curve are largely independent
of one another. ECM with tiny bounds — stage 1 to `B1` by the Montgomery ladder,
stage 2 to `B2` by baby steps `j ⊥ 60` and giant steps `60 m` — on Suyama curves
(group orders divisible by 12) needs about three curves for such factors. All
arithmetic is `mulmod50` on machine words; every result is a gcd with `m`,
checked by the caller. -/

/-- `a + b mod m` for `a, b < m < 2^62`, by the sign of `a + b - m` (masks rather
than comparisons: clang 19's SLP vectorizer crashes on the compare-and-select
form of `uecmLadder` at `-march=native`). -/
@[inline] def addM (a b m : UInt64) : UInt64 :=
  let t := a + b - m
  t + (m &&& -(t >>> 63))

/-- `a - b mod m` for `a, b < m < 2^62`. -/
@[inline] def subM (a b m : UInt64) : UInt64 :=
  let t := a - b
  t + (m &&& -(t >>> 63))

/-- `2^dᵢ mod mᵢ` for four lanes at once, left to right over the bits `k - 1, …, 0`
of the exponents (a squaring, then a branch-free doubling where the bit is set):
the four chains of squarings overlap. -/
def pow2x4 (m0 m1 m2 m3 d0 d1 d2 d3 : UInt64) (f0 f1 f2 f3 : Float) :
    Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 × UInt64 × UInt64 × UInt64
  | 0, x0, x1, x2, x3 => (x0, x1, x2, x3)
  | k + 1, x0, x1, x2, x3 =>
    let s := k.toUInt64
    let y0 := mulmod50 x0 x0 m0 f0
    let y1 := mulmod50 x1 x1 m1 f1
    let y2 := mulmod50 x2 x2 m2 f2
    let y3 := mulmod50 x3 x3 m3 f3
    let b0 := -((d0 >>> s) &&& 1)
    let b1 := -((d1 >>> s) &&& 1)
    let b2 := -((d2 >>> s) &&& 1)
    let b3 := -((d3 >>> s) &&& 1)
    pow2x4 m0 m1 m2 m3 d0 d1 d2 d3 f0 f1 f2 f3 k
      (y0 ^^^ ((y0 ^^^ addM y0 y0 m0) &&& b0)) (y1 ^^^ ((y1 ^^^ addM y1 y1 m1) &&& b1))
      (y2 ^^^ ((y2 ^^^ addM y2 y2 m2) &&& b2)) (y3 ^^^ ((y3 ^^^ addM y3 y3 m3) &&& b3))

/-- `sprp2` of four odd moduli `3 < mᵢ < 2^51` at once (`pow2x4`): bit `i` of the
result is set when `mᵢ` is a strong probable prime to base 2. -/
def sprp2x4 (m0 m1 m2 m3 : UInt64) : UInt64 :=
  let f0 := 1.0 / m0.toFloat
  let f1 := 1.0 / m1.toFloat
  let f2 := 1.0 / m2.toFloat
  let f3 := 1.0 / m3.toFloat
  -- mᵢ - 1 = 2^tᵢ · dᵢ with dᵢ odd
  let t0 := ((m0 - 1) &&& (-(m0 - 1))).toNat.log2
  let t1 := ((m1 - 1) &&& (-(m1 - 1))).toNat.log2
  let t2 := ((m2 - 1) &&& (-(m2 - 1))).toNat.log2
  let t3 := ((m3 - 1) &&& (-(m3 - 1))).toNat.log2
  let d0 := (m0 - 1) >>> t0.toUInt64
  let d1 := (m1 - 1) >>> t1.toUInt64
  let d2 := (m2 - 1) >>> t2.toUInt64
  let d3 := (m3 - 1) >>> t3.toUInt64
  let (x0, x1, x2, x3) := pow2x4 m0 m1 m2 m3 d0 d1 d2 d3 f0 f1 f2 f3
    ((d0 ||| d1 ||| d2 ||| d3).toNat.log2 + 1) 1 1 1 1
  let ok (m x : UInt64) (f : Float) (t : Nat) : UInt64 :=
    if x == 1 || x == m - 1 || sprp2.squares m x f t then 1 else 0
  ok m0 x0 f0 t0 ||| (ok m1 x1 f1 t1 <<< 1) ||| (ok m2 x2 f2 t2 <<< 2) ||| (ok m3 x3 f3 t3 <<< 3)

/-- The Montgomery ladder over `bits[i-1], …, bits[0]` (stage 1 of `uecmCurve`)
from `(X0 : Z0) = [k]P`, `(X1 : Z1) = [k+1]P` for `P = (x0 : 1)` on the curve
`a24`; the bit selects (without branching) which point is doubled. -/
def uecmLadder (m a24 x0 : UInt64) (mf : Float) (bits : ByteArray) :
    Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 × UInt64
  | 0, X0, Z0, _, _ => (X0, Z0)
  | i + 1, X0, Z0, X1, Z1 =>
    -- all ones when the bit is set
    let sel := -(bits.get! i).toUInt64
    let Ax := X0 ^^^ ((X0 ^^^ X1) &&& sel)
    let Az := Z0 ^^^ ((Z0 ^^^ Z1) &&& sel)
    let p := addM Ax Az m
    let q := subM Ax Az m
    let sp := mulmod50 p p m mf
    let sq := mulmod50 q q m mf
    let t := subM sp sq m
    let DX := mulmod50 sp sq m mf
    let DZ := mulmod50 t (addM sq (mulmod50 a24 t m mf) m) m mf
    let u := mulmod50 (subM X1 Z1 m) (addM X0 Z0 m) m mf
    let w := mulmod50 (addM X1 Z1 m) (subM X0 Z0 m) m mf
    let e := addM u w m
    let f := subM u w m
    let SX := mulmod50 e e m mf
    let SZ := mulmod50 x0 (mulmod50 f f m mf) m mf
    uecmLadder m a24 x0 mf bits i (DX ^^^ ((DX ^^^ SX) &&& sel)) (DZ ^^^ ((DZ ^^^ SZ) &&& sel))
      (SX ^^^ ((SX ^^^ DX) &&& sel)) (SZ ^^^ ((SZ ^^^ DZ) &&& sel))

/-- `[2]P` for `P = (X : Z)`. -/
@[inline] def uecmDbl (m a24 : UInt64) (mf : Float) (X Z : UInt64) : UInt64 × UInt64 :=
  let p := addM X Z m
  let q := subM X Z m
  let sp := mulmod50 p p m mf
  let sq := mulmod50 q q m mf
  let t := subM sp sq m
  (mulmod50 sp sq m mf, mulmod50 t (addM sq (mulmod50 a24 t m mf) m) m mf)

/-- `P + Q` from `P - Q = (Xd : Zd)`. -/
@[inline] def uecmAdd (m : UInt64) (mf : Float) (X1 Z1 X0 Z0 Xd Zd : UInt64) : UInt64 × UInt64 :=
  let u := mulmod50 (subM X1 Z1 m) (addM X0 Z0 m) m mf
  let w := mulmod50 (addM X1 Z1 m) (subM X0 Z0 m) m mf
  let e := addM u w m
  let f := subM u w m
  (mulmod50 Zd (mulmod50 e e m mf) m mf, mulmod50 Xd (mulmod50 f f m mf) m mf)

/-- The stage-1 exponent `∏ q^⌊log_q B1⌋` over the primes `q ≤ B1`, least
significant bit first. -/
def uecmBits (b1 : Nat) : ByteArray := Id.run do
  let mut k := 1
  for q in primesUpTo b1 do
    let mut e := q
    while e * q ≤ b1 do e := e * q
    k := k * e
  let mut out := ByteArray.empty
  while k > 0 do
    out := out.push (if k % 2 == 1 then 1 else 0)
    k := k / 2
  return out

/-- The babies of stage 2: `j < 30` coprime to `60`. -/
def uecmBabies : Array Nat := #[1, 7, 11, 13, 17, 19, 23, 29]

/-- The stage-2 schedule for `(B1, B2]` with giant steps `60 m`, `m = 1 … mmax`:
for giant `m` and baby `i`, whether `60 m - j_i` or `60 m + j_i` is a prime of
`(B1, B2]` (each prime covered once). -/
def uecmSched (b1 b2 : Nat) : Nat × ByteArray := Id.run do
  let mmax := b2 / 60 + 1
  let isP := (primesUpTo (60 * mmax + 60)).foldl (fun s p => s.insert p) (Std.HashSet.emptyWithCapacity 1024)
  let mut done : Std.HashSet Nat := {}
  let mut out := ByteArray.empty
  for m in [1:mmax + 1] do
    for j in uecmBabies do
      let lo := 60 * m - j
      let hi := 60 * m + j
      let hit (x : Nat) := x > b1 && x ≤ b2 && isP.contains x && !done.contains x
      let take := hit lo || hit hi
      if hit lo then done := done.insert lo
      if hit hi then done := done.insert hi
      out := out.push (if take then 1 else 0)
  return (mmax, out)

/-- A plan of `uecm`: the stage-1 bits, the last giant step and the stage-2 schedule. -/
def uecmMkPlan (b1 b2 : Nat) : ByteArray × Nat × ByteArray :=
  let (mm, sch) := uecmSched b1 b2
  (uecmBits b1, mm, sch)

set_option compiler.extract_closed false in
/-- The plan of `uecm`, built on first use: `B1 = 70`, `B2 = 25 B1` (on 2000
cofactors of the 100-digit number field sieve, two primes of `[650000, 2^26)`:
13 µs per split; `B1` 50 to 105 with `B2` 25 or 50 times `B1` all within 13 to
17 µs, 85 (the earlier choice) 14 µs). -/
def uecmPlan : Thunk (ByteArray × Nat × ByteArray) :=
  Thunk.mk fun _ => uecmMkPlan 70 1750

/-- The eight baby points `[j]Q`, `j ∈ uecmBabies`, as words. -/
structure Babies where
  x0 : UInt64
  z0 : UInt64
  x1 : UInt64
  z1 : UInt64
  x2 : UInt64
  z2 : UInt64
  x3 : UInt64
  z3 : UInt64
  x4 : UInt64
  z4 : UInt64
  x5 : UInt64
  z5 : UInt64
  x6 : UInt64
  z6 : UInt64
  x7 : UInt64
  z7 : UInt64

/-- `acc · ∏ (X_G Z_j - X_j Z_G)` over the scheduled babies of one giant step
(`base` its offset in the schedule): the eight factors (`1` where not scheduled)
multiplied as a tree, so that `acc` waits for one product per giant step rather
than one per prime. -/
@[inline] def uecmPairs (m : UInt64) (mf : Float) (bb : Babies) (sch : ByteArray)
    (base : Nat) (XG ZG acc : UInt64) : UInt64 :=
  let t (f : UInt8) (x z : UInt64) : UInt64 :=
    if f == 1 then subM (mulmod50 XG z m mf) (mulmod50 x ZG m mf) m else 1
  let p01 := mulmod50 (t (sch.get! base) bb.x0 bb.z0) (t (sch.get! (base + 1)) bb.x1 bb.z1) m mf
  let p23 := mulmod50 (t (sch.get! (base + 2)) bb.x2 bb.z2) (t (sch.get! (base + 3)) bb.x3 bb.z3) m mf
  let p45 := mulmod50 (t (sch.get! (base + 4)) bb.x4 bb.z4) (t (sch.get! (base + 5)) bb.x5 bb.z5) m mf
  let p67 := mulmod50 (t (sch.get! (base + 6)) bb.x6 bb.z6) (t (sch.get! (base + 7)) bb.x7 bb.z7) m mf
  mulmod50 acc (mulmod50 (mulmod50 p01 p23 m mf) (mulmod50 p45 p67 m mf) m mf) m mf

/-- Stage 2 over the giants `G_k = [60 k]Q`, `k = …, mmax` (`(Xp : Zp)` the giant
before, `(X1 : Z1) = [60]Q`). -/
def uecmGiants (m : UInt64) (mf : Float) (bb : Babies) (sch : ByteArray)
    (X1 Z1 : UInt64) (mmax : Nat) : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → Nat → UInt64
  | 0, _, _, _, _, acc, _ => acc
  | fuel + 1, Xp, Zp, Xc, Zc, acc, k =>
    if k > mmax then acc
    else
      let acc := uecmPairs m mf bb sch (8 * (k - 1)) Xc Zc acc
      let (Xn, Zn) := uecmAdd m mf Xc Zc X1 Z1 Xp Zp
      uecmGiants m mf bb sch X1 Z1 mmax fuel Xc Zc Xn Zn acc (k + 1)

/-- One curve (Suyama parameter `σ`) on `m < 2^51`: the gcd of `m` with the
product of the stage-1 `Z` and the stage-2 factors (`1` or `m` when it found
nothing; one gcd per curve). -/
def uecmCurveP (plan : ByteArray × Nat × ByteArray) (m σ : UInt64) (mf : Float) : UInt64 :=
  let (bits, mmax, sch) := plan
  -- Suyama: u = σ² - 5, v = 4σ, x₀ = u³/v³, a24 = (v - u)³ (3u + v) / (16 u³ v)
  let u := subM (mulmod50 σ σ m mf) 5 m
  let v := mulmod50 4 σ m mf
  let u2 := mulmod50 u u m mf
  let u3 := mulmod50 u2 u m mf
  let v2 := mulmod50 v v m mf
  let v3 := mulmod50 v2 v m mf
  -- one inversion: 1 / (16 u³ v⁴)
  let c := mulmod50 (mulmod50 16 u3 m mf) (mulmod50 v3 v m mf) m mf
  let s := invLoop m c 0 1 100
  if s == 0 then gcd64 c m
  else
    let inv := if s < 0 then (s + m.toInt64).toUInt64 else s.toUInt64
    let vmu := subM v u m
    let a24 := mulmod50 (mulmod50 (mulmod50 (mulmod50 vmu vmu m mf) vmu m mf)
      (addM (mulmod50 3 u m mf) v m) m mf) (mulmod50 v3 inv m mf) m mf
    let x0 := mulmod50 (mulmod50 (mulmod50 16 (mulmod50 u3 u3 m mf) m mf) v m mf) inv m mf
    -- stage 1 from the top bit: (P, [2]P), then the ladder over the rest
    let (D2X, D2Z) := uecmDbl m a24 mf x0 1
    let (QX, QZ) := uecmLadder m a24 x0 mf bits (bits.size - 1) x0 1 D2X D2Z
    -- babies: the odd multiples [j]Q, j < 30, by differential additions from [2]Q
    let (X2, Z2) := uecmDbl m a24 mf QX QZ
    let ad (xa za xb zb : UInt64) := uecmAdd m mf xa za X2 Z2 xb zb
    let (X3, Z3) := uecmAdd m mf X2 Z2 QX QZ QX QZ
    let (X5, Z5) := ad X3 Z3 QX QZ
    let (X7, Z7) := ad X5 Z5 X3 Z3
    let (X9, Z9) := ad X7 Z7 X5 Z5
    let (X11, Z11) := ad X9 Z9 X7 Z7
    let (X13, Z13) := ad X11 Z11 X9 Z9
    let (X15, Z15) := ad X13 Z13 X11 Z11
    let (X17, Z17) := ad X15 Z15 X13 Z13
    let (X19, Z19) := ad X17 Z17 X15 Z15
    let (X21, Z21) := ad X19 Z19 X17 Z17
    let (X23, Z23) := ad X21 Z21 X19 Z19
    let (X25, Z25) := ad X23 Z23 X21 Z21
    let (X27, Z27) := ad X25 Z25 X23 Z23
    let (X29, Z29) := ad X27 Z27 X25 Z25
    let bb : Babies := ⟨QX, QZ, X7, Z7, X11, Z11, X13, Z13, X17, Z17, X19, Z19, X23, Z23, X29, Z29⟩
    -- [30]Q = [2][15]Q, [60]Q = [2][30]Q, [120]Q = [2][60]Q
    let (X30, Z30) := uecmDbl m a24 mf X15 Z15
    let (X60, Z60) := uecmDbl m a24 mf X30 Z30
    let (X120, Z120) := uecmDbl m a24 mf X60 Z60
    -- the stage-1 Z starts the product (a factor found by stage 1 survives it)
    let acc := uecmPairs m mf bb sch 0 X60 Z60 QZ
    let acc := uecmGiants m mf bb sch X60 Z60 mmax (mmax + 1) X60 Z60 X120 Z120 acc 2
    gcd64 acc m

/-! #### Two curves at once

A curve is latency-bound (each ladder step waits for three products in a row),
so two curves of the same `m` in one loop overlap their chains: about the cost
of one and a half curves for two. -/

/-- `uecmLadder` on two curves (`a24 = a`, base `x` and `a24 = b`, base `y`). -/
def uecmLadder2 (m a x b y : UInt64) (mf : Float) (bits : ByteArray) :
    Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
      UInt64 × UInt64 × UInt64 × UInt64
  | 0, X0, Z0, _, _, Y0, W0, _, _ => (X0, Z0, Y0, W0)
  | i + 1, X0, Z0, X1, Z1, Y0, W0, Y1, W1 =>
    let sel := -(bits.get! i).toUInt64
    -- lane a: (X0 : Z0), (X1 : Z1)
    let Ax := X0 ^^^ ((X0 ^^^ X1) &&& sel)
    let Az := Z0 ^^^ ((Z0 ^^^ Z1) &&& sel)
    -- lane b: (Y0 : W0), (Y1 : W1)
    let By := Y0 ^^^ ((Y0 ^^^ Y1) &&& sel)
    let Bw := W0 ^^^ ((W0 ^^^ W1) &&& sel)
    let p := addM Ax Az m
    let q := subM Ax Az m
    let p' := addM By Bw m
    let q' := subM By Bw m
    let sp := mulmod50 p p m mf
    let sp' := mulmod50 p' p' m mf
    let sq := mulmod50 q q m mf
    let sq' := mulmod50 q' q' m mf
    let t := subM sp sq m
    let t' := subM sp' sq' m
    let DX := mulmod50 sp sq m mf
    let DX' := mulmod50 sp' sq' m mf
    let DZ := mulmod50 t (addM sq (mulmod50 a t m mf) m) m mf
    let DZ' := mulmod50 t' (addM sq' (mulmod50 b t' m mf) m) m mf
    let u := mulmod50 (subM X1 Z1 m) (addM X0 Z0 m) m mf
    let u' := mulmod50 (subM Y1 W1 m) (addM Y0 W0 m) m mf
    let w := mulmod50 (addM X1 Z1 m) (subM X0 Z0 m) m mf
    let w' := mulmod50 (addM Y1 W1 m) (subM Y0 W0 m) m mf
    let e := addM u w m
    let e' := addM u' w' m
    let f := subM u w m
    let f' := subM u' w' m
    let SX := mulmod50 e e m mf
    let SX' := mulmod50 e' e' m mf
    let SZ := mulmod50 x (mulmod50 f f m mf) m mf
    let SZ' := mulmod50 y (mulmod50 f' f' m mf) m mf
    uecmLadder2 m a x b y mf bits i
      (DX ^^^ ((DX ^^^ SX) &&& sel)) (DZ ^^^ ((DZ ^^^ SZ) &&& sel))
      (SX ^^^ ((SX ^^^ DX) &&& sel)) (SZ ^^^ ((SZ ^^^ DZ) &&& sel))
      (DX' ^^^ ((DX' ^^^ SX') &&& sel)) (DZ' ^^^ ((DZ' ^^^ SZ') &&& sel))
      (SX' ^^^ ((SX' ^^^ DX') &&& sel)) (SZ' ^^^ ((SZ' ^^^ DZ') &&& sel))

/-- The baby points `[j]Q`, `j ∈ uecmBabies`, of one curve. -/
@[inline] def uecmBabyPts (m a24 : UInt64) (mf : Float) (QX QZ : UInt64) : Babies :=
  let (X2, Z2) := uecmDbl m a24 mf QX QZ
  let ad (xa za xb zb : UInt64) := uecmAdd m mf xa za X2 Z2 xb zb
  let (X3, Z3) := uecmAdd m mf X2 Z2 QX QZ QX QZ
  let (X5, Z5) := ad X3 Z3 QX QZ
  let (X7, Z7) := ad X5 Z5 X3 Z3
  let (X9, Z9) := ad X7 Z7 X5 Z5
  let (X11, Z11) := ad X9 Z9 X7 Z7
  let (X13, Z13) := ad X11 Z11 X9 Z9
  let (X15, Z15) := ad X13 Z13 X11 Z11
  let (X17, Z17) := ad X15 Z15 X13 Z13
  let (X19, Z19) := ad X17 Z17 X15 Z15
  let (X21, Z21) := ad X19 Z19 X17 Z17
  let (X23, Z23) := ad X21 Z21 X19 Z19
  let (X25, Z25) := ad X23 Z23 X21 Z21
  let (X27, Z27) := ad X25 Z25 X23 Z23
  let (X29, Z29) := ad X27 Z27 X25 Z25
  ⟨QX, QZ, X7, Z7, X11, Z11, X13, Z13, X17, Z17, X19, Z19, X23, Z23, X29, Z29⟩

/-- `[15]Q` by the chain of odd multiples (`(X2 : Z2) = [2]Q`). -/
@[inline] def uecmOdd15 (m : UInt64) (mf : Float) (QX QZ X2 Z2 : UInt64) : UInt64 × UInt64 :=
  let ad (xa za xb zb : UInt64) := uecmAdd m mf xa za X2 Z2 xb zb
  let (X3, Z3) := uecmAdd m mf X2 Z2 QX QZ QX QZ
  let (X5, Z5) := ad X3 Z3 QX QZ
  let (X7, Z7) := ad X5 Z5 X3 Z3
  let (X9, Z9) := ad X7 Z7 X5 Z5
  let (X11, Z11) := ad X9 Z9 X7 Z7
  let (X13, Z13) := ad X11 Z11 X9 Z9
  ad X13 Z13 X11 Z11

/-- `uecmGiants` on two curves (`acc`, `acc'` their products). -/
def uecmGiants2 (m : UInt64) (mf : Float) (bb bb' : Babies) (sch : ByteArray)
    (X1 Z1 Y1 W1 : UInt64) (mmax : Nat) :
    Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
      UInt64 → UInt64 → Nat → UInt64 × UInt64
  | 0, _, _, _, _, _, _, _, _, acc, acc', _ => (acc, acc')
  | fuel + 1, Xp, Zp, Xc, Zc, Yp, Wp, Yc, Wc, acc, acc', k =>
    if k > mmax then (acc, acc')
    else
      let acc := uecmPairs m mf bb sch (8 * (k - 1)) Xc Zc acc
      let acc' := uecmPairs m mf bb' sch (8 * (k - 1)) Yc Wc acc'
      let (Xn, Zn) := uecmAdd m mf Xc Zc X1 Z1 Xp Zp
      let (Yn, Wn) := uecmAdd m mf Yc Wc Y1 W1 Yp Wp
      uecmGiants2 m mf bb bb' sch X1 Z1 Y1 W1 mmax fuel Xc Zc Xn Zn Yc Wc Yn Wn acc acc' (k + 1)

/-- Suyama's curve `σ` on `m`: `(a24, x₀)` from `(u³, v³, 16 u³ v⁴)` and the
inverse `inv` of the last. -/
@[inline] def uecmSuyama (m : UInt64) (mf : Float) (u v u3 v3 inv : UInt64) : UInt64 × UInt64 :=
  let vmu := subM v u m
  let a24 := mulmod50 (mulmod50 (mulmod50 (mulmod50 vmu vmu m mf) vmu m mf)
    (addM (mulmod50 3 u m mf) v m) m mf) (mulmod50 v3 inv m mf) m mf
  let x0 := mulmod50 (mulmod50 (mulmod50 16 (mulmod50 u3 u3 m mf) m mf) v m mf) inv m mf
  (a24, x0)

/-- The curves `σ` and `σ + 1` at once (one inversion for both): a gcd of `m`
with one curve's product (`1` or `m` when neither found a proper factor). -/
def uecmCurve2P (plan : ByteArray × Nat × ByteArray) (m σ : UInt64) (mf : Float) : UInt64 :=
  let (bits, mmax, sch) := plan
  let σ' := σ + 1
  let u := subM (mulmod50 σ σ m mf) 5 m
  let v := mulmod50 4 σ m mf
  let u' := subM (mulmod50 σ' σ' m mf) 5 m
  let v' := mulmod50 4 σ' m mf
  let u3 := mulmod50 (mulmod50 u u m mf) u m mf
  let v3 := mulmod50 (mulmod50 v v m mf) v m mf
  let u3' := mulmod50 (mulmod50 u' u' m mf) u' m mf
  let v3' := mulmod50 (mulmod50 v' v' m mf) v' m mf
  let c := mulmod50 (mulmod50 16 u3 m mf) (mulmod50 v3 v m mf) m mf
  let c' := mulmod50 (mulmod50 16 u3' m mf) (mulmod50 v3' v' m mf) m mf
  -- one inversion of c c' gives both inverses
  let s := invLoop m (mulmod50 c c' m mf) 0 1 100
  if s == 0 then
    let g := gcd64 c m
    if g != 1 then g else gcd64 c' m
  else
    let inv := if s < 0 then (s + m.toInt64).toUInt64 else s.toUInt64
    let (a, x) := uecmSuyama m mf u v u3 v3 (mulmod50 c' inv m mf)
    let (b, y) := uecmSuyama m mf u' v' u3' v3' (mulmod50 c inv m mf)
    let (D2X, D2Z) := uecmDbl m a mf x 1
    let (D2Y, D2W) := uecmDbl m b mf y 1
    let (QX, QZ, RX, RZ) :=
      uecmLadder2 m a x b y mf bits (bits.size - 1) x 1 D2X D2Z y 1 D2Y D2W
    let bb := uecmBabyPts m a mf QX QZ
    let bb' := uecmBabyPts m b mf RX RZ
    -- [60]Q from [15]Q (the eighth odd multiple is not a baby: recompute it)
    let (X2, Z2) := uecmDbl m a mf QX QZ
    let (Y2, W2) := uecmDbl m b mf RX RZ
    let (X15, Z15) := uecmOdd15 m mf QX QZ X2 Z2
    let (Y15, W15) := uecmOdd15 m mf RX RZ Y2 W2
    let (X30, Z30) := uecmDbl m a mf X15 Z15
    let (Y30, W30) := uecmDbl m b mf Y15 W15
    let (X60, Z60) := uecmDbl m a mf X30 Z30
    let (Y60, W60) := uecmDbl m b mf Y30 W30
    let (X120, Z120) := uecmDbl m a mf X60 Z60
    let (Y120, W120) := uecmDbl m b mf Y60 W60
    let acc := uecmPairs m mf bb sch 0 X60 Z60 QZ
    let acc' := uecmPairs m mf bb' sch 0 Y60 W60 RZ
    let (acc, acc') := uecmGiants2 m mf bb bb' sch X60 Z60 Y60 W60 mmax (mmax + 1)
      X60 Z60 X120 Z120 Y60 W60 Y120 W120 acc acc' 2
    let g := gcd64 acc m
    if g != 1 && g != m then g else gcd64 acc' m

/-- One curve with the standard plan. -/
def uecmCurve (m σ : UInt64) (mf : Float) : UInt64 := uecmCurveP uecmPlan.get m σ mf

/-- A factor of a composite `u < 2^51` from up to `curves` curves of `plan` (`0` if none). -/
def uecmP (plan : ByteArray × Nat × ByteArray) (u : UInt64) (curves : Nat) : UInt64 := go 6 curves
where
  go (σ : UInt64) : Nat → UInt64
    | 0 => 0
    | k + 1 =>
      let g := uecmCurveP plan u σ (1.0 / u.toFloat)
      if g != 1 && g != u then g else go (σ + 1) k

/-- `uecmP` with the standard plan. -/
def uecm (u : UInt64) (curves : Nat) : UInt64 := uecmP uecmPlan.get u curves

/-- `uecmP` two curves at a time (`pairs` pairs). -/
def uecm2P (plan : ByteArray × Nat × ByteArray) (u : UInt64) (pairs : Nat) : UInt64 := go 6 pairs
where
  go (σ : UInt64) : Nat → UInt64
    | 0 => 0
    | k + 1 =>
      let g := uecmCurve2P plan u σ (1.0 / u.toFloat)
      if g != 1 && g != u then g else go (σ + 2) k

/-- `uecm2P` with the standard plan. -/
def uecm2 (u : UInt64) (pairs : Nat) : UInt64 := uecm2P uecmPlan.get u pairs

/-- SQUFOF as a last resort (kept in a single call site so that it is only
evaluated when needed). -/
@[noinline] def squfofFactor (u : Nat) : Nat := ((SQUFOF.race u).map (·.val)).getD 0

/-- A factor of a composite `u` (`0` if none was found): ECM with tiny bounds
(`uecm`, up to 32 curves) for `u < 2^51`, then rho; on 2000 products of two
primes of 19 to 26 bits, 25 µs against 55 µs for rho alone (14 µs and 14 µs
since the corrections of `mulmod50` are branch-free, on 2000 cofactors of the
100-digit number field sieve: two primes of `[lim, 2^lpb)`, 39 to 51 bits). -/
def cofactorFactor (u : Nat) : Nat :=
  -- Brent's rho finds a factor `p ≤ u^(1/2)` after about `1.25 √p ≤ 1.25 u^(1/4)`
  -- steps: a budget of `8 u^(1/4)` (and at least 2000) rarely gives up early
  let iters := (max 2000 (8 * iroot u 4)).toUInt64
  -- `u >>> 51 == 0` rather than `u < 2 ^ 51`: `Nat` literals above `2^32` are
  -- parsed from their digits at every use
  let g := if u >>> 51 == 0 then
      let g := uecm u.toUInt64 32
      if g != 0 then g else
      let g := rho50 u.toUInt64 1 iters
      if g != 0 then g else rho50 u.toUInt64 3 iters
    else 0
  if g != 0 then g.toNat else squfofFactor u

/-- Split a double-large-prime cofactor `u` into two primes below `lp` (a base-2
probable-prime screen first). -/
def splitCofactor (u lp : Nat) : Option (Nat × Nat) :=
  if u >>> 51 == 0 && u % 2 == 1 && sprp2 u.toUInt64 then none
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
exactly later). Accumulates the indices and their `log8`. `p ∣ j - r` iff
`(j + p - r) p⁻¹ ≤ ⌊(2^32 - 1)/p⌋ (mod 2^32)` (Granlund–Montgomery; `j + p - r`
is positive, so no comparison of `j` with the root), both roots at once by a
`min` (no branch but the rare hit). -/
def smallTest (logp log8 : ByteArray) (prime : Array UInt32) (pl roots : Array Nat) (j : UInt32)
    (i stop : USize) (h1 : stop.toNat ≤ logp.size) (h2 : stop.toNat ≤ log8.size)
    (h3 : stop.toNat ≤ prime.size) (h4 : stop.toNat ≤ pl.size) (h5 : stop.toNat ≤ roots.size)
    (hits : List Nat) (l : Nat) : List Nat × Nat :=
  if hi : i < stop then
    have hlt := USize.lt_iff_toNat_lt.mp hi
    if logp.uget i (by omega) == 0 then
      smallTest logp log8 prime pl roots j (i + 1) stop h1 h2 h3 h4 h5 hits l
    else
      let w := roots.uget i (by omega)
      let c := (pl.uget i (by omega)).toUInt64
      let q := (c >>> 31).toUInt32
      let jp := j + prime.uget i (by omega)
      if min ((jp - root1 w) * q) ((jp - root2 w) * q) ≤ (c &&& 0x7FFFFFFF).toUInt32 then
        smallTest logp log8 prime pl roots j (i + 1) stop h1 h2 h3 h4 h5 (i.toNat :: hits)
          (l + (log8.uget i (by omega)).toNat)
      else smallTest logp log8 prime pl roots j (i + 1) stop h1 h2 h3 h4 h5 hits l
  else (hits, l)
termination_by stop.toNat - i.toNat
decreasing_by all_goals (rw [usize_succ_of_lt i stop hi]; omega)

/-- `count` clamped steps of the progressions `a, b (+ p)`: record
`pos <<< 24 ||| tag` for every position whose byte is `≥ 128`. The trash byte at
`len` (where clamped positions land) is zero during candidate processing, so a
clamped step never records anything. -/
def walk2 (buf : ByteArray) (len a b p tag : USize) (h : len.toNat < buf.size)
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
      let acc := if va ≥ 128 then acc.push ((ka <<< 24) ||| tag).toNat else acc
      let acc := if vb ≥ 128 then acc.push ((kb <<< 24) ||| tag).toNat else acc
      walk2 buf len (a + p) (b + p) p tag h acc (count - 1)
    else walk2 buf len (a + p) (b + p) p tag h acc (count - 1)
termination_by count.toNat
decreasing_by all_goals exact usize_pred_lt count hc

/-- Walk the primes `[i, stop)` below the interval (skipping zero logarithms). -/
def walkMed (prime cnt : Array UInt32) (logp : ByteArray) (roots : Array Nat) (buf : ByteArray)
    (len : USize) (h : len.toNat < buf.size) (i stop : USize) (h1 : stop.toNat ≤ prime.size)
    (h2 : stop.toNat ≤ cnt.size) (h3 : stop.toNat ≤ logp.size) (h4 : stop.toNat ≤ roots.size)
    (acc : Array Nat) : Array Nat :=
  if hi : i < stop then
    have hlt := USize.lt_iff_toNat_lt.mp hi
    if logp.uget i (by omega) == 0 then
      walkMed prime cnt logp roots buf len h (i + 1) stop h1 h2 h3 h4 acc
    else
      let w := roots.uget i (by omega)
      let acc := walk2 buf len (root1 w).toUSize (root2 w).toUSize (prime.uget i (by omega)).toUSize
        i h acc (cnt.uget i (by omega)).toUSize
      walkMed prime cnt logp roots buf len h (i + 1) stop h1 h2 h3 h4 acc
  else acc
termination_by stop.toNat - i.toNat
decreasing_by all_goals (rw [usize_succ_of_lt i stop hi]; omega)

/-- Primes `[i, stop)` beyond the interval: one look at each root. -/
def checkBig (logp : ByteArray) (roots : Array Nat) (buf : ByteArray) (len : USize)
    (h : len.toNat < buf.size) (i stop : USize) (h3 : stop.toNat ≤ logp.size)
    (h4 : stop.toNat ≤ roots.size) (acc : Array Nat) : Array Nat :=
  if hi : i < stop then
    have hlt := USize.lt_iff_toNat_lt.mp hi
    if logp.uget i (by omega) == 0 then checkBig logp roots buf len h (i + 1) stop h3 h4 acc
    else
      let w := roots.uget i (by omega)
      checkBig logp roots buf len h (i + 1) stop h3 h4
        (walk2 buf len (root1 w).toUSize (root2 w).toUSize 0 i h acc 1)
  else acc
termination_by stop.toNat - i.toNat
decreasing_by all_goals (rw [usize_succ_of_lt i stop hi]; omega)

/-- The first index in `[lo, hi)` of the increasing array `cands` whose entry is
`≥ pos` (binary search; tail recursive, so no loop state is allocated). -/
def findCandGo (cands : Array Nat) (pos : Nat) (lo hi : Nat) : Nat → Nat
  | 0 => lo
  | fuel + 1 =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if cands[mid]! < pos then findCandGo cands pos (mid + 1) hi fuel
      else findCandGo cands pos lo mid fuel
    else lo

/-- Index of `pos` in the increasing array `cands` (`cands.size` if absent). -/
def findCand (cands : Array Nat) (pos : Nat) : Nat :=
  let lo := findCandGo cands pos 0 cands.size 64
  if lo < cands.size && cands[lo]! == pos then lo else cands.size

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

/-- The large primes of a cofactor `u` (`none`: not a relation): `1` and `1` for
`u = 1`, `1` and `u` below the large-prime bound, two primes below it for
composite `u` below the double-large-prime bound. -/
def largePrimes (ctx : Ctx) (u : Nat) : Option (Nat × Nat) :=
  if u == 1 then some (1, 1)
  else if u < ctx.lpBound then some (1, u)
  else if ctx.dlpBound > 0 && u < ctx.dlpBound then splitCofactor u ctx.lpBound
  else none

/-- `w` with every factor `p` divided out. -/
def stripW (p : UInt64) : Nat → UInt64 → UInt64
  | 0, w => w
  | fuel + 1, w => if w % p == 0 then stripW p fuel (w / p) else w

/-- `e + k` for `r = p^k`. -/
def logP (p : UInt64) : Nat → UInt64 → Nat → Nat
  | 0, _, e => e
  | fuel + 1, r, e => if r ≥ p then logP p fuel (r / p) (e + 1) else e

/-- `∏ p⁻¹ mod 2^64` over the primes of `found` times `r` (`p⁻¹ mod 2^64` from
`p⁻¹ mod 2^32` by one Newton step). -/
def invProd (prime pinv : Array UInt32) : List Nat → UInt64 → UInt64
  | [], r => r
  | i :: rest, r =>
    let p := (prime[i]!).toUInt64
    let x := (pinv[i]!).toUInt64
    invProd prime pinv rest (r * (x * (2 - p * x)))

/-- `∏ p` over the primes of `found`, in floating point. -/
def floatProd (prime : Array UInt32) : List Nat → Float → Float
  | [], f => f
  | i :: rest, f => floatProd prime rest (f * (prime[i]!).toUInt64.toFloat)

/-- A cofactor and the exponents found so far. -/
structure Stripped where
  w : UInt64
  exps : List (Nat × Nat)

/-- Divide the further powers of the primes of `found` out of `w` (each divides
`v(x)` once already): exponents `1 + k`. -/
def stripFound (prime : Array UInt32) : List Nat → UInt64 → List (Nat × Nat) → Stripped
  | [], w, exps => ⟨w, exps⟩
  | i :: rest, w, exps =>
    let p := (prime[i]!).toUInt64
    let w' := stripW p 64 w
    let e := if w' == w then 1 else logP p 64 (w / w') 1
    stripFound prime rest w' ((i, e) :: exps)

/-- Divide the powers of the primes `idx[k]`, `k ≥ start`, out of `w`, adding the
exponents found (`one`: also add exponent 1 for every prime, the primes of `A`). -/
def stripIdx (prime : Array UInt32) (idx : Array Nat) (one : Bool) (k : Nat) (w : UInt64)
    (exps : List (Nat × Nat)) : Stripped :=
  if h : k < idx.size then
    let i := idx[k]
    let p := (prime[i]!).toUInt64
    let exps := if one then (i, 1) :: exps else exps
    let w' := stripW p 64 w
    let exps := if w' == w then exps else (i, logP p 64 (w / w') 0) :: exps
    stripIdx prime idx one (k + 1) w' exps
  else ⟨w, exps⟩
termination_by idx.size - k

/-- What `fastCofactor` concludes about a candidate. -/
inductive Cof where
  /-- No conclusion: factor exactly. -/
  | unknown
  /-- Not a relation. -/
  | reject
  /-- The exponents (unsorted, an index may repeat), the cofactor and its large primes. -/
  | accept (exps : List (Nat × Nat)) (u l1 l2 : Nat)

/-- The factorization of `v(x)` in machine words, for a candidate whose
factor-base primes `found` (each dividing `v(x)`; those of `A` and `kN` aside)
are known. `w = |v| / (2^e2 ∏ found)` is an integer, and `|v| mod 2^64`
(`absLow`) gives `w mod 2^(64 - e2) = (|v| / 2^e2) ∏ p⁻¹`, which is `w` itself
when `w < 2^(62 - e2)`; that is checked against the floating-point estimate
`vf / (2^e2 ∏ p)`. The repeated primes and those of `A` and `kN` are then
divided out of `w`, leaving the cofactor. The relation is checked when it is
built (`Relation.mk?`), so a wrong answer here can only lose a relation; most
candidates are rejected here without big-number arithmetic. -/
def fastCofactor (ctx : Ctx) (ap : APoly) (found : List Nat) (absLow : UInt64) (e2 : Nat)
    (vf : Float) : Cof :=
  if e2 ≥ 40 then .unknown else
  let r := invProd ctx.prime ctx.pinv found (absLow >>> e2.toUInt64)
  let wf := vf / (floatProd ctx.prime found (fc 1) * ((1 : UInt64) <<< e2.toUInt64).toFloat)
  let bound : UInt64 := (1 : UInt64) <<< (62 - e2).toUInt64
  if wf ≥ bound.toFloat then .unknown else
  let w0 := r &&& (bound - 1)
  -- consistency with the estimate (a prime of `found` not dividing `v(x)` would break it)
  if (w0.toFloat - wf).abs > wf / fc 1048576 + fc 2 then .unknown else
  let st := stripFound ctx.prime found w0 []
  let st := stripIdx ctx.prime ap.qs true 0 st.w st.exps
  let st := stripIdx ctx.prime ctx.special false 0 st.w st.exps
  let exps := if e2 > 0 then (0, e2) :: st.exps else st.exps
  let u := st.w.toNat
  match largePrimes ctx u with
  | some (l1, l2) => .accept exps u l1 l2
  | none => .reject

/-- The checked relation at position `j` from the exponents and cofactor of
`fastCofactor` (`neg`: the sign of `v(x)`). -/
def relationOf (ctx : Ctx) (ap : APoly) (B : Int) (j : Nat) (neg : Bool) (u : Nat)
    (exps : List (Nat × Nat)) (l1 l2 : Nat) : Option (Found ctx.n ctx.fb) :=
  let x : Int := (j : Int) - (ctx.M : Int)
  let A : Int := ap.A
  let X := ((if ctx.q2 then 2 * A * x + B else A * x + B) % (ctx.n : Int)).toNat
  let sorted := exps.mergeSort (fun a b => a.1 ≤ b.1)
  match Relation.mk? ctx.n ctx.fb X (if ctx.q2 then 2 else 1) u neg sorted with
  | some r => some ⟨r, l1, l2⟩
  | none => none

/-- The lists of medium and big factor-base primes of the candidates: the
progressions of the medium primes are walked once, the roots of the big primes
looked at once. -/
def walkLists (ctx : Ctx) (ap : APoly) (roots : Array Nat) (buf : ByteArray) (cands : Array Nat) :
    Array (List Nat) := Id.run do
  let len : USize := ctx.size.toUSize
  let smallU := ctx.smallEnd.toUSize
  let medU := ctx.medEnd.toUSize
  let FU := ctx.fb.size.toUSize
  let mut recs : Array Nat := #[]
  if h : len.toNat < buf.size ∧ medU.toNat ≤ ctx.prime.size ∧ medU.toNat ≤ ctx.cnt.size ∧
      medU.toNat ≤ ap.logp.size ∧ medU.toNat ≤ roots.size then
    recs := walkMed ctx.prime ctx.cnt ap.logp roots buf len h.1 smallU medU h.2.1 h.2.2.1
      h.2.2.2.1 h.2.2.2.2 recs
  if h : len.toNat < buf.size ∧ FU.toNat ≤ ap.logp.size ∧ FU.toNat ≤ roots.size then
    recs := checkBig ap.logp roots buf len h.1 medU FU h.2.1 h.2.2 recs
  let mut lists : Array (List Nat) := Array.replicate cands.size []
  for r in recs do
    let c := findCand cands (r >>> 24)
    if c < cands.size then lists := lists.modify c ((r &&& 0xFFFFFF) :: ·)
  return lists

/-- All relations from the candidates of one polynomial. -/
def processCands (ctx : Ctx) (ap : APoly) (B C : Int) (roots : Array Nat) (buf : ByteArray)
    (cands : Array Nat) (rels : Array (Found ctx.n ctx.fb)) : Array (Found ctx.n ctx.fb) := Id.run do
  let lists := walkLists ctx ap roots buf cands
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
  let spvU := ctx.spv.toUSize
  let smallU := ctx.smallEnd.toUSize
  for c in [0:cands.size] do
    let j := cands[c]!
    let x := nf j - Mf
    let vs := (Af * x + B2f) * x + Cf
    let vf := vs.abs
    let l8v := if vf < fc 2 then fc 0 else fc 8 * Float.log2 vf
    let x64 := j.toUInt64 - M64
    let v64 := (A64 * x64 + B64) * x64 + C64
    let e2 : Nat := if v64 == 0 then 64 else (v64 &&& (-v64)).toNat.log2
    -- first filter: the power of 2, the unsieved primes (index < spv) by their
    -- roots and the sieved ones through the sieve byte (rounded logarithms, each
    -- prime once), with four bits for rounding and prime powers
    let (tiny, lt) :=
      if h : spvU.toNat ≤ ap.logp.size ∧ spvU.toNat ≤ ctx.log8.size ∧ spvU.toNat ≤ ctx.prime.size ∧
          spvU.toNat ≤ ctx.pl.size ∧ spvU.toNat ≤ roots.size then
        smallTest ap.logp ctx.log8 ctx.prime ctx.pl roots j.toUInt32 1 spvU h.1 h.2.1 h.2.2.1
          h.2.2.2.1 h.2.2.2.2 [] (8 * e2)
      else ([], 8 * e2)
    let sieved := ((buf.get! j).toUInt64.toFloat - biasF) * ctx.scale * fc 8
    if l8v > nf lt + sieved + pre8F then continue
    let (hits, l8) :=
      if h : smallU.toNat ≤ ap.logp.size ∧ smallU.toNat ≤ ctx.log8.size ∧
          smallU.toNat ≤ ctx.prime.size ∧ smallU.toNat ≤ ctx.pl.size ∧ smallU.toNat ≤ roots.size then
        smallTest ap.logp ctx.log8 ctx.prime ctx.pl roots j.toUInt32 spvU smallU h.1 h.2.1
          h.2.2.1 h.2.2.2.1 h.2.2.2.2 tiny lt
      else (tiny, lt)
    let lc := lists[c]!
    let l8 := lc.foldl (fun acc i => acc + (ctx.log8.get! i).toNat) l8
    let found := lc.foldl (fun acc i => i :: acc) hits
    if l8v ≤ (nf (l8 + ctx.allow8)) then
      let neg := vs < fc 0
      -- the sign of a value far below the size of its terms is not trusted
      let vmag := (Af * x * x).abs + (B2f * x).abs + Cf.abs
      let cof := if vf * fc 1073741824 < vmag then .unknown
        else fastCofactor ctx ap found (if neg then -v64 else v64) e2 vf
      match cof with
      | .reject => pure ()
      | .accept exps u l1 l2 =>
        if let some r := relationOf ctx ap B j neg u exps l1 l2 then rels := rels.push r
      | .unknown =>
        if let some r := exactRelation ctx ap B C j found then rels := rels.push r
  return rels

/-! ## One `A`: all of its Gray-code polynomials -/

/-- Sieve every sieved prime at `roots` (the first polynomial of an `A`). -/
def sieveAt (ctx : Ctx) (ap : APoly) (roots : Array Nat) (buf : ByteArray) : ByteArray :=
  let len : USize := ctx.size.toUSize
  let spvU := ctx.spv.toUSize
  let medU := ctx.medEnd.toUSize
  let FU := ctx.fb.size.toUSize
  let buf :=
    if h : len.toNat < buf.size ∧ medU.toNat ≤ ctx.prime.size ∧ medU.toNat ≤ ctx.cnt.size ∧
        medU.toNat ≤ roots.size ∧ medU.toNat ≤ ap.logp.size then
      sieveMed ctx.prime ctx.cnt roots ap.logp buf len h.1 spvU medU h.2.1 h.2.2.1 h.2.2.2.1
        h.2.2.2.2
    else buf
  if h : len.toNat < 2 ^ 31 ∧ len.toNat + 64 ≤ buf.size ∧ FU.toNat ≤ roots.size ∧
      FU.toNat ≤ ap.logp.size then
    sieveLarge roots ap.logp buf len h.1 h.2.1 medU FU h.2.2.1 h.2.2.2
  else buf

/-- The next Gray-code polynomial: the roots move by `±δ` (`drow`, `negate`) and
the buffer (a copy of the template) is sieved at the new roots; the roots of the
unsieved small primes move too. -/
def switchPoly (ctx : Ctx) (ap : APoly) (drow : Array Nat) (negate : Bool) (roots : Array Nat)
    (buf : ByteArray) : Array Nat × ByteArray :=
  let len : USize := ctx.size.toUSize
  let spvU := ctx.spv.toUSize
  let medU := ctx.medEnd.toUSize
  let FU := ctx.fb.size.toUSize
  let (roots, buf) :=
    if h : len.toNat < buf.size ∧ medU.toNat ≤ drow.size ∧ medU.toNat ≤ ap.logp.size ∧
        medU.toNat ≤ roots.size then
      switchMed drow ap.logp negate roots buf len h.1 spvU medU h.2.1 h.2.2.1 h.2.2.2
    else (roots, buf)
  let (roots, buf) :=
    if h : len.toNat < 2 ^ 31 ∧ len.toNat + 64 ≤ buf.size ∧ FU.toNat ≤ drow.size ∧
        FU.toNat ≤ ap.logp.size ∧ FU.toNat ≤ roots.size then
      switchBig drow ap.logp negate roots buf len h.1 h.2.1 medU FU h.2.2.1 h.2.2.2.1 h.2.2.2.2
    else (roots, buf)
  let roots :=
    if h : spvU.toNat ≤ drow.size ∧ spvU.toNat ≤ roots.size then
      moveTiny drow negate roots 1 spvU h.1 h.2
    else roots
  (roots, buf)

/-- Sieve every polynomial of the `A` chosen by `seed`. -/
def processA (ctx : Ctx) (seed : Nat) : Array (Found ctx.n ctx.fb) := Id.run do
  let some ap := mkAPoly ctx seed | return #[]
  let s := ap.qs.size
  let mut rels : Array (Found ctx.n ctx.fb) := #[]
  let mut B : Int := (ap.Bl.foldl (· + ·) 0 : Nat)
  let A : Int := ap.A
  let mut roots := ap.roots
  let mut buf := ctx.template.copySlice 0 ByteArray.empty 0 ctx.template.size
  -- first polynomial: sieve at the initial roots
  buf := sieveAt ctx ap ap.roots buf
  -- clamped updates land on the first trash byte; clear it for candidate processing
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
    -- B decreases by 2B_v: roots A⁻¹(±t - B) increase by δ_v, and conversely
    let (roots', buf') := switchPoly ctx ap ap.pdc[v]! negate roots buf
    roots := roots'
    buf := buf'
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
Tasks of one `A` each are kept queued, twice as many as threads, and their
results are taken oldest first: no round waits for its slowest task, and the
bookkeeping here overlaps the sieving (rounds of equal tasks with the
bookkeeping in between idled the threads 12% of the time at 64 digits, 9% at
72 and 4% at 80, besides their slowest tasks). Near the end, no task is queued
while the queued ones should bring the rest at the yield of the last `threads`
tasks; tasks still running at the end are abandoned. -/
def collect (ctx : Ctx) (needed threads maxRounds : Nat) : Array (Relation ctx.n ctx.fb) := Id.run do
  let mut fulls : Array (Relation ctx.n ctx.fb) := #[]
  let mut edges : Array (Found ctx.n ctx.fb) := #[]
  let mut uf : UnionFind := {}
  let mut cycles := 0
  let mut seen : Std.HashSet Nat := {}
  -- the queue: tasks `[head, queue.size)` are running or waiting
  let mut queue : Array (Task (Array (Found ctx.n ctx.fb))) := #[]
  let mut head := 0
  -- `got` (full relations and cycles) after each task taken, for the recent yield
  let mut gots : Array Nat := #[]
  -- give up after many tasks without a single relation (e.g. no usable `A`)
  let mut idle := 0
  let depth := 2 * threads
  while fulls.size + cycles < needed && idle < 50 * threads && queue.size < maxRounds * threads do
    let got := fulls.size + cycles
    let recent := if gots.size > threads then got - gots[gots.size - 1 - threads]! else 0
    -- queue more unless the queued tasks should suffice (`recent / threads` per task)
    let mut q := queue
    while q.size - head < depth && q.size < maxRounds * threads &&
        (recent == 0 || got + (q.size - head) * recent / threads < needed) do
      let seed := q.size
      q := q.push (Task.spawn fun _ => processA ctx seed)
    queue := q
    if head == queue.size then break
    let batch := queue[head]!.get
    queue := queue.set! head (.pure #[])
    head := head + 1
    let before := fulls.size + edges.size
    for f in batch do
      -- `X` and `n - X` give the same row (the same polynomial reached
      -- again with `B` negated): such a pair is a dependency whose square
      -- roots are always `X ≡ -Y`, so keep one relation per `±X`
      let key := min f.rel.x (ctx.n - f.rel.x)
      if seen.contains key then continue
      seen := seen.insert key
      if f.l1 == 1 && f.l2 == 1 then
        fulls := fulls.push f.rel
      else
        edges := edges.push f
        let (uf', closed) := uf.union f.l1 f.l2
        uf := uf'
        if closed then cycles := cycles + 1
    idle := if fulls.size + edges.size == before then idle + 1 else 0
    gots := gots.push (fulls.size + cycles)
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
    let attempt (k : Nat) : Option (ProperFactor n) :=
      let rels := collect ctx (k * needed) (max 1 cfg.threads) cfg.maxRounds
      if h : ctx.n = n then h ▸ extract ctx rels (max 1 cfg.threads) else none
    -- every dependency failing is unlikely, but the caller's fallback is trial
    -- division: once more with twice the relations
    (attempt 1).orElse fun _ => attempt 2

/-- The threads worth using on `digits` digits: below 44 digits a sieving round
of many tasks costs more than it gains (wall time, best of three: 22 digits 7.4
ms on 2 threads, 27.6 ms on 16; 30 digits 7.5 ms on 4, 17.4 ms on 16; 38 digits
11.0 ms on 8, 11.5 ms on 16). -/
def threadsFor (digits threads : Nat) : Nat :=
  min threads (if digits < 28 then 2 else if digits < 36 then 4 else if digits < 44 then 8 else threads)

/-- The public splitter: even numbers and perfect powers are handled first;
inputs below 20 digits use the simpler SIQS of `QS` (no suitable `A` with the
fast parameters). -/
def split (n : Nat) (cfg : Config := {}) : Option (ProperFactor n) :=
  if n < 4 then none
  else if n % 2 = 0 then checkFactor n 2
  else
    let threads := threadsFor (decimalDigits n) cfg.threads
    if decimalDigits n < 20 then QS.split n { variant := .siqs, threads := threads }
    else match perfectPower n with
      | some (r, _) => checkFactor n r
      | none => splitCore n { cfg with threads := threads }

/-- Every factor returned by the fast SIQS is a proper divisor. -/
theorem split_sound {n : Nat} {cfg : Config} {d : ProperFactor n}
    (_h : split n cfg = some d) : 1 < d.val ∧ d.val < n ∧ d.val ∣ n := d.property

end PrimeFactorLean.SIQS
