import PrimeFactorLean.NFS.Lattice
import PrimeFactorLean.SIQS

/-!
# A Franke–Kleinjung lattice siever

Special-`q` lattice sieving as in GGNFS/CADO-NFS's `las`, with the hot loops
written like the fast SIQS (`PrimeFactorLean.SIQS`): compact per-ideal data,
tail-recursive kernels and branch-free updates.

For a special-`q` ideal `(q, ρ)` with reduced lattice basis `u, v`, the sieve
region is `(a, b) = i u + j v` for `-I/2 ≤ i < I/2`, `0 ≤ j < J`, stored row by
row (`position = j I + i + I/2`). A factor-base ideal `(p, r)` divides the norm
exactly on the lattice `{(i, j) : i ≡ j R (mod p)}` (`R` its *lattice root*).

* Ideals with `p < I` are *line sieved*: every row has about `I / p` hits.
* Ideals with `p ≥ I` hit a row at most once; their hits are enumerated in
  order of `j` with the Franke–Kleinjung basis `(-x, β₀), (y, β₁)` of the
  `p`-lattice (`0 < x, y < I ≤ x + y`): from column `c` the next hit is at
  `c - x`, `c + y` or `c - x + y`, whichever stays in `[0, I)`.

Survivors on both sides are factored exactly (small ideals by trial division,
larger ones by a resieving pass that records the ideals landing on a survivor),
cofactors up to `2^mfb` are split into large primes below `2^lpb`, and each
relation is checked exactly (`verify`). All of this is untrusted search code:
the congruence of squares is proved in `PrimeFactorLean.GNFS`.
-/

namespace PrimeFactorLean.NFS.Las

open Arith SIQS

/-! ## Arithmetic modulo factor-base primes -/

/-- `x mod p` for an integer `x` and `0 < p < 2^32`. -/
@[inline] def modU (x : Int) (p : UInt64) : UInt64 :=
  (x % (p.toNat : Int)).toNat.toUInt64

/-- The lattice root of the ideal `(p, r)` (`r = p` for the projective root)
under the basis `u = (u_a, u_b)`, `v = (v_a, v_b)`: `R` with `i ≡ j R (mod p)`
on the hits, or `p` when the progression is degenerate (`p ∣ (u_a - r u_b)`,
only `j ≡ 0`; such ideals are not sieved). -/
def latticeRootU (p r : UInt64) (ua ub va vb : Int) : UInt64 :=
  let (α, β) :=
    if r == p then (modU ub p, modU vb p)
    else
      let rN : Int := r.toNat
      (modU (ua - rN * ub) p, modU (va - rN * vb) p)
  if α == 0 then p
  else
    let inv := invModU α p
    if inv == 0 then p
    else
      -- R = -β / α mod p
      let t := β * inv % p
      if t == 0 then 0 else p - t

/-! ## Franke–Kleinjung reduction -/

/-- The Franke–Kleinjung basis of `{(i, j) : i ≡ j R (mod p)}` for `p ≥ I`:
`(-x, b₀)` and `(y, b₁)` with `0 < x < I`, `0 ≤ y < I`, `x + y ≥ I`,
`b₀, b₁ > 0`. Euclid's algorithm on `(x, y) = (p, R)`, stopped (with a partial
last step) as soon as both entries are below `I`. Returns `none` for `R = 0`. -/
def fkReduce (p R I : Nat) : Option (Nat × Nat × Nat × Nat) := Id.run do
  if R == 0 then return none
  let mut x := p
  let mut b0 := 0
  let mut y := R
  let mut b1 := 1
  let mut fuel := 128
  while fuel > 0 do
    fuel := fuel - 1
    if x < I && y < I then break
    if x ≥ y then
      if y == 0 then return none
      let k := x / y
      if x - k * y + y ≥ I then
        x := x - k * y
        b0 := b0 + k * b1
      else
        -- partial step: the smallest multiple bringing x below I
        let k' := (x - I) / y + 1
        x := x - k' * y
        b0 := b0 + k' * b1
    else
      if x == 0 then return none
      let k := y / x
      if y - k * x + x ≥ I then
        y := y - k * x
        b1 := b1 + k * b0
      else
        let k' := (y - I) / x + 1
        y := y - k' * x
        b1 := b1 + k' * b0
  if x == 0 || x ≥ I || y ≥ I || x + y < I || b0 == 0 || b1 == 0 then return none
  return some (x, b0, y, b1)

/-! ## Sieve kernels

The buffer holds `I · J` bytes plus a trash byte at index `len = I · J`; clamped
positions land there. -/

/-- Add `lg` at `pos` (or at the trash byte when `pos ≥ len`). -/
@[inline] def addAt (s : ByteArray) (len pos : USize) (lg : UInt8) (h : len.toNat < s.size) :
    ByteArray := hitClamp s len pos lg h

/-- One row of a line-sieved ideal: `count` clamped updates at `base + c, base + c + p, …`
where positions past the row (`c ≥ I`) are redirected to the trash byte. -/
def lineRow (s : ByteArray) (len base c p I : USize) (lg : UInt8) (h : len.toNat < s.size) :
    Nat → ByteArray
  | 0 => s
  | count + 1 =>
    let pos := if c < I then base + c else len
    lineRow (addAt s len pos lg h) len base (c + p) p I lg (by simp [addAt, size_hitClamp]; exact h)
      count

theorem size_lineRow (s : ByteArray) (len base c p I : USize) (lg : UInt8)
    (h : len.toNat < s.size) (k : Nat) : (lineRow s len base c p I lg h k).size = s.size := by
  induction k generalizing s c with
  | zero => rfl
  | succ k ih => simp only [lineRow]; rw [ih, addAt, size_hitClamp]

/-- Line sieve one ideal with lattice root `R < p < I` over rows `j ∈ [j, J)`:
the first column of row `j` is `c ≡ j R + I/2 (mod p)`. -/
def lineSieve (s : ByteArray) (len : USize) (h : len.toNat < s.size) (p R I J : USize)
    (lg : UInt8) (count : Nat) (j start : USize) : Nat → ByteArray
  | 0 => s
  | fuel + 1 =>
    if j < J then
      let t := lineRow s len (j * I) start p I lg h count
      let start' := start + R
      let start' := if start' ≥ p then start' - p else start'
      lineSieve t len (by rw [size_lineRow]; exact h) p R I J lg count (j + 1) start' fuel
    else s

theorem size_lineSieve (s : ByteArray) (len : USize) (h : len.toNat < s.size) (p R I J : USize)
    (lg : UInt8) (count : Nat) (j start : USize) (fuel : Nat) :
    (lineSieve s len h p R I J lg count j start fuel).size = s.size := by
  induction fuel generalizing s j start with
  | zero => rfl
  | succ fuel ih =>
    simp only [lineSieve]
    split
    · rw [ih, size_lineRow]
    · rfl

/-- The next hit in row order (Franke–Kleinjung): from column `c = pos mod I`
move by `(-x, b₀)` if `c ≥ x`, by `(y, b₁)` if `c < I - y`, and by their sum
otherwise (`d₀ = b₀ I - x`, `d₁ = b₁ I + y` in position units). -/
@[inline] def fkNext (mask x y d0 d1 pos : USize) : USize :=
  -- branch free (conditional moves): `d₀` when `c ≥ x` or `c + y > I - 1`, `d₁`
  -- when `c < x`; the three cases above are exactly these combinations
  let c := pos &&& mask
  let s0 : USize := if c ≥ x then d0 else 0
  let s0 := if c + y > mask then d0 else s0
  let s1 : USize := if c < x then d1 else 0
  pos + s0 + s1

/-- Walk the hits of a large ideal, adding `lg`, until `pos ≥ len`. -/
def fkSieve (s : ByteArray) (len : USize) (h : len.toNat < s.size) (mask x y d0 d1 : USize)
    (lg : UInt8) (pos : USize) : Nat → ByteArray
  | 0 => s
  | fuel + 1 =>
    let pos := fkNext mask x y d0 d1 pos
    if pos < len then
      fkSieve (addAt s len pos lg h) len (by simp [addAt, size_hitClamp]; exact h) mask x y d0 d1 lg
        pos fuel
    else s

theorem size_fkSieve (s : ByteArray) (len : USize) (h : len.toNat < s.size) (mask x y d0 d1 : USize)
    (lg : UInt8) (pos : USize) (fuel : Nat) :
    (fkSieve s len h mask x y d0 d1 lg pos fuel).size = s.size := by
  induction fuel generalizing s pos with
  | zero => rfl
  | succ fuel ih =>
    simp only [fkSieve]
    split
    · rw [ih, addAt, size_hitClamp]
    · rfl

/-- Resieve walk: record ideal `k` for every labelled survivor (`128 + c`,
`c < 127`) among the hits of a large ideal. -/
def fkResieve (s : ByteArray) (len mask x y d0 d1 : USize) (k : Nat) (pos : USize)
    (acc : Array (Array Nat)) : Nat → Array (Array Nat)
  | 0 => acc
  | fuel + 1 =>
    let pos := fkNext mask x y d0 d1 pos
    if pos < len then
      let b := s.get! pos.toNat
      let acc := if b ≥ 128 && b != 255 then acc.modify (b - 128).toNat (·.push k) else acc
      fkResieve s len mask x y d0 d1 k pos acc fuel
    else acc

/-! ### Machine-word reduction fused with the walks

`fkReduce` above is the reference (and is unit tested against brute force);
the sieve uses `fkGo`/`fkGoR`, which run the same reduction on `UInt64` in a
tail-recursive loop and continue directly into the walk, so no basis needs to
be allocated per ideal. -/

/-- Franke–Kleinjung reduction of `(x, y) = (p, R)` (state `x, b₀, y, b₁`), then
the sieve walk adding `lg`. -/
def fkGo (s : ByteArray) (len : USize) (h : len.toNat < s.size) (I : UInt64) (p : UInt64)
    (lg : UInt8) (x b0 y b1 : UInt64) : Nat → ByteArray
  | 0 => s
  | fuel + 1 =>
    if x < I && y < I then
      if x == 0 || x + y < I || b0 == 0 || b1 == 0 then s
      else fkSieve s len h (I - 1).toUSize x.toUSize y.toUSize (b0 * I - x).toUSize
        (b1 * I + y).toUSize lg (I / 2).toUSize (2 * len.toNat / p.toNat + 4)
    else if x ≥ y then
      if y == 0 then s
      else
        let k := x / y
        if x - k * y + y ≥ I then fkGo s len h I p lg (x - k * y) (b0 + k * b1) y b1 fuel
        else
          let k' := (x - I) / y + 1
          fkGo s len h I p lg (x - k' * y) (b0 + k' * b1) y b1 fuel
    else
      if x == 0 then s
      else
        let k := y / x
        if y - k * x + x ≥ I then fkGo s len h I p lg x b0 (y - k * x) (b1 + k * b0) fuel
        else
          let k' := (y - I) / x + 1
          fkGo s len h I p lg x b0 (y - k' * x) (b1 + k' * b0) fuel

/-- Resieve walk: record `pos <<< 24 ||| k` at every hit on a marked survivor. -/
def fkWalkR (lab : ByteArray) (len mask x y d0 d1 : USize) (k : Nat) (pos : USize)
    (acc : Array Nat) : Nat → Array Nat
  | 0 => acc
  | fuel + 1 =>
    let pos := fkNext mask x y d0 d1 pos
    if h : pos < len ∧ pos.toNat < lab.size then
      let acc := if lab.uget pos h.2 != 0 then acc.push ((pos.toUInt64 <<< 24) ||| k.toUInt64).toNat
        else acc
      fkWalkR lab len mask x y d0 d1 k pos acc fuel
    else acc

/-- The reduction of `fkGo`, continuing into the resieve walk. -/
def fkGoR (lab : ByteArray) (len : USize) (I p : UInt64) (k : Nat) (acc : Array Nat)
    (x b0 y b1 : UInt64) : Nat → Array Nat
  | 0 => acc
  | fuel + 1 =>
    if x < I && y < I then
      if x == 0 || x + y < I || b0 == 0 || b1 == 0 then acc
      else fkWalkR lab len (I - 1).toUSize x.toUSize y.toUSize (b0 * I - x).toUSize
        (b1 * I + y).toUSize k (I / 2).toUSize acc (2 * len.toNat / p.toNat + 4)
    else if x ≥ y then
      if y == 0 then acc
      else
        let k1 := x / y
        if x - k1 * y + y ≥ I then fkGoR lab len I p k acc (x - k1 * y) (b0 + k1 * b1) y b1 fuel
        else
          let k' := (x - I) / y + 1
          fkGoR lab len I p k acc (x - k' * y) (b0 + k' * b1) y b1 fuel
    else
      if x == 0 then acc
      else
        let k1 := y / x
        if y - k1 * x + x ≥ I then fkGoR lab len I p k acc x b0 (y - k1 * x) (b1 + k1 * b0) fuel
        else
          let k' := (y - I) / x + 1
          fkGoR lab len I p k acc x b0 (y - k' * x) (b1 + k' * b0) fuel

/-- Resieve walk on a survivor bitmap (bit `pos` of `bits`: `len / 8` bytes stay
in the second-level cache, a byte per position does not): record
`pos <<< 24 ||| k` at every hit on a survivor. -/
def fkWalkB (bits : ByteArray) (len mask x y d0 d1 : USize) (k : Nat) (pos : USize)
    (acc : Array Nat) : Nat → Array Nat
  | 0 => acc
  | fuel + 1 =>
    let pos := fkNext mask x y d0 d1 pos
    if pos < len then
      let i := pos >>> 3
      let acc := if h : i.toNat < bits.size then
          if ((bits.uget i h).toUInt64 >>> (pos &&& 7).toUInt64) &&& 1 != 0 then
            acc.push ((pos.toUInt64 <<< 24) ||| k.toUInt64).toNat
          else acc
        else acc
      fkWalkB bits len mask x y d0 d1 k pos acc fuel
    else acc

/-- The reduction of `fkGo`, continuing into the bitmap resieve walk. -/
def fkGoB (bits : ByteArray) (len : USize) (I p : UInt64) (k : Nat) (acc : Array Nat)
    (x b0 y b1 : UInt64) : Nat → Array Nat
  | 0 => acc
  | fuel + 1 =>
    if x < I && y < I then
      if x == 0 || x + y < I || b0 == 0 || b1 == 0 then acc
      else fkWalkB bits len (I - 1).toUSize x.toUSize y.toUSize (b0 * I - x).toUSize
        (b1 * I + y).toUSize k (I / 2).toUSize acc (2 * len.toNat / p.toNat + 4)
    else if x ≥ y then
      if y == 0 then acc
      else
        let k1 := x / y
        if x - k1 * y + y ≥ I then fkGoB bits len I p k acc (x - k1 * y) (b0 + k1 * b1) y b1 fuel
        else
          let k' := (x - I) / y + 1
          fkGoB bits len I p k acc (x - k' * y) (b0 + k' * b1) y b1 fuel
    else
      if x == 0 then acc
      else
        let k1 := y / x
        if y - k1 * x + x ≥ I then fkGoB bits len I p k acc x b0 (y - k1 * x) (b1 + k1 * b0) fuel
        else
          let k' := (y - I) / x + 1
          fkGoB bits len I p k acc x b0 (y - k' * x) (b1 + k' * b0) fuel

/-- `a⁻¹ mod p` for `0 < a < p < 2^32` by extended Euclid on 32-bit words (`0` if
not invertible). -/
def inv32Loop (r0 r1 : UInt32) (s0 s1 : Int64) : Nat → Int64
  | 0 => 0
  | fuel + 1 =>
    if r1 == 0 then (if r0 == 1 then s0 else 0)
    else
      let q := r0 / r1
      inv32Loop r1 (r0 - q * r1) s1 (s0 - q.toUInt64.toInt64 * s1) fuel

def invMod32 (a p : UInt32) : UInt64 :=
  let s := inv32Loop p a 0 1 64
  if s < 0 then (s + p.toUInt64.toInt64).toUInt64 else s.toUInt64

/-- `x mod p` (nonnegative) for an integer `x`. -/
@[inline] def modW (x : Int) (p : Nat) : UInt64 := (x % (p : Int)).toNat.toUInt64

/-- The lattice root (as `latticeRootU`) from residues of the basis modulo `p`. -/
@[inline] def latticeRootW (p r ua ub va vb : UInt64) : UInt64 :=
  let α := if r == p then ub else (ua + p - r * ub % p) % p
  let β := if r == p then vb else (va + p - r * vb % p) % p
  if α == 0 then p
  else
    let inv := invMod32 α.toUInt32 p.toUInt32
    if inv == 0 then p
    else
      let t := β * inv % p
      if t == 0 then 0 else p - t

/-! ## Context -/

structure LasParams where
  /-- `I = 2^logI` columns, `J = I / 2` rows. -/
  logI : Nat := 11
  /-- Large-prime bounds `2^lpb` and cofactor bounds `2^mfb` (rational, algebraic). -/
  lpbR : Nat := 22
  lpbA : Nat := 22
  mfbR : Nat := 40
  mfbA : Nat := 40
  /-- Ideals with `p` below this are not sieved (their contribution is in the slack). -/
  sieveFrom : Nat := 30
  /-- Threshold slack in bits. -/
  fudge : Nat := 4
  /-- Slack of the survivor prefilter in bits. -/
  preSlack : Nat := 6
  /-- `J = I / jDiv` rows per special-`q`. -/
  jDiv : Nat := 2
  deriving Repr, Inhabited

/-- One side's factor base: ideals `(p, r)` (`r = p` projective) with logarithms. -/
structure Side where
  primes : Array Nat
  roots : Array Nat
  logs : ByteArray
  /-- First index with `p ≥ I` (Franke–Kleinjung enumeration from here on). -/
  largeStart : Nat
  /-- First index with `p ≥ sieveFrom`. -/
  sieveStart : Nat
  /-- `p⁻¹ mod 2^32` and `⌊(2^32 - 1)/p⌋` for the small ideals: `p ∣ y` iff
  `y p⁻¹ ≤ lim (mod 2^32)` for `y < 2^32`. -/
  pinv : Array UInt32
  lim : Array UInt32

structure LasCtx where
  base : Ctx
  params : LasParams
  rat : Side
  alg : Side
  I : Nat
  J : Nat
  skew : Nat
  /-- Row templates: `I` bytes of value `v` at index `v` (for per-row biases). -/
  rowTemplates : Array ByteArray
  /-- The largest factor-base primes (bounds of the cofactors' prime factors). -/
  limR : Nat
  limA : Nat

def mkSide (primes roots : Array Nat) (logs : ByteArray) (I sieveFrom : Nat) : Side := Id.run do
  let mut largeStart := 0
  while largeStart < primes.size && primes[largeStart]! < I do largeStart := largeStart + 1
  let mut sieveStart := 0
  while sieveStart < primes.size && primes[sieveStart]! < sieveFrom do sieveStart := sieveStart + 1
  let small := (primes.extract 0 largeStart).map (·.toUInt32)
  return { primes, roots, logs, largeStart, sieveStart, pinv := small.map SIQS.inv32,
           lim := small.map fun p => if p == 0 then 0 else (0xFFFFFFFF : UInt32) / p }

def mkLasCtx (base : Ctx) (params : LasParams) : LasCtx :=
  let I := 2 ^ params.logI
  let fb := base.fb
  { base := base, params := params,
    rat := mkSide fb.ratPrimes fb.ratRoots fb.ratLogs I params.sieveFrom,
    alg := mkSide fb.algPrimes fb.algRoots fb.algLogs I params.sieveFrom,
    I := I, J := I / max 1 params.jDiv, skew := skewness base.sel,
    rowTemplates := (Array.range 256).map fun v => ByteArray.mk (Array.replicate I v.toUInt8),
    limR := fb.ratPrimes.back?.getD 0, limA := fb.algPrimes.back?.getD 0 }

/-! ## One special-`q` -/

/-- `x mod p` in `[0, p)` for a signed word (`%` truncates toward zero). -/
@[inline] def smodW (x : Int64) (p : Int64) : UInt64 :=
  let t := x % p
  (if t < 0 then t + p else t).toUInt64

/-- `latticeRootW` from the basis as signed words: `u_a - r u_b` and `v_a - r v_b`
are reduced once each (the basis is far below `2^31`, `r p < 2^48`). -/
@[inline] def latticeRootI (p r : UInt64) (ua ub va vb : Int64) : UInt64 :=
  let pi := p.toInt64
  let α := if r == p then smodW ub pi else smodW (ua - r.toInt64 * ub) pi
  let β := if r == p then smodW vb pi else smodW (va - r.toInt64 * vb) pi
  if α == 0 then p
  else
    let inv := invMod32 α.toUInt32 p.toUInt32
    if inv == 0 then p
    else
      let t := β * inv % p
      if t == 0 then 0 else p - t

/-- Lattice roots of one side's ideals for the basis `u, v` (machine words). -/
def latticeRoots (side : Side) (ua ub va vb : Int) : Array Nat := Id.run do
  let mut out : Array Nat := Array.mkEmpty side.primes.size
  -- signed words when the basis allows (always, in practice)
  if ua.natAbs < 2 ^ 31 && ub.natAbs < 2 ^ 31 && va.natAbs < 2 ^ 31 && vb.natAbs < 2 ^ 31 then
    let (a, b, c, d) := (ua.toInt64, ub.toInt64, va.toInt64, vb.toInt64)
    for k in [0:side.primes.size] do
      out := out.push (latticeRootI side.primes[k]!.toUInt64 side.roots[k]!.toUInt64 a b c d).toNat
  else
    for k in [0:side.primes.size] do
      let p := side.primes[k]!
      let r := side.roots[k]!
      out := out.push (latticeRootW p.toUInt64 r.toUInt64 (modW ua p) (modW ub p) (modW va p)
        (modW vb p)).toNat
  return out

/-- `n` zero bytes. -/
def zeroBytes (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  for _ in [0:n] do b := b.push 0
  return b

/-- Biased rows: row `j` starts at `128 - thr j` (so a byte reaching `128` passed);
the trash byte at `I · J` is cleared. Fills `buf` in place. -/
def fillRows (ctx : LasCtx) (buf : ByteArray) (thr : Array Nat) : ByteArray := Id.run do
  let mut b := buf
  for j in [0:ctx.J] do
    let bias := 128 - min 127 (thr[j]!)
    b := ctx.rowTemplates[bias]!.copySlice 0 b (j * ctx.I) ctx.I
  return b.set! (ctx.I * ctx.J) 0

/-- Biased rows in a fresh buffer. -/
def initBuffer (ctx : LasCtx) (thr : Array Nat) : ByteArray :=
  fillRows ctx (zeroBytes (ctx.I * ctx.J + 1)) thr

/-- Sieve one side. -/
def sieveSide (ctx : LasCtx) (side : Side) (R : Array Nat) (buf : ByteArray) : ByteArray := Id.run do
  let I := ctx.I
  let len := I * ctx.J
  let lenU := len.toUSize
  let mut buf := buf
  if lenU.toNat < buf.size then
    -- small ideals: line sieving, rows 1 .. J-1
    let mut b := buf
    for k in [side.sieveStart:side.largeStart] do
      let p := side.primes[k]!
      let r := R[k]!
      if r ≥ p then continue
      let lg := side.logs.get! k
      -- row 1 starts at R + I/2 (mod p)
      let start := (r + I / 2) % p
      let count := (I + p - 1) / p
      if hb' : lenU.toNat < b.size then
        b := lineSieve b lenU hb' p.toUSize r.toUSize I.toUSize ctx.J.toUSize lg count 1 start.toUSize
          ctx.J
    -- large ideals: Franke–Kleinjung reduction and walk from (i, j) = (0, 0)
    let IU := I.toUInt64
    for k in [side.largeStart:side.primes.size] do
      let p := side.primes[k]!
      let r := R[k]!
      if r ≥ p then continue
      let lg := side.logs.get! k
      if hb' : lenU.toNat < b.size then
        b := fkGo b lenU hb' IU p.toUInt64 lg p.toUInt64 0 r.toUInt64 1 128
    buf := b
  return buf

/-- `F(a, b)` in floating point (only its logarithm is needed). -/
def homEvalF (cs : Array Float) (a b : Float) : Float := Id.run do
  let d := cs.size - 1
  let mut acc := cs[d]!
  let mut bp : Float := 1.0
  for i' in [0:d] do
    let i := d - 1 - i'
    bp := bp * b
    acc := acc * a + cs[i]! * bp
  return acc

/-- `log₂ x` for `x ≥ 1` to within `0.09`: the exponent plus the mantissa's
linear interpolation. -/
@[inline] def fastLog2 (x : Float) : Float :=
  let bits := x.toBits
  let e := ((bits >>> 52) &&& 0x7FF).toFloat - fc 1023
  e + (Float.ofBits ((bits &&& 0x000FFFFFFFFFFFFF) ||| 0x3FF0000000000000) - fc 1)

/-- `Σ_{i ≤ k} c_i a^i b^{d-i}` continued by Horner's rule: `acc` holds the
leading part, `bp = b^(d-1-k)` (allocation free: unboxed floats). -/
def homEvalFA (cs : FloatArray) (a b : Float) : Nat → Float → Float → Float
  | 0, acc, _ => acc
  | k + 1, acc, bp => homEvalFA cs a b k (acc * a + cs.get! k * (bp * b)) (bp * b)

/-- `log₂ |norm|` at column offset `iF`, row `jF` of the lattice (`cs` the
algebraic coefficients, `d` the degree). -/
@[inline] def normBits (alg : Bool) (cs : FloatArray) (d : Nat)
    (uaf ubf vaf vbf mF y1F qF iF jF : Float) : Float :=
  let a := iF * uaf + jF * vaf
  let b := iF * ubf + jF * vbf
  let nrm := if alg then (homEvalFA cs a b d (cs.get! d) (fc 1)).abs / qF else (y1F * a - mF * b).abs
  fastLog2 (nrm + fc 1)

/-- The algebraic coefficients as unboxed floats. -/
def coeffsF (ctx : LasCtx) : FloatArray :=
  ⟨ctx.base.sel.coeffs.map intF⟩

/-- Per-row thresholds (in bits): the largest norm on the row, sampled at five
columns, minus the cofactor allowance `2^mfb` and the slack. Norms are
evaluated in floating point (a threshold needs only their size). -/
def rowThresholds (ctx : LasCtx) (q : Nat) (ua ub va vb : Int) (mfb : Nat) (alg : Bool) :
    Array Nat := Id.run do
  let I : Float := nf ctx.I
  let m : Float := nf ctx.base.sel.m
  let y1 : Float := nf ctx.base.sel.y1
  let cs : Array Float := ctx.base.sel.coeffs.map intF
  let qf := nf q
  let (uaf, ubf, vaf, vbf) := (intF ua, intF ub, intF va, intF vb)
  let cols : Array Float := #[-(I / 2.0), -(I / 4.0), 0.0, I / 4.0, I / 2.0 - 1.0]
  let mut out : Array Nat := Array.mkEmpty ctx.J
  for j in [0:ctx.J] do
    let jf := nf j
    let mut best : Float := 1.0
    for i in cols do
      let a := i * uaf + jf * vaf
      let b := i * ubf + jf * vbf
      let nrm := if alg then (homEvalF cs a b).abs / qf else (y1 * a - b * m).abs
      if nrm > best then best := nrm
    let bits := (Float.log2 best).floor.toUInt64.toNat + 1
    out := out.push (if bits > mfb + ctx.params.fudge then bits - mfb - ctx.params.fudge else 0)
  return out

/-- Positions `[j, e)` where both regions reached `128` (the algebraic byte,
less often set, is tested first). -/
def scanBoth (a r : ByteArray) (j e : Nat) (acc : Array Nat) : Array Nat :=
  if h : j < e ∧ j < a.size ∧ j < r.size then
    scanBoth a r (j + 1) e (if a.get j h.2.1 ≥ 128 && r.get j h.2.2 ≥ 128 then acc.push j else acc)
  else acc
termination_by e - j

/-- Positions where both sides reached `128` (in increasing order): blocks of
4096 bytes are skipped unless both sides' `OR` folds (vectorized) have bit 7
set, then 16-byte groups unless the algebraic side's has (its threshold is
reached far less often than the rational side's). -/
def survivors (bufR bufA : ByteArray) (len : Nat) : Array Nat := Id.run do
  let size := min len (min bufR.size bufA.size)
  let fold (s : ByteArray) (a b : Nat) : UInt8 := s.foldl (fun acc x => acc ||| x) 0 a b
  let mut out : Array Nat := #[]
  let mut b := 0
  while b < size do
    let e := min size (b + 4096)
    if fold bufA b e ≥ 128 && fold bufR b e ≥ 128 then
      let mut c := b
      while c < e do
        let ce := min e (c + 16)
        if fold bufA c ce ≥ 128 then out := scanBoth bufA bufR c ce out
        c := ce
    b := e
  return out

/-- Indices `k < stop` of the small ideals whose progression `i ≡ j R (mod p)`
contains the column `c` of row `j` (`y = c + I p - I/2 - j R` is divisible by
`p`, tested by multiplication with `p⁻¹ mod 2^32`), and of the degenerate or
projective ideals (`R ≥ p`), which the caller tests on the norm. -/
def smallHits (side : Side) (R : Array Nat) (c j I : UInt64) (k stop : Nat) (acc : List Nat) :
    List Nat :=
  if k < stop then
    let p := side.primes[k]!.toUInt64
    let r := R[k]!.toUInt64
    let hit := if r ≥ p then true else
      let y := c + I * p - I / 2 - j * r
      -- the inverse trick needs an odd p
      if p == 2 then y &&& 1 == 0 else y.toUInt32 * side.pinv[k]! ≤ side.lim[k]!
    smallHits side R c j I (k + 1) stop (if hit then k :: acc else acc)
  else acc
termination_by stop - k

/-- Divide `u` by `p` as often as possible. -/
def stripNat (u p : Nat) : Nat × Nat := Id.run do
  let mut u := u
  let mut e := 0
  while u % p == 0 && u > 0 do
    u := u / p
    e := e + 1
  return (u, e)

/-- Split a cofactor into at most two primes below `2^lpb` (`none` if it cannot be
done within the bounds): the large-prime part of a relation. All factor-base
primes (below `lim`) are divided out, so a cofactor below `lim²` above the
large-prime bound cannot split into admissible primes (it is prime, or has a
factor below `lim`), and only `[lim², 2^mfb)` needs a factoring attempt. -/
def largePrimes (u lpb mfb lim : Nat) : Option (List Nat) :=
  if u == 1 then some []
  else if u >>> mfb != 0 then none
  else if u >>> lpb == 0 then
    -- a single large prime (a composite below the bound would mean a missed
    -- factor-base prime; it still yields a valid relation)
    some [u]
  else if u < lim * lim then none
  else
    match splitCofactor u (2 ^ lpb) with
    | some (a, b) => some [a, b]
    | none => none

/-- Factor one survivor exactly; small ideals are tested by lattice position,
the others are given by the resieve lists. -/
def factorSurvivor (ctx : LasCtx) (q ρ : Nat) (ua ub va vb : Int) (Rr Ra : Array Nat)
    (listR listA : List Nat) (pos : Nat) : Option Rel := Id.run do
  let I := ctx.I
  let j := pos / I
  let c := pos % I
  let i : Int := (c : Int) - (I / 2 : Nat)
  let a0 := i * ua + (j : Int) * va
  let b0 := i * ub + (j : Int) * vb
  let (a, b) := if b0 < 0 then (-a0, -b0) else (a0, b0)
  if b == 0 then return none
  if Nat.gcd a.natAbs b.natAbs != 1 then return none
  let bn := b.natAbs
  let sel := ctx.base.sel
  -- rational side
  let nr : Int := sel.ratNorm a b
  if nr == 0 then return none
  let mut u := nr.natAbs
  let mut rat : List (Nat × Nat) := []
  let side := ctx.rat
  for k in smallHits side Rr c.toUInt64 j.toUInt64 I.toUInt64 0 side.largeStart [] do
    let p := side.primes[k]!
    let (u', e) := stripNat u p
    if e > 0 then
      u := u'
      rat := (p, e) :: rat
  for k in listR do
    let p := side.primes[k]!
    let (u', e) := stripNat u p
    if e > 0 then
      u := u'
      rat := (p, e) :: rat
  let some lr := largePrimes u ctx.params.lpbR ctx.params.mfbR ctx.limR | return none
  for L in lr do rat := (L, 1) :: rat
  -- algebraic side
  let na := homEval sel.coeffs a b
  if na == 0 then return none
  let (z0, eq) := stripNat na.natAbs q
  if eq == 0 then return none
  let mut z := z0
  let mut alg : List (Nat × Nat × Nat) := [(q, ρ, eq)]
  let sideA := ctx.alg
  for k in smallHits sideA Ra c.toUInt64 j.toUInt64 I.toUInt64 0 sideA.largeStart [] do
    let p := sideA.primes[k]!
    let r := sideA.roots[k]!
    -- degenerate or projective progressions: test the ideal itself
    let ok := Ra[k]! < p ||
      (if r == p then bn % p == 0 else (a - b * (r : Int)) % (p : Int) == 0)
    if ok then
      let (z', e) := stripNat z p
      if e > 0 then
        z := z'
        alg := (p, r, e) :: alg
  for k in listA do
    let p := sideA.primes[k]!
    let (z', e) := stripNat z p
    if e > 0 then
      z := z'
      alg := (p, sideA.roots[k]!, e) :: alg
  let some la := largePrimes z ctx.params.lpbA ctx.params.mfbA ctx.limA | return none
  for L in la do
    let r := if bn % L == 0 then L else
      match invMod (bn % L) L with
      | some inv => (a % (L : Int)).toNat * inv % L
      | none => L
    alg := (L, r, 1) :: alg
  return some ⟨a, bn, rat, decide (nr < 0), alg⟩

/-- Large ideals of one side landing on a marked survivor (one resieve pass):
records `pos <<< 24 ||| k`. -/
def resieveSide (ctx : LasCtx) (side : Side) (R : Array Nat) (lab : ByteArray) (acc : Array Nat) :
    Array Nat := Id.run do
  let I := ctx.I.toUInt64
  let len := (ctx.I * ctx.J).toUSize
  let mut acc := acc
  for k in [side.largeStart:side.primes.size] do
    let p := side.primes[k]!
    let r := R[k]!
    if r ≥ p then continue
    acc := fkGoR lab len I p.toUInt64 k acc p.toUInt64 0 r.toUInt64 1 128
  return acc

/-- `resieveSide` on a survivor bitmap. -/
def resieveSideB (ctx : LasCtx) (side : Side) (R : Array Nat) (bits : ByteArray) (acc : Array Nat) :
    Array Nat := Id.run do
  let I := ctx.I.toUInt64
  let len := (ctx.I * ctx.J).toUSize
  let mut acc := acc
  for k in [side.largeStart:side.primes.size] do
    let p := side.primes[k]!
    let r := R[k]!
    if r ≥ p then continue
    acc := fkGoB bits len I p.toUInt64 k acc p.toUInt64 0 r.toUInt64 1 128
  return acc

/-- Records `pos <<< 24 ||| k` grouped by survivor (`survs` increasing). -/
def groupRecords (survs : Array Nat) (recs : Array Nat) : Array (List Nat) := Id.run do
  let mut lists : Array (List Nat) := Array.replicate survs.size []
  for r in recs do
    let c := SIQS.findCand survs (r >>> 24)
    if c < survs.size then lists := lists.modify c ((r &&& 0xFFFFFF) :: ·)
  return lists

/-- Label the survivors in a cleared region for the resieve: the byte of a
survivor is its rank within its row plus one (`255` from the 255th on), and
`rowStart[j]` is the index of the first survivor of row `j`, so that a resieve
record finds its survivor without a search. -/
def labelSurvivors (ctx : LasCtx) (lab : ByteArray) (surv : Array Nat) : ByteArray × Array Nat :=
  Id.run do
  let mut lab := lab
  let mut rowStart : Array Nat := Array.replicate (ctx.J + 1) 0
  let mut prev := ctx.J
  let mut rank := 0
  for k in [0:surv.size] do
    let pos := surv[k]!
    let j := pos / ctx.I
    if j != prev then
      prev := j
      rank := 0
      rowStart := rowStart.set! j k
    rank := rank + 1
    lab := lab.set! pos (min rank 255).toUInt8
  return (lab, rowStart)

/-- Records `pos <<< 24 ||| k` grouped by survivor, located through the labels
of `labelSurvivors` (a binary search only past rank 254 of a row). -/
def groupLabelled (ctx : LasCtx) (survs : Array Nat) (lab : ByteArray) (rowStart : Array Nat)
    (recs : Array Nat) : Array (List Nat) := Id.run do
  let mut lists : Array (List Nat) := Array.replicate survs.size []
  for r in recs do
    let pos := r >>> 24
    let v := (lab.get! pos).toNat
    let c := if v < 255 then rowStart[pos / ctx.I]! + v - 1 else SIQS.findCand survs pos
    if c < survs.size then lists := lists.modify c ((r &&& 0xFFFFFF) :: ·)
  return lists

/-- Per-task buffers reused from one special-`q` to the next: the two sieve
regions (the algebraic one also marks the survivors during resieving). -/
structure Scratch where
  bufR : ByteArray
  bufA : ByteArray
  /-- The survivor bitmap of the resieve (zero between special-`q`). -/
  bits : ByteArray

def Scratch.new (ctx : LasCtx) : Scratch :=
  let n := ctx.I * ctx.J + 1
  ⟨zeroBytes n, zeroBytes n, zeroBytes (n / 8 + 1)⟩

/-- Set (`on`) or clear the survivors' bits. -/
def markBits (bits : ByteArray) (surv : Array Nat) (on : Bool) : ByteArray := Id.run do
  let mut b := bits
  for pos in surv do
    let i := pos / 8
    b := b.set! i (if on then b.get! i ||| ((1 : UInt8) <<< (pos % 8).toUInt8) else 0)
  return b

/-- Zero the region (row by row from the zero template). -/
def zeroRows (ctx : LasCtx) (buf : ByteArray) : ByteArray := Id.run do
  let mut b := buf
  for j in [0:ctx.J] do
    b := ctx.rowTemplates[0]!.copySlice 0 b (j * ctx.I) ctx.I
  return b

/-- The survivors whose norms (floating point), less the sieved logarithms (the
bytes above the row bias), are at most `2^(mfb + preSlack)` on both sides; the
unsieved small primes and the rounding are covered by `preSlack`. -/
def prefilterRows (ctx : LasCtx) (q : Nat) (ua ub va vb : Int) (thrR thrA : Array Nat)
    (bufR bufA : ByteArray) (surv0 : Array Nat) : Array Nat :=
  let (uaf, ubf, vaf, vbf) := (intF ua, intF ub, intF va, intF vb)
  let mF := nf ctx.base.sel.m
  let y1F := nf ctx.base.sel.y1
  let qF := nf q
  let I := ctx.I
  let csF := coeffsF ctx
  let d := csF.size - 1
  let limR := nf (ctx.params.mfbR + ctx.params.preSlack)
  let limA := nf (ctx.params.mfbA + ctx.params.preSlack)
  surv0.filter fun pos =>
    let j := pos / I
    let iF := nf (pos % I) - nf (I / 2)
    let jF := nf j
    let biasR := nf (128 - min 127 thrR[j]!)
    let biasA := nf (128 - min 127 thrA[j]!)
    let estR := normBits false csF d uaf ubf vaf vbf mF y1F qF iF jF -
      ((bufR.get! pos).toUInt64.toFloat - biasR)
    let estA := normBits true csF d uaf ubf vaf vbf mF y1F qF iF jF -
      ((bufA.get! pos).toUInt64.toFloat - biasA)
    estR ≤ limR && estA ≤ limA

/-- Sieve one special-`q` and return its relations, reusing the buffers of `sc`. -/
def processQWith (ctx : LasCtx) (q ρ : Nat) (sc : Scratch) : Array Rel × Scratch := Id.run do
  let ⟨b1, b2, bits⟩ := sc
  let (u, v) := reduceLattice q ρ ctx.skew
  let (ua, ub, va, vb) := (u.1, u.2, v.1, v.2)
  let len := ctx.I * ctx.J
  let Rr := latticeRoots ctx.rat ua ub va vb
  let Ra := latticeRoots ctx.alg ua ub va vb
  let thrR := rowThresholds ctx q ua ub va vb ctx.params.mfbR false
  let thrA := rowThresholds ctx q ua ub va vb ctx.params.mfbA true
  let bufR := sieveSide ctx ctx.rat Rr (fillRows ctx b1 thrR)
  let bufA := sieveSide ctx ctx.alg Ra (fillRows ctx b2 thrA)
  let surv := prefilterRows ctx q ua ub va vb thrR thrA bufR bufA (survivors bufR bufA len)
  if surv.isEmpty then return (#[], ⟨bufR, bufA, bits⟩)
  -- the algebraic region is no longer needed: cleared, it labels the survivors
  -- for the resieve (a third buffer would only add cache pressure)
  let (lab, rowStart) := labelSurvivors ctx (zeroRows ctx bufA) surv
  let bits := markBits bits surv true
  let listsR := groupLabelled ctx surv lab rowStart (resieveSideB ctx ctx.rat Rr bits #[])
  let listsA := groupLabelled ctx surv lab rowStart (resieveSideB ctx ctx.alg Ra bits #[])
  let bits := markBits bits surv false
  let mut rels : Array Rel := #[]
  for k in [0:surv.size] do
    if let some rel := factorSurvivor ctx q ρ ua ub va vb Rr Ra listsR[k]! listsA[k]! surv[k]! then
      rels := rels.push rel
  return (rels, ⟨bufR, lab, bits⟩)

/-- Sieve one special-`q` with fresh buffers. -/
def processQ (ctx : LasCtx) (q ρ : Nat) : Array Rel := (processQWith ctx q ρ (Scratch.new ctx)).1

/-! ## Per-segment norms and the exact small-prime part

Each 64-column segment of a row starts from the logarithm of its largest norm
(at its ends) instead of the row's, so that the threshold `mfb + fudge` means
the same everywhere; the segment biases are kept for the prefilter. The primes
below `sieveFrom` are not sieved: the prefilter computes their exact
contribution `U` from the norms modulo prime powers below `2^20` (a few
machine-word operations from the lattice position), so that it can accept a
survivor exactly when `log₂ |norm| - sieved - U ≤ mfb` up to the rounding of
the sieved logarithms. -/

/-- Initialize the segments `[s, segs)` of row `j`, recording their biases
(`prev` is the norm's logarithm at the left end of segment `s`). -/
def fillRowSegs (ctx : LasCtx) (alg : Bool) (cs : FloatArray) (d : Nat)
    (uaf ubf vaf vbf mF y1F qF : Float) (mfbF : Float) (j : Nat) (jF : Float) (b bias : ByteArray)
    (prev : Float) (s segs : Nat) : ByteArray × ByteArray :=
  if s < segs then
    let iF := nf ((s + 1) * 64) - nf (ctx.I / 2)
    let next := normBits alg cs d uaf ubf vaf vbf mF y1F qF iF jF
    let bits := if prev > next then prev else next
    let t := bits - mfbF
    let ti : Nat := if t ≤ fc 0 then 0 else if t ≥ fc 127 then 127 else t.toUInt64.toNat
    let b := ctx.rowTemplates[128 - ti]!.copySlice 0 b (j * ctx.I + s * 64) 64
    fillRowSegs ctx alg cs d uaf ubf vaf vbf mF y1F qF mfbF j jF b (bias.push (128 - ti).toUInt8)
      next (s + 1) segs
  else (b, bias)
termination_by segs - s

/-- The whole region, row by row, and the segment biases (`J · I / 64` bytes). -/
def fillSegments (ctx : LasCtx) (buf : ByteArray) (alg : Bool) (q : Nat) (ua ub va vb : Int)
    (mfb : Nat) : ByteArray × ByteArray := Id.run do
  let cs := coeffsF ctx
  let d := cs.size - 1
  let (uaf, ubf, vaf, vbf) := (intF ua, intF ub, intF va, intF vb)
  let mF := nf ctx.base.sel.m
  let y1F := nf ctx.base.sel.y1
  let qF := nf q
  let mfbF := nf (mfb + ctx.params.fudge)
  let segs := ctx.I / 64
  let mut b := buf
  let mut bias := ByteArray.emptyWithCapacity (ctx.J * segs)
  for j in [0:ctx.J] do
    let jF := nf j
    let first := normBits alg cs d uaf ubf vaf vbf mF y1F qF (Float.neg (nf (ctx.I / 2))) jF
    let (b', bias') := fillRowSegs ctx alg cs d uaf ubf vaf vbf mF y1F qF mfbF j jF b bias first 0 segs
    b := b'
    bias := bias'
  return (b.set! (ctx.I * ctx.J) 0, bias)

/-- The tiny primes (below `sieveFrom`) with their largest powers `≤ 2^20`. -/
def tinyPowers (bound : Nat) : Array (Nat × Nat) :=
  (primesUpTo (bound - 1)).map fun p => Id.run do
    let mut P := p
    while P * p ≤ 1048576 do P := P * p
    return (p, P)

/-- `v_p(r)` for a residue `r` modulo `p^K` (`K` if `r = 0`). -/
def valMod (r p : UInt64) (K : Nat) : Nat := Id.run do
  if r == 0 then return K
  let mut r := r
  let mut v := 0
  while r % p == 0 do
    r := r / p
    v := v + 1
  return v

/-- Per special-`q` residues for the tiny primes: for each `(p, P = p^K)`,
`N_R ≡ i A + j B (mod P)`, and `a ≡ i ua + j va`, `b ≡ i ub + j vb (mod P)`
with the algebraic coefficients modulo `P`. -/
structure TinyQ where
  p : Array Nat
  P : Array Nat
  K : Array Nat
  lg : FloatArray
  rA : Array Nat
  rB : Array Nat
  ua : Array Nat
  ub : Array Nat
  va : Array Nat
  vb : Array Nat
  cs : Array (Array Nat)

def mkTinyQ (ctx : LasCtx) (ua ub va vb : Int) : TinyQ := Id.run do
  let tps := tinyPowers ctx.params.sieveFrom
  let y1 : Int := ctx.base.sel.y1
  let m : Int := ctx.base.sel.m
  let md (x : Int) (P : Nat) : Nat := (x % (P : Int)).toNat
  let mut t : TinyQ := ⟨#[], #[], #[], ⟨#[]⟩, #[], #[], #[], #[], #[], #[], #[]⟩
  for (p, P) in tps do
    let mut K := 0
    let mut x := 1
    while x < P do
      x := x * p
      K := K + 1
    t := { t with p := t.p.push p, P := t.P.push P, K := t.K.push K,
                  lg := t.lg.push (Float.log2 (nf p)),
                  rA := t.rA.push (md (y1 * ua - m * ub) P), rB := t.rB.push (md (y1 * va - m * vb) P),
                  ua := t.ua.push (md ua P), ub := t.ub.push (md ub P),
                  va := t.va.push (md va P), vb := t.vb.push (md vb P),
                  cs := t.cs.push (ctx.base.sel.coeffs.map fun c => md c P) }
  return t

/-- The bits of the rational norm in the tiny primes at column offset `i`
(as the residue `iP` modulo each `P`) and row `j`. -/
def tinyRat (t : TinyQ) (c j I : Nat) : Float := Id.run do
  let mut u : Float := fc 0
  for k in [0:t.p.size] do
    let P := t.P[k]!.toUInt64
    let i := ((c + t.P[k]! - (I / 2) % t.P[k]!) % t.P[k]!).toUInt64
    let r := (i * t.rA[k]!.toUInt64 + j.toUInt64 * t.rB[k]!.toUInt64) % P
    u := u + (nf (valMod r t.p[k]!.toUInt64 t.K[k]!)) * t.lg.get! k
  return u

/-- The same for the algebraic norm `F(a, b)`. -/
def tinyAlg (t : TinyQ) (c j I : Nat) : Float := Id.run do
  let mut u : Float := fc 0
  for k in [0:t.p.size] do
    let P := t.P[k]!.toUInt64
    let i := ((c + t.P[k]! - (I / 2) % t.P[k]!) % t.P[k]!).toUInt64
    let ju := j.toUInt64
    let a := (i * t.ua[k]!.toUInt64 + ju * t.va[k]!.toUInt64) % P
    let b := (i * t.ub[k]!.toUInt64 + ju * t.vb[k]!.toUInt64) % P
    let cs := t.cs[k]!
    -- Horner in a, with powers of b
    let d := cs.size - 1
    let mut acc := cs[d]!.toUInt64 % P
    let mut bp : UInt64 := 1
    for i' in [0:d] do
      bp := bp * b % P
      acc := (acc * a + cs[d - 1 - i']!.toUInt64 * bp) % P
    u := u + (nf (valMod acc t.p[k]!.toUInt64 t.K[k]!)) * t.lg.get! k
  return u

/-- The survivors whose norms, less the sieved logarithms (above the segment
biases) and the exact tiny-prime part, are at most `2^(mfb + slack)` on both
sides (rational side first). -/
def prefilterExact (ctx : LasCtx) (q : Nat) (ua ub va vb : Int) (bufR bufA biasR biasA : ByteArray)
    (surv0 : Array Nat) : Array Nat :=
  let cs := coeffsF ctx
  let d := cs.size - 1
  let (uaf, ubf, vaf, vbf) := (intF ua, intF ub, intF va, intF vb)
  let mF := nf ctx.base.sel.m
  let y1F := nf ctx.base.sel.y1
  let qF := nf q
  let I := ctx.I
  let segs := I / 64
  let limR := nf (ctx.params.mfbR + ctx.params.preSlack)
  let limA := nf (ctx.params.mfbA + ctx.params.preSlack)
  let t := mkTinyQ ctx ua ub va vb
  surv0.filter fun pos =>
    let j := pos / I
    let c := pos % I
    let iF := nf c - nf (I / 2)
    let jF := nf j
    let seg := j * segs + c / 64
    let estR := normBits false cs d uaf ubf vaf vbf mF y1F qF iF jF -
      ((bufR.get! pos).toUInt64.toFloat - (biasR.get! seg).toUInt64.toFloat)
    if estR - tinyRat t c j I > limR then false
    else
      let estA := normBits true cs d uaf ubf vaf vbf mF y1F qF iF jF -
        ((bufA.get! pos).toUInt64.toFloat - (biasA.get! seg).toUInt64.toFloat)
      estA - tinyAlg t c j I ≤ limA

/-- Sieve one special-`q` with per-segment norms and the exact prefilter. -/
def processQ5 (ctx : LasCtx) (q ρ : Nat) (sc : Scratch) : Array Rel × Scratch := Id.run do
  let ⟨b1, b2, bits⟩ := sc
  let (u, v) := reduceLattice q ρ ctx.skew
  let (ua, ub, va, vb) := (u.1, u.2, v.1, v.2)
  let len := ctx.I * ctx.J
  let Rr := latticeRoots ctx.rat ua ub va vb
  let Ra := latticeRoots ctx.alg ua ub va vb
  let (fR, biasR) := fillSegments ctx b1 false q ua ub va vb ctx.params.mfbR
  let (fA, biasA) := fillSegments ctx b2 true q ua ub va vb ctx.params.mfbA
  let bufR := sieveSide ctx ctx.rat Rr fR
  let bufA := sieveSide ctx ctx.alg Ra fA
  let surv := prefilterExact ctx q ua ub va vb bufR bufA biasR biasA (survivors bufR bufA len)
  if surv.isEmpty then return (#[], ⟨bufR, bufA, bits⟩)
  let (lab, rowStart) := labelSurvivors ctx (zeroRows ctx bufA) surv
  let bits := markBits bits surv true
  let listsR := groupLabelled ctx surv lab rowStart (resieveSideB ctx ctx.rat Rr bits #[])
  let listsA := groupLabelled ctx surv lab rowStart (resieveSideB ctx ctx.alg Ra bits #[])
  let bits := markBits bits surv false
  let mut rels : Array Rel := #[]
  for k in [0:surv.size] do
    if let some rel := factorSurvivor ctx q ρ ua ub va vb Rr Ra listsR[k]! listsA[k]! surv[k]! then
      rels := rels.push rel
  return (rels, ⟨bufR, lab, bits⟩)

/-- Segment biases (`J · I / 64` bytes) of row-initialized regions. -/
def rowBiases (ctx : LasCtx) (thr : Array Nat) : ByteArray := Id.run do
  let segs := ctx.I / 64
  let mut out := ByteArray.emptyWithCapacity (ctx.J * segs)
  for j in [0:ctx.J] do
    let b := (128 - min 127 thr[j]!).toUInt8
    for _ in [0:segs] do out := out.push b
  return out

/-- Row-maximum initialization with the exact prefilter. -/
def processQ6 (ctx : LasCtx) (q ρ : Nat) (sc : Scratch) : Array Rel × Scratch := Id.run do
  let ⟨b1, b2, bits⟩ := sc
  let (u, v) := reduceLattice q ρ ctx.skew
  let (ua, ub, va, vb) := (u.1, u.2, v.1, v.2)
  let len := ctx.I * ctx.J
  let Rr := latticeRoots ctx.rat ua ub va vb
  let Ra := latticeRoots ctx.alg ua ub va vb
  let thrR := rowThresholds ctx q ua ub va vb ctx.params.mfbR false
  let thrA := rowThresholds ctx q ua ub va vb ctx.params.mfbA true
  let bufR := sieveSide ctx ctx.rat Rr (fillRows ctx b1 thrR)
  let bufA := sieveSide ctx ctx.alg Ra (fillRows ctx b2 thrA)
  let surv := prefilterExact ctx q ua ub va vb bufR bufA (rowBiases ctx thrR) (rowBiases ctx thrA)
    (survivors bufR bufA len)
  if surv.isEmpty then return (#[], ⟨bufR, bufA, bits⟩)
  let (lab, rowStart) := labelSurvivors ctx (zeroRows ctx bufA) surv
  let bits := markBits bits surv true
  let listsR := groupLabelled ctx surv lab rowStart (resieveSideB ctx ctx.rat Rr bits #[])
  let listsA := groupLabelled ctx surv lab rowStart (resieveSideB ctx ctx.alg Ra bits #[])
  let bits := markBits bits surv false
  let mut rels : Array Rel := #[]
  for k in [0:surv.size] do
    if let some rel := factorSurvivor ctx q ρ ua ub va vb Rr Ra listsR[k]! listsA[k]! surv[k]! then
      rels := rels.push rel
  return (rels, ⟨bufR, lab, bits⟩)

end PrimeFactorLean.NFS.Las
