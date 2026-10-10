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
  let c := pos &&& mask
  if c ≥ x then pos + d0 else if c + y ≤ mask then pos + d1 else pos + d0 + d1

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
    I := I, J := I / 2, skew := skewness base.sel,
    rowTemplates := (Array.range 256).map fun v => ByteArray.mk (Array.replicate I v.toUInt8) }

/-! ## One special-`q` -/

/-- Lattice roots of one side's ideals for the basis `u, v` (machine words). -/
def latticeRoots (side : Side) (ua ub va vb : Int) : Array Nat := Id.run do
  let mut out : Array Nat := Array.mkEmpty side.primes.size
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
  ⟨ctx.base.sel.coeffs.map Float.ofInt⟩

/-- Per-row thresholds (in bits): the largest norm on the row, sampled at five
columns, minus the cofactor allowance `2^mfb` and the slack. Norms are
evaluated in floating point (a threshold needs only their size). -/
def rowThresholds (ctx : LasCtx) (q : Nat) (ua ub va vb : Int) (mfb : Nat) (alg : Bool) :
    Array Nat := Id.run do
  let I : Float := ctx.I.toFloat
  let m : Float := ctx.base.sel.m.toFloat
  let y1 : Float := ctx.base.sel.y1.toFloat
  let cs : Array Float := ctx.base.sel.coeffs.map Float.ofInt
  let qf := q.toFloat
  let (uaf, ubf, vaf, vbf) := (Float.ofInt ua, Float.ofInt ub, Float.ofInt va, Float.ofInt vb)
  let cols : Array Float := #[-(I / 2.0), -(I / 4.0), 0.0, I / 4.0, I / 2.0 - 1.0]
  let mut out : Array Nat := Array.mkEmpty ctx.J
  for j in [0:ctx.J] do
    let jf := j.toFloat
    let mut best : Float := 1.0
    for i in cols do
      let a := i * uaf + jf * vaf
      let b := i * ubf + jf * vbf
      let nrm := if alg then (homEvalF cs a b).abs / qf else (y1 * a - b * m).abs
      if nrm > best then best := nrm
    let bits := (Float.log2 best).floor.toUInt64.toNat + 1
    out := out.push (if bits > mfb + ctx.params.fudge then bits - mfb - ctx.params.fudge else 0)
  return out

/-- Positions where both sides reached `128` (in increasing order): blocks of
4096 bytes and chunks of 64 are skipped unless both sides' `OR` folds
(vectorized) have bit 7 set. -/
def survivors (bufR bufA : ByteArray) (len : Nat) : Array Nat := Id.run do
  let size := min len (min bufR.size bufA.size)
  let fold (s : ByteArray) (a b : Nat) : UInt8 := s.foldl (fun acc x => acc ||| x) 0 a b
  let mut out : Array Nat := #[]
  let mut b := 0
  while b < size do
    let e := min size (b + 4096)
    if fold bufR b e ≥ 128 && fold bufA b e ≥ 128 then
      let mut c := b
      while c < e do
        let ce := min e (c + 64)
        if fold bufR c ce ≥ 128 && fold bufA c ce ≥ 128 then
          for pos in [c:ce] do
            if bufR.get! pos ≥ 128 && bufA.get! pos ≥ 128 then out := out.push pos
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
done within the bounds): the large-prime part of a relation. -/
def largePrimes (u lpb mfb : Nat) : Option (List Nat) :=
  if u == 1 then some []
  else if u.log2 ≥ mfb then none
  else if u < 2 ^ lpb then
    -- a single large prime (a composite below the bound would mean a missed
    -- factor-base prime; it still yields a valid relation)
    some [u]
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
  let some lr := largePrimes u ctx.params.lpbR ctx.params.mfbR | return none
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
  let some la := largePrimes z ctx.params.lpbA ctx.params.mfbA | return none
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

/-- Records `pos <<< 24 ||| k` grouped by survivor (`survs` increasing). -/
def groupRecords (survs : Array Nat) (recs : Array Nat) : Array (List Nat) := Id.run do
  let mut lists : Array (List Nat) := Array.replicate survs.size []
  for r in recs do
    let c := SIQS.findCand survs (r >>> 24)
    if c < survs.size then lists := lists.modify c ((r &&& 0xFFFFFF) :: ·)
  return lists

/-- Per-task buffers reused from one special-`q` to the next: the two sieve
regions (the algebraic one also marks the survivors during resieving). -/
structure Scratch where
  bufR : ByteArray
  bufA : ByteArray

def Scratch.new (ctx : LasCtx) : Scratch :=
  let n := ctx.I * ctx.J + 1
  ⟨zeroBytes n, zeroBytes n⟩

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
  let (uaf, ubf, vaf, vbf) := (Float.ofInt ua, Float.ofInt ub, Float.ofInt va, Float.ofInt vb)
  let mF := ctx.base.sel.m.toFloat
  let y1F := ctx.base.sel.y1.toFloat
  let qF := q.toFloat
  let I := ctx.I
  let csF := coeffsF ctx
  let d := csF.size - 1
  let limR := (ctx.params.mfbR + ctx.params.preSlack).toFloat
  let limA := (ctx.params.mfbA + ctx.params.preSlack).toFloat
  surv0.filter fun pos =>
    let j := pos / I
    let iF := (pos % I).toFloat - (I / 2).toFloat
    let jF := j.toFloat
    let biasR := (128 - min 127 thrR[j]!).toFloat
    let biasA := (128 - min 127 thrA[j]!).toFloat
    let estR := normBits false csF d uaf ubf vaf vbf mF y1F qF iF jF -
      ((bufR.get! pos).toUInt64.toFloat - biasR)
    let estA := normBits true csF d uaf ubf vaf vbf mF y1F qF iF jF -
      ((bufA.get! pos).toUInt64.toFloat - biasA)
    estR ≤ limR && estA ≤ limA

/-- Sieve one special-`q` and return its relations, reusing the buffers of `sc`. -/
def processQWith (ctx : LasCtx) (q ρ : Nat) (sc : Scratch) : Array Rel × Scratch := Id.run do
  let ⟨b1, b2⟩ := sc
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
  if surv.isEmpty then return (#[], ⟨bufR, bufA⟩)
  -- the algebraic region is no longer needed: cleared, it labels the survivors
  -- for the resieve (a third buffer would only add cache pressure)
  let mut lab := zeroRows ctx bufA
  for pos in surv do lab := lab.set! pos 1
  let listsR := groupRecords surv (resieveSide ctx ctx.rat Rr lab #[])
  let listsA := groupRecords surv (resieveSide ctx ctx.alg Ra lab #[])
  let mut rels : Array Rel := #[]
  for k in [0:surv.size] do
    if let some rel := factorSurvivor ctx q ρ ua ub va vb Rr Ra listsR[k]! listsA[k]! surv[k]! then
      rels := rels.push rel
  return (rels, ⟨bufR, lab⟩)

/-- Sieve one special-`q` with fresh buffers. -/
def processQ (ctx : LasCtx) (q ρ : Nat) : Array Rel := (processQWith ctx q ρ (Scratch.new ctx)).1

end PrimeFactorLean.NFS.Las
