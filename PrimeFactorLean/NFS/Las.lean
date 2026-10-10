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
  return { primes, roots, logs, largeStart, sieveStart }

def mkLasCtx (base : Ctx) (params : LasParams) : LasCtx :=
  let I := 2 ^ params.logI
  let fb := base.fb
  { base := base, params := params,
    rat := mkSide fb.ratPrimes fb.ratRoots fb.ratLogs I params.sieveFrom,
    alg := mkSide fb.algPrimes fb.algRoots fb.algLogs I params.sieveFrom,
    I := I, J := I / 2, skew := skewness base.sel,
    rowTemplates := (Array.range 256).map fun v => ByteArray.mk (Array.replicate I v.toUInt8) }

/-! ## One special-`q` -/

/-- Lattice roots of one side's ideals for the basis `u, v`. -/
def latticeRoots (side : Side) (ua ub va vb : Int) : Array Nat :=
  (Array.range side.primes.size).map fun k =>
    let p := side.primes[k]!
    (latticeRootU p.toUInt64 side.roots[k]!.toUInt64 ua ub va vb).toNat

/-- Biased rows: row `j` starts at `128 - thr j` (so a byte reaching `128` passed). -/
def initBuffer (ctx : LasCtx) (thr : Array Nat) : ByteArray := Id.run do
  let len := ctx.I * ctx.J
  let mut buf := ByteArray.mk (Array.replicate (len + 1) 0)
  for j in [0:ctx.J] do
    let bias := 128 - min 127 (thr[j]!)
    buf := ctx.rowTemplates[bias]!.copySlice 0 buf (j * ctx.I) ctx.I
  return buf

/-- Sieve one side. -/
def sieveSide (ctx : LasCtx) (side : Side) (R : Array Nat) (buf : ByteArray) : ByteArray := Id.run do
  let I := ctx.I
  let len := I * ctx.J
  let lenU := len.toUSize
  let mut buf := buf
  if h : lenU.toNat < buf.size then
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
    -- large ideals: Franke–Kleinjung walks from (i, j) = (0, 0)
    for k in [side.largeStart:side.primes.size] do
      let p := side.primes[k]!
      let r := R[k]!
      if r ≥ p then continue
      match fkReduce p r I with
      | none => continue
      | some (x, b0, y, b1) =>
        let lg := side.logs.get! k
        if hb' : lenU.toNat < b.size then
          b := fkSieve b lenU hb' (I - 1).toUSize x.toUSize y.toUSize (b0 * I - x).toUSize
            (b1 * I + y).toUSize lg (I / 2).toUSize (2 * len / p + 4)
    buf := b
  return buf

/-- Per-row thresholds (in bits): the largest norm on the row, sampled at five
columns, minus the cofactor allowance `2^mfb` and the slack. -/
def rowThresholds (ctx : LasCtx) (q : Nat) (ua ub va vb : Int) (mfb : Nat) (alg : Bool) :
    Array Nat :=
  let I : Int := ctx.I
  let m : Int := ctx.base.sel.m
  let cs := ctx.base.sel.coeffs
  (Array.range ctx.J).map fun (j : Nat) =>
    let jI : Int := j
    let bits := [-(I / 2), -(I / 4), 0, I / 4, I / 2 - 1].foldl (fun acc (i : Int) =>
      let a := i * ua + jI * va
      let b := i * ub + jI * vb
      let nrm := if alg then (homEval cs a b).natAbs / q else (a - b * m).natAbs
      max acc (nrm.log2 + 1)) 0
    if bits > mfb + ctx.params.fudge then bits - mfb - ctx.params.fudge else 0

/-- Positions where both sides reached `128`. -/
def survivors (bufR bufA : ByteArray) (len : Nat) : Array Nat := Id.run do
  let block := 4096
  let mut out : Array Nat := #[]
  let mut b := 0
  while b < len do
    let e := min len (b + block)
    if bufR.foldl (fun acc x => acc ||| x) 0 b e ≥ 128 then
      for pos in [b:e] do
        if bufR.get! pos ≥ 128 && bufA.get! pos ≥ 128 then out := out.push pos
    b := e
  return out

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
    (listR listA : Array Nat) (pos : Nat) : Option Rel := Id.run do
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
  let nr : Int := a - b * (sel.m : Int)
  if nr == 0 then return none
  let mut u := nr.natAbs
  let mut rat : List (Nat × Nat) := []
  let side := ctx.rat
  for k in [0:side.largeStart] do
    let p := side.primes[k]!
    let R := Rr[k]!
    let hit := if R ≥ p then u % p == 0 else (c + p * j + p - (I / 2) % p) % p == (j * R) % p
    if hit then
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
  for k in [0:sideA.largeStart] do
    let p := sideA.primes[k]!
    let r := sideA.roots[k]!
    let R := Ra[k]!
    let hit :=
      if R ≥ p then
        (if r == p then bn % p == 0 else (a - b * (r : Int)) % (p : Int) == 0) && z % p == 0
      else (c + p * j + p - (I / 2) % p) % p == (j * R) % p
    if hit then
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

/-- A label buffer: zero everywhere except the survivors of the batch, which get
`128 + k` (the sieve buffers cannot be relabelled in place: positions that
passed on one side only also hold bytes `≥ 128`). -/
def labelSurvivors (batch : Array Nat) (len : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.mk (Array.replicate (len + 1) 0)
  for k in [0:batch.size] do
    b := b.set! batch[k]! (if k < 126 then (128 + k).toUInt8 else 255)
  return b

/-- Large ideals of one side landing on labelled survivors (one resieve pass). -/
def resieveSide (ctx : LasCtx) (side : Side) (R : Array Nat) (buf : ByteArray) (count : Nat) :
    Array (Array Nat) := Id.run do
  let I := ctx.I
  let len := I * ctx.J
  let mut acc : Array (Array Nat) := Array.replicate count #[]
  for k in [side.largeStart:side.primes.size] do
    let p := side.primes[k]!
    let r := R[k]!
    if r ≥ p then continue
    match fkReduce p r I with
    | none => continue
    | some (x, b0, y, b1) =>
      acc := fkResieve buf len.toUSize (I - 1).toUSize x.toUSize y.toUSize (b0 * I - x).toUSize
        (b1 * I + y).toUSize k (I / 2).toUSize acc (2 * len / p + 4)
  return acc

/-- Sieve one special-`q` and return its relations. -/
def processQ (ctx : LasCtx) (q ρ : Nat) : Array Rel := Id.run do
  let (u, v) := reduceLattice q ρ ctx.skew
  let (ua, ub, va, vb) := (u.1, u.2, v.1, v.2)
  let len := ctx.I * ctx.J
  let Rr := latticeRoots ctx.rat ua ub va vb
  let Ra := latticeRoots ctx.alg ua ub va vb
  let thrR := rowThresholds ctx q ua ub va vb ctx.params.mfbR false
  let thrA := rowThresholds ctx q ua ub va vb ctx.params.mfbA true
  let bufR := sieveSide ctx ctx.rat Rr (initBuffer ctx thrR)
  let bufA := sieveSide ctx ctx.alg Ra (initBuffer ctx thrA)
  let surv := survivors bufR bufA len
  let mut rels : Array Rel := #[]
  let mut start := 0
  while start < surv.size do
    let batch := surv.extract start (start + 126)
    let labels := labelSurvivors batch len
    let listsR := resieveSide ctx ctx.rat Rr labels batch.size
    let listsA := resieveSide ctx ctx.alg Ra labels batch.size
    for k in [0:batch.size] do
      if let some rel := factorSurvivor ctx q ρ ua ub va vb Rr Ra listsR[k]! listsA[k]! batch[k]! then
        rels := rels.push rel
    start := start + 126
  return rels

end PrimeFactorLean.NFS.Las
