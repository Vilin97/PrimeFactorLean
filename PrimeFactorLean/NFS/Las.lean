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

/-! ### Kernels with machine-word counters

The same loops with `USize` counters and fuel: a `Nat` counter costs a scalar
test, a subtraction and a reference-count decrement per iteration. -/

/-- `lineRow` with a machine-word counter. -/
def lineRowU (s : ByteArray) (len base c p I : USize) (lg : UInt8) (h : len.toNat < s.size)
    (count : USize) : ByteArray :=
  if hc : count = 0 then s
  else
    let pos := if c < I then base + c else len
    lineRowU (addAt s len pos lg h) len base (c + p) p I lg (by simp [addAt, size_hitClamp]; exact h)
      (count - 1)
termination_by count.toNat
decreasing_by exact usize_pred_lt count hc

theorem size_lineRowU (s : ByteArray) (len base c p I : USize) (lg : UInt8)
    (h : len.toNat < s.size) (k : USize) : (lineRowU s len base c p I lg h k).size = s.size := by
  fun_induction lineRowU s len base c p I lg h k with
  | case1 => rfl
  | case2 s c h k hk pos ih => rw [ih, addAt, size_hitClamp]

/-- `lineSieve` with machine-word counters: rows `j, …, J - 1`. -/
def lineSieveU (s : ByteArray) (len : USize) (h : len.toNat < s.size) (p R I J : USize)
    (lg : UInt8) (count : USize) (j start : USize) (fuel : USize) : ByteArray :=
  if hf : fuel = 0 then s
  else if j < J then
    let t := lineRowU s len (j * I) start p I lg h count
    let start' := start + R
    let start' := if start' ≥ p then start' - p else start'
    lineSieveU t len (by rw [size_lineRowU]; exact h) p R I J lg count (j + 1) start' (fuel - 1)
  else s
termination_by fuel.toNat
decreasing_by exact usize_pred_lt fuel hf

/-- `fkSieve` with machine-word fuel. -/
def fkSieveU (s : ByteArray) (len : USize) (h : len.toNat < s.size) (mask x y d0 d1 : USize)
    (lg : UInt8) (pos : USize) (fuel : USize) : ByteArray :=
  if hf : fuel = 0 then s
  else
    let pos := fkNext mask x y d0 d1 pos
    if pos < len then
      fkSieveU (addAt s len pos lg h) len (by simp [addAt, size_hitClamp]; exact h) mask x y d0 d1 lg
        pos (fuel - 1)
    else s
termination_by fuel.toNat
decreasing_by exact usize_pred_lt fuel hf

/-- `fkGo` with machine-word fuel. -/
def fkGoU (s : ByteArray) (len : USize) (h : len.toNat < s.size) (I : UInt64) (p : UInt64)
    (lg : UInt8) (x b0 y b1 : UInt64) (fuel : USize) : ByteArray :=
  if hf : fuel = 0 then s
  else if x < I && y < I then
    if x == 0 || x + y < I || b0 == 0 || b1 == 0 then s
    else fkSieveU s len h (I - 1).toUSize x.toUSize y.toUSize (b0 * I - x).toUSize
      (b1 * I + y).toUSize lg (I / 2).toUSize (2 * len / p.toUSize + 4)
  else if x ≥ y then
    if y == 0 then s
    else
      let k := x / y
      if x - k * y + y ≥ I then fkGoU s len h I p lg (x - k * y) (b0 + k * b1) y b1 (fuel - 1)
      else
        let k' := (x - I) / y + 1
        fkGoU s len h I p lg (x - k' * y) (b0 + k' * b1) y b1 (fuel - 1)
  else
    if x == 0 then s
    else
      let k := y / x
      if y - k * x + x ≥ I then fkGoU s len h I p lg x b0 (y - k * x) (b1 + k * b0) (fuel - 1)
      else
        let k' := (y - I) / x + 1
        fkGoU s len h I p lg x b0 (y - k' * x) (b1 + k' * b0) (fuel - 1)
termination_by fuel.toNat
decreasing_by all_goals exact usize_pred_lt fuel hf

/-- `fkWalkB` with machine-word fuel and bounds (`bsz ≤ bits.size`). -/
def fkWalkBU (bits : ByteArray) (bsz : USize) (hb : bsz.toNat ≤ bits.size)
    (len mask x y d0 d1 : USize) (k : UInt64) (pos : USize) (acc : Array Nat) (fuel : USize) :
    Array Nat :=
  if hf : fuel = 0 then acc
  else
    let pos := fkNext mask x y d0 d1 pos
    if pos < len then
      let i := pos >>> 3
      let acc := if h : i < bsz then
          if ((bits.uget i (by rw [USize.lt_iff_toNat_lt] at h; omega)).toUInt64 >>>
              (pos &&& 7).toUInt64) &&& 1 != 0 then
            acc.push ((pos.toUInt64 <<< 24) ||| k).toNat
          else acc
        else acc
      fkWalkBU bits bsz hb len mask x y d0 d1 k pos acc (fuel - 1)
    else acc
termination_by fuel.toNat
decreasing_by exact usize_pred_lt fuel hf

/-- `fkGoB` with machine-word fuel. -/
def fkGoBU (bits : ByteArray) (bsz : USize) (hb : bsz.toNat ≤ bits.size) (len : USize)
    (I p : UInt64) (k : UInt64) (acc : Array Nat) (x b0 y b1 : UInt64) (fuel : USize) : Array Nat :=
  if hf : fuel = 0 then acc
  else if x < I && y < I then
    if x == 0 || x + y < I || b0 == 0 || b1 == 0 then acc
    else fkWalkBU bits bsz hb len (I - 1).toUSize x.toUSize y.toUSize (b0 * I - x).toUSize
      (b1 * I + y).toUSize k (I / 2).toUSize acc (2 * len / p.toUSize + 4)
  else if x ≥ y then
    if y == 0 then acc
    else
      let k1 := x / y
      if x - k1 * y + y ≥ I then fkGoBU bits bsz hb len I p k acc (x - k1 * y) (b0 + k1 * b1) y b1 (fuel - 1)
      else
        let k' := (x - I) / y + 1
        fkGoBU bits bsz hb len I p k acc (x - k' * y) (b0 + k' * b1) y b1 (fuel - 1)
  else
    if x == 0 then acc
    else
      let k1 := y / x
      if y - k1 * x + x ≥ I then fkGoBU bits bsz hb len I p k acc x b0 (y - k1 * x) (b1 + k1 * b0) (fuel - 1)
      else
        let k' := (y - I) / x + 1
        fkGoBU bits bsz hb len I p k acc x b0 (y - k' * x) (b1 + k' * b0) (fuel - 1)
termination_by fuel.toNat
decreasing_by all_goals exact usize_pred_lt fuel hf

/-! ### Two walks at once

Each step of a walk depends on the previous one (a few cycles of latency), and
a walk of a large ideal ends after a few steps with a mispredicted exit. Two
independent walks in one loop overlap their dependency chains; the longer one
then finishes alone.

Every walk is bounded by `2 len / p + 4` steps, twice the expected number of
lattice points of `p` in the region. A walk exceeds it only when the lattice
has a short vector `(s, t)`, `|s| < t`, along which the hits line up (one in
every row when `t = 1`): then every hit of the region is a multiple `k (s, t)`,
whose pair `(a, b)` has `gcd ≥ k` — the hits past the bound are never coprime
pairs, and the bound saves walking them. -/

/-- `fkSieveU` on two ideals at once (positions `pa`, `pb`, logarithms `lga`,
`lgb`): the same updates as two `fkSieveU` walks with budgets `fm + ra` and
`fm + rb` (`fm` the smaller budget, counted down by the pairs; one of `ra`, `rb`
is zero). -/
def fkSieve2U (s : ByteArray) (len : USize) (h : len.toNat < s.size) (mask : USize)
    (xa ya a0 a1 : USize) (lga : UInt8) (pa : USize)
    (xb yb b0 b1 : USize) (lgb : UInt8) (pb : USize) (fm ra rb : USize) : ByteArray :=
  if hf : fm = 0 then
    if ra = 0 then fkSieveU s len h mask xb yb b0 b1 lgb pb rb
    else fkSieveU s len h mask xa ya a0 a1 lga pa ra
  else
    let pa := fkNext mask xa ya a0 a1 pa
    let pb := fkNext mask xb yb b0 b1 pb
    if pa < len then
      if pb < len then
        fkSieve2U (addAt (addAt s len pa lga h) len pb lgb (by simp [addAt, size_hitClamp]; exact h))
          len (by simp [addAt, size_hitClamp]; exact h) mask xa ya a0 a1 lga pa xb yb b0 b1 lgb pb
          (fm - 1) ra rb
      else
        fkSieveU (addAt s len pa lga h) len (by simp [addAt, size_hitClamp]; exact h) mask xa ya a0 a1
          lga pa (fm - 1 + ra)
    else if pb < len then
      fkSieveU (addAt s len pb lgb h) len (by simp [addAt, size_hitClamp]; exact h) mask xb yb b0 b1
        lgb pb (fm - 1 + rb)
    else s
termination_by fm.toNat
decreasing_by exact usize_pred_lt fm hf

/-- Record `pos <<< 24 ||| k` when the bit of `pos` is set (the step of `fkWalkBU`). -/
@[inline] def markHit (bits : ByteArray) (bsz : USize) (hb : bsz.toNat ≤ bits.size) (pos : USize)
    (k : UInt64) (acc : Array Nat) : Array Nat :=
  let i := pos >>> 3
  if h : i < bsz then
    if ((bits.uget i (by rw [USize.lt_iff_toNat_lt] at h; omega)).toUInt64 >>>
        (pos &&& 7).toUInt64) &&& 1 != 0 then
      acc.push ((pos.toUInt64 <<< 24) ||| k).toNat
    else acc
  else acc

/-- `fkWalkBU` on two ideals at once (`ka`, `kb` their indices; budgets as for
`fkSieve2U`): the same records as two `fkWalkBU` walks. -/
def fkWalkB2U (bits : ByteArray) (bsz : USize) (hb : bsz.toNat ≤ bits.size) (len mask : USize)
    (xa ya a0 a1 : USize) (ka : UInt64) (pa : USize)
    (xb yb b0 b1 : USize) (kb : UInt64) (pb : USize) (acc : Array Nat) (fm ra rb : USize) :
    Array Nat :=
  if hf : fm = 0 then
    if ra = 0 then fkWalkBU bits bsz hb len mask xb yb b0 b1 kb pb acc rb
    else fkWalkBU bits bsz hb len mask xa ya a0 a1 ka pa acc ra
  else
    let pa := fkNext mask xa ya a0 a1 pa
    let pb := fkNext mask xb yb b0 b1 pb
    if pa < len then
      if pb < len then
        fkWalkB2U bits bsz hb len mask xa ya a0 a1 ka pa xb yb b0 b1 kb pb
          (markHit bits bsz hb pb kb (markHit bits bsz hb pa ka acc)) (fm - 1) ra rb
      else fkWalkBU bits bsz hb len mask xa ya a0 a1 ka pa (markHit bits bsz hb pa ka acc) (fm - 1 + ra)
    else if pb < len then
      fkWalkBU bits bsz hb len mask xb yb b0 b1 kb pb (markHit bits bsz hb pb kb acc) (fm - 1 + rb)
    else acc
termination_by fm.toNat
decreasing_by exact usize_pred_lt fm hf

/-! ### Reduced bases cached between the sieve and the resieve

The reduction of each large ideal (about five Euclid steps with divisions) cost
as much as a third of each walk; the sieve pass now stores the basis packed into
one word (`x | y << 13 | b₀ << 26 | b₁ << 44`, each `b` below `2^18`; `0` when
there is nothing to walk, `2^62 + R` when it does not fit) in place of the
lattice root, and the resieve walks from it. -/

/-- The packed Franke–Kleinjung basis of `(p, R)` (machine words, no allocation). -/
def fkBasis (I : UInt32) (x b0 y b1 : UInt32) : Nat → UInt64
  | 0 => 0
  | fuel + 1 =>
    if x < I && y < I then
      if x == 0 || x + y < I || b0 == 0 || b1 == 0 then 0
      else if b0 ≥ 262144 || b1 ≥ 262144 || I > 8192 then 1
      else x.toUInt64 ||| (y.toUInt64 <<< 13) ||| (b0.toUInt64 <<< 26) ||| (b1.toUInt64 <<< 44)
    else if x ≥ y then
      if y == 0 then 0
      else
        let k := x / y
        if x - k * y + y ≥ I then fkBasis I (x - k * y) (b0 + k * b1) y b1 fuel
        else
          let k' := (x - I) / y + 1
          fkBasis I (x - k' * y) (b0 + k' * b1) y b1 fuel
    else
      if x == 0 then 0
      else
        let k := y / x
        if y - k * x + x ≥ I then fkBasis I x b0 (y - k * x) (b1 + k * b0) fuel
        else
          let k' := (y - I) / x + 1
          fkBasis I x b0 (y - k' * x) (b1 + k' * b0) fuel

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
  /-- Odd ideals with `p` below this are not sieved: `processQ10` counts them at
the survivors (`tinyAt`), and `fudge` covers them in the thresholds. -/
  sieveFrom : Nat := 30
  /-- Threshold slack in bits. -/
  fudge : Nat := 4
  /-- Additional threshold slack of the algebraic side: the unsieved primes
  below `sieveFrom` divide algebraic norms far more than rational ones when the
  polynomial has many small roots (good `α`). -/
  fudgeA : Nat := 0
  /-- Slack of the survivor prefilter in bits. -/
  preSlack : Nat := 6
  /-- `J = I / jDiv` rows per special-`q`. -/
  jDiv : Nat := 2
  /-- Tolerance in bits of the survivor prefilter (`prefilterGap`). -/
  gapSlack : Nat := 3
  /-- The siever: `12` for `processQ12` (row thresholds, cached reduced bases),
`11` for `processQ11`, `10` for `processQ10` (segment thresholds, the odd tiny
primes counted at the survivors), `13` and `14` for `processQ13` and
`processQs14` (`processQ12` with segment thresholds, prime powers and the tiny
primes counted at the survivors; `14` computes the lattice roots of four
special-q at once). -/
  variant : Nat := 12
  /-- Tasks per thread in a sieving round (a round waits for its slowest task;
  smaller tasks balance better but each keeps its own buffers). -/
  taskMul : Nat := 2
  /-- Prime powers below this are not sieved (`sievePowers`). -/
  powMin : Nat := 0
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
  /-- Powers `p^k < I` (`k ≥ 2`) of the small ideals with a simple root, with the
  root lifted modulo `p^k` and the logarithm of `p`: sieving them too makes the
  sieved logarithm count prime powers. -/
  pw : Array Nat := #[]
  pwRoots : Array Nat := #[]
  pwLogs : ByteArray := .empty
  /-- The prime of each power. -/
  pwBase : Array Nat := #[]
  /-- `log₂ p` of each prime (the floating-point cofactor bounds). -/
  lg2 : FloatArray := .empty
  /-- For each small ideal `(p, r)`, a root modulo `p²` above `r` (`p²` if there
  is none to use: projective or multiple roots), so that `p² ∣ norm` is a lattice
  condition (`squareRoots`). -/
  sqRoots : Array Nat := #[]
  /-- `pinv ||| lim <<< 32` of the ideals `[sieveStart, largeStart)` (one word
  each, below `2^59` since `p ≥ 31`). -/
  pinvLim : Array Nat := #[]

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
           lim := small.map fun p => if p == 0 then 0 else (0xFFFFFFFF : UInt32) / p,
           lg2 := ⟨primes.map fun p => Float.log2 (nf p)⟩,
           pinvLim := (small.extract sieveStart small.size).map fun p =>
             (SIQS.inv32 p).toNat + ((0xFFFFFFFF : UInt32) / p).toNat * 4294967296 }

/-- `f(x) = Σ c_i x^i` modulo `M`. -/
def evalModM (cs : Array Int) (x M : Nat) : Nat := Id.run do
  let mut acc : Int := 0
  for k in [0:cs.size] do
    let i := cs.size - 1 - k
    acc := (acc * (x : Int) + cs[i]!) % (M : Int)
  return (acc % (M : Int)).toNat

/-- `f'(x)` modulo `M`. -/
def evalDerivModM (cs : Array Int) (x M : Nat) : Nat :=
  evalModM ((Array.range (cs.size - 1)).map fun i => ((i + 1 : Nat) : Int) * cs[i + 1]!) x M

/-- The prime powers `p^k < I` (`k ≥ 2`) of the small ideals `(p, r)`, `r < p`,
with `r` lifted to a root modulo `p^k` (rational side: `m / Y₁`; algebraic
side: Hensel lifting of a simple root of `f`). -/
def smallPowers (primes roots : Array Nat) (logs : ByteArray) (I : Nat)
    (lift : Nat → Nat → Nat → Option Nat) (proj : Nat → Nat → Bool) :
    Array Nat × Array Nat × ByteArray × Array Nat := Id.run do
  let mut pw : Array Nat := #[]
  let mut pr : Array Nat := #[]
  let mut pl : ByteArray := .empty
  let mut pb : Array Nat := #[]
  for k in [0:primes.size] do
    let p := primes[k]!
    let r := roots[k]!
    if p ≥ I then break
    let mut M := p * p
    let mut rk := r
    while M < I do
      -- a projective root (`r = p`) stays projective (`M`): `p^k ∣ b`
      match (if r ≥ p then (if proj p M then some M else none) else lift p M rk) with
      | some r' =>
        pw := pw.push M
        pr := pr.push r'
        pl := pl.push (logs.get! k)
        pb := pb.push p
        rk := r'
        M := M * p
      | none => M := I
  return (pw, pr, pl, pb)

def mkLasCtx (base : Ctx) (params : LasParams) : LasCtx :=
  let I := 2 ^ params.logI
  let fb := base.fb
  let sel := base.sel
  let ratLift (_ M _ : Nat) : Option Nat :=
    if sel.y1 % M == 0 then none
    else (invMod (sel.y1 % M) M).map fun inv => sel.m % M * inv % M
  let algLift (_ M r : Nat) : Option Nat :=
    -- Newton step from a root modulo M / p (simple: f'(r) invertible)
    let d := evalDerivModM sel.coeffs r M
    match invMod d M with
    | some inv => some ((r + M - evalModM sel.coeffs r M * inv % M) % M)
    | none => none
  -- projective roots: `v_p(norm) = min(v_p(lead), v_p(b))` when `p` does not
  -- divide the next coefficient, so `p^k ∣ b` gives `p^k` up to `v_p(lead)`
  let cs := sel.coeffs
  let ratProj (p M : Nat) : Bool := sel.y1 % M == 0 && sel.m % p != 0
  let algProj (p M : Nat) : Bool :=
    cs[cs.size - 1]! % (M : Int) == 0 && cs.size ≥ 2 && cs[cs.size - 2]! % (p : Int) != 0
  let (rpw, rpr, rpl, rpb) := smallPowers fb.ratPrimes fb.ratRoots fb.ratLogs I ratLift ratProj
  let (apw, apr, apl, apb) := smallPowers fb.algPrimes fb.algRoots fb.algLogs I algLift algProj
  -- roots modulo p² of the small ideals (simple roots only)
  let sq (primes roots : Array Nat) (lift : Nat → Nat → Nat → Option Nat) : Array Nat :=
    (Array.range primes.size).filterMap fun k =>
      let p := primes[k]!
      if p ≥ I then none
      else
        let r := roots[k]!
        some (if r ≥ p then p * p else (lift p (p * p) r).getD (p * p))
  { base := base, params := params,
    rat := { mkSide fb.ratPrimes fb.ratRoots fb.ratLogs I params.sieveFrom with
             pw := rpw, pwRoots := rpr, pwLogs := rpl, pwBase := rpb,
             sqRoots := sq fb.ratPrimes fb.ratRoots ratLift },
    alg := { mkSide fb.algPrimes fb.algRoots fb.algLogs I params.sieveFrom with
             pw := apw, pwRoots := apr, pwLogs := apl, pwBase := apb,
             sqRoots := sq fb.algPrimes fb.algRoots algLift },
    I := I, J := I / max 1 params.jDiv, skew := skewness base.sel,
    rowTemplates := (Array.range 256).map fun v => ByteArray.mk (Array.replicate I v.toUInt8),
    limR := fb.ratPrimes.back?.getD 0, limA := fb.algPrimes.back?.getD 0 }

/-! ## Thread-private copies

An object shared between tasks counts its references atomically: when the 16
sieving tasks all increment and decrement the counts of the same factor-base
arrays, row templates and coefficients, the contended cache lines cost a fifth
of the sieve's throughput. Each task therefore works on its own copy of the
context (`LasCtx.copy`, about a millisecond); objects allocated by a task are
private to it. -/

/-- A fresh array with the same elements. -/
def copyArray {α : Type} (a : Array α) : Array α :=
  a.foldl (fun acc x => acc.push x) (Array.mkEmpty a.size)

/-- A fresh byte array with the same bytes. -/
def copyBytes (b : ByteArray) : ByteArray :=
  b.copySlice 0 (ByteArray.emptyWithCapacity b.size) 0 b.size

/-- A fresh float array with the same entries. -/
def copyFloats (f : FloatArray) : FloatArray :=
  f.foldl (fun acc x => acc.push x) (FloatArray.emptyWithCapacity f.size)

/-- A fresh integer (a big integer is a shared object too). -/
def copyInt (x : Int) : Int := (x + 1) - 1

def Side.copy (s : Side) : Side :=
  { primes := copyArray s.primes, roots := copyArray s.roots, logs := copyBytes s.logs,
    largeStart := s.largeStart, sieveStart := s.sieveStart, pinv := copyArray s.pinv,
    lim := copyArray s.lim, pw := copyArray s.pw, pwRoots := copyArray s.pwRoots,
    pwLogs := copyBytes s.pwLogs, pwBase := copyArray s.pwBase, lg2 := copyFloats s.lg2,
    sqRoots := copyArray s.sqRoots, pinvLim := copyArray s.pinvLim }

/-- The context with every array the sieve touches copied (for one task). -/
def LasCtx.copy (c : LasCtx) : LasCtx :=
  let sel := c.base.sel
  { c with
    base := { c.base with sel := { sel with coeffs := sel.coeffs.map copyInt } },
    rat := c.rat.copy, alg := c.alg.copy, rowTemplates := c.rowTemplates.map copyBytes }

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

/-- Lattice roots of the prime-power ideals of a side (all below `2^31`). -/
def powerRoots (side : Side) (ua ub va vb : Int) : Array Nat := Id.run do
  let mut out : Array Nat := Array.mkEmpty side.pw.size
  for k in [0:side.pw.size] do
    let M := side.pw[k]!
    out := out.push (latticeRootW M.toUInt64 side.pwRoots[k]!.toUInt64 (modW ua M) (modW ub M)
      (modW va M) (modW vb M)).toNat
  return out

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

/-- `(u_a - r u_b) mod p` and `(v_a - r v_b) mod p` (`u_b`, `v_b` for the
projective root `r = p`). -/
@[inline] def latticeAB (p r : UInt64) (ua ub va vb : Int64) : UInt64 × UInt64 :=
  let pi := p.toInt64
  if r == p then (smodW ub pi, smodW vb pi)
  else (smodW (ua - r.toInt64 * ub) pi, smodW (va - r.toInt64 * vb) pi)

/-- The lattice root `-β/α mod p` from `α⁻¹` (`α = 0`: the projective root `p`). -/
@[inline] def rootOf (p α β inv : UInt64) : Nat :=
  if α == 0 then p.toNat
  else
    let t := β * inv % p
    if t == 0 then 0 else (p - t).toNat

/-- The lattice roots of the ideals `[k, …)` for four special-`q` bases at once:
the four inverses modulo each prime come from one extended Euclid and nine
products (Montgomery's trick) instead of four extended Euclids. (Reductions by
a floating-point reciprocal of `p` instead of the divisions measured slower.) -/
def roots4Go (primes roots : Array Nat)
    (a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3 : Int64) (k : Nat)
    (o0 o1 o2 o3 : Array Nat) : Array Nat × Array Nat × Array Nat × Array Nat :=
  if h : k < primes.size ∧ k < roots.size then
    let p := primes[k].toUInt64
    let r := roots[k].toUInt64
    let (x0, y0) := latticeAB p r a0 b0 c0 d0
    let (x1, y1) := latticeAB p r a1 b1 c1 d1
    let (x2, y2) := latticeAB p r a2 b2 c2 d2
    let (x3, y3) := latticeAB p r a3 b3 c3 d3
    let z0 := if x0 == 0 then 1 else x0
    let z1 := if x1 == 0 then 1 else x1
    let z2 := if x2 == 0 then 1 else x2
    let z3 := if x3 == 0 then 1 else x3
    let p01 := z0 * z1 % p
    let p012 := p01 * z2 % p
    let inv := invMod32 (p012 * z3 % p).toUInt32 p.toUInt32
    let i3 := inv * p012 % p
    let j2 := inv * z3 % p
    let i2 := j2 * p01 % p
    let j1 := j2 * z2 % p
    let i1 := j1 * z0 % p
    let i0 := j1 * z1 % p
    roots4Go primes roots a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3 (k + 1)
      (o0.push (rootOf p x0 y0 i0)) (o1.push (rootOf p x1 y1 i1)) (o2.push (rootOf p x2 y2 i2))
      (o3.push (rootOf p x3 y3 i3))
  else (o0, o1, o2, o3)
termination_by primes.size - k

/-- `latticeRoots` for up to four bases `(u_a, u_b, v_a, v_b)` at once (`roots4Go`;
bases beyond `2^31` take the general path). -/
def latticeRoots4 (side : Side) (bs : Array (Int × Int × Int × Int)) : Array (Array Nat) :=
  let small := bs.all fun (a, b, c, d) =>
    a.natAbs < 2 ^ 31 && b.natAbs < 2 ^ 31 && c.natAbs < 2 ^ 31 && d.natAbs < 2 ^ 31
  if bs.isEmpty || bs.size > 4 || !small then
    bs.map fun (a, b, c, d) => latticeRoots side a b c d
  else
    let g (i : Nat) : Int64 × Int64 × Int64 × Int64 :=
      let (a, b, c, d) := bs[min i (bs.size - 1)]!
      (a.toInt64, b.toInt64, c.toInt64, d.toInt64)
    let (a0, b0, c0, d0) := g 0
    let (a1, b1, c1, d1) := g 1
    let (a2, b2, c2, d2) := g 2
    let (a3, b3, c3, d3) := g 3
    let n := side.primes.size
    let (o0, o1, o2, o3) := roots4Go side.primes side.roots a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2
      a3 b3 c3 d3 0 (Array.mkEmpty n) (Array.mkEmpty n) (Array.mkEmpty n) (Array.mkEmpty n)
    #[o0, o1, o2, o3].extract 0 bs.size

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

/-- The logarithms of the degenerate small prime ideals (lattice root `≥ p`: the
ideal divides the norm on every row `j ≡ 0 (mod p)` and on no other) per row.
(A degenerate power `p^k` does not divide whole rows.) -/
def rowExtras (ctx : LasCtx) (side : Side) (R : Array Nat) : Array Nat := Id.run do
  let mut ex : Array Nat := Array.replicate ctx.J 0
  for k in [0:side.largeStart] do
    let p := side.primes[k]!
    if R[k]! < p then continue
    let lg := (side.logs.get! k).toNat
    let mut j := 0
    while j < ctx.J do
      ex := ex.modify j (· + lg)
      j := j + p
  return ex

/-- Line sieve the prime-power ideals (lattice roots `Rp`) of a side (the
machine-word kernels of `lineSieveSide`). -/
def sievePowers (ctx : LasCtx) (side : Side) (Rp : Array Nat) (buf : ByteArray) : ByteArray :=
  Id.run do
  let I := ctx.I
  let len := I * ctx.J
  let lenU := len.toUSize
  let mut b := buf
  for k in [0:side.pw.size] do
    let p := side.pw[k]!
    let r := Rp[k]!
    if r ≥ p || p < ctx.params.powMin then continue
    let lg := side.pwLogs.get! k
    if hb' : lenU.toNat < b.size then
      b := lineSieveU b lenU hb' p.toUSize r.toUSize I.toUSize ctx.J.toUSize lg
        ((I + p - 1) / p).toUSize 1 ((r + I / 2) % p).toUSize ctx.J.toUSize
  return b

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
    let fudge := ctx.params.fudge + (if alg then ctx.params.fudgeA else 0)
    out := out.push (if bits > mfb + fudge then bits - mfb - fudge else 0)
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
def survivors (bufR bufA : ByteArray) (len : Nat) : Array Nat :=
  let size := min len (min bufR.size bufA.size)
  survBlocks bufR bufA 0 size #[] (size / 4096 + 1)
where
  fold (s : ByteArray) (a b : Nat) : UInt8 := s.foldl (fun acc x => acc ||| x) 0 a b
  /-- The 16-byte groups of `[c, e)` (tail recursive, no loop state). -/
  survGroups (bufR bufA : ByteArray) (c e : Nat) (acc : Array Nat) : Nat → Array Nat
    | 0 => acc
    | fuel + 1 =>
      if c < e then
        let ce := min e (c + 16)
        let acc := if fold bufA c ce ≥ 128 then scanBoth bufA bufR c ce acc else acc
        survGroups bufR bufA ce e acc fuel
      else acc
  /-- The blocks of 4096 bytes of `[b, size)`. -/
  survBlocks (bufR bufA : ByteArray) (b size : Nat) (acc : Array Nat) : Nat → Array Nat
    | 0 => acc
    | fuel + 1 =>
      if b < size then
        let e := min size (b + 4096)
        let acc := if fold bufA b e ≥ 128 && fold bufR b e ≥ 128 then
            survGroups bufR bufA b e acc 257 else acc
        survBlocks bufR bufA e size acc fuel
      else acc

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

/-- The cheap checks of `largePrimes`, without factoring: `0` the cofactor
cannot be admissible, `1` it is (no large prime or one), `2` it must be split. -/
def cofactorClass (u lpb mfb lim : Nat) : Nat :=
  if u == 1 then 1
  else if u >>> mfb != 0 then 0
  else if u >>> lpb == 0 then 1
  else if u < lim * lim then 0
  else if u >>> 52 == 0 && u % 2 == 1 && sprp2 u.toUInt64 then 0
  else 2

/-- The admissible large primes of a cofactor of class `c` (`cofactorClass`). -/
def largePrimesOf (c u lpb : Nat) : Option (List Nat) :=
  if c == 1 then (if u == 1 then some [] else some [u])
  else match splitCofactor u (2 ^ lpb) with
    | some (a, b) => some [a, b]
    | none => none

/-- `factorSurvivor` with the cheap checks of both sides before any cofactor is
split (most survivors fail them), and machine-word inverses for the roots of the
large algebraic primes. -/
def factorSurvivor2 (ctx : LasCtx) (q ρ : Nat) (ua ub va vb : Int) (Rr Ra : Array Nat)
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
  -- rational side: trial division and the cheap checks
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
  let cr := cofactorClass u ctx.params.lpbR ctx.params.mfbR ctx.limR
  if cr == 0 then return none
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
  let ca := cofactorClass z ctx.params.lpbA ctx.params.mfbA ctx.limA
  if ca == 0 then return none
  -- only now the (expensive) splits
  let some la := largePrimesOf ca z ctx.params.lpbA | return none
  let some lr := largePrimesOf cr u ctx.params.lpbR | return none
  for L in lr do rat := (L, 1) :: rat
  for L in la do
    let r := if bn % L == 0 then L else
      if L >>> 31 == 0 then
        let inv := invMod32 (bn % L).toUInt32 L.toUInt32
        if inv == 0 then L else (a % (L : Int)).toNat * inv.toNat % L
      else match invMod (bn % L) L with
        | some inv => (a % (L : Int)).toNat * inv % L
        | none => L
    alg := (L, r, 1) :: alg
  return some ⟨a, bn, rat, decide (nr < 0), alg⟩

/-- Survivors with `i` or `j` odd (`(a, b)` is even when both are). -/
def dropEvenEven (ctx : LasCtx) (surv : Array Nat) : Array Nat :=
  surv.filter fun pos => (pos / ctx.I) % 2 == 1 || pos % 2 == 1

/-- Survivors with no prime `p ≤ 7` dividing both `i` and `j` (then `p` divides
`gcd(a, b)`, `(a, b) = i u + j v`). -/
def dropSmallGcd (ctx : LasCtx) (surv : Array Nat) : Array Nat :=
  let half := ctx.I / 2
  surv.filter fun pos =>
    let j := pos / ctx.I
    -- `i = c - I/2` with `I/2` a power of two: `i ≡ c - I/2 (mod p)`
    let c := pos % ctx.I + 210 * ctx.I - half
    !((j % 2 == 0 && c % 2 == 0) || (j % 3 == 0 && c % 3 == 0) || (j % 5 == 0 && c % 5 == 0) ||
      (j % 7 == 0 && c % 7 == 0))

/-- Survivors whose estimated cofactors (norm less the sieved logarithms) are at
most `2^(mfb + slack)` on both sides and outside the gap between one large prime
(`< 2^lpb`) and two (`≥ lim²`), with `slack` bits of tolerance each way. -/
def prefilterGap (ctx : LasCtx) (q : Nat) (ua ub va vb : Int) (bufR bufA biasR biasA : ByteArray)
    (slack : Nat) (surv0 : Array Nat) : Array Nat :=
  let cs := coeffsF ctx
  let d := cs.size - 1
  let (uaf, ubf, vaf, vbf) := (intF ua, intF ub, intF va, intF vb)
  let mF := nf ctx.base.sel.m
  let y1F := nf ctx.base.sel.y1
  let qF := nf q
  let I := ctx.I
  let segs := I / 64
  let sl := nf slack
  let limR := nf ctx.params.mfbR + sl
  let limA := nf ctx.params.mfbA + sl
  let gapR0 := nf ctx.params.lpbR + sl
  let gapR1 := fc 2 * Float.log2 (nf ctx.limR) - sl - fc 1
  let gapA0 := nf ctx.params.lpbA + sl
  let gapA1 := fc 2 * Float.log2 (nf ctx.limA) - sl - fc 1
  surv0.filter fun pos =>
    let j := pos / I
    let c := pos % I
    let iF := nf c - nf (I / 2)
    let jF := nf j
    let seg := j * segs + c / 64
    let estR := normBits false cs d uaf ubf vaf vbf mF y1F qF iF jF -
      ((bufR.get! pos).toUInt64.toFloat - (biasR.get! seg).toUInt64.toFloat)
    if estR > limR || (estR > gapR0 && estR < gapR1) then false
    else
      let estA := normBits true cs d uaf ubf vaf vbf mF y1F qF iF jF -
        ((bufA.get! pos).toUInt64.toFloat - (biasA.get! seg).toUInt64.toFloat)
      estA ≤ limA && !(estA > gapA0 && estA < gapA1)

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

/-- `resieveSideB` with the machine-word kernels. -/
def resieveSideBU (ctx : LasCtx) (side : Side) (R : Array Nat) (bits : ByteArray) (acc : Array Nat) :
    Array Nat := Id.run do
  let I := ctx.I.toUInt64
  let len := (ctx.I * ctx.J).toUSize
  let bsz := bits.size.toUSize
  if hb : bsz.toNat ≤ bits.size then
    let mut acc := acc
    for k in [side.largeStart:side.primes.size] do
      let p := side.primes[k]!
      let r := R[k]!
      if r ≥ p then continue
      acc := fkGoBU bits bsz hb len I p.toUInt64 k.toUInt64 acc p.toUInt64 0 r.toUInt64 1 128
    return acc
  else return acc

/-- Sieve the large ideals of a side, returning the region and the lattice roots
with the packed bases in place of the large ideals' roots. -/
def sieveLargeCached (ctx : LasCtx) (side : Side) (R : Array Nat) (buf : ByteArray) :
    ByteArray × Array Nat := Id.run do
  let I := ctx.I
  let len := (I * ctx.J).toUSize
  let IU := I.toUInt64
  let I32 := I.toUInt32
  let mut b := buf
  let mut R := R
  if len.toNat < b.size then
    for k in [side.largeStart:side.primes.size] do
      let p := side.primes[k]!
      let r := R[k]!
      if r ≥ p then
        R := R.set! k 0
        continue
      let w := fkBasis I32 p.toUInt32 0 r.toUInt32 1 128
      -- `1` from `fkBasis`: the basis does not fit, keep the root behind a flag
      R := R.set! k (if w == 1 then 4611686018427387904 + r else w.toNat)
      let lg := side.logs.get! k
      if hb' : len.toNat < b.size then
        if w == 0 then continue
        else if w == 1 then
          b := fkGoU b len hb' IU p.toUInt64 lg p.toUInt64 0 r.toUInt64 1 128
        else
          let x := w &&& 8191
          let y := (w >>> 13) &&& 8191
          let b0 := (w >>> 26) &&& 262143
          let b1 := (w >>> 44) &&& 262143
          b := fkSieveU b len hb' (IU - 1).toUSize x.toUSize y.toUSize (b0 * IU - x).toUSize
            (b1 * IU + y).toUSize lg (IU / 2).toUSize (2 * len / p.toUSize + 4)
  return (b, R)

/-- The resieve of the large ideals from the cached bases (`RB` from
`sieveLargeCached`). -/
def resieveCached (ctx : LasCtx) (side : Side) (RB : Array Nat) (bits : ByteArray)
    (acc : Array Nat) : Array Nat := Id.run do
  let I := ctx.I.toUInt64
  let len := (ctx.I * ctx.J).toUSize
  let bsz := bits.size.toUSize
  if hb : bsz.toNat ≤ bits.size then
    let mut acc := acc
    for k in [side.largeStart:side.primes.size] do
      let w := RB[k]!.toUInt64
      if w == 0 then continue
      let p := side.primes[k]!
      if w ≥ 4611686018427387904 then
        acc := fkGoBU bits bsz hb len I p.toUInt64 k.toUInt64 acc p.toUInt64 0
          (w - 4611686018427387904) 1 128
      else
        let x := w &&& 8191
        let y := (w >>> 13) &&& 8191
        let b0 := (w >>> 26) &&& 262143
        let b1 := (w >>> 44) &&& 262143
        acc := fkWalkBU bits bsz hb len (I - 1).toUSize x.toUSize y.toUSize (b0 * I - x).toUSize
          (b1 * I + y).toUSize k.toUInt64 (I / 2).toUSize acc (2 * len / p.toUSize + 4)
    return acc
  else return acc

/-- `sieveLargeCached` from the ideal `k` on, tail recursive (a `for` loop with
two mutable variables allocates its state at every ideal) and with the walks of
consecutive ideals paired (`fkSieve2U`): `hasP` and the `p…` arguments hold a
walk waiting for its partner. -/
def largeGo (side : Side) (I32 : UInt32) (IU : UInt64) (len : USize) (k : Nat) (R : Array Nat)
    (b : ByteArray) (hasP : Bool) (px py pd0 pd1 : USize) (plg : UInt8) (pfuel : USize) :
    ByteArray × Array Nat :=
  if hk : k < side.primes.size then
    if h : len.toNat < b.size then
      let p := side.primes[k]
      let r := R[k]!
      if r ≥ p then largeGo side I32 IU len (k + 1) (R.set! k 0) b hasP px py pd0 pd1 plg pfuel
      else
        let w := fkBasis I32 p.toUInt32 0 r.toUInt32 1 128
        -- `1` from `fkBasis`: the basis does not fit, keep the root behind a flag
        let R := R.set! k (if w == 1 then 4611686018427387904 + r else w.toNat)
        let lg := side.logs.get! k
        if w == 0 then largeGo side I32 IU len (k + 1) R b hasP px py pd0 pd1 plg pfuel
        else if w == 1 then
          largeGo side I32 IU len (k + 1) R (fkGoU b len h IU p.toUInt64 lg p.toUInt64 0 r.toUInt64 1 128)
            hasP px py pd0 pd1 plg pfuel
        else
          let x := (w &&& 8191).toUSize
          let y := ((w >>> 13) &&& 8191).toUSize
          let d0 := (((w >>> 26) &&& 262143) * IU).toUSize - x
          let d1 := (((w >>> 44) &&& 262143) * IU).toUSize + y
          let fuel := 2 * len / p.toUSize + 4
          if hasP then
            largeGo side I32 IU len (k + 1) R
              (fkSieve2U b len h (IU - 1).toUSize px py pd0 pd1 plg (IU / 2).toUSize x y d0 d1 lg
                (IU / 2).toUSize (min pfuel fuel) (pfuel - min pfuel fuel) (fuel - min pfuel fuel))
              false 0 0 0 0 0 0
          else largeGo side I32 IU len (k + 1) R b true x y d0 d1 lg fuel
    else (b, R)
  else if h : hasP ∧ len.toNat < b.size then
    (fkSieveU b len h.2 (IU - 1).toUSize px py pd0 pd1 plg (IU / 2).toUSize pfuel, R)
  else (b, R)
termination_by side.primes.size - k

/-- `sieveLargeCached` by `largeGo`. -/
def sieveLargePaired (ctx : LasCtx) (side : Side) (R : Array Nat) (buf : ByteArray) :
    ByteArray × Array Nat :=
  largeGo side ctx.I.toUInt32 ctx.I.toUInt64 (ctx.I * ctx.J).toUSize side.largeStart R buf
    false 0 0 0 0 0 0

/-- `resieveCached` with the walks of consecutive ideals paired (`fkWalkB2U`). -/
def resieveGo (side : Side) (RB : Array Nat) (bits : ByteArray) (bsz : USize)
    (hb : bsz.toNat ≤ bits.size) (I : UInt64) (len : USize) (k : Nat) (acc : Array Nat)
    (hasP : Bool) (px py pd0 pd1 : USize) (pk : UInt64) (pfuel : USize) : Array Nat :=
  if hk : k < side.primes.size then
    let w := RB[k]!.toUInt64
    if w == 0 then resieveGo side RB bits bsz hb I len (k + 1) acc hasP px py pd0 pd1 pk pfuel
    else
      let p := side.primes[k]
      if w ≥ 4611686018427387904 then
        resieveGo side RB bits bsz hb I len (k + 1)
          (fkGoBU bits bsz hb len I p.toUInt64 k.toUInt64 acc p.toUInt64 0 (w - 4611686018427387904) 1 128)
          hasP px py pd0 pd1 pk pfuel
      else
        let x := (w &&& 8191).toUSize
        let y := ((w >>> 13) &&& 8191).toUSize
        let d0 := (((w >>> 26) &&& 262143) * I).toUSize - x
        let d1 := (((w >>> 44) &&& 262143) * I).toUSize + y
        let fuel := 2 * len / p.toUSize + 4
        if hasP then
          resieveGo side RB bits bsz hb I len (k + 1)
            (fkWalkB2U bits bsz hb len (I - 1).toUSize px py pd0 pd1 pk (I / 2).toUSize x y d0 d1
              k.toUInt64 (I / 2).toUSize acc (min pfuel fuel) (pfuel - min pfuel fuel)
              (fuel - min pfuel fuel))
            false 0 0 0 0 0 0
        else resieveGo side RB bits bsz hb I len (k + 1) acc true x y d0 d1 k.toUInt64 fuel
  else if hasP then fkWalkBU bits bsz hb len (I - 1).toUSize px py pd0 pd1 pk (I / 2).toUSize acc pfuel
  else acc
termination_by side.primes.size - k

/-- `resieveCached` by `resieveGo`. -/
def resievePaired (ctx : LasCtx) (side : Side) (RB : Array Nat) (bits : ByteArray)
    (acc : Array Nat) : Array Nat :=
  let bsz := bits.size.toUSize
  if hb : bsz.toNat ≤ bits.size then
    resieveGo side RB bits bsz hb ctx.I.toUInt64 (ctx.I * ctx.J).toUSize side.largeStart acc
      false 0 0 0 0 0 0
  else acc

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

/-- `sieveSide` with the machine-word kernels. -/
def sieveSideU (ctx : LasCtx) (side : Side) (R : Array Nat) (buf : ByteArray) : ByteArray := Id.run do
  let I := ctx.I
  let len := I * ctx.J
  let lenU := len.toUSize
  let mut b := buf
  if lenU.toNat < b.size then
    for k in [side.sieveStart:side.largeStart] do
      let p := side.primes[k]!
      let r := R[k]!
      if r ≥ p then continue
      let lg := side.logs.get! k
      if hb' : lenU.toNat < b.size then
        b := lineSieveU b lenU hb' p.toUSize r.toUSize I.toUSize ctx.J.toUSize lg
          ((I + p - 1) / p).toUSize 1 ((r + I / 2) % p).toUSize ctx.J.toUSize
    let IU := I.toUInt64
    for k in [side.largeStart:side.primes.size] do
      let p := side.primes[k]!
      let r := R[k]!
      if r ≥ p then continue
      let lg := side.logs.get! k
      if hb' : lenU.toNat < b.size then
        b := fkGoU b lenU hb' IU p.toUInt64 lg p.toUInt64 0 r.toUInt64 1 128
  return b

/-- `processQWith` with the machine-word kernels, small common factors of
`(i, j)` dropped before the prefilter and `factorSurvivor2`. -/
def processQ11 (ctx : LasCtx) (q ρ : Nat) (sc : Scratch) : Array Rel × Scratch := Id.run do
  let ⟨b1, b2, bits⟩ := sc
  let (u, v) := reduceLattice q ρ ctx.skew
  let (ua, ub, va, vb) := (u.1, u.2, v.1, v.2)
  let len := ctx.I * ctx.J
  let Rr := latticeRoots ctx.rat ua ub va vb
  let Ra := latticeRoots ctx.alg ua ub va vb
  let thrR := rowThresholds ctx q ua ub va vb ctx.params.mfbR false
  let thrA := rowThresholds ctx q ua ub va vb ctx.params.mfbA true
  let bufR := sieveSideU ctx ctx.rat Rr (fillRows ctx b1 thrR)
  let bufA := sieveSideU ctx ctx.alg Ra (fillRows ctx b2 thrA)
  let surv := prefilterRows ctx q ua ub va vb thrR thrA bufR bufA
    (dropSmallGcd ctx (survivors bufR bufA len))
  if surv.isEmpty then return (#[], ⟨bufR, bufA, bits⟩)
  let (lab, rowStart) := labelSurvivors ctx (zeroRows ctx bufA) surv
  let bits := markBits bits surv true
  let listsR := groupLabelled ctx surv lab rowStart (resieveSideBU ctx ctx.rat Rr bits #[])
  let listsA := groupLabelled ctx surv lab rowStart (resieveSideBU ctx ctx.alg Ra bits #[])
  let bits := markBits bits surv false
  let mut rels : Array Rel := #[]
  for k in [0:surv.size] do
    if let some rel := factorSurvivor2 ctx q ρ ua ub va vb Rr Ra listsR[k]! listsA[k]! surv[k]! then
      rels := rels.push rel
  return (rels, ⟨bufR, lab, bits⟩)

/-- `sieveSideU` without the large ideals (line sieve only). -/
def lineSieveSide (ctx : LasCtx) (side : Side) (R : Array Nat) (buf : ByteArray) : ByteArray :=
  Id.run do
  let I := ctx.I
  let len := I * ctx.J
  let lenU := len.toUSize
  let mut b := buf
  for k in [side.sieveStart:side.largeStart] do
    let p := side.primes[k]!
    let r := R[k]!
    if r ≥ p then continue
    let lg := side.logs.get! k
    if hb' : lenU.toNat < b.size then
      b := lineSieveU b lenU hb' p.toUSize r.toUSize I.toUSize ctx.J.toUSize lg
        ((I + p - 1) / p).toUSize 1 ((r + I / 2) % p).toUSize ctx.J.toUSize
  return b

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
(`prev` is the norm's logarithm at the left end of segment `s`); the row starts
`extra` above its bias (the degenerate ideals dividing the whole row). -/
def fillRowSegs (ctx : LasCtx) (alg : Bool) (cs : FloatArray) (d : Nat)
    (uaf ubf vaf vbf mF y1F qF : Float) (mfbF : Float) (j : Nat) (jF : Float) (b bias : ByteArray)
    (prev : Float) (s segs extra : Nat) : ByteArray × ByteArray :=
  if s < segs then
    let iF := nf ((s + 1) * 64) - nf (ctx.I / 2)
    let next := normBits alg cs d uaf ubf vaf vbf mF y1F qF iF jF
    let bits := if prev > next then prev else next
    let t := bits - mfbF
    let ti : Nat := if t ≤ fc 0 then 0 else if t ≥ fc 127 then 127 else t.toUInt64.toNat
    let b := ctx.rowTemplates[min 255 (128 - ti + extra)]!.copySlice 0 b (j * ctx.I + s * 64) 64
    fillRowSegs ctx alg cs d uaf ubf vaf vbf mF y1F qF mfbF j jF b (bias.push (128 - ti).toUInt8)
      next (s + 1) segs extra
  else (b, bias)
termination_by segs - s

/-- The whole region, row by row, and the segment biases (`J · I / 64` bytes);
row `j` starts `extra[j]` above its biases (`#[]`: none). -/
def fillSegments (ctx : LasCtx) (buf : ByteArray) (alg : Bool) (q : Nat) (ua ub va vb : Int)
    (mfb : Nat) (extra : Array Nat := #[]) : ByteArray × ByteArray := Id.run do
  let cs := coeffsF ctx
  let d := cs.size - 1
  let (uaf, ubf, vaf, vbf) := (intF ua, intF ub, intF va, intF vb)
  let mF := nf ctx.base.sel.m
  let y1F := nf ctx.base.sel.y1
  let qF := nf q
  let mfbF := nf (mfb + ctx.params.fudge + (if alg then ctx.params.fudgeA else 0))
  let segs := ctx.I / 64
  let mut b := buf
  let mut bias := ByteArray.emptyWithCapacity (ctx.J * segs)
  for j in [0:ctx.J] do
    let jF := nf j
    let first := normBits alg cs d uaf ubf vaf vbf mF y1F qF (Float.neg (nf (ctx.I / 2))) jF
    let (b', bias') := fillRowSegs ctx alg cs d uaf ubf vaf vbf mF y1F qF mfbF j jF b bias first 0 segs
      (extra.getD j 0)
    b := b'
    bias := bias'
  return (b.set! (ctx.I * ctx.J) 0, bias)

/-- The tiny prime ideals of a side (`p < sieveFrom`, nondegenerate, `2`
included), which `processQ13` does not sieve (their powers it does):
`(p, lattice root, log, p⁻¹ mod 2^32 (0 for 2), ⌊(2^32-1)/p⌋)` for `tinyAt2`. -/
def tinyPrimes (ctx : LasCtx) (side : Side) (R : Array Nat) :
    Array (Nat × Nat × Nat × UInt32 × UInt32) := Id.run do
  let mut out := #[]
  for k in [0:side.largeStart] do
    let p := side.primes[k]!
    if p ≥ ctx.params.sieveFrom || R[k]! ≥ p then continue
    out := out.push (p, R[k]!, (side.logs.get! k).toNat,
      if p == 2 then 0 else SIQS.inv32 p.toUInt32, (0xFFFFFFFF : UInt32) / p.toUInt32)
  return out

/-- `tinyAt` for `tinyPrimes` (the prime `2` tested by parity). -/
def tinyAt2 (tiny : Array (Nat × Nat × Nat × UInt32 × UInt32)) (c j I : UInt64) : Nat := Id.run do
  let mut acc := 0
  for (p, R, lg, inv, lim) in tiny do
    let y := c + I * p.toUInt64 - I / 2 - j * R.toUInt64
    if (if p == 2 then y &&& 1 == 0 else y.toUInt32 * inv ≤ lim) then acc := acc + lg
  return acc

/-- `prefilterGap` counting the tiny prime ideals exactly (`tinyPrimes` of each
side), so that `slack` only covers rounding. -/
def prefilterGap4 (ctx : LasCtx) (q : Nat) (ua ub va vb : Int) (bufR bufA biasR biasA : ByteArray)
    (tR tA : Array (Nat × Nat × Nat × UInt32 × UInt32)) (slack : Nat) (surv0 : Array Nat) :
    Array Nat :=
  let cs := coeffsF ctx
  let d := cs.size - 1
  let (uaf, ubf, vaf, vbf) := (intF ua, intF ub, intF va, intF vb)
  let mF := nf ctx.base.sel.m
  let y1F := nf ctx.base.sel.y1
  let qF := nf q
  let I := ctx.I
  let segs := I / 64
  let sl := nf slack
  let limR := nf ctx.params.mfbR + sl
  let limA := nf ctx.params.mfbA + sl
  let gapR0 := nf ctx.params.lpbR + sl
  let gapR1 := fc 2 * Float.log2 (nf ctx.limR) - sl - fc 1
  let gapA0 := nf ctx.params.lpbA + sl
  let gapA1 := fc 2 * Float.log2 (nf ctx.limA) - sl - fc 1
  surv0.filter fun pos =>
    let j := pos / I
    let c := pos % I
    let iF := nf c - nf (I / 2)
    let jF := nf j
    let seg := j * segs + c / 64
    let estR := normBits false cs d uaf ubf vaf vbf mF y1F qF iF jF -
      ((bufR.get! pos).toUInt64.toFloat - (biasR.get! seg).toUInt64.toFloat) -
      nf (tinyAt2 tR c.toUInt64 j.toUInt64 I.toUInt64)
    if estR > limR || (estR > gapR0 && estR < gapR1) then false
    else
      let estA := normBits true cs d uaf ubf vaf vbf mF y1F qF iF jF -
        ((bufA.get! pos).toUInt64.toFloat - (biasA.get! seg).toUInt64.toFloat) -
        nf (tinyAt2 tA c.toUInt64 j.toUInt64 I.toUInt64)
      estA ≤ limA && !(estA > gapA0 && estA < gapA1)

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

/-- `processQ5` with the even-even survivors dropped and `factorSurvivor2`. -/
def processQ7 (ctx : LasCtx) (q ρ : Nat) (sc : Scratch) : Array Rel × Scratch := Id.run do
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
  let surv := prefilterExact ctx q ua ub va vb bufR bufA biasR biasA
    (dropEvenEven ctx (survivors bufR bufA len))
  if surv.isEmpty then return (#[], ⟨bufR, bufA, bits⟩)
  let (lab, rowStart) := labelSurvivors ctx (zeroRows ctx bufA) surv
  let bits := markBits bits surv true
  let listsR := groupLabelled ctx surv lab rowStart (resieveSideB ctx ctx.rat Rr bits #[])
  let listsA := groupLabelled ctx surv lab rowStart (resieveSideB ctx ctx.alg Ra bits #[])
  let bits := markBits bits surv false
  let mut rels : Array Rel := #[]
  for k in [0:surv.size] do
    if let some rel := factorSurvivor2 ctx q ρ ua ub va vb Rr Ra listsR[k]! listsA[k]! surv[k]! then
      rels := rels.push rel
  return (rels, ⟨bufR, lab, bits⟩)

/-- `processQ7` with prime powers sieved, small common factors of `(i, j)`
dropped and the gap prefilter (`slack` bits). -/
def processQ8 (ctx : LasCtx) (slack : Nat) (q ρ : Nat) (sc : Scratch) : Array Rel × Scratch :=
  Id.run do
  let ⟨b1, b2, bits⟩ := sc
  let (u, v) := reduceLattice q ρ ctx.skew
  let (ua, ub, va, vb) := (u.1, u.2, v.1, v.2)
  let len := ctx.I * ctx.J
  let Rr := latticeRoots ctx.rat ua ub va vb
  let Ra := latticeRoots ctx.alg ua ub va vb
  let Pr := powerRoots ctx.rat ua ub va vb
  let Pa := powerRoots ctx.alg ua ub va vb
  let (fR, biasR) := fillSegments ctx b1 false q ua ub va vb ctx.params.mfbR (rowExtras ctx ctx.rat Rr)
  let (fA, biasA) := fillSegments ctx b2 true q ua ub va vb ctx.params.mfbA (rowExtras ctx ctx.alg Ra)
  let bufR := sievePowers ctx ctx.rat Pr (sieveSide ctx ctx.rat Rr fR)
  let bufA := sievePowers ctx ctx.alg Pa (sieveSide ctx ctx.alg Ra fA)
  let surv := prefilterGap ctx q ua ub va vb bufR bufA biasR biasA slack
    (dropSmallGcd ctx (survivors bufR bufA len))
  if surv.isEmpty then return (#[], ⟨bufR, bufA, bits⟩)
  let (lab, rowStart) := labelSurvivors ctx (zeroRows ctx bufA) surv
  let bits := markBits bits surv true
  let listsR := groupLabelled ctx surv lab rowStart (resieveSideB ctx ctx.rat Rr bits #[])
  let listsA := groupLabelled ctx surv lab rowStart (resieveSideB ctx ctx.alg Ra bits #[])
  let bits := markBits bits surv false
  let mut rels : Array Rel := #[]
  for k in [0:surv.size] do
    if let some rel := factorSurvivor2 ctx q ρ ua ub va vb Rr Ra listsR[k]! listsA[k]! surv[k]! then
      rels := rels.push rel
  return (rels, ⟨bufR, lab, bits⟩)

/-! ## Unbiased regions: the powers of 2 as a pattern, thresholds per segment

The region starts from the contribution of the ideals above 2 (their powers up
to `2^6`): it repeats every 64 columns, so each row is one 64-byte pattern
replicated by copying. The other ideals are sieved on top; a position survives
when its byte reaches its segment's threshold (the largest norm of the 64-column
segment less `mfb + fudge` and the degenerate ideals of the row). -/

/-- The ideals above 2 of a side as `(2^k, lattice root)` (`k ≤ 6`, nondegenerate),
from the prime ideals (`R`) and their powers (`Rp`). -/
def twoIdeals (side : Side) (R Rp : Array Nat) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  for k in [0:side.largeStart] do
    if side.primes[k]! == 2 && R[k]! < 2 then out := out.push (2, R[k]!)
  for k in [0:side.pw.size] do
    let M := side.pw[k]!
    if M ≤ 64 && M &&& (M - 1) == 0 && Rp[k]! < M then out := out.push (M, Rp[k]!)
  return out

/-- Add 1 at `c, c + M, …` below 64 in the 64-byte pattern `b` (offset `base`). -/
def patAdd (b : ByteArray) (base c M : Nat) : ByteArray := Id.run do
  let mut b := b
  let mut c := c
  while c < 64 do
    b := b.set! (base + c) (b.get! (base + c) + 1)
    c := c + M
  return b

/-- Initialize every row with the pattern of the ideals above 2 (`twos`): the
64-byte pattern is replicated into a 512-byte block, copied across the row (the
copies go between distinct arrays: a slice copied within one array would make
Lean copy the whole array first). -/
def initTwos (ctx : LasCtx) (twos : Array (Nat × Nat)) (buf : ByteArray) : ByteArray := Id.run do
  let I := ctx.I
  let half := I / 2
  let mut b := buf
  let mut pat := ctx.rowTemplates[0]!.extract 0 64
  let mut blk := ctx.rowTemplates[0]!.extract 0 512
  for j in [0:ctx.J] do
    let base := j * I
    pat := ctx.rowTemplates[0]!.copySlice 0 pat 0 64
    for (M, R) in twos do
      pat := patAdd pat 0 ((j * R + half) % M) M
    for k in [0:8] do
      blk := pat.copySlice 0 blk (64 * k) 64
    let mut w := 0
    while w < I do
      b := blk.copySlice 0 b (base + w) (min 512 (I - w))
      w := w + 512
  return b.set! (I * ctx.J) 0

/-- Per-segment thresholds (`J · I / 64` bytes): the largest norm's logarithm on
the segment (at its ends) less `mfb + fudge` and the row's degenerate ideals. -/
def segThresholds (ctx : LasCtx) (alg : Bool) (q : Nat) (ua ub va vb : Int) (mfb : Nat)
    (extra : Array Nat) : ByteArray := Id.run do
  let cs := coeffsF ctx
  let d := cs.size - 1
  let (uaf, ubf, vaf, vbf) := (intF ua, intF ub, intF va, intF vb)
  let mF := nf ctx.base.sel.m
  let y1F := nf ctx.base.sel.y1
  let qF := nf q
  let mfbF := nf (mfb + ctx.params.fudge)
  let segs := ctx.I / 64
  let mut out := ByteArray.emptyWithCapacity (ctx.J * segs)
  for j in [0:ctx.J] do
    let jF := nf j
    let ex := nf (extra.getD j 0)
    let mut prev := normBits alg cs d uaf ubf vaf vbf mF y1F qF (Float.neg (nf (ctx.I / 2))) jF
    for s in [0:segs] do
      let next := normBits alg cs d uaf ubf vaf vbf mF y1F qF (nf ((s + 1) * 64) - nf (ctx.I / 2)) jF
      let t := (if prev > next then prev else next) - mfbF - ex
      out := out.push (if t ≤ fc 0 then 0 else if t ≥ fc 255 then 255 else t.toUInt64.toUInt8)
      prev := next
  return out

/-- Positions `[c, e)` where both regions reach their thresholds. -/
def scanSeg (bA bR : ByteArray) (tA tR : UInt8) (c e : Nat) (acc : Array Nat) : Array Nat :=
  if h : c < e ∧ c < bA.size ∧ c < bR.size then
    scanSeg bA bR tA tR (c + 1) e
      (if bA.get c h.2.1 ≥ tA && bR.get c h.2.2 ≥ tR then acc.push c else acc)
  else acc
termination_by e - c

/-- Survivors of unbiased regions: segments are skipped unless their largest
byte reaches the threshold on both sides (the algebraic side first). -/
def survivorsSeg (ctx : LasCtx) (bufR bufA thrR thrA : ByteArray) : Array Nat := Id.run do
  let segs := ctx.I / 64
  let fmax (s : ByteArray) (a b : Nat) : UInt8 := s.foldl (fun acc x => max acc x) 0 a b
  let mut out : Array Nat := #[]
  for j in [0:ctx.J] do
    for sg in [0:segs] do
      let k := j * segs + sg
      let tA := thrA.get! k
      let c := j * ctx.I + sg * 64
      if fmax bufA c (c + 64) ≥ tA then
        let tR := thrR.get! k
        if fmax bufR c (c + 64) ≥ tR then
          out := scanSeg bufA bufR tA tR c (c + 64) out
  return out

/-- `prefilterGap` for unbiased regions (`extra`: the rows' degenerate ideals). -/
def prefilterGap2 (ctx : LasCtx) (q : Nat) (ua ub va vb : Int) (bufR bufA : ByteArray)
    (exR exA : Array Nat) (slack : Nat) (surv0 : Array Nat) : Array Nat :=
  let cs := coeffsF ctx
  let d := cs.size - 1
  let (uaf, ubf, vaf, vbf) := (intF ua, intF ub, intF va, intF vb)
  let mF := nf ctx.base.sel.m
  let y1F := nf ctx.base.sel.y1
  let qF := nf q
  let I := ctx.I
  let sl := nf slack
  let limR := nf ctx.params.mfbR + sl
  let limA := nf ctx.params.mfbA + sl
  let gapR0 := nf ctx.params.lpbR + sl
  let gapR1 := fc 2 * Float.log2 (nf ctx.limR) - sl - fc 1
  let gapA0 := nf ctx.params.lpbA + sl
  let gapA1 := fc 2 * Float.log2 (nf ctx.limA) - sl - fc 1
  surv0.filter fun pos =>
    let j := pos / I
    let c := pos % I
    let iF := nf c - nf (I / 2)
    let jF := nf j
    let estR := normBits false cs d uaf ubf vaf vbf mF y1F qF iF jF -
      (bufR.get! pos).toUInt64.toFloat - nf (exR.getD j 0)
    if estR > limR || (estR > gapR0 && estR < gapR1) then false
    else
      let estA := normBits true cs d uaf ubf vaf vbf mF y1F qF iF jF -
        (bufA.get! pos).toUInt64.toFloat - nf (exA.getD j 0)
      estA ≤ limA && !(estA > gapA0 && estA < gapA1)

/-- Line sieve the small ideals and their powers, except those above 2. -/
def sieveOdd (ctx : LasCtx) (side : Side) (R Rp : Array Nat) (buf : ByteArray) : ByteArray :=
  Id.run do
  let I := ctx.I
  let len := I * ctx.J
  let lenU := len.toUSize
  let mut b := buf
  if lenU.toNat < b.size then
    let mut bb := b
    for k in [0:side.largeStart] do
      let p := side.primes[k]!
      let r := R[k]!
      if r ≥ p || p < ctx.params.sieveFrom || p == 2 then continue
      let lg := side.logs.get! k
      if hb' : lenU.toNat < bb.size then
        bb := lineSieveU bb lenU hb' p.toUSize r.toUSize I.toUSize ctx.J.toUSize lg
          ((I + p - 1) / p).toUSize 1 ((r + I / 2) % p).toUSize ctx.J.toUSize
    for k in [0:side.pw.size] do
      let p := side.pw[k]!
      let r := Rp[k]!
      if r ≥ p || p &&& (p - 1) == 0 || side.pwBase[k]! < ctx.params.sieveFrom then continue
      let lg := side.pwLogs.get! k
      if hb' : lenU.toNat < bb.size then
        bb := lineSieveU bb lenU hb' p.toUSize r.toUSize I.toUSize ctx.J.toUSize lg
          ((I + p - 1) / p).toUSize 1 ((r + I / 2) % p).toUSize ctx.J.toUSize
    -- large ideals: Franke–Kleinjung reduction and walk
    let IU := I.toUInt64
    for k in [side.largeStart:side.primes.size] do
      let p := side.primes[k]!
      let r := R[k]!
      if r ≥ p then continue
      let lg := side.logs.get! k
      if hb' : lenU.toNat < bb.size then
        bb := fkGoU bb lenU hb' IU p.toUInt64 lg p.toUInt64 0 r.toUInt64 1 128
    b := bb
  return b

/-- The odd tiny ideals of a side (`3 ≤ p < sieveFrom`, and their powers), not
sieved: `(M, lattice root, log, M⁻¹ mod 2^32, ⌊(2^32-1)/M⌋)` for the test of
`tinyAt`. -/
def tinyIdeals (ctx : LasCtx) (side : Side) (R Rp : Array Nat) :
    Array (Nat × Nat × Nat × UInt32 × UInt32) := Id.run do
  let mut out := #[]
  for k in [0:side.largeStart] do
    let p := side.primes[k]!
    if p == 2 || p ≥ ctx.params.sieveFrom || R[k]! ≥ p then continue
    out := out.push (p, R[k]!, (side.logs.get! k).toNat, SIQS.inv32 p.toUInt32,
      (0xFFFFFFFF : UInt32) / p.toUInt32)
  for k in [0:side.pw.size] do
    let M := side.pw[k]!
    let p := side.pwBase[k]!
    if p == 2 || p ≥ ctx.params.sieveFrom || Rp[k]! ≥ M then continue
    out := out.push (M, Rp[k]!, (side.pwLogs.get! k).toNat, SIQS.inv32 M.toUInt32,
      (0xFFFFFFFF : UInt32) / M.toUInt32)
  return out

/-- The logarithm of the tiny ideals dividing the norm at column `c` of row `j`:
`M ∣ c + I M - I/2 - j R` tested by multiplication with `M⁻¹ (mod 2^32)`. -/
def tinyAt (tiny : Array (Nat × Nat × Nat × UInt32 × UInt32)) (c j I : UInt64) : Nat := Id.run do
  let mut acc := 0
  for (M, R, lg, inv, lim) in tiny do
    let y := c + I * M.toUInt64 - I / 2 - j * R.toUInt64
    if y.toUInt32 * inv ≤ lim then acc := acc + lg
  return acc

/-- `prefilterGap2` counting the odd tiny ideals exactly. -/
def prefilterGap3 (ctx : LasCtx) (q : Nat) (ua ub va vb : Int) (bufR bufA : ByteArray)
    (exR exA : Array Nat) (tR tA : Array (Nat × Nat × Nat × UInt32 × UInt32)) (slack : Nat)
    (surv0 : Array Nat) : Array Nat :=
  let cs := coeffsF ctx
  let d := cs.size - 1
  let (uaf, ubf, vaf, vbf) := (intF ua, intF ub, intF va, intF vb)
  let mF := nf ctx.base.sel.m
  let y1F := nf ctx.base.sel.y1
  let qF := nf q
  let I := ctx.I
  let sl := nf slack
  let limR := nf ctx.params.mfbR + sl
  let limA := nf ctx.params.mfbA + sl
  let gapR0 := nf ctx.params.lpbR + sl
  let gapR1 := fc 2 * Float.log2 (nf ctx.limR) - sl - fc 1
  let gapA0 := nf ctx.params.lpbA + sl
  let gapA1 := fc 2 * Float.log2 (nf ctx.limA) - sl - fc 1
  surv0.filter fun pos =>
    let j := pos / I
    let c := pos % I
    let iF := nf c - nf (I / 2)
    let jF := nf j
    let estR := normBits false cs d uaf ubf vaf vbf mF y1F qF iF jF -
      (bufR.get! pos).toUInt64.toFloat - nf (exR.getD j 0) -
      nf (tinyAt tR c.toUInt64 j.toUInt64 I.toUInt64)
    if estR > limR || (estR > gapR0 && estR < gapR1) then false
    else
      let estA := normBits true cs d uaf ubf vaf vbf mF y1F qF iF jF -
        (bufA.get! pos).toUInt64.toFloat - nf (exA.getD j 0) -
        nf (tinyAt tA c.toUInt64 j.toUInt64 I.toUInt64)
      estA ≤ limA && !(estA > gapA0 && estA < gapA1)

/-- `processQ9` with the odd tiny ideals counted at the survivors instead of
sieved (`sieveFrom` the first sieved odd prime; `fudge` covers them). -/
def processQ10 (ctx : LasCtx) (slack : Nat) (q ρ : Nat) (sc : Scratch) : Array Rel × Scratch :=
  Id.run do
  let ⟨b1, b2, bits⟩ := sc
  let (u, v) := reduceLattice q ρ ctx.skew
  let (ua, ub, va, vb) := (u.1, u.2, v.1, v.2)
  let Rr := latticeRoots ctx.rat ua ub va vb
  let Ra := latticeRoots ctx.alg ua ub va vb
  let Pr := powerRoots ctx.rat ua ub va vb
  let Pa := powerRoots ctx.alg ua ub va vb
  let exR := rowExtras ctx ctx.rat Rr
  let exA := rowExtras ctx ctx.alg Ra
  let thrR := segThresholds ctx false q ua ub va vb ctx.params.mfbR exR
  let thrA := segThresholds ctx true q ua ub va vb ctx.params.mfbA exA
  let bufR := sieveOdd ctx ctx.rat Rr Pr (initTwos ctx (twoIdeals ctx.rat Rr Pr) b1)
  let bufA := sieveOdd ctx ctx.alg Ra Pa (initTwos ctx (twoIdeals ctx.alg Ra Pa) b2)
  let surv := prefilterGap3 ctx q ua ub va vb bufR bufA exR exA (tinyIdeals ctx ctx.rat Rr Pr)
    (tinyIdeals ctx ctx.alg Ra Pa) slack (dropSmallGcd ctx (survivorsSeg ctx bufR bufA thrR thrA))
  if surv.isEmpty then return (#[], ⟨bufR, bufA, bits⟩)
  let (lab, rowStart) := labelSurvivors ctx (zeroRows ctx bufA) surv
  let bits := markBits bits surv true
  let listsR := groupLabelled ctx surv lab rowStart (resieveSideBU ctx ctx.rat Rr bits #[])
  let listsA := groupLabelled ctx surv lab rowStart (resieveSideBU ctx ctx.alg Ra bits #[])
  let bits := markBits bits surv false
  let mut rels : Array Rel := #[]
  for k in [0:surv.size] do
    if let some rel := factorSurvivor2 ctx q ρ ua ub va vb Rr Ra listsR[k]! listsA[k]! surv[k]! then
      rels := rels.push rel
  return (rels, ⟨bufR, lab, bits⟩)

/-- `processQ8` on unbiased regions with the powers of 2 as a pattern. -/
def processQ9 (ctx : LasCtx) (slack : Nat) (q ρ : Nat) (sc : Scratch) : Array Rel × Scratch :=
  Id.run do
  let ⟨b1, b2, bits⟩ := sc
  let (u, v) := reduceLattice q ρ ctx.skew
  let (ua, ub, va, vb) := (u.1, u.2, v.1, v.2)
  let Rr := latticeRoots ctx.rat ua ub va vb
  let Ra := latticeRoots ctx.alg ua ub va vb
  let Pr := powerRoots ctx.rat ua ub va vb
  let Pa := powerRoots ctx.alg ua ub va vb
  let exR := rowExtras ctx ctx.rat Rr
  let exA := rowExtras ctx ctx.alg Ra
  let thrR := segThresholds ctx false q ua ub va vb ctx.params.mfbR exR
  let thrA := segThresholds ctx true q ua ub va vb ctx.params.mfbA exA
  let bufR := sieveOdd ctx ctx.rat Rr Pr (initTwos ctx (twoIdeals ctx.rat Rr Pr) b1)
  let bufA := sieveOdd ctx ctx.alg Ra Pa (initTwos ctx (twoIdeals ctx.alg Ra Pa) b2)
  let surv := prefilterGap2 ctx q ua ub va vb bufR bufA exR exA slack
    (dropSmallGcd ctx (survivorsSeg ctx bufR bufA thrR thrA))
  if surv.isEmpty then return (#[], ⟨bufR, bufA, bits⟩)
  let (lab, rowStart) := labelSurvivors ctx (zeroRows ctx bufA) surv
  let bits := markBits bits surv true
  let listsR := groupLabelled ctx surv lab rowStart (resieveSideB ctx ctx.rat Rr bits #[])
  let listsA := groupLabelled ctx surv lab rowStart (resieveSideB ctx ctx.alg Ra bits #[])
  let bits := markBits bits surv false
  let mut rels : Array Rel := #[]
  for k in [0:surv.size] do
    if let some rel := factorSurvivor2 ctx q ρ ua ub va vb Rr Ra listsR[k]! listsA[k]! surv[k]! then
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

/-! ## Floating-point cofactor bounds before exact factoring

`factorSurvivor2` computes the norms with big numbers and divides out every
factor-base prime before its cheap checks reject most survivors (at 100 digits
four in five, on the rational side). The bound below needs no big numbers: the
norm's logarithm (floating point), less the exact part of the tiny primes
(`tinyRat`, `tinyAlg`) and `log₂ p` once for every other factor-base ideal found
at the survivor (`smallLogs` and the resieve lists), bounds the cofactor's
logarithm from above unless the square of a prime `≥ sieveFrom` divides the norm
(rare: such a survivor can be lost, never a wrong relation produced). Survivors
whose bound exceeds `mfb` or lies inside the gap `(lpb, 2 log₂ lim)` of
`cofactorClass` are rejected; the others are factored by `factorSurvivor2`. -/

/-- The lattice roots modulo `p²` of the small ideals `[sieveStart, largeStart)`
of a side (from `sqRoots`; `p²` when there is none: no simple root, or the
ideal is degenerate for this basis). -/
def squareRoots (side : Side) (ua ub va vb : Int) : Array Nat := Id.run do
  let mut out : Array Nat := Array.replicate side.largeStart 0
  if ua.natAbs < 2 ^ 31 && ub.natAbs < 2 ^ 31 && va.natAbs < 2 ^ 31 && vb.natAbs < 2 ^ 31 then
    let (a, b, c, d) := (ua.toInt64, ub.toInt64, va.toInt64, vb.toInt64)
    for k in [side.sieveStart:side.largeStart] do
      let p := side.primes[k]!
      let M := p * p
      let r := side.sqRoots[k]!
      out := out.set! k (if r ≥ M then M else (latticeRootI M.toUInt64 r.toUInt64 a b c d).toNat)
  else
    for k in [side.sieveStart:side.largeStart] do
      out := out.set! k (side.primes[k]! * side.primes[k]!)
  return out

/-- `Σ log₂ p` (twice when `p²` divides) over the small ideals `[k, stop)` (odd
`p`) whose progression contains column `c` of row `j`, as `smallHits`; a
degenerate ideal (lattice root `R ≥ p`) divides the norm exactly on the rows
`j ≡ 0 (mod p)` (`rowExtras`). `S`: the roots modulo `p²` (`squareRoots`). -/
def smallLogs (side : Side) (R S : Array Nat) (c j I : UInt64) (k stop : Nat) (acc : Float) :
    Float :=
  if k < stop then
    let p := side.primes[k]!.toUInt64
    let r := R[k]!.toUInt64
    let hit := if r ≥ p then j % p == 0
      else (c + I * p - I / 2 - j * r).toUInt32 * side.pinv[k]! ≤ side.lim[k]!
    let acc := if hit then
        let lg := side.lg2.get! k
        let M := p * p
        let r2 := S[k]!.toUInt64
        if r < p && r2 < M && (c + I * M - I / 2 - j * r2) % M == 0 then acc + lg + lg else acc + lg
      else acc
    smallLogs side R S c j I (k + 1) stop acc
  else acc
termination_by stop - k

/-- Per special-`q` words of the small ideals `[sieveStart, largeStart)` of a side
for `smallLogsP`: `p ||| r <<< 12 ||| r₂ <<< 24` with the lattice roots `r`
modulo `p` (`p`: degenerate) and `r₂` modulo `p²` (`p²`: none). -/
def packSmall (side : Side) (R S : Array Nat) : Array Nat :=
  (Array.range (side.largeStart - side.sieveStart)).map fun i =>
    let k := side.sieveStart + i
    let p := side.primes[k]!
    p + (min R[k]! p) * 4096 + (min S[k]! (p * p)) * 16777216

/-- `smallLogs` from the packed words of `packSmall` and `Side.pinvLim` (two
reads per ideal); `x0 = c - I/2` (wrapping). -/
def smallLogsP (tab pl : Array Nat) (lg2 : FloatArray) (off : Nat) (x0 j I : UInt64) (k : Nat)
    (acc : Float) : Float :=
  if h : k < tab.size ∧ k < pl.size then
    let w := tab[k].toUInt64
    let p := w &&& 4095
    let r := (w >>> 12) &&& 4095
    let v := pl[k].toUInt64
    let hit := if r ≥ p then j % p == 0
      else (x0 + I * p - j * r).toUInt32 * v.toUInt32 ≤ (v >>> 32).toUInt32
    let acc := if hit then
        let lg := lg2.get! (off + k)
        let M := p * p
        let r2 := w >>> 24
        if r < p && r2 < M && (x0 + I * M - j * r2) % M == 0 then acc + lg + lg else acc + lg
      else acc
    smallLogsP tab pl lg2 off x0 j I (k + 1) acc
  else acc
termination_by tab.size - k

/-- `v_p(r)` for a residue modulo `p^K` (`K` if `r = 0`), tail recursive. -/
def valU (r p : UInt64) (acc : Nat) : Nat → Nat
  | 0 => acc
  | K + 1 => if r % p == 0 then valU (r / p) p (acc + 1) K else acc

/-- `Σ c_k a^k b^(d-k) mod P` by Horner's rule from the top (`acc` the leading
part, `bp` the current power of `b`): no allocation. -/
def hornerMod (cs : Array Nat) (a b P : UInt64) : Nat → UInt64 → UInt64 → UInt64
  | 0, acc, _ => acc
  | k + 1, acc, bp =>
    let bp := bp * b % P
    hornerMod cs a b P k ((acc * a + cs[k]!.toUInt64 * bp) % P) bp

/-- `tinyRat` with machine words, tail recursive (`i0 = I/2`). -/
def tinyRatU (t : TinyQ) (c j i0 : UInt64) (k : Nat) (acc : Float) : Float :=
  if k < t.p.size then
    let P := t.P[k]!.toUInt64
    let i := (c + P - i0 % P) % P
    let r := (i * t.rA[k]!.toUInt64 + j * t.rB[k]!.toUInt64) % P
    tinyRatU t c j i0 (k + 1) (acc + nf (valU r t.p[k]!.toUInt64 0 t.K[k]!) * t.lg.get! k)
  else acc
termination_by t.p.size - k

/-- `tinyAlg` with machine words, tail recursive (`i0 = I/2`). -/
def tinyAlgU (t : TinyQ) (c j i0 : UInt64) (k : Nat) (acc : Float) : Float :=
  if k < t.p.size then
    let P := t.P[k]!.toUInt64
    let i := (c + P - i0 % P) % P
    let a := (i * t.ua[k]!.toUInt64 + j * t.va[k]!.toUInt64) % P
    let b := (i * t.ub[k]!.toUInt64 + j * t.vb[k]!.toUInt64) % P
    let cs := t.cs[k]!
    let d := cs.size - 1
    let v := hornerMod cs a b P d (cs[d]!.toUInt64 % P) 1
    tinyAlgU t c j i0 (k + 1) (acc + nf (valU v t.p[k]!.toUInt64 0 t.K[k]!) * t.lg.get! k)
  else acc
termination_by t.p.size - k

/-- Per special-`q` data of the floating-point bounds: the tiny-prime residues,
the basis and polynomials as floats, and the rejection limits of each side
(`mfb`, and the gap `(lpb, 2 log₂ lim)`, each narrowed by a quarter bit). -/
structure Bounds where
  tq : TinyQ
  /-- `packSmall` of each side. -/
  tabR : Array Nat
  tabA : Array Nat
  /-- The basis, `Y₁`, `m`, `q` and the algebraic coefficients modulo `2^64`. -/
  ua64 : UInt64
  ub64 : UInt64
  va64 : UInt64
  vb64 : UInt64
  y1U : UInt64
  mU : UInt64
  qU : UInt64
  cs64 : Array UInt64
  /-- `lpb`, `mfb` and `lim²` of each side as words. -/
  lpbR : UInt64
  mfbR : UInt64
  lim2R : UInt64
  lpbA : UInt64
  mfbA : UInt64
  lim2A : UInt64
  cs : FloatArray
  uaf : Float
  ubf : Float
  vaf : Float
  vbf : Float
  mF : Float
  y1F : Float
  qF : Float
  hiR : Float
  loR : Float
  gapR : Float
  hiA : Float
  loA : Float
  gapA : Float

def mkBounds (ctx : LasCtx) (q : Nat) (ua ub va vb : Int) (Rr Ra : Array Nat) : Bounds :=
  let tol := fc 1 / fc 4
  let w (x : Int) : UInt64 := (x % 18446744073709551616).toNat.toUInt64
  { tq := mkTinyQ ctx ua ub va vb, tabR := packSmall ctx.rat Rr (squareRoots ctx.rat ua ub va vb),
    tabA := packSmall ctx.alg Ra (squareRoots ctx.alg ua ub va vb), cs := coeffsF ctx,
    ua64 := w ua, ub64 := w ub, va64 := w va, vb64 := w vb, y1U := w ctx.base.sel.y1,
    mU := w ctx.base.sel.m, qU := w q, cs64 := ctx.base.sel.coeffs.map w,
    lpbR := ctx.params.lpbR.toUInt64, mfbR := ctx.params.mfbR.toUInt64,
    lim2R := (ctx.limR * ctx.limR).toUInt64, lpbA := ctx.params.lpbA.toUInt64,
    mfbA := ctx.params.mfbA.toUInt64, lim2A := (ctx.limA * ctx.limA).toUInt64,
    uaf := intF ua, ubf := intF ub, vaf := intF va, vbf := intF vb,
    mF := nf ctx.base.sel.m, y1F := nf ctx.base.sel.y1, qF := nf q,
    hiR := nf ctx.params.mfbR + tol, loR := nf ctx.params.lpbR + tol,
    gapR := fc 2 * Float.log2 (nf ctx.limR) - tol,
    hiA := nf ctx.params.mfbA + tol, loA := nf ctx.params.lpbA + tol,
    gapA := fc 2 * Float.log2 (nf ctx.limA) - tol }

/-- A cofactor bound (bits) above `hi` or inside the gap `(lo, gap)`. -/
@[inline] def hopeless (est hi lo gap : Float) : Bool :=
  est > hi || (est > lo && est < gap)

/-- The floating-point bounds (bits) of the rational and algebraic cofactors at
`pos` (the latter only when `rat` is false). -/
def cofactorBound (ctx : LasCtx) (bd : Bounds) (rat : Bool) (list : List Nat) (pos : Nat) : Float :=
  let I := ctx.I
  let j := pos / I
  let c := pos % I
  let iF := nf c - nf (I / 2)
  let jF := nf j
  let aF := iF * bd.uaf + jF * bd.vaf
  let bF := iF * bd.ubf + jF * bd.vbf
  let (cU, jU, IU) := (c.toUInt64, j.toUInt64, I.toUInt64)
  let x0 := cU - IU / 2
  if rat then
    let side := ctx.rat
    Float.log2 ((bd.y1F * aF - bd.mF * bF).abs + fc 1) - tinyRatU bd.tq cU jU (IU / 2) 0 (fc 0) -
      smallLogsP bd.tabR side.pinvLim side.lg2 side.sieveStart x0 jU IU 0 (fc 0) -
      list.foldl (fun acc k => acc + side.lg2.get! k) (fc 0)
  else
    let d := bd.cs.size - 1
    let side := ctx.alg
    Float.log2 ((homEvalFA bd.cs aF bF d (bd.cs.get! d) (fc 1)).abs / bd.qF + fc 1) -
      tinyAlgU bd.tq cU jU (IU / 2) 0 (fc 0) -
      smallLogsP bd.tabA side.pinvLim side.lg2 side.sieveStart x0 jU IU 0 (fc 0) -
      list.foldl (fun acc k => acc + side.lg2.get! k) (fc 0)

/-- `factorSurvivor2` behind the floating-point cofactor bounds of both sides. -/
def factorSurvivor3 (ctx : LasCtx) (bd : Bounds) (q ρ : Nat) (ua ub va vb : Int)
    (Rr Ra : Array Nat) (listR listA : List Nat) (pos : Nat) : Option Rel :=
  if hopeless (cofactorBound ctx bd true listR pos) bd.hiR bd.loR bd.gapR then none
  else if hopeless (cofactorBound ctx bd false listA pos) bd.hiA bd.loA bd.gapA then none
  else factorSurvivor2 ctx q ρ ua ub va vb Rr Ra listR listA pos

/-! ### Cofactors modulo `2^64`

Four in five survivors fail the cheap checks of `factorSurvivor2`, most of them
because their cofactor (40 to 48 bits, no factor below the factor-base bound) is
prime, which the floating-point bound cannot see. The cofactor itself fits in a
machine word: the norm modulo `2^64` (wrapping arithmetic), shifted by the power
of 2 and multiplied by the inverse of the found odd prime powers, is the
cofactor modulo `2^(64 - v₂)`. It is trusted only when its logarithm matches the
floating-point bound (a missed power would give an unrelated word), and then
classified like `cofactorClass` (with the base-2 probable-prime screen). Only
survivors that pass on both sides are factored with big numbers. -/

/-- `Σ log₂ p` and `Π p mod 2^64` over the found ideals. -/
structure LogProd where
  lg : Float
  prod : UInt64

/-- `smallLogsP` that also multiplies the found primes (squares twice). -/
def smallScan (tab pl : Array Nat) (lg2 : FloatArray) (off : Nat) (x0 j I : UInt64) (k : Nat)
    (acc : Float) (pr : UInt64) : LogProd :=
  if h : k < tab.size ∧ k < pl.size then
    let w := tab[k].toUInt64
    let p := w &&& 4095
    let r := (w >>> 12) &&& 4095
    let v := pl[k].toUInt64
    let hit := if r ≥ p then j % p == 0
      else (x0 + I * p - j * r).toUInt32 * v.toUInt32 ≤ (v >>> 32).toUInt32
    if hit then
      let lg := lg2.get! (off + k)
      let M := p * p
      let r2 := w >>> 24
      if r < p && r2 < M && (x0 + I * M - j * r2) % M == 0 then
        smallScan tab pl lg2 off x0 j I (k + 1) (acc + lg + lg) (pr * M)
      else smallScan tab pl lg2 off x0 j I (k + 1) (acc + lg) (pr * p)
    else smallScan tab pl lg2 off x0 j I (k + 1) acc pr
  else ⟨acc, pr⟩
termination_by tab.size - k

/-- The tiny primes' part of a norm: `Σ v_p log₂ p`, `Π_{p odd} p^{v_p} mod 2^64`
and `v₂`. -/
structure TinyPart where
  lg : Float
  prod : UInt64
  v2 : UInt64

/-- `p^e` modulo `2^64`. -/
def powU (p : UInt64) : Nat → UInt64
  | 0 => 1
  | e + 1 => p * powU p e

/-- The tiny part of the rational norm at column `c` of row `j` (`i0 = I/2`). -/
def tinyRatP (t : TinyQ) (c j i0 : UInt64) (k : Nat) (lg : Float) (pr v2 : UInt64) : TinyPart :=
  if k < t.p.size then
    let P := t.P[k]!.toUInt64
    let p := t.p[k]!.toUInt64
    let i := (c + P - i0 % P) % P
    let r := (i * t.rA[k]!.toUInt64 + j * t.rB[k]!.toUInt64) % P
    let v := valU r p 0 t.K[k]!
    let lg := lg + nf v * t.lg.get! k
    if p == 2 then tinyRatP t c j i0 (k + 1) lg pr v.toUInt64
    else tinyRatP t c j i0 (k + 1) lg (pr * powU p v) v2
  else ⟨lg, pr, v2⟩
termination_by t.p.size - k

/-- The tiny part of the algebraic norm (`i0 = I/2`). -/
def tinyAlgP (t : TinyQ) (c j i0 : UInt64) (k : Nat) (lg : Float) (pr v2 : UInt64) : TinyPart :=
  if k < t.p.size then
    let P := t.P[k]!.toUInt64
    let p := t.p[k]!.toUInt64
    let i := (c + P - i0 % P) % P
    let a := (i * t.ua[k]!.toUInt64 + j * t.va[k]!.toUInt64) % P
    let b := (i * t.ub[k]!.toUInt64 + j * t.vb[k]!.toUInt64) % P
    let cs := t.cs[k]!
    let d := cs.size - 1
    let v := valU (hornerMod cs a b P d (cs[d]!.toUInt64 % P) 1) p 0 t.K[k]!
    let lg := lg + nf v * t.lg.get! k
    if p == 2 then tinyAlgP t c j i0 (k + 1) lg pr v.toUInt64
    else tinyAlgP t c j i0 (k + 1) lg (pr * powU p v) v2
  else ⟨lg, pr, v2⟩
termination_by t.p.size - k

/-- `x⁻¹ mod 2^64` for odd `x` (Newton's iteration; `x` is its own inverse
modulo 8). -/
@[inline] def inv64 (x : UInt64) : UInt64 :=
  let y := x * (2 - x * x)
  let y := y * (2 - x * y)
  let y := y * (2 - x * y)
  let y := y * (2 - x * y)
  y * (2 - x * y)

/-- `F(a, b) mod 2^64` (Horner from the top, as `hornerMod`). -/
def hornerU (cs : Array UInt64) (a b : UInt64) : Nat → UInt64 → UInt64 → UInt64
  | 0, acc, _ => acc
  | k + 1, acc, bp =>
    let bp := bp * b
    hornerU cs a b k (acc * a + cs[k]! * bp) bp

/-- `cofactorClass` on a word. -/
@[inline] def cofactorClassU (u lpb mfb lim2 : UInt64) : Nat :=
  if u == 1 then 1
  else if u >>> mfb != 0 then 0
  else if u >>> lpb == 0 then 1
  else if u < lim2 then 0
  else if u >>> 52 == 0 && u &&& 1 == 1 && sprp2 u then 0
  else 2

/-- The class of a side's cofactor from the norm modulo `2^64` (`n64`, absolute
value), the product of the found odd prime powers and `v₂`, if the word matches
the floating-point bound `est`; `3` (undecided) otherwise. -/
def sideClass (est : Float) (n64 odd v2 lpb mfb lim2 : UInt64) : Nat :=
  let u := (n64 >>> v2) * inv64 odd
  let u := if v2 == 0 then u else u &&& ((1 <<< (64 - v2)) - 1)
  if (Float.log2 u.toFloat - est).abs < fc 1 / fc 4 then cofactorClassU u lpb mfb lim2 else 3

/-- Where the word checks leave a survivor: `0`/`1` rejected by the rational
bound or class, `2`/`3` by the algebraic ones, `4 + 2 cr' + ca'` passed (`cr'`,
`ca'` whether the class was decided, `1`, or undecided, `0`). -/
def survivorGate (ctx : LasCtx) (bd : Bounds) (listR listA : List Nat) (pos : Nat) : Nat :=
  let I := ctx.I
  let j := pos / I
  let c := pos % I
  let iF := nf c - nf (I / 2)
  let jF := nf j
  let aF := iF * bd.uaf + jF * bd.vaf
  let bF := iF * bd.ubf + jF * bd.vbf
  let (cU, jU, IU) := (c.toUInt64, j.toUInt64, I.toUInt64)
  let x0 := cU - IU / 2
  let a64 := x0 * bd.ua64 + jU * bd.va64
  let b64 := x0 * bd.ub64 + jU * bd.vb64
  let side := ctx.rat
  let nF := bd.y1F * aF - bd.mF * bF
  let tR := tinyRatP bd.tq cU jU (IU / 2) 0 (fc 0) 1 0
  let sR := smallScan bd.tabR side.pinvLim side.lg2 side.sieveStart x0 jU IU 0 (fc 0) 1
  let lR := listR.foldl (fun acc k => acc + side.lg2.get! k) (fc 0)
  let estR := Float.log2 (nF.abs + fc 1) - tR.lg - sR.lg - lR
  if hopeless estR bd.hiR bd.loR bd.gapR then 0
  else
    let n64 := bd.y1U * a64 - bd.mU * b64
    let pR := listR.foldl (fun acc k => acc * side.primes[k]!.toUInt64) 1
    let cr := sideClass estR (if nF < fc 0 then -n64 else n64) (tR.prod * sR.prod * pR) tR.v2
      bd.lpbR bd.mfbR bd.lim2R
    if cr == 0 then 1
    else
      let d := bd.cs.size - 1
      let sideA := ctx.alg
      let fF := homEvalFA bd.cs aF bF d (bd.cs.get! d) (fc 1)
      let tA := tinyAlgP bd.tq cU jU (IU / 2) 0 (fc 0) 1 0
      let sA := smallScan bd.tabA sideA.pinvLim sideA.lg2 sideA.sieveStart x0 jU IU 0 (fc 0) 1
      let lA := listA.foldl (fun acc k => acc + sideA.lg2.get! k) (fc 0)
      let estA := Float.log2 (fF.abs / bd.qF + fc 1) - tA.lg - sA.lg - lA
      if hopeless estA bd.hiA bd.loA bd.gapA then 2
      else
        let f64 := hornerU bd.cs64 a64 b64 d (bd.cs64[d]!) 1
        let pA := listA.foldl (fun acc k => acc * sideA.primes[k]!.toUInt64) 1
        let ca := sideClass estA (if fF < fc 0 then -f64 else f64)
          (bd.qU * tA.prod * sA.prod * pA) tA.v2 bd.lpbA bd.mfbA bd.lim2A
        if ca == 0 then 3
        else 4 + 2 * (if cr == 3 then 0 else 1) + (if ca == 3 then 0 else 1)

/-- `factorSurvivor2` behind `survivorGate`. -/
def factorSurvivor4 (ctx : LasCtx) (bd : Bounds) (q ρ : Nat) (ua ub va vb : Int)
    (Rr Ra : Array Nat) (listR listA : List Nat) (pos : Nat) : Option Rel :=
  if survivorGate ctx bd listR listA pos < 4 then none
  else factorSurvivor2 ctx q ρ ua ub va vb Rr Ra listR listA pos


/-! ### The gate over all survivors at once

`survivorGate` scans the small ideals once per survivor (some 560 ideals per
side at 100 digits, 2.6 ns each: 5.4 ms per special-`q` on the rational side).
`gateAll` turns the loops around: each small ideal scans every survivor, with
its constants in registers and a handful of word operations per survivor. -/

/-- The survivors `[s, …)` (positions `j I + c`) in the progression of the
small ideal `(p, r)`, `r < p`: `log₂ p` added into `lgs` and `p` multiplied into
`prs` (twice and `p²` when the root `r2` modulo `p²` matches as well, `r2 < p²`).
With `K = I p - I/2`, `y = c + K - j r` is the exact positive value
`x₀ + I p - j r` of `smallScan`, divisible by `p` iff `y p⁻¹ ≤ lim (mod 2^32)`. -/
def scanIdeal (survs : Array Nat) (mask logI half p r r2 K : UInt64) (pinv lim : UInt32)
    (lg : Float) (s : Nat) (lgs : FloatArray) (prs : Array UInt64) :
    FloatArray × Array UInt64 :=
  if h : s < survs.size then
    let pos := survs[s].toUInt64
    let c := pos &&& mask
    let j := pos >>> logI
    if (c + K - j * r).toUInt32 * pinv ≤ lim then
      let M := p * p
      let sq := r2 < M && (c + (M <<< logI) - half - j * r2) % M == 0
      scanIdeal survs mask logI half p r r2 K pinv lim lg (s + 1)
        (lgs.set! s (lgs.get! s + (if sq then lg + lg else lg)))
        (prs.set! s (prs[s]! * (if sq then M else p)))
    else scanIdeal survs mask logI half p r r2 K pinv lim lg (s + 1) lgs prs
  else (lgs, prs)
termination_by survs.size - s

/-- A degenerate small ideal (`R ≥ p`): it divides the norm exactly on the rows
`j ≡ 0 (mod p)`. -/
def scanRows (survs : Array Nat) (logI p : UInt64) (lg : Float) (s : Nat) (lgs : FloatArray)
    (prs : Array UInt64) : FloatArray × Array UInt64 :=
  if h : s < survs.size then
    if (survs[s].toUInt64 >>> logI) % p == 0 then
      scanRows survs logI p lg (s + 1) (lgs.set! s (lgs.get! s + lg)) (prs.set! s (prs[s]! * p))
    else scanRows survs logI p lg (s + 1) lgs prs
  else (lgs, prs)
termination_by survs.size - s

/-- `smallScan` at every survivor, ideal by ideal (`tab`, `pl`, `lg2`, `off` as
for `smallScan`): the sums of logarithms and the products modulo `2^64`. -/
def smallScanAll (tab pl : Array Nat) (lg2 : FloatArray) (off : Nat) (survs : Array Nat)
    (I logI : UInt64) : FloatArray × Array UInt64 := Id.run do
  let n := survs.size
  let mut lgs : FloatArray := FloatArray.emptyWithCapacity n
  for _ in [0:n] do lgs := lgs.push (fc 0)
  let mut prs : Array UInt64 := Array.replicate n 1
  let mask := I - 1
  let half := I / 2
  for k in [0:min tab.size pl.size] do
    let w := tab[k]!.toUInt64
    let p := w &&& 4095
    let r := (w >>> 12) &&& 4095
    let lg := lg2.get! (off + k)
    if r ≥ p then
      (lgs, prs) := scanRows survs logI p lg 0 lgs prs
    else
      let v := pl[k]!.toUInt64
      (lgs, prs) := scanIdeal survs mask logI half p r (w >>> 24) (I * p - half) v.toUInt32
        (v >>> 32).toUInt32 lg 0 lgs prs
  return (lgs, prs)

/-- The rational half of `survivorGate` with the small ideals' part given
(`sLg`, `sPr` from `smallScanAll`): whether the survivor passes. -/
def ratPass (ctx : LasCtx) (bd : Bounds) (listR : List Nat) (pos : Nat) (sLg : Float)
    (sPr : UInt64) : Bool :=
  let I := ctx.I
  let j := pos / I
  let c := pos % I
  let iF := nf c - nf (I / 2)
  let jF := nf j
  let aF := iF * bd.uaf + jF * bd.vaf
  let bF := iF * bd.ubf + jF * bd.vbf
  let (cU, jU, IU) := (c.toUInt64, j.toUInt64, I.toUInt64)
  let x0 := cU - IU / 2
  let a64 := x0 * bd.ua64 + jU * bd.va64
  let b64 := x0 * bd.ub64 + jU * bd.vb64
  let side := ctx.rat
  let nF := bd.y1F * aF - bd.mF * bF
  let tR := tinyRatP bd.tq cU jU (IU / 2) 0 (fc 0) 1 0
  let lR := listR.foldl (fun acc k => acc + side.lg2.get! k) (fc 0)
  let estR := Float.log2 (nF.abs + fc 1) - tR.lg - sLg - lR
  if hopeless estR bd.hiR bd.loR bd.gapR then false
  else
    let n64 := bd.y1U * a64 - bd.mU * b64
    let pR := listR.foldl (fun acc k => acc * side.primes[k]!.toUInt64) 1
    sideClass estR (if nF < fc 0 then -n64 else n64) (tR.prod * sPr * pR) tR.v2
      bd.lpbR bd.mfbR bd.lim2R != 0

/-- The algebraic half of `survivorGate` (as `ratPass`). -/
def algPass (ctx : LasCtx) (bd : Bounds) (listA : List Nat) (pos : Nat) (sLg : Float)
    (sPr : UInt64) : Bool :=
  let I := ctx.I
  let j := pos / I
  let c := pos % I
  let iF := nf c - nf (I / 2)
  let jF := nf j
  let aF := iF * bd.uaf + jF * bd.vaf
  let bF := iF * bd.ubf + jF * bd.vbf
  let (cU, jU, IU) := (c.toUInt64, j.toUInt64, I.toUInt64)
  let x0 := cU - IU / 2
  let a64 := x0 * bd.ua64 + jU * bd.va64
  let b64 := x0 * bd.ub64 + jU * bd.vb64
  let d := bd.cs.size - 1
  let sideA := ctx.alg
  let fF := homEvalFA bd.cs aF bF d (bd.cs.get! d) (fc 1)
  let tA := tinyAlgP bd.tq cU jU (IU / 2) 0 (fc 0) 1 0
  let lA := listA.foldl (fun acc k => acc + sideA.lg2.get! k) (fc 0)
  let estA := Float.log2 (fF.abs / bd.qF + fc 1) - tA.lg - sLg - lA
  if hopeless estA bd.hiA bd.loA bd.gapA then false
  else
    let f64 := hornerU bd.cs64 a64 b64 d (bd.cs64[d]!) 1
    let pA := listA.foldl (fun acc k => acc * sideA.primes[k]!.toUInt64) 1
    sideClass estA (if fF < fc 0 then -f64 else f64) (bd.qU * tA.prod * sPr * pA) tA.v2
      bd.lpbA bd.mfbA bd.lim2A != 0

/-- The indices of the survivors that pass `survivorGate` (the same decisions),
each side's small ideals scanned over all its survivors at once: the rational
side over every survivor, the algebraic side over those that passed it. -/
def gateAll (ctx : LasCtx) (bd : Bounds) (survs : Array Nat) (listsR listsA : Array (List Nat)) :
    Array Nat := Id.run do
  let IU := ctx.I.toUInt64
  let logI := ctx.params.logI.toUInt64
  let side := ctx.rat
  let (lgR, prR) := smallScanAll bd.tabR side.pinvLim side.lg2 side.sieveStart survs IU logI
  let mut idx : Array Nat := #[]
  for s in [0:survs.size] do
    if ratPass ctx bd listsR[s]! survs[s]! (lgR.get! s) prR[s]! then idx := idx.push s
  let sideA := ctx.alg
  let (lgA, prA) := smallScanAll bd.tabA sideA.pinvLim sideA.lg2 sideA.sieveStart
    (idx.map (survs[·]!)) IU logI
  let mut out : Array Nat := #[]
  for t in [0:idx.size] do
    let s := idx[t]!
    if algPass ctx bd listsA[s]! survs[s]! (lgA.get! t) prA[t]! then out := out.push s
  return out

/-! ## The production sievers (survivors through `gateAll`) -/

/-- `processQ11` with the reduced bases of the large ideals cached for the resieve. -/
def processQ12 (ctx : LasCtx) (q ρ : Nat) (sc : Scratch) : Array Rel × Scratch := Id.run do
  let ⟨b1, b2, bits⟩ := sc
  let (u, v) := reduceLattice q ρ ctx.skew
  let (ua, ub, va, vb) := (u.1, u.2, v.1, v.2)
  let len := ctx.I * ctx.J
  let Rr := latticeRoots ctx.rat ua ub va vb
  let Ra := latticeRoots ctx.alg ua ub va vb
  let thrR := rowThresholds ctx q ua ub va vb ctx.params.mfbR false
  let thrA := rowThresholds ctx q ua ub va vb ctx.params.mfbA true
  let (bufR, Rr) := sieveLargePaired ctx ctx.rat Rr (lineSieveSide ctx ctx.rat Rr (fillRows ctx b1 thrR))
  let (bufA, Ra) := sieveLargePaired ctx ctx.alg Ra (lineSieveSide ctx ctx.alg Ra (fillRows ctx b2 thrA))
  let surv := prefilterRows ctx q ua ub va vb thrR thrA bufR bufA
    (dropSmallGcd ctx (survivors bufR bufA len))
  if surv.isEmpty then return (#[], ⟨bufR, bufA, bits⟩)
  let (lab, rowStart) := labelSurvivors ctx (zeroRows ctx bufA) surv
  let bits := markBits bits surv true
  let listsR := groupLabelled ctx surv lab rowStart (resievePaired ctx ctx.rat Rr bits #[])
  let listsA := groupLabelled ctx surv lab rowStart (resievePaired ctx ctx.alg Ra bits #[])
  let bits := markBits bits surv false
  let bd := mkBounds ctx q ua ub va vb Rr Ra
  let mut rels : Array Rel := #[]
  for k in gateAll ctx bd surv listsR listsA do
    if let some rel := factorSurvivor2 ctx q ρ ua ub va vb Rr Ra listsR[k]! listsA[k]! surv[k]! then
      rels := rels.push rel
  return (rels, ⟨bufR, lab, bits⟩)

/-- `processQ12` with a threshold per 64-column segment (`fillSegments`: the
largest norm on the segment, rather than on the whole row, which misses the
smooth points of rows whose norms vary widely), the prime powers sieved and the
gap prefilter (`slack` bits): the yield of `processQ8` with the kernels of
`processQ12`. -/
def processQ13 (ctx : LasCtx) (slack : Nat) (q ρ : Nat) (sc : Scratch) : Array Rel × Scratch :=
  Id.run do
  let ⟨b1, b2, bits⟩ := sc
  let (u, v) := reduceLattice q ρ ctx.skew
  let (ua, ub, va, vb) := (u.1, u.2, v.1, v.2)
  let len := ctx.I * ctx.J
  let Rr := latticeRoots ctx.rat ua ub va vb
  let Ra := latticeRoots ctx.alg ua ub va vb
  let Pr := powerRoots ctx.rat ua ub va vb
  let Pa := powerRoots ctx.alg ua ub va vb
  let (fR, biasR) := fillSegments ctx b1 false q ua ub va vb ctx.params.mfbR (rowExtras ctx ctx.rat Rr)
  let (fA, biasA) := fillSegments ctx b2 true q ua ub va vb ctx.params.mfbA (rowExtras ctx ctx.alg Ra)
  let (bufR, Rr) := sieveLargePaired ctx ctx.rat Rr
    (sievePowers ctx ctx.rat Pr (lineSieveSide ctx ctx.rat Rr fR))
  let (bufA, Ra) := sieveLargePaired ctx ctx.alg Ra
    (sievePowers ctx ctx.alg Pa (lineSieveSide ctx ctx.alg Ra fA))
  let surv := prefilterGap4 ctx q ua ub va vb bufR bufA biasR biasA (tinyPrimes ctx ctx.rat Rr)
    (tinyPrimes ctx ctx.alg Ra) slack
    (dropSmallGcd ctx (survivors bufR bufA len))
  if surv.isEmpty then return (#[], ⟨bufR, bufA, bits⟩)
  let (lab, rowStart) := labelSurvivors ctx (zeroRows ctx bufA) surv
  let bits := markBits bits surv true
  let listsR := groupLabelled ctx surv lab rowStart (resievePaired ctx ctx.rat Rr bits #[])
  let listsA := groupLabelled ctx surv lab rowStart (resievePaired ctx ctx.alg Ra bits #[])
  let bits := markBits bits surv false
  let bd := mkBounds ctx q ua ub va vb Rr Ra
  let mut rels : Array Rel := #[]
  for k in gateAll ctx bd surv listsR listsA do
    if let some rel := factorSurvivor2 ctx q ρ ua ub va vb Rr Ra listsR[k]! listsA[k]! surv[k]! then
      rels := rels.push rel
  return (rels, ⟨bufR, lab, bits⟩)

/-- `processQ13` for the basis `u, v` of `q` with the lattice roots `Rr`, `Ra`
already computed. -/
def processQ13R (ctx : LasCtx) (slack : Nat) (q ρ : Nat) (ua ub va vb : Int) (Rr Ra : Array Nat)
    (sc : Scratch) : Array Rel × Scratch := Id.run do
  let ⟨b1, b2, bits⟩ := sc
  let len := ctx.I * ctx.J
  let Pr := powerRoots ctx.rat ua ub va vb
  let Pa := powerRoots ctx.alg ua ub va vb
  let (fR, biasR) := fillSegments ctx b1 false q ua ub va vb ctx.params.mfbR (rowExtras ctx ctx.rat Rr)
  let (fA, biasA) := fillSegments ctx b2 true q ua ub va vb ctx.params.mfbA (rowExtras ctx ctx.alg Ra)
  let (bufR, Rr) := sieveLargePaired ctx ctx.rat Rr
    (sievePowers ctx ctx.rat Pr (lineSieveSide ctx ctx.rat Rr fR))
  let (bufA, Ra) := sieveLargePaired ctx ctx.alg Ra
    (sievePowers ctx ctx.alg Pa (lineSieveSide ctx ctx.alg Ra fA))
  let surv := prefilterGap4 ctx q ua ub va vb bufR bufA biasR biasA (tinyPrimes ctx ctx.rat Rr)
    (tinyPrimes ctx ctx.alg Ra) slack
    (dropSmallGcd ctx (survivors bufR bufA len))
  if surv.isEmpty then return (#[], ⟨bufR, bufA, bits⟩)
  let (lab, rowStart) := labelSurvivors ctx (zeroRows ctx bufA) surv
  let bits := markBits bits surv true
  let listsR := groupLabelled ctx surv lab rowStart (resievePaired ctx ctx.rat Rr bits #[])
  let listsA := groupLabelled ctx surv lab rowStart (resievePaired ctx ctx.alg Ra bits #[])
  let bits := markBits bits surv false
  let bd := mkBounds ctx q ua ub va vb Rr Ra
  let mut rels : Array Rel := #[]
  for k in gateAll ctx bd surv listsR listsA do
    if let some rel := factorSurvivor2 ctx q ρ ua ub va vb Rr Ra listsR[k]! listsA[k]! surv[k]! then
      rels := rels.push rel
  return (rels, ⟨bufR, lab, bits⟩)

/-- `processQ13` over a list of special-`q`, four at a time: the lattice roots of
each group come from `latticeRoots4` (one modular inversion per prime for the
four). -/
def processQs14 (ctx : LasCtx) (slack : Nat) (qs : Array (Nat × Nat)) (sc : Scratch) :
    Array Rel × Scratch := Id.run do
  let mut out : Array Rel := #[]
  let mut sc := sc
  let mut i := 0
  while i < qs.size do
    let grp := qs.extract i (i + 4)
    let bases := grp.map fun (q, ρ) =>
      let (u, v) := reduceLattice q ρ ctx.skew
      (u.1, u.2, v.1, v.2)
    let Rrs := latticeRoots4 ctx.rat bases
    let Ras := latticeRoots4 ctx.alg bases
    for j in [0:grp.size] do
      let (q, ρ) := grp[j]!
      let (ua, ub, va, vb) := bases[j]!
      let (rels, sc') := processQ13R ctx slack q ρ ua ub va vb Rrs[j]! Ras[j]! sc
      sc := sc'
      out := out ++ rels
    i := i + 4
  return (out, sc)

end PrimeFactorLean.NFS.Las
