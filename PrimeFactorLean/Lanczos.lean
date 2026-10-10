import PrimeFactorLean.GF2

/-!
# Block Lanczos over GF(2)

Montgomery's block Lanczos algorithm (Eurocrypt 1995), in the formulation of
msieve's `lanczos.c`, finds vectors in the null space of a sparse matrix `B`
whose columns are relations and whose rows are primes. With `A = Bᵀ B`
(symmetric), a random block `Y` and `V₀ = A Y`, the three-term block
recurrence produces `X` with `A X = A Y`; then `X - Y` and the last iterate
`V_m` span vectors whose images under `B` are combined to zero by a final
elimination on `128` columns.

Blocks of 64 vectors of length `n` are stored as `n` 64-bit words, split into
two `UInt32` halves of an `Array UInt32` (unboxed scalars). 64 × 64 matrices are
arrays of 64 words (row `i`, bit `j` = entry `(i, j)`).

Like `GF2`, this module is **untrusted**: each returned dependency is
re-validated by `Squares.Relation.toSquares`. A wrong or failed answer can only
waste time.
-/

namespace PrimeFactorLean.Lanczos

/-! ## Blocks of 64-bit words

A 64-bit word is stored as two `UInt32` halves of an `Array UInt32`: small
scalars are unboxed in Lean arrays, whereas every element of an
`Array UInt64` would be a heap object (and `FloatArray` cannot carry arbitrary
bit patterns: NaN payloads are canonicalized). -/

/-- Packed words: word `k` is `d[2k] + 2^32 d[2k+1]`. -/
structure Words where
  d : Array UInt32
  deriving Inhabited

def Words.zeros (n : Nat) : Words := ⟨Array.replicate (2 * n) 0⟩

@[inline] def Words.get (w : Words) (k : Nat) : UInt64 :=
  w.d[2 * k]!.toUInt64 ||| (w.d[2 * k + 1]!.toUInt64 <<< 32)

@[inline] def Words.set (w : Words) (k : Nat) (x : UInt64) : Words :=
  ⟨(w.d.set! (2 * k) x.toUInt32).set! (2 * k + 1) (x >>> 32).toUInt32⟩

@[inline] def Words.push (w : Words) (x : UInt64) : Words :=
  ⟨(w.d.push x.toUInt32).push (x >>> 32).toUInt32⟩

def Words.size (w : Words) : Nat := w.d.size / 2

/-- `n` words, one per row of a block of 64 vectors of length `n`. -/
structure Block where
  data : Words
  deriving Inhabited

def Block.zero (n : Nat) : Block := ⟨Words.zeros n⟩

@[inline] def Block.get (b : Block) (k : Nat) : UInt64 := b.data.get k

@[inline] def Block.set (b : Block) (k : Nat) (w : UInt64) : Block := ⟨b.data.set k w⟩

def Block.size (b : Block) : Nat := b.data.size

/-- A 64 × 64 matrix over GF(2): row `i` is a word. -/
structure Mat where
  d : Words
  deriving Inhabited

@[inline] def Mat.get (m : Mat) (i : Nat) : UInt64 := m.d.get i
@[inline] def Mat.set (m : Mat) (i : Nat) (w : UInt64) : Mat := ⟨m.d.set i w⟩

instance : GetElem Mat Nat UInt64 (fun _ i => i < 64) where
  getElem m i _ := m.get i

instance : GetElem? Mat Nat UInt64 (fun _ i => i < 64) where
  getElem? m i := if i < 64 then some (m.get i) else none
  getElem! m i := m.get i

def Mat.ofFn (f : Nat → UInt64) : Mat := Id.run do
  let mut a : Words := ⟨Array.mkEmpty 128⟩
  for i in [0:64] do a := a.push (f i)
  return ⟨a⟩

def bit (j : Nat) : UInt64 := (1 : UInt64) <<< j.toUInt64

def Mat.zero : Mat := ⟨Words.zeros 64⟩
def Mat.identity : Mat := Mat.ofFn bit

/-- `⊕_{j ∈ w} N[j]` over the bits `j ≥ j₀` of `w` (tail recursive: a `while`
loop with several mutable variables would allocate its state every step). -/
def Mat.rowTimes (N : Mat) (w : UInt64) (j : Nat) (acc : UInt64) : Nat → UInt64
  | 0 => acc
  | fuel + 1 =>
    if w == 0 then acc
    else Mat.rowTimes N (w >>> 1) (j + 1) (if w &&& 1 == 1 then acc ^^^ N.get j else acc) fuel

/-- `(M N)[i] = ⊕_{j ∈ M[i]} N[j]`. -/
def Mat.mul (M N : Mat) : Mat := Mat.ofFn fun i => Mat.rowTimes N (M.get i) 0 0 64

def Mat.andMask (M : Mat) (m : UInt64) : Mat := Mat.ofFn fun i => M.get i &&& m
def Mat.xor (M N : Mat) : Mat := Mat.ofFn fun i => M.get i ^^^ N.get i
def Mat.isZero (M : Mat) : Bool := (List.range 64).all fun i => M.get i == 0

/-! ## Products with blocks -/

/-- Eight byte-indexed tables of `⊕` combinations of the rows of `M`, so that
`w · M` costs eight lookups: `table[256 b + v]` for byte `b` of value `v`. -/
def tables (M : Mat) : Words := Id.run do
  let mut t := Words.zeros 2048
  for b in [0:8] do
    for v in [1:256] do
      -- lowest set bit of v: reuse the entry without it
      let low := v &&& (256 - v)
      let j := (Nat.log2 low) + 8 * b
      let x := t.get (256 * b + (v - low)) ^^^ M.get j
      t := t.set (256 * b + v) x
  return t

@[inline] def applyTables (t : Words) (w : UInt64) : UInt64 :=
  t.get (w &&& 255).toNat ^^^ t.get (256 + ((w >>> 8) &&& 255).toNat) ^^^
  t.get (512 + ((w >>> 16) &&& 255).toNat) ^^^ t.get (768 + ((w >>> 24) &&& 255).toNat) ^^^
  t.get (1024 + ((w >>> 32) &&& 255).toNat) ^^^ t.get (1280 + ((w >>> 40) &&& 255).toNat) ^^^
  t.get (1536 + ((w >>> 48) &&& 255).toNat) ^^^ t.get (1792 + (w >>> 56).toNat)

/-- `acc ⊕ V M` (an `n × 64` block times a 64 × 64 matrix). -/
def mulAcc (V : Block) (M : Mat) (acc : Block) : Block := Id.run do
  let t := tables M
  let mut a := acc.data
  for k in [0:V.size] do
    let w := V.get k
    if w != 0 then
      let x := a.get k ^^^ applyTables t w
      a := a.set k x
  return ⟨a⟩

/-- `acc ⊕` the byte tables of `Vᵀ W` over the rows `[lo, hi)`: entry
`256 b + v` accumulates `W[k]` over the `k` whose byte `b` of `V[k]` is `v`. -/
def innerAcc (V W : Block) (lo hi : Nat) (acc : Words) : Words := Id.run do
  let mut acc := acc
  for k in [lo:hi] do
    let v := V.get k
    if v == 0 then continue
    let w := W.get k
    for b in [0:8] do
      let byte := ((v >>> (8 * b).toUInt64) &&& 255).toNat
      if byte != 0 then
        let idx := 256 * b + byte
        let x := acc.get idx ^^^ w
        acc := acc.set idx x
  return acc

/-- The 64 × 64 matrix of accumulated byte tables: row `i` is the `⊕` of
`acc[256 b + v]` over the `v` with bit `i mod 8` set, `b = i / 8`. -/
def tablesMat (acc : Words) : Mat :=
  Mat.ofFn fun i => Id.run do
    let b := i / 8
    let m := i % 8
    let mut r : UInt64 := 0
    for v in [1:256] do
      if (v >>> m) % 2 == 1 then r := r ^^^ acc.get (256 * b + v)
    return r

/-- `Vᵀ W` (64 × 64). -/
def inner (V W : Block) : Mat := tablesMat (innerAcc V W 0 V.size (Words.zeros 2048))

/-- Elementwise `⊕`. -/
def Words.xor (a b : Words) : Words :=
  ⟨(Array.range a.d.size).map fun i => a.d[i]! ^^^ b.d[i]!⟩

/-! ## The matrix -/

/-- A sparse matrix by columns (relations), with its transpose by rows, both in
compressed form: entries of column `c` are `colIdx[colPtr[c] .. colPtr[c+1])`.
Very large matrices (`packed`, at least `2^26` entries) keep their indices in
three bytes each instead (`colIdxB`, `rowIdxB`): an `Array UInt32` spends eight
bytes per entry (at `2^24` entries the decoding still costs more than it saves). -/
structure Sparse where
  nrows : Nat
  ncols : Nat
  colPtr : Array Nat
  colIdx : Array UInt32
  rowPtr : Array Nat
  rowIdx : Array UInt32
  packed : Bool
  colIdxB : ByteArray
  rowIdxB : ByteArray

/-- Append `x < 2^24` in three bytes (little endian). -/
def push3 (b : ByteArray) (x : Nat) : ByteArray :=
  ((b.push x.toUInt8).push (x >>> 8).toUInt8).push (x >>> 16).toUInt8

def Sparse.mk' (nrows : Nat) (cols : Array (Array Nat)) (packAt : Nat := 67108864) : Sparse :=
  Id.run do
  let nnz := cols.foldl (· + ·.size) 0
  let packed := nnz ≥ packAt && nrows < 16777216 && cols.size < 16777216
  let mut colPtr : Array Nat := Array.mkEmpty (cols.size + 1)
  let mut colIdx : Array UInt32 := #[]
  let mut colIdxB : ByteArray := ByteArray.emptyWithCapacity (if packed then 3 * nnz else 0)
  let mut count : Array Nat := Array.replicate nrows 0
  let mut k := 0
  colPtr := colPtr.push 0
  for c in cols do
    for r in c do
      if packed then colIdxB := push3 colIdxB r else colIdx := colIdx.push r.toUInt32
      count := count.set! r (count[r]! + 1)
    k := k + c.size
    colPtr := colPtr.push k
  let mut rowPtr : Array Nat := Array.mkEmpty (nrows + 1)
  rowPtr := rowPtr.push 0
  for r in [0:nrows] do rowPtr := rowPtr.push (rowPtr[r]! + count[r]!)
  let mut fill := rowPtr
  let mut rowEnt : Array UInt32 := Array.replicate nnz 0
  for c in [0:cols.size] do
    for r in cols[c]! do
      let pos := fill[r]!
      rowEnt := rowEnt.set! pos c.toUInt32
      fill := fill.set! r (pos + 1)
  let mut rowIdxB : ByteArray := ByteArray.emptyWithCapacity (if packed then 3 * nnz else 0)
  if packed then
    for c in rowEnt do rowIdxB := push3 rowIdxB c.toNat
  return { nrows := nrows, ncols := cols.size, colPtr, colIdx,
           rowPtr, rowIdx := if packed then #[] else rowEnt, packed, colIdxB, rowIdxB }

/-- `⊕ x[idx[k]]` for `k ∈ [lo, hi)`. -/
def gather (x : Words) (idx : Array UInt32) (lo hi : Nat) (acc : UInt64) : UInt64 :=
  if h : lo < hi ∧ lo < idx.size then
    gather x idx (lo + 1) hi (acc ^^^ x.get idx[lo].toNat)
  else acc
termination_by hi - lo

/-- `gather` on indices of three bytes (machine-word decoding: `Nat` shifts left
are run-time calls). -/
def gather3 (x : Words) (idx : ByteArray) (lo hi : Nat) (acc : UInt64) : UInt64 :=
  if h : lo < hi ∧ 3 * lo + 2 < idx.size then
    let i := (idx[3 * lo].toUInt64 ||| (idx[3 * lo + 1].toUInt64 <<< 8) |||
      (idx[3 * lo + 2].toUInt64 <<< 16)).toNat
    gather3 x idx (lo + 1) hi (acc ^^^ x.get i)
  else acc
termination_by hi - lo

/-- Rows `[lo, hi)` of a compressed product (`idxB` if `packed`). -/
def gatherRange (x : Block) (ptr : Array Nat) (idx : Array UInt32) (packed : Bool)
    (idxB : ByteArray) (lo hi : Nat) : Words := Id.run do
  let mut out : Words := ⟨Array.mkEmpty (2 * (hi - lo))⟩
  for r in [lo:hi] do
    out := out.push (if packed then gather3 x.data idxB ptr[r]! ptr[r + 1]! 0
      else gather x.data idx ptr[r]! ptr[r + 1]! 0)
  return out

/-- The first `r ∈ [lo, hi]` with `ptr[r] ≥ target` (binary search; `ptr` nondecreasing). -/
def firstAtLeast (ptr : Array Nat) (target lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if ptr[mid]! < target then firstAtLeast ptr target (mid + 1) hi else firstAtLeast ptr target lo mid
  else lo
termination_by hi - lo

/-- A compressed product, split over `threads` tasks (one task for small products). -/
def mulCompressed (x : Block) (ptr : Array Nat) (idx : Array UInt32) (packed : Bool)
    (idxB : ByteArray) (count threads : Nat) : Block := Id.run do
  let nnz := ptr[count]!
  -- below about 100000 nonzeros a single task is faster than spawning
  let threads := if nnz < 100000 then 1 else threads
  if threads ≤ 1 then return ⟨gatherRange x ptr idx packed idxB 0 count⟩
  -- chunks of equal numbers of entries (the dense rows of small primes and
  -- characters would otherwise all fall into the first chunk); the last bound
  -- is `count` itself: trailing rows may be empty
  let bounds := ((List.range threads).map fun t => firstAtLeast ptr (t * nnz / threads) 0 count) ++
    [count]
  let tasks := (bounds.zip bounds.tail).map fun (lo, hi) =>
    Task.spawn fun _ => gatherRange x ptr idx packed idxB lo hi
  let mut data : Array UInt32 := Array.mkEmpty (2 * count)
  for task in tasks do data := data ++ task.get.d
  return ⟨⟨data⟩⟩

/-- `B x` for a block over the columns (gathering along each row). -/
def mulB (B : Sparse) (x : Block) (threads : Nat) : Block :=
  mulCompressed x B.rowPtr B.rowIdx B.packed B.rowIdxB B.nrows threads

/-- `Bᵀ y` for a block over the rows (gathering along each column). -/
def mulBT (B : Sparse) (y : Block) (threads : Nat) : Block :=
  mulCompressed y B.colPtr B.colIdx B.packed B.colIdxB B.ncols threads

/-- `A x = Bᵀ (B x)`. -/
def mulA (B : Sparse) (x : Block) (threads : Nat) : Block := mulBT B (mulB B x threads) threads

/-! ## Column selection (Montgomery's `find_nonsingular_sub`) -/

/-- Choose columns `S` of `T = Vᵀ A V` so that `Sᵀ T S` is invertible, using
first the columns not chosen last time; returns the inverse (embedded in a
64 × 64 matrix), the chosen columns and their mask, or `none`. -/
def selectColumns (T : Mat) (lastS : Array Nat) : Option (Mat × Array Nat × UInt64) := Id.run do
  -- M = [T | I]
  let mut m0 : Mat := T
  let mut m1 : Mat := Mat.identity
  -- order: columns not in lastS first, then those in lastS
  let mut lastMask : UInt64 := 0
  for c in lastS do lastMask := lastMask ||| bit c
  let mut order : Array Nat := #[]
  for i in [0:64] do
    if lastMask &&& bit i == 0 then order := order.push i
  order := order ++ lastS
  let mut s : Array Nat := #[]
  for i in [0:64] do
    let si := order[i]!
    let mask := bit si
    -- find a pivot row among order[i..] with bit si in the left half
    let mut found := false
    for j in [i:64] do
      let sj := order[j]!
      if m0.get sj &&& mask != 0 then
        -- swap rows si and sj
        let a0 := m0.get si
        let a1 := m1.get si
        let b0 := m0.get sj
        let b1 := m1.get sj
        m0 := (m0.set si b0).set sj a0
        m1 := (m1.set si b1).set sj a1
        found := true
        break
    if found then
      let p0 := m0.get si
      let p1 := m1.get si
      for j in [0:64] do
        let sj := order[j]!
        if sj != si && m0.get sj &&& mask != 0 then
          let x0 := m0.get sj
          let x1 := m1.get sj
          m0 := m0.set sj (x0 ^^^ p0)
          m1 := m1.set sj (x1 ^^^ p1)
      s := s.push si
    else
      -- use the right half to compensate for the missing pivot
      let mut found2 := false
      for j in [i:64] do
        let sj := order[j]!
        if m1.get sj &&& mask != 0 then
          let a0 := m0.get si
          let a1 := m1.get si
          let b0 := m0.get sj
          let b1 := m1.get sj
          m0 := (m0.set si b0).set sj a0
          m1 := (m1.set si b1).set sj a1
          found2 := true
          break
      if !found2 then return none
      let p0 := m0.get si
      let p1 := m1.get si
      for j in [0:64] do
        let sj := order[j]!
        if sj != si && m1.get sj &&& mask != 0 then
          let x0 := m0.get sj
          let x1 := m1.get sj
          m0 := m0.set sj (x0 ^^^ p0)
          m1 := m1.set sj (x1 ^^^ p1)
      m0 := m0.set si 0
      m1 := m1.set si 0
  if s.isEmpty then return none
  let mut mask : UInt64 := 0
  for c in s do mask := mask ||| bit c
  -- every column must be in s or lastS
  if mask ||| lastMask != 0xFFFFFFFFFFFFFFFF then return none
  return some (m1, s, mask)

/-! ## The iteration -/

/-- SplitMix64 output for state `s`. -/
def splitmix (s : UInt64) : UInt64 :=
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

/-- A deterministic pseudo-random block (SplitMix64: its multiplications make
the bits non-linear over GF(2); a linear generator such as xorshift yields
blocks whose 64 bit-columns are dependent). -/
def randomBlock (n seed : Nat) : Block := Id.run do
  let mut a : Words := ⟨Array.mkEmpty (2 * n)⟩
  for k in [0:n] do
    a := a.push (splitmix ((seed * n + k + 1).toUInt64 * 0x9E3779B97F4A7C15))
  return ⟨a⟩

def Block.xor (a b : Block) : Block :=
  ⟨⟨(Array.range a.data.d.size).map fun i => a.data.d[i]! ^^^ b.data.d[i]!⟩⟩

def Block.andMask (a : Block) (m : UInt64) : Block := Id.run do
  let lo := m.toUInt32
  let hi := (m >>> 32).toUInt32
  let mut d := a.data.d
  for k in [0:a.size] do
    -- read both halves before writing: reading the old array after a `set!`
    -- would keep it alive and force a copy of the whole array per element
    let l := d[2 * k]! &&& lo
    let h := d[2 * k + 1]! &&& hi
    d := (d.set! (2 * k) l).set! (2 * k + 1) h
  return ⟨⟨d⟩⟩

/-- The recurrence state after step `i`. -/
structure LState where
  v : Block
  v1 : Block
  v2 : Block
  x : Block
  winv1 : Mat
  winv2 : Mat
  vtav1 : Mat
  vta2v1 : Mat
  s1 : Array Nat
  mask1 : UInt64

/-- Rows `[lo, hi)` of `(A V ∧ mask) ⊕ V D ⊕ V₁ E ⊕ V₂ F` (tables of `D, E, F`). -/
def nextRange (v v1 v2 av : Block) (mask : UInt64) (tD tE tF : Words) (lo hi : Nat) : Words := Id.run do
  let mut out : Words := ⟨Array.mkEmpty (2 * (hi - lo))⟩
  for k in [lo:hi] do
    out := out.push ((av.get k &&& mask) ^^^ applyTables tD (v.get k) ^^^
      applyTables tE (v1.get k) ^^^ applyTables tF (v2.get k))
  return out

/-- Rows `[lo, hi)` of `X ⊕ V W` (table of `W`). -/
def xRange (x v : Block) (tW : Words) (lo hi : Nat) : Words := Id.run do
  let mut out : Words := ⟨Array.mkEmpty (2 * (hi - lo))⟩
  for k in [lo:hi] do
    out := out.push (x.get k ^^^ applyTables tW (v.get k))
  return out

/-- The row ranges of `n` rows split over `tasks` chunks. -/
def chunks (n tasks : Nat) : List (Nat × Nat) :=
  let c := (n + tasks - 1) / max 1 tasks
  (List.range tasks).map fun t => (min n (t * c), min n ((t + 1) * c))

/-- One step of the recurrence; `none` when `VᵀAV = 0` (converged) or the
column selection fails (`some false` / `none` distinguish the two). The three
inner products and the two block updates each run as one parallel pass over
row chunks. -/
def step (B : Sparse) (threads : Nat) (v0 : Block) (st : LState) : Except Bool LState :=
  let av := mulA B st.v threads
  let n := st.v.size
  let tasks := if n < 4096 then 1 else threads
  let z := Words.zeros 2048
  -- each task reduces its rows to 64 × 64 matrices (`tablesMat` is linear)
  let parts := (chunks n tasks).map fun (lo, hi) => Task.spawn fun _ =>
    (tablesMat (innerAcc st.v av lo hi z), tablesMat (innerAcc av av lo hi z),
      tablesMat (innerAcc st.v v0 lo hi z))
  let (vtav, vta2v, vtv0) := parts.foldl (fun (x1, x2, x3) tk =>
    let (y1, y2, y3) := tk.get
    (x1.xor y1, x2.xor y2, x3.xor y3)) (Mat.zero, Mat.zero, Mat.zero)
  if vtav.isZero then .error true else
  match selectColumns vtav st.s1 with
  | none => .error false
  | some (winv, s, mask0) =>
    -- d = I - Winv (VᵀA²V S Sᵀ + VᵀAV)
    let d := (winv.mul ((vta2v.andMask mask0).xor vtav)).xor Mat.identity
    -- e = Winv₁ VᵀAV S Sᵀ
    let e := st.winv1.mul (vtav.andMask mask0)
    -- f = Winv₂ (I - VᵀAV₁ Winv₁) (VᵀA²V₁ S₁S₁ᵀ + VᵀAV₁) S Sᵀ
    let f := ((st.winv2.mul ((st.vtav1.mul st.winv1).xor Mat.identity)).mul
      (((st.vta2v1.andMask st.mask1).xor st.vtav1).andMask mask0))
    -- x += V Winv Vᵀ V₀; next V = A V S Sᵀ + V d + V₁ e + V₂ f
    let tW := tables (winv.mul vtv0)
    let (tD, tE, tF) := (tables d, tables e, tables f)
    let upd := (chunks n tasks).map fun (lo, hi) => Task.spawn fun _ =>
      (nextRange st.v st.v1 st.v2 av mask0 tD tE tF lo hi, xRange st.x st.v tW lo hi)
    let (nd, xd) := upd.foldl (fun (a, b) tk =>
      let (c, e) := tk.get
      (a ++ c.d, b ++ e.d)) ((Array.mkEmpty (2 * n) : Array UInt32), (Array.mkEmpty (2 * n) : Array UInt32))
    .ok ⟨⟨⟨nd⟩⟩, st.v, st.v1, ⟨⟨xd⟩⟩, winv, st.winv1, vtav, vta2v, s, mask0⟩

/-- Iterate until `VᵀAV = 0` (at most `fuel` steps). -/
def loop (B : Sparse) (threads : Nat) (v0 : Block) : Nat → LState → Option LState
  | 0, _ => none
  | fuel + 1, st =>
    match step B threads v0 st with
    | .error true => some st
    | .error false => none
    | .ok st' => loop B threads v0 fuel st'

/-- Run the recurrence; returns `(X - Y, V_m)` on convergence. -/
def iterate (B : Sparse) (threads seed : Nat) : Option (Block × Block) :=
  let n := B.ncols
  let y := randomBlock n seed
  let v0 := mulA B y threads
  let st0 : LState := ⟨v0, Block.zero n, Block.zero n, Block.zero n, Mat.zero, Mat.zero,
    Mat.zero, Mat.zero, Array.range 64, 0xFFFFFFFFFFFFFFFF⟩
  match loop B threads v0 (n / 60 + 100) st0 with
  | some st => some (st.x.xor y, st.v)
  | none => none

/-! ## From the iterates to null vectors of `B` -/

/-- Parity of the number of set bits. -/
def parity (w : UInt64) : Bool :=
  let w := w ^^^ (w >>> 32)
  let w := w ^^^ (w >>> 16)
  let w := w ^^^ (w >>> 8)
  let w := w ^^^ (w >>> 4)
  let w := w ^^^ (w >>> 2)
  let w := w ^^^ (w >>> 1)
  w &&& 1 == 1

@[inline] def test128 (lo hi : UInt64) (p : Nat) : Bool :=
  if p < 64 then lo &&& bit p != 0 else hi &&& bit (p - 64) != 0

/-- Lowest set bit index of a nonzero 128-bit word. -/
def lowest128 (lo hi : UInt64) : Nat :=
  -- `-x`, not `0 - x`: Lean 4.24's compiler rewrites `0 - x` to `x`
  if lo != 0 then Nat.log2 (lo &&& -lo).toNat else 64 + Nat.log2 (hi &&& -hi).toNat

/-- Combine the 128 columns of `[U | V]` so that `B` maps them to zero:
reduced row echelon form of the rows of `[B U | B V]` (128-bit words), then the
null space of that row basis. Returns the corresponding sets of relations. -/
def combine (B : Sparse) (U V : Block) (threads maxDeps : Nat) : Array (Array Nat) := Id.run do
  let BU := mulB B U threads
  let BV := mulB B V threads
  -- the reduced basis: 128-bit rows (lo, hi) with pivot bp
  let mut blo : Words := ⟨Array.mkEmpty 256⟩
  let mut bhi : Words := ⟨Array.mkEmpty 256⟩
  let mut bps : Array Nat := #[]
  for r in [0:B.nrows] do
    let mut lo := BU.get r
    let mut hi := BV.get r
    for k in [0:bps.size] do
      if test128 lo hi bps[k]! then
        lo := lo ^^^ blo.get k
        hi := hi ^^^ bhi.get k
    if lo != 0 || hi != 0 then
      let p := lowest128 lo hi
      for k in [0:bps.size] do
        let xl := blo.get k
        let xh := bhi.get k
        if test128 xl xh p then
          blo := blo.set k (xl ^^^ lo)
          bhi := bhi.set k (xh ^^^ hi)
      blo := blo.push lo
      bhi := bhi.push hi
      bps := bps.push p
  let mut deps : Array (Array Nat) := #[]
  for f in [0:128] do
    if deps.size ≥ maxDeps then break
    if bps.contains f then continue
    let mut clo : UInt64 := if f < 64 then bit f else 0
    let mut chi : UInt64 := if f < 64 then 0 else bit (f - 64)
    for k in [0:bps.size] do
      if test128 (blo.get k) (bhi.get k) f then
        let bp := bps[k]!
        if bp < 64 then clo := clo ||| bit bp else chi := chi ||| bit (bp - 64)
    let mut dep : Array Nat := #[]
    for c in [0:B.ncols] do
      if parity ((U.get c &&& clo) ^^^ (V.get c &&& chi)) then dep := dep.push c
    if !dep.isEmpty then deps := deps.push dep
  return deps

/-- Dependencies among `rows` (relations, as lists of odd-exponent columns
`< numCols`): singleton removal, then block Lanczos on the surviving relations
and active columns. Interface as `GF2.dependencies`. -/
def dependencies (numCols : Nat) (rows : Array (Array Nat)) (maxDeps : Nat := 64)
    (threads : Nat := 8) (seed : Nat := 1) : Array (Array Nat) := Id.run do
  let kept := GF2.removeSingletons numCols rows
  -- dense renumbering of the active columns (matrix rows)
  let mut index : Array Nat := Array.replicate numCols numCols
  let mut active := 0
  for i in kept do
    for c in rows[i]! do
      if c < numCols && index[c]! == numCols then
        index := index.set! c active
        active := active + 1
  -- keep at most active + 64 relations (more only slows the iteration)
  let take := min kept.size (active + 64)
  let mut cols : Array (Array Nat) := Array.mkEmpty take
  for k in [0:take] do
    cols := cols.push ((rows[kept[k]!]!.filter (· < numCols)).map fun c => index[c]!)
  if cols.size ≤ active then return #[]
  let B := Sparse.mk' active cols
  for attempt in [0:3] do
    match iterate B (max 1 threads) (seed + attempt) with
    | none => continue
    | some (x, v) =>
      let deps := combine B x v (max 1 threads) maxDeps
      if !deps.isEmpty then
        return deps.map fun dep => dep.map fun k => kept[k]!
  return #[]

end PrimeFactorLean.Lanczos
