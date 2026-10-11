/-!
# Null-space vectors over GF(2)

The sieve methods need subsets of relations whose exponent vectors sum to zero
modulo 2. This module finds such subsets. It is deliberately **untrusted**:
every dependency it returns is re-validated by `Squares.Relation.toSquares`,
whose evenness check is part of the proved pipeline. A wrong answer here can
only waste time, never produce an incorrect factor.

Algorithm:

1. *Singleton removal* (the first step of structured Gaussian elimination):
   repeatedly delete rows containing a column that occurs in no other live row.
   Such rows can never belong to a dependency.
2. Columns that remain are renumbered densely; sparse (large-prime) columns
   receive the highest bit positions.
3. *Merging* (structured Gaussian elimination): a column met by exactly two
   rows is eliminated by adding one row to the other, which removes a row and
   a column at once. Each merged row remembers the original rows it combines.
4. *Incremental elimination* on GMP-backed bitsets: each row is reduced by the
   pivot row of its highest set bit. A row that vanishes yields a dependency,
   recorded by a second bitset of combined row indices.
-/

namespace PrimeFactorLean.GF2

/-- Indices of the set bits of `x`, highest first. -/
def bitIndices (x : Nat) : Array Nat := Id.run do
  let mut x := x
  let mut out := #[]
  while x != 0 do
    let k := x.log2
    out := out.push k
    x := x ^^^ (1 <<< k)
  return out

/-- The weights of the columns `< numCols` over the rows from `i` (row `i` from
its entry `j`; tail recursive over a fuel bound, no loop state to allocate). -/
def colCounts (numCols : Nat) (rows : Array (Array Nat)) (i j : Nat) (count : Array Nat) :
    Nat → Array Nat
  | 0 => count
  | fuel + 1 =>
    if h : i < rows.size then
      let r := rows[i]
      if hj : j < r.size then
        let c := r[j]
        colCounts numCols rows i (j + 1)
          (if c < numCols then count.set! c (count[c]! + 1) else count) fuel
      else colCounts numCols rows (i + 1) 0 count fuel
    else count

/-- The rows of each column: entry `fill[c]` of `idx` (advanced) gets the rows
from `i` containing `c` (tail recursive as `colCounts`). -/
def placeRows (numCols : Nat) (rows : Array (Array Nat)) (i j : Nat) (idx fill : Array Nat) :
    Nat → Array Nat
  | 0 => idx
  | fuel + 1 =>
    if h : i < rows.size then
      let r := rows[i]
      if hj : j < r.size then
        let c := r[j]
        if c < numCols then
          let k := fill[c]!
          placeRows numCols rows i (j + 1) (idx.set! k i) (fill.set! c (k + 1)) fuel
        else placeRows numCols rows i (j + 1) idx fill fuel
      else placeRows numCols rows (i + 1) 0 idx fill fuel
    else idx

/-- The first live row among `idx[k], …, idx[e - 1]`. -/
def firstAlive (alive : Array Bool) (idx : Array Nat) (k e : Nat) : Option Nat :=
  if k < e then
    let i := idx[k]!
    if alive[i]! then some i else firstAlive alive idx (k + 1) e
  else none
termination_by e - k

/-- The column weights after removing the row `r` (from its entry `j`), with the
columns that become singletons queued. -/
def dropRow (numCols : Nat) (r : Array Nat) (j : Nat) (count queue : Array Nat) :
    Array Nat × Array Nat :=
  if h : j < r.size then
    let c := r[j]
    if c < numCols then
      let v := count[c]! - 1
      dropRow numCols r (j + 1) (count.set! c v) (if v == 1 then queue.push c else queue)
    else dropRow numCols r (j + 1) count queue
  else (count, queue)
termination_by r.size - j

/-- The queue of singleton columns from position `qi`: each one's live row is
removed (tail recursive over a fuel bound). -/
def cascade (numCols : Nat) (rows : Array (Array Nat)) (start idx : Array Nat) (qi : Nat)
    (queue : Array Nat) (alive : Array Bool) (count : Array Nat) : Nat → Array Bool
  | 0 => alive
  | fuel + 1 =>
    if qi < queue.size then
      let c := queue[qi]!
      if count[c]! != 1 then cascade numCols rows start idx (qi + 1) queue alive count fuel
      else match firstAlive alive idx start[c]! start[c + 1]! with
        | some i =>
          let (count, queue) := dropRow numCols rows[i]! 0 count queue
          cascade numCols rows start idx (qi + 1) queue (alive.set! i false) count fuel
        | none => cascade numCols rows start idx (qi + 1) queue alive count fuel
    else alive

/-- `removeSingletons` with the rows of each column indexed
(compressed), then a queue of singleton columns is processed: removing the row
of a singleton may create new singletons (linear time, instead of passes over
all rows until nothing changes). The loops are tail recursive: as `for` loops
with two mutable arrays they rebuilt their state at each of the ~75 million
entries of a 100-digit run. -/
def removeSingletonsIdx (numCols : Nat) (rows : Array (Array Nat)) : Array Nat := Id.run do
  let nnz := rows.foldl (fun a r => a + r.size) 0
  let count := colCounts numCols rows 0 0 (Array.replicate numCols 0) (nnz + rows.size + 1)
  let mut start : Array Nat := Array.mkEmpty (numCols + 1)
  start := start.push 0
  for c in [0:numCols] do start := start.push (start[c]! + count[c]!)
  let idx := placeRows numCols rows 0 0 (Array.replicate start[numCols]! 0) start
    (nnz + rows.size + 1)
  let mut queue : Array Nat := #[]
  for c in [0:numCols] do
    if count[c]! == 1 then queue := queue.push c
  let alive := cascade numCols rows start idx 0 queue (Array.replicate rows.size true) count
    (nnz + numCols + 1)
  return (Array.range rows.size).filter (alive[·]!)

/-- The weights of the columns `< numCols` and the `XOR` of the indices of the
rows containing each, over the rows from `i` (row `i` from its entry `j`; tail
recursive over a fuel bound). -/
def colCountsXor (numCols : Nat) (rows : Array (Array Nat)) (i j : Nat) (count xr : Array Nat) :
    Nat → Array Nat × Array Nat
  | 0 => (count, xr)
  | fuel + 1 =>
    if h : i < rows.size then
      let r := rows[i]
      if hj : j < r.size then
        let c := r[j]
        if c < numCols then
          colCountsXor numCols rows i (j + 1) (count.set! c (count[c]! + 1)) (xr.set! c (xr[c]! ^^^ i))
            fuel
        else colCountsXor numCols rows i (j + 1) count xr fuel
      else colCountsXor numCols rows (i + 1) 0 count xr fuel
    else (count, xr)

/-- The queue of singleton columns from position `qi`: a column of weight one
names its live row in `xr`, which is removed (its entries from `j` while
`dropping`, updating the weights and `XOR`s and queueing the new singletons).
`none` if a column's `XOR` does not name a live row containing it (a row listing
a column twice). -/
def cascadeXor (numCols : Nat) (rows : Array (Array Nat)) (qi : Nat) (queue : Array Nat)
    (alive : Array Bool) (count xr : Array Nat) (cur j : Nat) (dropping : Bool) :
    Nat → Option (Array Bool)
  | 0 => some alive
  | fuel + 1 =>
    if dropping then
      let r := rows[cur]!
      if hj : j < r.size then
        let c := r[j]
        if c < numCols then
          let v := count[c]! - 1
          cascadeXor numCols rows qi (if v == 1 then queue.push c else queue) alive (count.set! c v)
            (xr.set! c (xr[c]! ^^^ cur)) cur (j + 1) true fuel
        else cascadeXor numCols rows qi queue alive count xr cur (j + 1) true fuel
      else cascadeXor numCols rows qi queue alive count xr cur 0 false fuel
    else if qi < queue.size then
      let c := queue[qi]!
      if count[c]! != 1 then cascadeXor numCols rows (qi + 1) queue alive count xr cur 0 false fuel
      else
        let i := xr[c]!
        if i < rows.size && alive[i]! && rows[i]!.contains c then
          cascadeXor numCols rows (qi + 1) queue (alive.set! i false) count xr i 0 true fuel
        else none
    else some alive

/-- Remove rows that contain a column of weight one, iterating to a fixed point.
Returns the indices of surviving rows. Each column keeps its weight and the
`XOR` of the indices of its live rows, so a column of weight one names its row:
a queue of singleton columns is processed, removing the row of each may create
new singletons (linear time, and no index of the rows of each column, whose
76 million entries at 100 digits made this memory-bound). A row listing a
column twice (not made by the sieves) falls back to `removeSingletonsIdx`. -/
def removeSingletons (numCols : Nat) (rows : Array (Array Nat)) : Array Nat := Id.run do
  let nnz := rows.foldl (fun a r => a + r.size) 0
  let (count, xr) := colCountsXor numCols rows 0 0 (Array.replicate numCols 0)
    (Array.replicate numCols 0) (nnz + rows.size + 1)
  let mut queue : Array Nat := #[]
  for c in [0:numCols] do
    if count[c]! == 1 then queue := queue.push c
  match cascadeXor numCols rows 0 queue (Array.replicate rows.size true) count xr 0 0 false
      (2 * nnz + numCols + 1) with
  | some alive => return (Array.range rows.size).filter (alive[·]!)
  | none => return removeSingletonsIdx numCols rows

/-- Symmetric difference of two sorted arrays without repetitions. -/
def symmDiff (a b : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := Array.mkEmpty (a.size + b.size)
  let mut i := 0
  let mut j := 0
  while i < a.size || j < b.size do
    if j ≥ b.size then
      out := out.push a[i]!
      i := i + 1
    else if i ≥ a.size then
      out := out.push b[j]!
      j := j + 1
    else
      let x := a[i]!
      let y := b[j]!
      if x < y then
        out := out.push x
        i := i + 1
      else if y < x then
        out := out.push y
        j := j + 1
      else
        i := i + 1
        j := j + 1
  return out

/-- Merge passes: eliminate weight-two columns (and drop weight-one columns'
rows), returning the reduced rows with the original rows each one combines. -/
def mergeColumns (numCols : Nat) (rows : Array (Array Nat)) (maxRowWeight : Nat := 64) :
    Array (Array Nat × Array Nat) := Id.run do
  let mut cur : Array (Array Nat × Array Nat) := (Array.range rows.size).map fun i =>
    ((rows[i]!.filter (· < numCols)).qsort (· < ·), #[i])
  let mut changed := true
  let mut passes := 0
  while changed && passes < 50 do
    changed := false
    passes := passes + 1
    -- Occurrence lists only for columns of weight at most two (in-place updates).
    let mut weight : Array Nat := Array.replicate numCols 0
    for i in [0:cur.size] do
      for c in cur[i]!.1 do
        weight := weight.set! c (weight[c]! + 1)
    let mut occ : Array (Array Nat) := Array.replicate numCols #[]
    for i in [0:cur.size] do
      for c in cur[i]!.1 do
        if weight[c]! ≤ 2 then occ := occ.modify c (·.push i)
    let mut dead : Array Bool := Array.replicate cur.size false
    let mut touched : Array Bool := Array.replicate cur.size false
    for c in [0:numCols] do
      let o := occ[c]!
      if o.size == 1 then
        let i := o[0]!
        if !touched[i]! && !dead[i]! then
          dead := dead.set! i true
          touched := touched.set! i true
          changed := true
      else if o.size == 2 then
        let i := o[0]!
        let j := o[1]!
        if !touched[i]! && !touched[j]! && !dead[i]! && !dead[j]! then
          let (ri, ci) := cur[i]!
          let (rj, cj) := cur[j]!
          let merged := symmDiff ri rj
          if merged.size ≤ maxRowWeight then
            cur := cur.set! j (merged, ci ++ cj)
            dead := dead.set! i true
            touched := (touched.set! i true).set! j true
            changed := true
    let mut next : Array (Array Nat × Array Nat) := Array.mkEmpty cur.size
    for i in [0:cur.size] do
      if !dead[i]! then next := next.push cur[i]!
    cur := next
  return cur

/-- Dense phase: singleton removal, then incremental bitset elimination. -/
def denseDependencies (numCols : Nat) (rows : Array (Array Nat)) (maxDeps : Nat := 64) :
    Array (Array Nat) := Id.run do
  let kept := removeSingletons numCols rows
  -- Dense renumbering of the live columns, keeping the original order
  -- (factor-base order puts small, dense primes at low bit positions).
  let mut weight : Array Nat := Array.replicate numCols 0
  for i in kept do
    for c in rows[i]! do
      if c < numCols then weight := weight.set! c (weight[c]! + 1)
  let mut newIndex : Array Nat := Array.replicate numCols 0
  let mut active := 0
  for c in [0:numCols] do
    if weight[c]! > 0 then
      newIndex := newIndex.set! c active
      active := active + 1
  -- Bitset rows over the active columns.
  let mut pivots : Array (Option (Nat × Nat)) := Array.replicate active none
  let mut deps : Array (Array Nat) := #[]
  for k in [0:kept.size] do
    if deps.size ≥ maxDeps then break
    let mut r : Nat := 0
    for c in rows[kept[k]!]! do
      if c < numCols then r := r ^^^ (1 <<< newIndex[c]!)
    let mut combo : Nat := 1 <<< k
    let mut done := false
    while !done do
      if r == 0 then
        deps := deps.push ((bitIndices combo).map fun j => kept[j]!)
        done := true
      else
        let j := r.log2
        match pivots[j]! with
        | some (pr, pc) =>
          r := r ^^^ pr
          combo := combo ^^^ pc
        | none =>
          pivots := pivots.set! j (some (r, combo))
          done := true
  return deps

/-- Find up to `maxDeps` subsets of `rows` (lists of column indices) whose
symmetric difference is empty. Each subset is returned as row indices. -/
def dependencies (numCols : Nat) (rows : Array (Array Nat)) (maxDeps : Nat := 64) :
    Array (Array Nat) := Id.run do
  -- Structured elimination first; then dense elimination on the merged rows.
  let merged := mergeColumns numCols rows
  let inner := denseDependencies numCols (merged.map (·.1)) maxDeps
  return inner.map fun dep => Id.run do
    let mut out : Array Nat := #[]
    for k in dep do
      out := out ++ merged[k]!.2
    return out

end PrimeFactorLean.GF2
