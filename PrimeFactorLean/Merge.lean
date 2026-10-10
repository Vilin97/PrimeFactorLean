import PrimeFactorLean.GF2

/-!
# Filtering: merging light columns before the linear algebra

The sieves produce sparse GF(2) matrices with many more columns than the
linear algebra needs to see: most columns (large primes, large ideals) occur in
only a few relations. *Merging* (structured Gaussian elimination, as in
CADO-NFS's `merge` and msieve's `filter`) removes such a column by adding its
lightest row to the other rows containing it and dropping the row and column;
it keeps the excess (rows − columns) unchanged while shrinking the matrix and
making it denser, which pays off since block Lanczos costs about
`N · (nonzeros / 64 + N)`.

Each merged row remembers the set of original rows it is the sum of (its
*history*); a dependency among merged rows is mapped back to the symmetric
difference of their histories, which is a dependency among the original rows.

This module is untrusted: every dependency is re-validated downstream (the
square-root steps check their congruences exactly).
-/

namespace PrimeFactorLean.Merge

/-- Symmetric difference of two increasing arrays. -/
def symmDiff (a b : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := Array.mkEmpty (a.size + b.size)
  let mut i := 0
  let mut j := 0
  -- tail-recursive merge would avoid the loop state; the arrays here are short
  while i < a.size || j < b.size do
    if j ≥ b.size || (i < a.size && a[i]! < b[j]!) then
      out := out.push a[i]!
      i := i + 1
    else if i ≥ a.size || b[j]! < a[i]! then
      out := out.push b[j]!
      j := j + 1
    else
      i := i + 1
      j := j + 1
  return out

/-- Whether the increasing array `a` contains `x` (binary search). -/
def containsSorted (a : Array Nat) (x : Nat) : Bool := Id.run do
  let mut lo := 0
  let mut hi := a.size
  while lo < hi do
    let mid := (lo + hi) / 2
    if a[mid]! < x then lo := mid + 1 else hi := mid
  return lo < a.size && a[lo]! == x

/-- Insertion sort for the (short) column lists of a row; removes duplicate
pairs (a column appearing twice cancels over GF(2)). -/
def normalize (r : Array Nat) : Array Nat := Id.run do
  let s := r.qsort (· < ·)
  let mut out : Array Nat := Array.mkEmpty s.size
  let mut i := 0
  while i < s.size do
    if i + 1 < s.size && s[i]! == s[i + 1]! then i := i + 2
    else
      out := out.push s[i]!
      i := i + 1
  return out

/-- Merge the matrix `rows` (columns `< numCols`; columns below `dense` are never
eliminated) until the average row weight reaches `density` or no column of
weight at most `maxW` is left. Returns the live rows (columns renumbered
densely), their histories and the number of active columns.

All state lives in local mutable arrays of one function, so that every update
is in place (passing a structure around would share and copy its arrays). -/
def merge (numCols dense : Nat) (rows0 : Array (Array Nat)) (density maxW : Nat) :
    Array (Array Nat) × Array (Array Nat) × Nat := Id.run do
  let mut rows := rows0.map normalize
  let mut colRows : Array (Array Nat) := Array.replicate numCols #[]
  let mut colWeight : Array Nat := Array.replicate numCols 0
  let mut weight := 0
  for i in [0:rows.size] do
    for c in rows[i]! do
      colRows := colRows.modify c (·.push i)
      colWeight := colWeight.set! c (colWeight[c]! + 1)
    weight := weight + rows[i]!.size
  let mut hist : Array (Array Nat) := (Array.range rows.size).map fun i => #[i]
  let mut alive : Array Bool := Array.replicate rows.size true
  let mut liveRows := rows.size
  for w in [1:maxW + 1] do
    let mut progress := true
    while progress do
      progress := false
      for c in [dense:numCols] do
        let cw := colWeight[c]!
        if cw == 0 || cw > w then continue
        if cw ≥ 2 && weight ≥ density * liveRows then continue
        -- the live rows containing `c`
        let mut rs : Array Nat := #[]
        for r in colRows[c]! do
          if alive[r]! && containsSorted rows[r]! c && !rs.contains r then rs := rs.push r
        colRows := colRows.set! c #[]
        if rs.isEmpty then continue
        progress := true
        -- pivot: the lightest row (a singleton column deletes its row)
        let mut pivot := rs[0]!
        for r in rs do
          if rows[r]!.size < rows[pivot]!.size then pivot := r
        let prow := rows[pivot]!
        let phist := hist[pivot]!
        for r in rs do
          if r != pivot then
            let old := rows[r]!
            let new := symmDiff old prow
            for x in old do
              if !containsSorted new x then colWeight := colWeight.set! x (colWeight[x]! - 1)
            for x in new do
              if !containsSorted old x then
                colWeight := colWeight.set! x (colWeight[x]! + 1)
                colRows := colRows.modify x (·.push r)
            weight := weight + new.size - old.size
            rows := rows.set! r new
            let h := symmDiff hist[r]! phist
            hist := hist.set! r h
        -- delete the pivot row
        for x in prow do colWeight := colWeight.set! x (colWeight[x]! - 1)
        weight := weight - prow.size
        rows := rows.set! pivot #[]
        alive := alive.set! pivot false
        liveRows := liveRows - 1
    if weight ≥ density * liveRows then break
  -- renumber the active columns densely
  let mut index : Array Nat := Array.replicate numCols numCols
  let mut next := 0
  let mut outRows : Array (Array Nat) := #[]
  let mut outHist : Array (Array Nat) := #[]
  for i in [0:rows.size] do
    if alive[i]! then
      let mut r : Array Nat := Array.mkEmpty rows[i]!.size
      for c in rows[i]! do
        if index[c]! == numCols then
          index := index.set! c next
          next := next + 1
        r := r.push index[c]!
      outRows := outRows.push r
      outHist := outHist.push hist[i]!
  return (outRows, outHist, next)

/-- Map one dependency among merged rows back to a set of original rows: the
rows occurring an odd number of times in the histories (`total` original rows). -/
def unmergeOne (total : Nat) (hist : Array (Array Nat)) (dep : Array Nat) : Array Nat := Id.run do
  -- bit 0: parity; bit 1: already listed
  let mut odd : ByteArray := ByteArray.mk (Array.replicate total 0)
  let mut touched : Array Nat := #[]
  for i in dep do
    for h in hist[i]! do
      if h < total then
        let v := odd.get! h
        if v &&& 2 == 0 then touched := touched.push h
        odd := odd.set! h ((v ^^^ 1) ||| 2)
  return (touched.filter fun h => odd.get! h &&& 1 == 1).qsort (· < ·)

/-- Map dependencies among merged rows back to sets of original rows. -/
def unmerge (total : Nat) (hist : Array (Array Nat)) (deps : Array (Array Nat)) :
    Array (Array Nat) :=
  deps.filterMap fun dep =>
    let s := unmergeOne total hist dep
    if s.isEmpty then none else some s

end PrimeFactorLean.Merge
