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

/-- Insertion sort of a short array of naturals (direct comparisons: `Array.qsort`
here called its comparator through a boxed closure, half of the merge's time). -/
def sortNat (a : Array Nat) : Array Nat := Id.run do
  let mut a := a
  for i in [1:a.size] do
    let x := a[i]!
    let mut j := i
    while j > 0 && a[j - 1]! > x do
      a := a.set! j a[j - 1]!
      j := j - 1
    a := a.set! j x
  return a

/-- Sorted column lists of a row; removes duplicate pairs (a column appearing
twice cancels over GF(2)). -/
def normalize (r : Array Nat) : Array Nat := Id.run do
  let s := sortNat r
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
            -- only the pivot's columns change: those also in `old` cancel, the
            -- others are added (one merge walk, no searches)
            let mut i := 0
            for x in prow do
              while i < old.size && old[i]! < x do i := i + 1
              if i < old.size && old[i]! == x then
                colWeight := colWeight.set! x (colWeight[x]! - 1)
              else
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

/-- The record of a merge (`mergeLog`): the original index of each output row,
the row additions `r ← r + p` in order (packed as `r · 2^24 + p`, original
indices), and the number of original rows. -/
structure Log where
  orig : Array Nat
  ops : Array Nat
  total : Nat
  deriving Inhabited

/-- Merge the matrix `rows` (columns `< numCols`; columns below `dense` are never
eliminated) until the average row weight reaches `density` or no column of
weight at most `maxW` is left. Returns the live rows (columns renumbered
densely), the log of the row additions (`Log`, for `unmergeLog`) and the number
of active columns. Rows keep their original indices, so a row addition is one
log entry instead of an update of the row's history.

All state lives in local mutable arrays of one function, so that every update
is in place (passing a structure around would share and copy its arrays). -/
def mergeLog (numCols dense : Nat) (rows0 : Array (Array Nat)) (density maxW : Nat) :
    Array (Array Nat) × Log × Nat := Id.run do
  let mut rows := rows0.map normalize
  let mut colRows : Array (Array Nat) := Array.replicate numCols #[]
  let mut colWeight : Array Nat := Array.replicate numCols 0
  let mut weight := 0
  for i in [0:rows.size] do
    for c in rows[i]! do
      colRows := colRows.modify c (·.push i)
      colWeight := colWeight.set! c (colWeight[c]! + 1)
    weight := weight + rows[i]!.size
  let mut ops : Array Nat := #[]
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
        for r in rs do
          if r != pivot then
            let old := rows[r]!
            let new := symmDiff old prow
            -- only the pivot's columns change: those also in `old` cancel, the
            -- others are added (one merge walk, no searches)
            let mut i := 0
            for x in prow do
              while i < old.size && old[i]! < x do i := i + 1
              if i < old.size && old[i]! == x then
                colWeight := colWeight.set! x (colWeight[x]! - 1)
              else
                colWeight := colWeight.set! x (colWeight[x]! + 1)
                colRows := colRows.modify x (·.push r)
            weight := weight + new.size - old.size
            rows := rows.set! r new
            ops := ops.push (r * 16777216 + pivot)
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
  let mut orig : Array Nat := #[]
  for i in [0:rows.size] do
    if alive[i]! then
      let mut r : Array Nat := Array.mkEmpty rows[i]!.size
      for c in rows[i]! do
        if index[c]! == numCols then
          index := index.set! c next
          next := next + 1
        r := r.push index[c]!
      outRows := outRows.push r
      orig := orig.push i
  return (outRows, ⟨orig, ops, rows.size⟩, next)

/-- The root of `x` in a union-find forest (`parent`; union by size keeps the
trees shallow, so no path compression is needed). -/
def findRoot (parent : Array Nat) (x : Nat) : Nat → Nat
  | 0 => x
  | fuel + 1 => let p := parent[x]!; if p == x then x else findRoot parent p fuel

/-- Clique removal (Cavallar's filtering, CADO-NFS `purge`): while the excess
(rows less active columns) of the rows `kept` exceeds `target`, delete whole
*cliques*, the connected components of the graph whose edges are the columns of
weight two (columns below `dense` are always active and never join rows),
largest first, then remove the singleton columns this creates. Deleting a
clique of `k` rows joined by `k - 1` columns of weight two lowers the excess by
one, so the largest cliques shrink the matrix most per unit of excess. Returns
the surviving rows (indices into `rows`). -/
def purge (numCols dense : Nat) (rows : Array (Array Nat)) (kept : Array Nat) (target : Nat) :
    Array Nat := Id.run do
  let mut kept := kept
  for _ in [0:12] do
    let mut count : Array Nat := Array.replicate numCols 0
    for i in kept do
      for c in rows[i]! do
        if c < numCols then count := count.set! c (count[c]! + 1)
    let mut active := 0
    for c in [0:numCols] do
      if count[c]! > 0 || c < dense then active := active + 1
    if kept.size ≤ active + target then return kept
    -- deleting a clique lowers the excess by at most one (a clique of `k` rows
    -- holds at least `k - 1` columns of weight two) and singleton removal never
    -- lowers it, so removing `excess` cliques cannot go below `target`
    let excess := kept.size - active - target
    -- union by size over positions in `kept`, joined by the columns of weight two
    let K := kept.size
    let mut parent : Array Nat := Array.range K
    let mut size : Array Nat := Array.replicate K 1
    let mut first : Array Nat := Array.replicate numCols K
    for k in [0:K] do
      for c in rows[kept[k]!]! do
        if c ≥ dense && c < numCols && count[c]! == 2 then
          let f := first[c]!
          if f == K then first := first.set! c k
          else
            let rf := findRoot parent f 64
            let rk := findRoot parent k 64
            if rf != rk then
              if size[rf]! ≥ size[rk]! then
                parent := parent.set! rk rf
                size := size.set! rf (size[rf]! + size[rk]!)
              else
                parent := parent.set! rf rk
                size := size.set! rk (size[rk]! + size[rf]!)
    -- the roots by clique size (buckets), largest first, `excess` of them
    let mut maxSize := 0
    for k in [0:K] do
      if parent[k]! == k && size[k]! > maxSize then maxSize := size[k]!
    let mut bySize : Array (Array Nat) := Array.replicate (maxSize + 1) #[]
    for k in [0:K] do
      if parent[k]! == k then bySize := bySize.modify size[k]! (·.push k)
    let mut doomed : ByteArray := ByteArray.mk (Array.replicate K 0)
    let mut left := excess
    let mut sz := maxSize
    while left > 0 && sz > 0 do
      for r in bySize[sz]! do
        if left > 0 then
          doomed := doomed.set! r 1
          left := left - 1
      sz := sz - 1
    let mut rest : Array Nat := #[]
    for k in [0:K] do
      if doomed.get! (findRoot parent k 64) == 0 then rest := rest.push kept[k]!
    -- singleton removal on what is left
    let alive := GF2.removeSingletons numCols (rest.map fun i => rows[i]!)
    kept := alive.map fun j => rest[j]!
  return kept

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

/-- `mask[p] ^= mask[r]` for the logged additions `r ← r + p`, last to first
(`lo`, `hi`: the two 32-bit halves of each row's mask). -/
def replay (ops : Array Nat) (lo hi : Array Nat) : Nat → Array Nat × Array Nat
  | 0 => (lo, hi)
  | k + 1 =>
    let op := ops[k]!
    let r := op >>> 24
    let p := op &&& 16777215
    let lr := lo[r]!
    let hr := hi[r]!
    if lr == 0 && hr == 0 then replay ops lo hi k
    else replay ops (lo.set! p (lo[p]! ^^^ lr)) (hi.set! p (hi[p]! ^^^ hr)) k

/-- Map up to 64 dependencies among merged rows back to sets of original rows
(`unmerge` from the merge's log): each output row carries a bit per dependency,
and the logged additions are undone last to first. -/
def unmergeLog (log : Log) (deps : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let deps := deps.extract 0 64
  let n := log.total
  let mut lo : Array Nat := Array.replicate n 0
  let mut hi : Array Nat := Array.replicate n 0
  for d in [0:deps.size] do
    let b := 1 <<< (d % 32)
    for i in deps[d]! do
      let r := log.orig[i]!
      if d < 32 then lo := lo.set! r (lo[r]! ^^^ b) else hi := hi.set! r (hi[r]! ^^^ b)
  let (lo', hi') := replay log.ops lo hi log.ops.size
  let mut out : Array (Array Nat) := Array.replicate deps.size #[]
  for r in [0:n] do
    let l := lo'[r]!
    let h := hi'[r]!
    if l != 0 || h != 0 then
      for d in [0:deps.size] do
        let w := if d < 32 then l else h
        if (w >>> (d % 32)) &&& 1 == 1 then out := out.modify d (·.push r)
  return out.filter fun s => !s.isEmpty

end PrimeFactorLean.Merge
