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

/-- Remove rows that contain a column of weight one, iterating to a fixed point.
Returns the indices of surviving rows. -/
def removeSingletons (numCols : Nat) (rows : Array (Array Nat)) : Array Nat := Id.run do
  let mut count : Array Nat := Array.replicate numCols 0
  for r in rows do
    for c in r do
      if c < numCols then count := count.set! c (count[c]! + 1)
  let mut alive : Array Bool := Array.replicate rows.size true
  let mut changed := true
  while changed do
    changed := false
    for i in [0:rows.size] do
      if alive[i]! then
        let r := rows[i]!
        if r.any (fun c => c < numCols && count[c]! == 1) then
          alive := alive.set! i false
          changed := true
          for c in r do
            if c < numCols then count := count.set! c (count[c]! - 1)
  let mut kept := #[]
  for i in [0:rows.size] do
    if alive[i]! then kept := kept.push i
  return kept

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
    let mut occ : Array (Array Nat) := Array.replicate numCols #[]
    for i in [0:cur.size] do
      for c in cur[i]!.1 do
        occ := occ.set! c (occ[c]!.push i)
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
