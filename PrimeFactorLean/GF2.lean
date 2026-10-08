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
3. *Incremental elimination* on GMP-backed bitsets: each row is reduced by the
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

/-- Find up to `maxDeps` subsets of `rows` (lists of column indices) whose
symmetric difference is empty. Each subset is returned as row indices. -/
def dependencies (numCols : Nat) (rows : Array (Array Nat)) (maxDeps : Nat := 64) :
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

end PrimeFactorLean.GF2
