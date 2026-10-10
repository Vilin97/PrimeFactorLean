/-! Micro-benchmarks of loop styles for the sieve kernels. -/

namespace Micro

theorem size_set' (s : ByteArray) (j : Nat) (v : UInt8) (h : j < s.size) :
    (s.set j v h).size = s.size := by
  cases s; simp [ByteArray.set, ByteArray.size]

theorem size_uset' (s : ByteArray) (j : USize) (v : UInt8) (h : j.toNat < s.size) :
    (s.uset j v h).size = s.size := by
  cases s; simp [ByteArray.uset, ByteArray.size]

/-- Style A: `while` loop with `Nat` indices (the current kernel). -/
def sieveA (s : ByteArray) (ps : Array Nat) (starts : Array Nat) (lg : UInt8) : ByteArray := Id.run do
  let size := s.size
  let mut s := s
  for i in [0:ps.size] do
    let p := ps[i]!
    let mut j := starts[i]!
    while j < size do
      s := s.set! j (s.get! j + lg)
      j := j + p
  return s

/-- Style B: tail recursion with `Nat` indices and proofs (no bounds checks). -/
def stepB (s : ByteArray) (j p : Nat) (lg : UInt8) (hp : 0 < p) : ByteArray :=
  if h : j < s.size then stepB (s.set j (s.get j h + lg) h) (j + p) p lg hp else s
termination_by s.size - j
decreasing_by rw [size_set']; omega

def sieveB (s : ByteArray) (ps : Array Nat) (starts : Array Nat) (lg : UInt8) : ByteArray := Id.run do
  let mut s := s
  for i in [0:ps.size] do
    let p := ps[i]!
    if hp : 0 < p then s := stepB s starts[i]! p lg hp
  return s

/-- Style C: tail recursion with `USize` indices, unchecked access, fuel. -/
def stepC (s : ByteArray) (j p : USize) (lg : UInt8) : Nat → ByteArray
  | 0 => s
  | fuel + 1 =>
    if h : j < s.usize then
      have h' : j.toNat < s.size := by
        have := USize.lt_iff_toNat_lt.mp h
        simp [ByteArray.usize] at this
        exact Nat.lt_of_lt_of_le this (Nat.mod_le _ _)
      stepC (s.uset j (s.uget j h' + lg) h') (j + p) p lg fuel
    else s

def sieveC (s : ByteArray) (ps : Array Nat) (starts : Array Nat) (lg : UInt8) : ByteArray := Id.run do
  let mut s := s
  for i in [0:ps.size] do
    let p := ps[i]!
    s := stepC s starts[i]!.toUSize p.toUSize lg (s.size / p + 1)
  return s

/-- Style D: the outer loop is also a tail-recursive function. -/
def outerD (ps : Array Nat) (starts : Array Nat) (lg : UInt8) (s : ByteArray) (i : Nat) :
    ByteArray :=
  if h : i < ps.size then
    let p := ps[i]
    let s := stepC s starts[i]!.toUSize p.toUSize lg (s.size / p + 1)
    outerD ps starts lg s (i + 1)
  else s

/-- Root update loop styles over a large factor base. -/
def rootsNat (pos : Array Nat) (ps : Array Nat) (d : Array Nat) : Array Nat := Id.run do
  let mut pos := pos
  for i in [0:ps.size] do
    let p := ps[i]!
    let a := pos[i]!
    pos := pos.set! i ((a + p - d[i]!) % p)
  return pos

def rootsU32 (pos : Array UInt32) (ps : Array UInt32) (d : Array UInt32) (i : Nat) :
    Array UInt32 :=
  if h : i < ps.size then
    let p := ps[i]
    let a := pos[i]!
    let x := a + p - d[i]!
    let x := if x ≥ p then x - p else x
    rootsU32 (pos.set! i x) ps d (i + 1)
  else pos

end Micro

open Micro in
def microMain : IO Unit := do
  -- primes 31..32768 with pseudo-random starts
  let mut ps : Array Nat := #[]
  for q in [31:32768] do
    if q % 2 == 0 || q % 3 == 0 || q % 5 == 0 then continue
    if (List.range (q / 2 + 1)).all (fun t => t < 2 || q % t != 0) then ps := ps.push q
  let starts := ps.map fun p => (p * 7919 + 13) % p
  IO.println s!"{ps.size} primes"
  let buf := ByteArray.mk (Array.replicate 32768 0)
  let reps := 3000
  let updates := reps * (ps.foldl (fun acc p => acc + 32768 / p) 0)
  for (name, f) in [("A while/Nat", sieveA), ("B rec/Nat/proof", sieveB), ("C rec/USize/fuel", sieveC),
                    ("D rec outer", fun s ps st lg => outerD ps st lg s 0)] do
    let t0 ← IO.monoNanosNow
    let mut s := buf
    for r in [0:reps] do
      s ← IO.lazyPure fun _ => f s ps starts (UInt8.ofNat (r % 7 + 1))
    let t1 ← IO.monoNanosNow
    IO.println s!"{name}: {(t1 - t0).toFloat / updates.toFloat} ns/update (check {s.get! 100})"
  -- root updates
  let fb : Array Nat := (Array.range 46000).map fun i => 1000003 + 2 * i
  let d := fb.map fun p => p / 3
  let reps := 2000
  let t0 ← IO.monoNanosNow
  let mut pos := fb.map fun p => p / 2
  for _ in [0:reps] do
    pos ← IO.lazyPure fun _ => rootsNat pos fb d
  let t1 ← IO.monoNanosNow
  IO.println s!"roots Array Nat: {(t1 - t0).toFloat / (reps * fb.size).toFloat} ns/prime ({pos[5]!})"
  let fb32 := fb.map (·.toUInt32)
  let d32 := d.map (·.toUInt32)
  let t0 ← IO.monoNanosNow
  let mut pos32 := fb32.map fun p => p / 2
  for _ in [0:reps] do
    pos32 ← IO.lazyPure fun _ => rootsU32 pos32 fb32 d32 0
  let t1 ← IO.monoNanosNow
  IO.println s!"roots Array UInt32 rec: {(t1 - t0).toFloat / (reps * fb.size).toFloat} ns/prime ({pos32[5]!})"
