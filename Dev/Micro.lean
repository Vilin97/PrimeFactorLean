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

namespace Micro2

theorem size_uset' (s : ByteArray) (j : USize) (v : UInt8) (h : j.toNat < s.size) :
    (s.uset j v h).size = s.size := by
  cases s; simp [ByteArray.uset, ByteArray.size]

theorem numBits_ge : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide

theorem toNat_add_small (j p : USize) (hj : j.toNat < 2 ^ 31) (hp : p.toNat < 2 ^ 31) :
    (j + p).toNat = j.toNat + p.toNat := by
  rw [USize.toNat_add]
  apply Nat.mod_eq_of_lt
  have := numBits_ge
  omega

/-- Fuel-free loop: sizes below `2^31` rule out `USize` overflow. -/
def stepE (s : ByteArray) (j p : USize) (lg : UInt8) (hs : s.size < 2 ^ 31)
    (hp : 0 < p.toNat ∧ p.toNat < 2 ^ 31) : ByteArray :=
  if h : j.toNat < s.size then
    stepE (s.uset j (s.uget j h + lg) h) (j + p) p lg (by rw [size_uset']; exact hs) hp
  else s
termination_by s.size - j.toNat
decreasing_by
  rw [size_uset', toNat_add_small j p (by omega) hp.2]
  omega

/-- Four updates per iteration while all four fit, then the plain loop. -/
def stepU (s : ByteArray) (j p : USize) (lg : UInt8) (hs : s.size < 2 ^ 31)
    (hp : 0 < p.toNat ∧ p.toNat < 2 ^ 28) : ByteArray :=
  if h : (j + p + p + p).toNat < s.size ∧ j.toNat < 2 ^ 29 then
    have e1 : (j + p).toNat = j.toNat + p.toNat := toNat_add_small j p (by omega) (by omega)
    have e2 : (j + p + p).toNat = j.toNat + p.toNat + p.toNat := by
      rw [toNat_add_small (j + p) p (by omega) (by omega), e1]
    have e3 : (j + p + p + p).toNat = j.toNat + p.toNat + p.toNat + p.toNat := by
      rw [toNat_add_small (j + p + p) p (by omega) (by omega), e2]
    have h0 : j.toNat < s.size := by omega
    have h1 : (j + p).toNat < s.size := by omega
    have h2 : (j + p + p).toNat < s.size := by omega
    have h3 : (j + p + p + p).toNat < s.size := h.1
    let s1 := s.uset j (s.uget j h0 + lg) h0
    have hs1 : s1.size = s.size := size_uset' _ _ _ _
    let s2 := s1.uset (j + p) (s1.uget (j + p) (by omega) + lg) (by omega)
    have hs2 : s2.size = s.size := by simp only [s2, size_uset', hs1]
    let s3 := s2.uset (j + p + p) (s2.uget (j + p + p) (by omega) + lg) (by omega)
    have hs3 : s3.size = s.size := by simp only [s3, size_uset', hs2]
    let s4 := s3.uset (j + p + p + p) (s3.uget (j + p + p + p) (by omega) + lg) (by omega)
    have hs4 : s4.size = s.size := by simp only [s4, size_uset', hs3]
    stepU s4 (j + p + p + p + p) p lg (by omega) hp
  else stepE s j p lg hs ⟨hp.1, by omega⟩
termination_by s.size - j.toNat
decreasing_by
  have e4 : (j + p + p + p + p).toNat = j.toNat + p.toNat + p.toNat + p.toNat + p.toNat := by
    rw [toNat_add_small (j + p + p + p) p (by omega) (by omega), e3]
  simp only [size_uset']
  omega

def sieveE (s : ByteArray) (ps : Array Nat) (starts : Array Nat) (lg : UInt8) (unroll : Bool) :
    ByteArray := Id.run do
  let mut s := s
  for i in [0:ps.size] do
    let p := ps[i]!
    if hs : s.size < 2 ^ 31 then
      if hp : 0 < p.toUSize.toNat ∧ p.toUSize.toNat < 2 ^ 28 then
        s := if unroll then stepU s starts[i]!.toUSize p.toUSize lg hs hp
             else stepE s starts[i]!.toUSize p.toUSize lg hs ⟨hp.1, by omega⟩
  return s

end Micro2

open Micro Micro2 in
def micro2Main : IO Unit := do
  let isPrime (q : Nat) : Bool := q ≥ 2 && (List.range (q / 2 + 1)).all (fun t => t < 2 || q % t != 0)
  let mut small : Array Nat := #[]
  for q in [230:32768] do
    if q % 2 == 1 && isPrime q && q % 4 == 1 then small := small.push q
  let mut large : Array Nat := #[]
  for q in [32768:1200000] do
    if q % 2 == 1 && q % 3 != 0 && q % 4 == 1 && isPrime q then large := large.push q
  IO.println s!"{small.size} medium primes, {large.size} large primes"
  for (label, size) in [("32KB", 32768), ("384KB", 393216)] do
    let buf := ByteArray.mk (Array.replicate size 0)
    for (pname, ps) in [("medium", small), ("large", large)] do
      let starts := ps.map fun p => (p * 7919 + 13) % p
      let reps := if pname == "medium" then 300 else 100
      let updates := reps * (ps.foldl (fun acc p => acc + (size + p - 1 - (p * 7919 + 13) % p) / p) 0)
      for (vname, f) in [("C fuel", fun s => sieveC s ps starts 3), ("E nofuel", fun s => sieveE s ps starts 3 false),
                         ("U unroll4", fun s => sieveE s ps starts 3 true)] do
        let t0 ← IO.monoNanosNow
        let mut s := buf
        for _ in [0:reps] do
          s ← IO.lazyPure fun _ => f s
        let t1 ← IO.monoNanosNow
        IO.println s!"{label} {pname} {vname}: {(t1 - t0).toFloat / updates.toFloat} ns/update ({updates / reps} updates/pass, {s.get! 7})"

namespace Micro3

/-- Positions `≥ thr` in `[j, size)`, scanning byte by byte. -/
def scanRec (s : ByteArray) (thr : UInt8) (j : Nat) (acc : Array Nat) : Array Nat :=
  if h : j < s.size then
    scanRec s thr (j + 1) (if s.get j h ≥ thr then acc.push j else acc)
  else acc
termination_by s.size - j

/-- Fold-based block test, then byte scan of hit blocks (the current kernel). -/
def scanFold (s : ByteArray) (thr : UInt8) : Array Nat := Id.run do
  let block := 1024
  let size := s.size
  let mut cands : Array Nat := #[]
  let mut b := 0
  while b < size do
    let e := min size (b + block)
    if s.foldl (fun acc x => acc || x ≥ thr) false b e then
      for j in [b:e] do
        if s.get! j ≥ thr then cands := cands.push j
    b := e
  return cands

/-- OR-accumulate the high bits of a block: candidates have bit 7 set. -/
def orBlock (s : ByteArray) (j e : Nat) (acc : UInt8) : UInt8 :=
  if h : j < e ∧ j < s.size then orBlock s (j + 1) e (acc ||| s.get j h.2) else acc
termination_by e - j

end Micro3

open Micro3 in
def micro3Main : IO Unit := do
  let size := 393216
  let mut s := ByteArray.mk (Array.replicate size 20)
  for k in [0:40] do s := s.set! (k * 9831 + 7) 200
  let reps := 2000
  for (name, f) in [("rec", fun s => scanRec s 128 0 #[]), ("fold", fun s => scanFold s 128)] do
    let t0 ← IO.monoNanosNow
    let mut c := 0
    for _ in [0:reps] do
      let r ← IO.lazyPure fun _ => f s
      c := c + r.size
    let t1 ← IO.monoNanosNow
    IO.println s!"{name}: {(t1 - t0).toFloat / (reps * size).toFloat} ns/byte ({c / reps} candidates)"
  let t0 ← IO.monoNanosNow
  let mut c : UInt8 := 0
  for _ in [0:reps] do
    let r ← IO.lazyPure fun _ => orBlock s 0 size 0
    c := c ||| r
  let t1 ← IO.monoNanosNow
  IO.println s!"orBlock: {(t1 - t0).toFloat / (reps * size).toFloat} ns/byte ({c})"

def micro4Main : IO Unit := do
  let size := 393216
  let mut s := ByteArray.mk (Array.replicate size 20)
  for k in [0:40] do s := s.set! (k * 9831 + 7) 200
  let reps := 2000
  let t0 ← IO.monoNanosNow
  let mut c : UInt8 := 0
  for _ in [0:reps] do
    let r ← IO.lazyPure fun _ => s.foldl (fun acc x => acc ||| x) 0 0 size
    c := c ||| r
  let t1 ← IO.monoNanosNow
  IO.println s!"foldl OR: {(t1 - t0).toFloat / (reps * size).toFloat} ns/byte ({c})"
  let t0 ← IO.monoNanosNow
  let mut c2 : Nat := 0
  for _ in [0:reps] do
    let r ← IO.lazyPure fun _ => Id.run do
      let mut cnt := 0
      let mut b := 0
      while b < size do
        if s.foldl (fun acc x => acc ||| x) 0 b (b + 2048) ≥ 128 then cnt := cnt + 1
        b := b + 2048
      return cnt
    c2 := c2 + r
  let t1 ← IO.monoNanosNow
  IO.println s!"foldl OR blocks: {(t1 - t0).toFloat / (reps * size).toFloat} ns/byte ({c2 / reps})"

namespace Micro5

/-- Count primes in `[i, stop)` whose roots match position `ju`: the
divisibility test `(ju - r) * p⁻¹ ≤ ⌊(2^32 - 1)/p⌋` on 32-bit words. -/
def countHits (r1 r2 pinv lim : Array UInt32) (ju : UInt32) (i stop : USize)
    (h1 : stop.toNat ≤ r1.size) (h2 : stop.toNat ≤ r2.size) (h3 : stop.toNat ≤ pinv.size)
    (h4 : stop.toNat ≤ lim.size) (acc : UInt32) : UInt32 :=
  if hi : i < stop then
    have hi' : i.toNat < stop.toNat := hi
    let a := r1.uget i (by omega)
    let b := r2.uget i (by omega)
    let q := pinv.uget i (by omega)
    let l := lim.uget i (by omega)
    let t := (if (ju - a) * q ≤ l then (1 : UInt32) else 0) ||| (if (ju - b) * q ≤ l then 1 else 0)
    countHits r1 r2 pinv lim ju (i + 1) stop h1 h2 h3 h4 (acc + t)
  else acc
termination_by stop.toNat - i.toNat
decreasing_by
  have hs := USize.toNat_lt_size stop
  have : (i + 1).toNat = i.toNat + 1 := by
    have h1 : USize.toNat 1 = 1 := USize.toNat_ofNat_of_lt_32 (by decide)
    rw [USize.toNat_add, h1]
    apply Nat.mod_eq_of_lt
    have : USize.size = 2 ^ System.Platform.numBits := rfl
    omega
  omega

end Micro5

open Micro5 in
def micro5Main : IO Unit := do
  let F := 30000
  let primes : Array UInt32 := (Array.range F).map fun i => (2 * i + 100001).toUInt32
  let inv (p : UInt32) : UInt32 := Id.run do
    -- Newton iteration for p⁻¹ mod 2^32 (p odd)
    let mut x : UInt32 := p
    for _ in [0:5] do x := x * (2 - p * x)
    return x
  let pinv := primes.map inv
  let lim := primes.map fun p => (0xFFFFFFFF : UInt32) / p
  let r1 := primes.map fun p => p / 3
  let r2 := primes.map fun p => p / 5
  let reps := 20000
  let t0 ← IO.monoNanosNow
  let mut c : UInt32 := 0
  for k in [0:reps] do
    let ju := (k * 7 + 3).toUInt32
    have hF : (USize.ofNat F).toNat = F := USize.toNat_ofNat_of_lt_32 (by decide)
    if h : F ≤ r1.size ∧ F ≤ r2.size ∧ F ≤ pinv.size ∧ F ≤ lim.size then
      let r ← IO.lazyPure fun _ => countHits r1 r2 pinv lim ju 0 (USize.ofNat F)
        (by rw [hF]; omega) (by rw [hF]; omega) (by rw [hF]; omega) (by rw [hF]; omega) 0
      c := c + r
  let t1 ← IO.monoNanosNow
  IO.println s!"countHits: {(t1 - t0).toFloat / (reps * F).toFloat} ns/prime ({c})"


namespace Micro6

/-- Primes in `[i, stop)` whose roots match `ju`, on packed 64-bit words:
`roots[i] = r1 | r2 << 32`, `consts[i] = p⁻¹ mod 2^32 | ⌊(2^32-1)/p⌋ << 32`. -/
def countHitsF (roots consts : FloatArray) (ju : UInt32) (i stop : USize)
    (h1 : stop.toNat ≤ roots.size) (h2 : stop.toNat ≤ consts.size) (acc : UInt32) : UInt32 :=
  if hi : i < stop then
    have hi' : i.toNat < stop.toNat := hi
    let w := (roots.uget i (by omega)).toBits
    let c := (consts.uget i (by omega)).toBits
    let q := c.toUInt32
    let l := (c >>> 32).toUInt32
    let a := w.toUInt32
    let b := (w >>> 32).toUInt32
    let t := (if (ju - a) * q ≤ l then (1 : UInt32) else 0) ||| (if (ju - b) * q ≤ l then 1 else 0)
    countHitsF roots consts ju (i + 1) stop h1 h2 (acc + t)
  else acc
termination_by stop.toNat - i.toNat
decreasing_by
  have hs := USize.toNat_lt_size stop
  have : (i + 1).toNat = i.toNat + 1 := by
    have h1 : USize.toNat 1 = 1 := USize.toNat_ofNat_of_lt_32 (by decide)
    rw [USize.toNat_add, h1]
    apply Nat.mod_eq_of_lt
    have : USize.size = 2 ^ System.Platform.numBits := rfl
    omega
  omega

end Micro6

open Micro6 in
def micro6Main : IO Unit := do
  let F := 30000
  let primes : Array UInt32 := (Array.range F).map fun i => (2 * i + 100001).toUInt32
  let inv (p : UInt32) : UInt32 := Id.run do
    let mut x : UInt32 := p
    for _ in [0:5] do x := x * (2 - p * x)
    return x
  let roots : FloatArray := ⟨primes.map fun p =>
    Float.ofBits ((p / 3).toUInt64 ||| ((p / 5).toUInt64 <<< (32 : UInt64)))⟩
  let consts : FloatArray := ⟨primes.map fun p =>
    Float.ofBits ((inv p).toUInt64 ||| (((0xFFFFFFFF : UInt32) / p).toUInt64 <<< (32 : UInt64)))⟩
  let reps := 20000
  let t0 ← IO.monoNanosNow
  let mut c : UInt32 := 0
  for k in [0:reps] do
    let ju := (k * 7 + 3).toUInt32
    if h : (USize.ofNat F).toNat ≤ roots.size ∧ (USize.ofNat F).toNat ≤ consts.size then
      let r ← IO.lazyPure fun _ => countHitsF roots consts ju 0 (USize.ofNat F) h.1 h.2 0
      c := c + r
  let t1 ← IO.monoNanosNow
  IO.println s!"countHitsF: {(t1 - t0).toFloat / (reps * F).toFloat} ns/prime ({c})"

namespace Micro7

/-- Current-style large-prime switch (bounds-checked accessors, two root arrays). -/
def switchLargeA (prime delta : Array UInt32) (logp : ByteArray) (r1 r2 : Array UInt32)
    (s : ByteArray) (i stop : Nat) : Array UInt32 × Array UInt32 × ByteArray :=
  if i < stop then
    let p := prime[i]!
    let d := delta[i]!
    let a := r1[i]! + d
    let a := if a ≥ p then a - p else a
    let b := r2[i]! + d
    let b := if b ≥ p then b - p else b
    let lg := logp.get! i
    let s := if a.toNat < s.size then s.set! a.toNat (s.get! a.toNat + lg) else s
    let s := if b.toNat < s.size then s.set! b.toNat (s.get! b.toNat + lg) else s
    switchLargeA prime delta logp (r1.set! i a) (r2.set! i b) s (i + 1) stop
  else (r1, r2, s)
termination_by stop - i

theorem size_set_byte (s : ByteArray) (j : Nat) (v : UInt8) (h : j < s.size) :
    (s.set j v h).size = s.size := by
  cases s; simp [ByteArray.set, ByteArray.size]

/-- Proof-indexed variant: no bounds checks; both roots packed in one `Nat`. -/
def switchLargeB (prime delta : Array UInt32) (logp : ByteArray) (roots : Array Nat)
    (s : ByteArray) (i stop : Nat) (h1 : stop ≤ prime.size) (h2 : stop ≤ delta.size)
    (h3 : stop ≤ logp.size) (h4 : stop ≤ roots.size) : Array Nat × ByteArray :=
  if hi : i < stop then
    let p := prime[i]
    let d := delta[i]
    let w := (roots[i]'(by omega)).toUInt64
    let a := w.toUInt32 + d
    let a := if a ≥ p then a - p else a
    let b := (w >>> 32).toUInt32 + d
    let b := if b ≥ p then b - p else b
    let lg := logp.get i (by omega)
    let s := if ha : a.toNat < s.size then s.set a.toNat (s.get a.toNat ha + lg) ha else s
    let s := if hb : b.toNat < s.size then s.set b.toNat (s.get b.toNat hb + lg) hb else s
    let roots' := roots.set i (a.toUInt64 ||| (b.toUInt64 <<< 32)).toNat (by omega)
    switchLargeB prime delta logp roots' s (i + 1) stop h1 h2 h3 (by simp [roots']; omega)
  else (roots, s)
termination_by stop - i

end Micro7

open Micro7 in
def micro7Main : IO Unit := do
  let F := 30000
  let size := 393216
  let prime : Array UInt32 := (Array.range F).map fun i => (2 * i + 400001).toUInt32
  let delta := prime.map fun p => p / 7
  let logp := ByteArray.mk (Array.replicate F 19)
  let r1 := prime.map fun p => p / 3
  let r2 := prime.map fun p => p / 5
  let roots : Array Nat := (Array.range F).map fun i => (r1[i]!.toNat ||| (r2[i]!.toNat <<< 32))
  let buf := ByteArray.mk (Array.replicate size 0)
  let reps := 2000
  let t0 ← IO.monoNanosNow
  let mut st := (r1, r2, buf)
  for _ in [0:reps] do
    let (a, b, c) := st
    st ← IO.lazyPure fun _ => switchLargeA prime delta logp a b c 0 F
  let t1 ← IO.monoNanosNow
  IO.println s!"switchLargeA: {(t1 - t0).toFloat / (reps * F).toFloat} ns/prime ({st.2.2.get! 77})"
  let t0 ← IO.monoNanosNow
  let mut st2 := (roots, buf)
  for _ in [0:reps] do
    let (a, c) := st2
    if h : F ≤ prime.size ∧ F ≤ delta.size ∧ F ≤ logp.size ∧ F ≤ a.size then
      st2 ← IO.lazyPure fun _ => switchLargeB prime delta logp a c 0 F h.1 h.2.1 h.2.2.1 h.2.2.2
  let t1 ← IO.monoNanosNow
  IO.println s!"switchLargeB: {(t1 - t0).toFloat / (reps * F).toFloat} ns/prime ({st2.2.get! 77})"
