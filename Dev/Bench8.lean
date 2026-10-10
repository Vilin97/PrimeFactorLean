import PrimeFactorLean.SIQS

/-! Micro-benchmarks for a blocked SIQS sieve: L1-sized blocks with per-block
positions for small primes, buckets for large primes, compared with the
current whole-interval (L2-resident) kernels. -/

namespace Bench8

open PrimeFactorLean PrimeFactorLean.SIQS

/-- `count` clamped updates at `a, a+p, …` and `b, b+p, …` (two roots per step). -/
def stride2 (s : ByteArray) (len a b p : USize) (lg : UInt8) (h : len.toNat < s.size) :
    Nat → ByteArray
  | 0 => s
  | count + 1 =>
    let t := hitClamp s len a lg h
    let t := hitClamp t len b lg (by rw [size_hitClamp]; exact h)
    stride2 t len (a + p) (b + p) p lg (by rw [size_hitClamp, size_hitClamp]; exact h) count

theorem size_stride2 (s : ByteArray) (len a b p : USize) (lg : UInt8) (h : len.toNat < s.size)
    (c : Nat) : (stride2 s len a b p lg h c).size = s.size := by
  induction c generalizing s a b with
  | zero => rfl
  | succ c ih => simp only [stride2]; rw [ih, size_hitClamp, size_hitClamp]

/-- Sieve one block of `bs` bytes for primes in `[i, stop)` whose positions
(relative to the block start, in `[0, p)`) are packed in `pos`; store the
positions relative to the next block. `cnt` holds `⌈bs / p⌉`. -/
def blockSmall (primeB cnt logp : ByteArray) (pos : Array Nat) (s : ByteArray) (bs : USize)
    (hs : bs.toNat < s.size) (i stop : Nat) (h1 : 4 * stop ≤ primeB.size) (h2 : stop ≤ cnt.size)
    (h3 : stop ≤ logp.size) (h4 : stop ≤ pos.size) : Array Nat × ByteArray :=
  if hi : i < stop then
    let p := (u32 primeB i (by omega)).toUSize
    let c := cnt.get i (by omega)
    let w := pos[i]
    let a := (root1 w).toUSize
    let b := (root2 w).toUSize
    let lg := logp.get i (by omega)
    let t := stride2 s bs a b p lg hs c.toNat
    let cp := c.toUSize * p - bs
    let a' := a + cp
    let a' := if a' ≥ p then a' - p else a'
    let b' := b + cp
    let b' := if b' ≥ p then b' - p else b'
    let pos' := pos.set i (packRoots a'.toUInt32 b'.toUInt32) (by omega)
    blockSmall primeB cnt logp pos' t bs (by rw [size_stride2]; exact hs) (i + 1) stop h1 h2 h3
      (by simp [pos']; omega)
  else (pos, s)
termination_by stop - i

/-- Bucket fill for large primes in `[i, stop)` (each root moved by `±δ`): every
hit `pos < len` appends `(pos mod bs) | i << 15` to bucket `pos / bs`
(`cap` slots each; counters in `cnt`). Primes may hit several times. -/
def fillBuckets (primeB deltaB : ByteArray) (add : Bool) (roots : Array Nat) (bk : Array Nat)
    (cnt : Array Nat) (len cap : Nat) (i stop : Nat) (h1 : 4 * stop ≤ primeB.size)
    (h2 : 4 * stop ≤ deltaB.size) (h4 : stop ≤ roots.size) :
    Array Nat × Array Nat × Array Nat :=
  if hi : i < stop then
    let p := u32 primeB i (by omega)
    let d := u32 deltaB i (by omega)
    let w := roots[i]
    let a := moveRoot add (root1 w) d p
    let b := moveRoot add (root2 w) d p
    let roots' := roots.set i (packRoots a b) (by omega)
    let (bk, cnt) := hitsOf bk cnt a.toNat p.toNat i len cap 64
    let (bk, cnt) := hitsOf bk cnt b.toNat p.toNat i len cap 64
    fillBuckets primeB deltaB add roots' bk cnt len cap (i + 1) stop h1 h2 (by simp [roots']; omega)
  else (roots, bk, cnt)
termination_by stop - i
where
  hitsOf (bk cnt : Array Nat) (pos p i len cap : Nat) : Nat → Array Nat × Array Nat
    | 0 => (bk, cnt)
    | fuel + 1 =>
      if pos < len then
        let blk := pos >>> 15
        let c := cnt[blk]!
        let bk := bk.set! (blk * cap + c) ((pos &&& 32767) ||| (i <<< 15))
        let cnt := cnt.set! blk (c + 1)
        hitsOf bk cnt (pos + p) p i len cap fuel
      else (bk, cnt)

/-- Apply bucket entries `[k, stop)` to a block. -/
def applyBucket (bk : Array Nat) (logp : ByteArray) (s : ByteArray) (k stop : Nat) : ByteArray :=
  if k < stop then
    let e := bk[k]!
    let pos := e &&& 32767
    let lg := logp.get! (e >>> 15)
    applyBucket bk logp (s.set! pos (s.get! pos + lg)) (k + 1) stop
  else s
termination_by stop - k

def primesFB (F : Nat) : Array Nat := Id.run do
  let ps := Arith.primesUpTo 3000000
  let mut out : Array Nat := #[2]
  let mut k := 1
  while out.size < F && k < ps.size do
    out := out.push ps[k]!
    k := k + 2
  return out

def bench8Main : IO Unit := do
  let F := 47000
  let bsN := 32768
  let nb := 12
  let lenN := bsN * nb
  let fb := primesFB F
  IO.println s!"F={fb.size} pmax={fb[fb.size - 1]!} len={lenN}"
  let prime := fb.map (·.toUInt32)
  let primeB := packU32 prime
  let deltaB := packU32 (prime.map fun p => p / 7 + 1)
  let logp := ByteArray.mk (fb.map fun p => (Nat.log2 p).toUInt8)
  let roots : Array Nat := fb.map fun p => packRoots (p / 3).toUInt32 (p * 5 / 7).toUInt32
  let mut spv := 0
  while fb[spv]! < 150 do spv := spv + 1
  let mut smallEnd := spv
  while fb[smallEnd]! < bsN do smallEnd := smallEnd + 1
  let mut medEnd := smallEnd
  while medEnd < F && fb[medEnd]! < lenN do medEnd := medEnd + 1
  IO.println s!"spv={spv} smallEnd={smallEnd} medEnd={medEnd}"
  let len : USize := lenN.toUSize
  let reps := 300
  -- current: switchMedium over [spv, medEnd), switchLarge over [medEnd, F)
  let template := ByteArray.mk (Array.replicate (lenN + 1) 0)
  let t0 ← IO.monoNanosNow
  let mut st := (roots, template)
  for r in [0:reps] do
    let (rs, buf) := st
    let buf := template.copySlice 0 buf 0 template.size
    if h : len.toNat < buf.size ∧ 4 * F ≤ primeB.size ∧ 4 * F ≤ deltaB.size ∧ F ≤ logp.size ∧
        F ≤ rs.size ∧ medEnd ≤ F then
      let (rs, buf) ← IO.lazyPure fun _ => switchMedium primeB deltaB logp (r % 2 == 0) rs buf len
        h.1 spv medEnd (by omega) (by omega) (by omega) (by omega)
      if h' : len.toNat < buf.size ∧ F ≤ rs.size then
        st ← IO.lazyPure fun _ => switchLarge primeB deltaB logp (r % 2 == 0) rs buf len h'.1
          medEnd F (by omega) (by omega) (by omega) h'.2
  let t1 ← IO.monoNanosNow
  IO.println s!"current (medium+large): {(t1 - t0).toFloat / reps.toFloat / 1000.0} us/poly ({st.2.get! 77})"
  -- current, medium only (p < len)
  let t0 ← IO.monoNanosNow
  let mut st3 := (roots, template)
  for r in [0:reps] do
    let (rs, buf) := st3
    let buf := template.copySlice 0 buf 0 template.size
    if h : len.toNat < buf.size ∧ 4 * F ≤ primeB.size ∧ 4 * F ≤ deltaB.size ∧ F ≤ logp.size ∧
        F ≤ rs.size ∧ smallEnd ≤ F then
      st3 ← IO.lazyPure fun _ => switchMedium primeB deltaB logp (r % 2 == 0) rs buf len
        h.1 spv smallEnd (by omega) (by omega) (by omega) (by omega)
  let t1 ← IO.monoNanosNow
  IO.println s!"current small primes (p < bs) whole interval: {(t1 - t0).toFloat / reps.toFloat / 1000.0} us/poly ({st3.2.get! 77})"
  -- blocked small primes: positions per block
  let cnt := ByteArray.mk (fb.map fun p => ((bsN + p - 1) / p).toUInt8)
  let blockT := ByteArray.mk (Array.replicate (bsN + 1) 0)
  let bs : USize := bsN.toUSize
  let t0 ← IO.monoNanosNow
  let mut acc := 0
  let mut posA := roots
  for _ in [0:reps] do
    let mut pos := roots
    let mut blk := blockT
    for _ in [0:nb] do
      blk := blockT.copySlice 0 blk 0 blockT.size
      if h : bs.toNat < blk.size ∧ 4 * smallEnd ≤ primeB.size ∧ smallEnd ≤ cnt.size ∧
          smallEnd ≤ logp.size ∧ smallEnd ≤ pos.size then
        let (p', b') ← IO.lazyPure fun _ => blockSmall primeB cnt logp pos blk bs h.1 spv smallEnd
          h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
        pos := p'
        blk := b'
      acc := acc + (blk.get! 77).toNat
    posA := pos
  let t1 ← IO.monoNanosNow
  IO.println s!"blocked small primes: {(t1 - t0).toFloat / reps.toFloat / 1000.0} us/poly ({acc} {posA[spv]!})"
  -- buckets for p ≥ bs: fill (with root update) + apply
  let cap := 24000
  let bk0 : Array Nat := Array.replicate (nb * cap) 0
  let cnt0 : Array Nat := Array.replicate nb 0
  let t0 ← IO.monoNanosNow
  let mut stb := (roots, bk0)
  let mut tot := 0
  let mut tApply := 0
  for r in [0:reps] do
    let (rs, bk) := stb
    if h : 4 * F ≤ primeB.size ∧ 4 * F ≤ deltaB.size ∧ F ≤ rs.size then
      let (rs, bk, cnt) ← IO.lazyPure fun _ => fillBuckets primeB deltaB (r % 2 == 0) rs bk cnt0
        lenN cap smallEnd F h.1 h.2.1 h.2.2
      let a0 ← IO.monoNanosNow
      let mut blk := blockT
      for b in [0:nb] do
        blk := blockT.copySlice 0 blk 0 blockT.size
        blk ← IO.lazyPure fun _ => applyBucket bk logp blk (b * cap) (b * cap + cnt[b]!)
        tot := tot + (blk.get! 99).toNat
      let a1 ← IO.monoNanosNow
      tApply := tApply + (a1 - a0)
      tot := tot + cnt.foldl (· + ·) 0
      stb := (rs, bk)
  let t1 ← IO.monoNanosNow
  IO.println s!"buckets p ≥ bs: {(t1 - t0).toFloat / reps.toFloat / 1000.0} us/poly (apply {tApply.toFloat / reps.toFloat / 1000.0}), hits/poly {tot / reps}"

end Bench8

namespace Bench9

open PrimeFactorLean PrimeFactorLean.SIQS

/-- Medium-prime switch with precomputed counts `⌈len/p⌉` (no division), unboxed
`Array UInt32` primes/deltas, and one two-root stride loop. -/
def switchMed2 (prime delta cnt : Array UInt32) (logp : ByteArray) (add : Bool) (roots : Array Nat)
    (s : ByteArray) (len : USize) (hs : len.toNat < s.size) (i stop : Nat)
    (h1 : stop ≤ prime.size) (h2 : stop ≤ delta.size) (h3 : stop ≤ logp.size)
    (h4 : stop ≤ roots.size) (h5 : stop ≤ cnt.size) : Array Nat × ByteArray :=
  if hi : i < stop then
    let p := prime[i]
    let d := delta[i]
    let w := roots[i]
    let a := moveRoot add (root1 w) d p
    let b := moveRoot add (root2 w) d p
    let lg := logp.get i (by omega)
    let t := Bench8.stride2 s len a.toUSize b.toUSize p.toUSize lg hs cnt[i].toNat
    let roots' := roots.set i (packRoots a b) (by omega)
    switchMed2 prime delta cnt logp add roots' t len (by rw [Bench8.size_stride2]; exact hs) (i + 1)
      stop h1 h2 h3 (by simp [roots']; omega) h5
  else (roots, s)
termination_by stop - i

def bench9Main : IO Unit := do
  let F := 47000
  let lenN := 393216
  let fb := Bench8.primesFB F
  let prime := fb.map (·.toUInt32)
  let primeB := packU32 prime
  let delta := prime.map fun p => p / 7 + 1
  let deltaB := packU32 delta
  let cnt := prime.map fun p => (lenN.toUInt32 + p - 1) / p
  let logp := ByteArray.mk (fb.map fun p => (Nat.log2 p).toUInt8)
  let roots : Array Nat := fb.map fun p => packRoots (p / 3).toUInt32 (p * 5 / 7).toUInt32
  let mut spv := 0
  while fb[spv]! < 150 do spv := spv + 1
  let mut medEnd := spv
  while medEnd < F && fb[medEnd]! < lenN do medEnd := medEnd + 1
  let len : USize := lenN.toUSize
  let reps := 300
  let template := ByteArray.mk (Array.replicate (lenN + 1) 0)
  for variant in [0, 1, 0, 1] do
    let t0 ← IO.monoNanosNow
    let mut rs := roots
    let mut buf := template
    let mut acc := 0
    for r in [0:reps] do
      buf := template.copySlice 0 buf 0 template.size
      if h : len.toNat < buf.size ∧ 4 * medEnd ≤ primeB.size ∧ 4 * medEnd ≤ deltaB.size ∧
          medEnd ≤ logp.size ∧ medEnd ≤ rs.size ∧ medEnd ≤ prime.size ∧ medEnd ≤ delta.size ∧
          medEnd ≤ cnt.size then
        if variant == 0 then
          let (rs', buf') ← IO.lazyPure fun _ => switchMedium primeB deltaB logp (r % 2 == 0) rs buf len
            h.1 spv medEnd h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
          rs := rs'
          buf := buf'
        else
          let (rs', buf') ← IO.lazyPure fun _ => switchMed2 prime delta cnt logp (r % 2 == 0) rs buf len
            h.1 spv medEnd h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2.2
          rs := rs'
          buf := buf'
      acc := acc + (buf.get! 1234).toNat
    let t1 ← IO.monoNanosNow
    IO.println s!"variant {variant}: {(t1 - t0).toFloat / reps.toFloat / 1000.0} us/poly (medEnd {medEnd}) {acc}"

end Bench9

namespace Bench10

open PrimeFactorLean PrimeFactorLean.SIQS

theorem size_fuset (a : FloatArray) (i : USize) (v : Float) (h : i.toNat < a.size) :
    (a.uset i v h).size = a.size := by
  cases a; simp [FloatArray.uset, FloatArray.size]

theorem size_fset (a : FloatArray) (i : Nat) (v : Float) (h : i < a.size) :
    (a.set i v h).size = a.size := by
  cases a; simp [FloatArray.set, FloatArray.size]

@[inline] def lo32 (f : Float) : UInt32 := f.toBits.toUInt32
@[inline] def hi32 (f : Float) : UInt32 := (f.toBits >>> 32).toUInt32
@[inline] def pack2 (a b : UInt32) : Float := Float.ofBits (a.toUInt64 ||| (b.toUInt64 <<< 32))

/-- Large-prime switch on packed rows: `pd[i] = p | δ << 32`, `roots[i] = r1 | r2 << 32`. -/
def switchBigF (pd : FloatArray) (logp : ByteArray) (add : Bool) (roots : FloatArray)
    (s : ByteArray) (len : USize) (hs : len.toNat < s.size) (i stop : Nat)
    (h1 : stop ≤ pd.size) (h4 : stop ≤ logp.size) (h5 : stop ≤ roots.size) : FloatArray × ByteArray :=
  if hi : i < stop then
    let e := pd.get i (by omega)
    let p := lo32 e
    let d := hi32 e
    let w := roots.get i (by omega)
    let a := moveRoot add (lo32 w) d p
    let b := moveRoot add (hi32 w) d p
    let lg := logp.get i (by omega)
    let t := hitClamp s len a.toUSize lg hs
    let t := hitClamp t len b.toUSize lg (by rw [size_hitClamp]; exact hs)
    let roots' := roots.set i (pack2 a b) (by omega)
    switchBigF pd logp add roots' t len (by rw [size_hitClamp, size_hitClamp]; exact hs)
      (i + 1) stop h1 h4 (by rw [size_fset]; omega)
  else (roots, s)
termination_by stop - i

def bench10Main : IO Unit := do
  let F := 47000
  let lenN := 393216
  let fb := Bench8.primesFB F
  let prime := fb.map (·.toUInt32)
  let primeB := packU32 prime
  let delta := prime.map fun p => p / 7 + 1
  let deltaB := packU32 delta
  let logp := ByteArray.mk (fb.map fun p => (Nat.log2 p).toUInt8)
  let roots : Array Nat := fb.map fun p => packRoots (p / 3).toUInt32 (p * 5 / 7).toUInt32
  let rootsF : FloatArray := ⟨fb.map fun p => Bench10.pack2 (p / 3).toUInt32 (p * 5 / 7).toUInt32⟩
  let pd : FloatArray := ⟨(Array.range F).map fun i => Bench10.pack2 prime[i]! delta[i]!⟩
  let mut medEnd := 0
  while medEnd < F && fb[medEnd]! < lenN do medEnd := medEnd + 1
  let len : USize := lenN.toUSize
  let reps := 300
  let template := ByteArray.mk (Array.replicate (lenN + 1) 0)
  for variant in [0, 1, 2, 0, 1, 2] do
    let t0 ← IO.monoNanosNow
    let mut rs := roots
    let mut rf := rootsF
    let mut buf := template
    for r in [0:reps] do
      buf := template.copySlice 0 buf 0 template.size
      if h : len.toNat < buf.size ∧ 4 * F ≤ primeB.size ∧ 4 * F ≤ deltaB.size ∧ F ≤ logp.size ∧
          F ≤ rs.size ∧ F ≤ prime.size ∧ F ≤ delta.size ∧ F ≤ pd.size ∧ F ≤ rf.size then
        if variant == 0 then
          let (a, b) ← IO.lazyPure fun _ => switchLarge primeB deltaB logp (r % 2 == 0) rs buf len h.1
            medEnd F h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
          rs := a
          buf := b
        else if variant == 1 then
          let (a, b) ← IO.lazyPure fun _ => switchBig prime delta logp (r % 2 == 0) rs buf len h.1
            medEnd F h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.1 h.2.2.2.2.1
          rs := a
          buf := b
        else
          let (a, b) ← IO.lazyPure fun _ => switchBigF pd logp (r % 2 == 0) rf buf len h.1
            medEnd F h.2.2.2.2.2.2.2.1 h.2.2.2.1 h.2.2.2.2.2.2.2.2
          rf := a
          buf := b
    let t1 ← IO.monoNanosNow
    IO.println s!"variant {variant}: {(t1 - t0).toFloat / reps.toFloat / 1000.0} us/poly for {F - medEnd} large primes ({buf.get! 1000})"

end Bench10
