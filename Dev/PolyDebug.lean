import PrimeFactorLean.NFS.PolySelect

open PrimeFactorLean PrimeFactorLean.NFS

/-- Print a Kleinjung-style polynomial in CADO-NFS format. -/
def polyDebug (n d adStep adCount ell qlo qhi U V : Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => PolySelect.select n d adStep adCount ell qlo qhi U V 16
  let t1 ← IO.monoNanosNow
  match r with
  | none => IO.println "no polynomial"
  | some sel =>
    IO.println s!"n: {n}"
    for i in [0:sel.coeffs.size] do IO.println s!"c{i}: {sel.coeffs[i]!}"
    IO.println s!"Y0: -{sel.m}"
    IO.println s!"Y1: {sel.y1}"
    IO.println s!"skew: {(PolySelect.logNorm sel.coeffs).2}"
    IO.println s!"# alpha {PolySelect.alpha sel.coeffs} lognorm {(PolySelect.logNorm sel.coeffs).1} time {(t1 - t0) / 1000000} ms"

/-- Collision-search polynomial in CADO-NFS format. -/
def polyDebug2 (n d P nq incr admax keep U V lpbR lpbA : Nat) (area : Float) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ =>
    PolySelect.selectCollision n d P nq incr admax keep U V lpbR lpbA area 16
  let t1 ← IO.monoNanosNow
  match r with
  | none => IO.println "no polynomial"
  | some sel =>
    IO.println s!"n: {n}"
    for i in [0:sel.coeffs.size] do IO.println s!"c{i}: {sel.coeffs[i]!}"
    IO.println s!"Y0: -{sel.m}"
    IO.println s!"Y1: {sel.y1}"
    IO.println s!"skew: {(PolySelect.logNorm sel.coeffs).2}"
    IO.println s!"# alpha {PolySelect.alpha sel.coeffs} lognorm {(PolySelect.logNorm sel.coeffs).1} time {(t1 - t0) / 1000000} ms"

/-- Check the rotation sieve against direct `α` on a polynomial pair. -/
def alphaCheck (cs : Array Int) (l m : Int) (V : Nat) : IO Unit := do
  let arr := PolySelect.alphaSieve cs l m 0 (-(V : Int)) (2 * V + 1)
  IO.println s!"alpha direct {PolySelect.alpha cs} sieve(v=0) {arr.get! V}"
  for v in ([1, 2, 3, 7, 100] : List Nat) do
    let rot := PolySelect.rotJ cs l m (v : Int) 0
    IO.println s!"v={v}: direct {PolySelect.alpha rot} sieve {arr.get! (V + v)}"
  let mut best := 0
  for t in [0:arr.size] do
    if arr.get! t < arr.get! best then best := t
  IO.println s!"min sieve alpha {arr.get! best} at v={(best : Int) - (V : Int)}"

/-- All size-optimized collision candidates for `ad ≤ admax`, with their Murphy `E`. -/
def polyStats (n d P nq incr admax : Nat) (lpbR lpbA : Nat) (area : Float) : IO Unit := do
  let t := 16
  let count := (admax + incr - 1) / incr
  let per := (count + t - 1) / t
  let tasks := (List.range t).map fun i =>
    Task.spawn fun _ => PolySelect.collisionSearch n d P nq incr (1 + i * per * incr)
      (min (admax + 1) (1 + (i + 1) * per * incr)) 100000
  let cands := tasks.foldl (fun acc tk => acc ++ tk.get) #[]
  let tbl := PolySelect.dickmanTable
  let bf := Float.exp2 lpbA.toFloat
  let bg := Float.exp2 lpbR.toFloat
  let scored := cands.map fun c =>
    let s := (PolySelect.logNorm c.cs).2
    (PolySelect.murphyE tbl c.cs c.l c.m s bf bg area, c)
  let sorted := scored.qsort fun a b => a.1 > b.1
  IO.println s!"{cands.size} candidates"
  for (e, c) in sorted.extract 0 10 do
    IO.println s!"E {e} score {c.score} lognorm {(PolySelect.logNorm c.cs).1} alpha {PolySelect.alpha c.cs} l {c.l} ad {c.cs.back!}"
  let byScore := cands.qsort fun a b => a.score < b.score
  let rank := fun (c : PolySelect.CCand) => (byScore.findIdx? fun x => x.cs == c.cs).getD 0
  IO.println s!"ranks by lognorm+alpha of the 10 best E: {(sorted.extract 0 10).map fun x => rank x.2}"

/-- Murphy `E` of the best candidates before and after root optimization. -/
def rootStats (n d P nq incr admax keep U V : Nat) (lpbR lpbA : Nat) (area : Float) : IO Unit := do
  let t := 16
  let count := (admax + incr - 1) / incr
  let per := (count + t - 1) / t
  let tasks := (List.range t).map fun i =>
    Task.spawn fun _ => PolySelect.collisionSearch n d P nq incr (1 + i * per * incr)
      (min (admax + 1) (1 + (i + 1) * per * incr)) keep
  let cands := ((tasks.foldl (fun acc tk => acc ++ tk.get) #[]).qsort fun a b => a.score < b.score).extract 0 keep
  let tbl := PolySelect.dickmanTable
  let bf := Float.exp2 lpbA.toFloat
  let bg := Float.exp2 lpbR.toFloat
  let E (c : PolySelect.CCand) : Float := PolySelect.murphyE tbl c.cs c.l c.m (PolySelect.logNorm c.cs).2 bf bg area
  let rot := cands.toList.map fun c => Task.spawn fun _ => PolySelect.rootOpt c 1.0 U V 32
  let mut outs : Array (Float × PolySelect.CCand) := #[]
  for (c, tk) in cands.toList.zip rot do
    let r := tk.get
    let (n0, s0) := PolySelect.logNorm c.cs
    let (n1, s1) := PolySelect.logNorm r.cs
    IO.println s!"expE {c.score}: E*1e6 {E c * 1000000.0} (lognorm {n0} alpha {PolySelect.alpha c.cs} skew {s0}) -> {E r * 1000000.0} (lognorm {n1} alpha {PolySelect.alpha r.cs} skew {s1})"
    outs := outs.push (E r, r)
  let top := (outs.qsort fun a b => a.1 > b.1).extract 0 5
  for k in [0:top.size] do
    let (e, c) := top[k]!
    let mut txt := s!"n: {n}\n"
    for i in [0:c.cs.size] do txt := txt ++ s!"c{i}: {c.cs[i]!}\n"
    txt := txt ++ s!"Y0: {-c.m}\nY1: {c.l}\nskew: {(PolySelect.logNorm c.cs).2}\n"
    IO.FS.writeFile s!"/tmp/claude-1000/-home-vas-Github-PrimeFactorLean/26690e62-2017-4080-96f2-e24819536d6f/scratchpad/top{k}.poly" txt
    IO.println s!"top{k}: ourE*1e6 {e * 1000000.0}"
