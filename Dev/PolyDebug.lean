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
