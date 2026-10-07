import PrimeFactorLean
import Tests.Dataset
import Tests.Primality
import Tests.Audit

open PrimeFactorLean

private def algorithms : List Algorithm := [.trial, .wheel, .fermat, .rho, .brent, .pMinusOne, .ecm, .qs, .mpqs, .nfsQuadratic, .nfsCubic, .auto]

def main : IO UInt32 := do
  let mut checked := 0
  for algorithm in algorithms do
    for c in Tests.dataset do
      if !c.stress then
        let result := (factor algorithm c.n).map (fun ps => ps.mergeSort (· ≤ ·))
        if result != c.factors then
          IO.eprintln s!"FAIL {algorithm.name} {c.name}: {repr result}, expected {repr c.factors}"
          return 1
        checked := checked + 1
  for algorithm in algorithms do
    for z in [(-360 : Int), -1, 1, 360] do
      let result := factorSigned algorithm z
      match result with
      | none => IO.eprintln s!"FAIL signed {z}"; return 1
      | some (sign, ps) =>
        if sign * (ps.prod : Int) != z then
          IO.eprintln s!"FAIL signed product {z}"
          return 1
  -- Search failures must remain failures, and invalid divisors must be rejected.
  if (checkedSplitter (fun _ => some 1) 91).isSome then return 1
  if (checkedSplitter (fun _ => some 10) 91).isSome then return 1
  if (checkedSplitter (fun _ => some 91) 91).isSome then return 1
  if (checkedSplitter (fun _ => some 7) 91).isNone then return 1
  if Search.fermat 8051 {fermatSteps := 0} != none then return 1
  if Search.brent 8051 {rhoSteps := 0} != none then return 1
  if ECM.split 8051 200 0 != none then return 1
  if QuadraticSieve.split 8051 3 0 != none then return 1
  -- These raw searches must split nontrivial odd composites without fallback.
  for (name, n, result) in [
      ("fermat", 100160063, Search.fermat 100160063),
      ("rho", 8051, Search.rho 8051),
      ("brent", 1000036000099, Search.brent 1000036000099),
      ("pminusone", 257000771, Search.pMinusOne 257000771),
      ("ecm", 1000036000099, ECM.split 1000036000099),
      ("nfs-quadratic", 221, NumberFieldSieve.split 221),
      ("nfs-cubic", 2479, CubicNumberFieldSieve.split 2479),
      ("mpqs", 30000023 * 10000019, QuadraticSieve.splitMPQS (30000023 * 10000019)),
      ("qs", 300320077, QuadraticSieve.split 300320077)] do
    match result with
    | none => IO.eprintln s!"FAIL raw {name} on {n}"; return 1
    | some d =>
      if !(1 < d && d < n && n % d == 0) then
        IO.eprintln s!"FAIL invalid raw {name} divisor {d}"; return 1
  let primeChecks ← Tests.checkPrimality
  if !primeChecks then return 1
  IO.println s!"PASS: {checked} dataset factorizations, signed cases, raw splitters, failure bounds, and certificate tampering."
  return 0
