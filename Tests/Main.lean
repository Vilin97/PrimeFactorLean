import PrimeFactorLean
import Tests.Dataset
import Tests.Primality

open PrimeFactorLean

/-- Algorithms expected to finish every `medium` case (up to 2^64) promptly. -/
private def mediumAlgorithms : List Algorithm :=
  [.rho, .brent, .squfof, .ecm, .cfrac, .qs, .mpqs, .siqs, .auto]

/-- Larger sample cases for the subexponential methods. -/
private def largeCases : List String :=
  ["balanced-20-0", "balanced-24-0", "balanced-28-0", "balanced-32-0", "balanced-36-0",
   "cunningham-2-101-minus", "cunningham-2-137-minus", "cunningham-10-37-minus",
   "cunningham-3-71-minus"]

private def largeAlgorithms : List Algorithm := [.siqs, .mpqs, .auto]

private def check (algorithm : Algorithm) (c : Tests.DatasetCase) (cfg : Config) :
    IO Bool := do
  let result := (factor algorithm c.n cfg).map (fun ps => ps.mergeSort (· ≤ ·))
  if result != c.factors then
    IO.eprintln s!"FAIL {algorithm.name} {c.name}: {repr result}, expected {repr c.factors}"
    return false
  return true

def main : IO UInt32 := do
  let cfg : Config := { threads := 4 }
  let mut checked := 0
  for algorithm in Algorithm.all do
    for c in Tests.dataset do
      if c.tier == "core" then
        unless (← check algorithm c cfg) do return 1
        checked := checked + 1
  for algorithm in mediumAlgorithms do
    for c in Tests.dataset do
      if c.tier == "medium" then
        unless (← check algorithm c cfg) do return 1
        checked := checked + 1
  for algorithm in largeAlgorithms do
    for c in Tests.dataset do
      if largeCases.contains c.name then
        unless (← check algorithm c cfg) do return 1
        checked := checked + 1
  for algorithm in Algorithm.all do
    for z in [(-360 : Int), -1, 1, 360] do
      match factorSigned algorithm z cfg with
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
  if (ECMM.split 8051 { curves := 0 }).isSome then return 1
  -- Raw splitters must split nontrivial composites without any fallback.
  let rawCases : List (Algorithm × Nat) := [
    (.fermat, 100160063), (.rho, 8051), (.brent, 1000036000099), (.squfof, 1000036000099),
    (.pMinusOne, 257000771), (.ecmAffine, 1000036000099), (.ecm, 2535301200456458802993406410751),
    (.cfrac, 2535301200456458802993406410751), (.qs, 399689307492338326227643),
    (.mpqs, 399689307492338326227643), (.siqs, 423983770233695968509874612799),
    (.gnfs, 399689307492338326227643), (.auto, 423983770233695968509874612799)]
  for (algorithm, n) in rawCases do
    match rawSearch algorithm cfg n with
    | none => IO.eprintln s!"FAIL raw {algorithm.name} on {n}"; return 1
    | some d =>
      if !(1 < d && d < n && n % d == 0) then
        IO.eprintln s!"FAIL invalid raw {algorithm.name} divisor {d}"; return 1
  let primeChecks ← Tests.checkPrimality
  if !primeChecks then return 1
  IO.println s!"PASS: {checked} dataset factorizations, signed cases, raw splitters, failure bounds, and certificates."
  return 0
