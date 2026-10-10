import PrimeFactorLean.Algorithms

/-! Timing of each stage of the automatic splitter on one input. -/

open PrimeFactorLean

def stageTime (label : String) (f : Unit → Option Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: {(t1 - t0).toFloat / 1.0e6} ms -> {r}"

def autoStages (n threads : Nat) : IO Unit := do
  let cfg : Config := { threads := threads }
  stageTime "trial 4096" fun _ => (smallSplitter 4096 n).map (·.val)
  stageTime "power" fun _ => (powerSplitter n).map (·.val)
  stageTime "brent 20000x2 (nat)" fun _ =>
    Search.brent n { cfg.search with rhoSteps := 20000, rhoRestarts := 2 }
  stageTime "brent 20000x2 (fast)" fun _ => (RhoF.split n 20000 2).map (·.val)
  stageTime "p-1 B1=20000 (nat)" fun _ => (PMinusOne.splitPMinusOne n 20000).map (·.val)
  stageTime "p-1 B1=20000 (fast)" fun _ => (PM1F.split n 20000).map (·.val)
  for (b1, curves) in ecmSchedule (QS.decimalDigits n) do
    stageTime s!"ecm B1={b1} curves={curves}" fun _ =>
      (ECMF.split n { b1 := b1, curves := curves, threads := threads }).map (·.val)
  stageTime "siqs" fun _ => (SIQS.split n { threads := threads }).map (·.val)
  stageTime "primeOracle(n)" fun _ => if primeOracle cfg n then some 1 else none
  stageTime "full factor auto" fun _ => (factor .auto n cfg).map (·.length)
