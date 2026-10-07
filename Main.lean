import PrimeFactorLean

open PrimeFactorLean Lean

-- An IO boundary prevents pure work from being moved outside the measured interval.
@[noinline] private def computeFactor (algorithm : Algorithm) (n : Nat) :
    IO (Option (List Nat)) := pure (factor algorithm n)

@[noinline] private def computeSplit (algorithm : Algorithm) (n : Nat) :
    IO (Option Nat) := pure (rawSearch algorithm {} n)

private def emit (algorithm : String) (z : Int) (factors : Option (List Nat))
    (elapsed : Nat) : IO Unit := do
  let data := Lean.Json.mkObj [
    ("algorithm", toJson algorithm),
    ("n", toJson (toString z)),
    ("sign", toJson (toString z.sign)),
    ("factors", match factors with
      | none => Lean.Json.null
      | some ps => toJson (ps.map toString)),
    ("elapsedNs", toJson elapsed)]
  (← IO.getStdout).putStrLn data.compress

def main (args : List String) : IO UInt32 := do
  match args with
  | [mode, input] =>
    match Algorithm.parse mode, input.toInt? with
    | some algorithm, some z =>
      let started ← IO.monoNanosNow
      let factors ← computeFactor algorithm z.natAbs
      let stopped ← IO.monoNanosNow
      emit mode z factors (stopped - started)
      return 0
    | _, _ =>
      (← IO.getStderr).putStrLn "Unknown algorithm or invalid integer."
      return 1
  | ["--split", mode, input] =>
    match Algorithm.parse mode, input.toNat? with
    | some algorithm, some n =>
      let started ← IO.monoNanosNow
      let result ← computeSplit algorithm n
      let stopped ← IO.monoNanosNow
      (← IO.getStdout).putStrLn (Lean.Json.mkObj [
        ("algorithm", toJson mode), ("n", toJson input),
        ("divisor", match result with | none => Lean.Json.null | some d => toJson (toString d)),
        ("elapsedNs", toJson (stopped - started))]).compress
      return 0
    | _, _ => return 1
  | _ =>
    (← IO.getStderr).putStrLn "Usage: factor ALGORITHM INTEGER | factor --split ALGORITHM NATURAL\nAlgorithms: trial-reference trial wheel fermat rho brent pminusone ecm qs mpqs nfs-quadratic nfs-cubic auto"
    return 1
