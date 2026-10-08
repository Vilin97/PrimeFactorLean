import PrimeFactorLean

open PrimeFactorLean Lean

-- An IO boundary prevents pure work from being moved outside the measured interval.
@[noinline] private def computeFactor (algorithm : Algorithm) (n : Nat) (cfg : Config) :
    IO (Option (List Nat)) := IO.lazyPure fun _ => factor algorithm n cfg

@[noinline] private def computeSplit (algorithm : Algorithm) (n : Nat) (cfg : Config) :
    IO (Option Nat) := IO.lazyPure fun _ => rawSearch algorithm cfg n

private def usage : String :=
  "Usage: factor [--threads T] ALGORITHM INTEGER\n" ++
  "       factor [--threads T] --split ALGORITHM NATURAL\n" ++
  "Algorithms: " ++ " ".intercalate (Algorithm.all.map Algorithm.name)

/-- Parse leading `--threads T` options. -/
private def parseOptions : List String → Config → List String × Config
  | "--threads" :: t :: rest, cfg =>
    match t.toNat? with
    | some k => parseOptions rest { cfg with threads := max 1 k }
    | none => (["--invalid"], cfg)
  | args, cfg => (args, cfg)

def main (args : List String) : IO UInt32 := do
  let (args, cfg) := parseOptions args {}
  match args with
  | [mode, input] =>
    match Algorithm.parse mode, input.toInt? with
    | some algorithm, some z =>
      let started ← IO.monoNanosNow
      let factors ← computeFactor algorithm z.natAbs cfg
      let stopped ← IO.monoNanosNow
      let data := Json.mkObj [
        ("algorithm", toJson mode),
        ("n", toJson (toString z)),
        ("sign", toJson (toString z.sign)),
        ("factors", match factors with
          | none => Json.null
          | some ps => toJson ((ps.mergeSort (· ≤ ·)).map toString)),
        ("elapsedNs", toJson (stopped - started))]
      (← IO.getStdout).putStrLn data.compress
      return 0
    | _, _ =>
      (← IO.getStderr).putStrLn ("Unknown algorithm or invalid integer.\n" ++ usage)
      return 1
  | ["--split", mode, input] =>
    match Algorithm.parse mode, input.toNat? with
    | some algorithm, some n =>
      let started ← IO.monoNanosNow
      let result ← computeSplit algorithm n cfg
      let stopped ← IO.monoNanosNow
      (← IO.getStdout).putStrLn (Json.mkObj [
        ("algorithm", toJson mode), ("n", toJson input),
        ("divisor", match result with | none => Json.null | some d => toJson (toString d)),
        ("elapsedNs", toJson (stopped - started))]).compress
      return 0
    | _, _ =>
      (← IO.getStderr).putStrLn usage
      return 1
  | _ =>
    (← IO.getStderr).putStrLn usage
    return 1
