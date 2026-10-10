import PrimeFactorLean.Algorithms

open PrimeFactorLean

/-! The CLI deliberately imports only the runtime layer (`PrimeFactorLean.Algorithms`,
Lean core only), so it starts without initializing mathlib or the Lean frontend.
JSON is therefore written by hand. -/

private def jsonString (s : String) : String := "\"" ++ s ++ "\""

private def jsonObject (fields : List (String × String)) : String :=
  "{" ++ ",".intercalate (fields.map fun (k, v) => jsonString k ++ ":" ++ v) ++ "}"

-- An IO boundary prevents pure work from being moved outside the measured interval.
@[noinline] private def computeFactor (algorithm : Algorithm) (n : Nat) (cfg : Config) :
    IO (Option (List Nat)) := IO.lazyPure fun _ => factor algorithm n cfg

@[noinline] private def computeSplit (algorithm : Algorithm) (n : Nat) (cfg : Config) :
    IO (Option Nat) := IO.lazyPure fun _ => rawSearch algorithm cfg n

private def usage : String :=
  "Usage: factor [--threads T] [--ecm-b1 B1 --ecm-curves C] ALGORITHM INTEGER\n" ++
  "       factor [options] --split ALGORITHM NATURAL\n" ++
  "Algorithms: " ++ " ".intercalate (Algorithm.all.map Algorithm.name)

/-- Parse leading options: `--threads T`, and a fixed ECM schedule
`--ecm-b1 B1 --ecm-curves C` for the `ecm` algorithm. -/
private def parseOptions : List String → Config → List String × Config
  | "--threads" :: t :: rest, cfg =>
    match t.toNat? with
    | some k => parseOptions rest { cfg with threads := max 1 k }
    | none => (["--invalid"], cfg)
  | "--ecm-b1" :: t :: rest, cfg =>
    match t.toNat? with
    | some k => parseOptions rest { cfg with ecmB1 := k }
    | none => (["--invalid"], cfg)
  | "--ecm-curves" :: t :: rest, cfg =>
    match t.toNat? with
    | some k => parseOptions rest { cfg with ecmCurves := k }
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
      let data := jsonObject [
        ("algorithm", jsonString mode),
        ("elapsedNs", toString (stopped - started)),
        ("factors", match factors with
          | none => "null"
          | some ps => "[" ++ ",".intercalate ((ps.mergeSort (· ≤ ·)).map fun p => jsonString (toString p)) ++ "]"),
        ("n", jsonString (toString z)),
        ("sign", jsonString (toString z.sign))]
      (← IO.getStdout).putStrLn data
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
      (← IO.getStdout).putStrLn (jsonObject [
        ("algorithm", jsonString mode),
        ("divisor", match result with | none => "null" | some d => jsonString (toString d)),
        ("elapsedNs", toString (stopped - started)),
        ("n", jsonString input)])
      return 0
    | _, _ =>
      (← IO.getStderr).putStrLn usage
      return 1
  | _ =>
    (← IO.getStderr).putStrLn usage
    return 1
