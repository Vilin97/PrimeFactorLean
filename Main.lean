import PrimeFactorLean.Algorithms
import PrimeFactorLean.Pool

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

/-- Grow the task pool (`PrimeFactorLean.warmPool`) for inputs whose searches
run long enough in parallel (from 45 digits; the millisecond it takes costs more
than it saves below). -/
private def prepare (cfg : Config) (n : Nat) : IO Unit := do
  if cfg.threads > 1 && n ≥ 10 ^ 44 then warmPool cfg.threads

/-- The runtime's worker pool admits up to `LEAN_NUM_THREADS` workers (read at
startup; by default every hardware thread, SMT siblings included), and nested
parallel phases (product trees, polynomial selection, sieving rounds split for
load balance) queue more tasks than `--threads`. So for inputs large enough to
run such phases the CLI runs itself once more with `LEAN_NUM_THREADS` set to
the thread budget, and no more workers than that run at once. Returns the exit
code of that run, or `none` when the pool is already capped or not needed. -/
private def capWorkers (cfg : Config) (n : Nat) (argv : List String) : IO (Option UInt32) := do
  if n < 10 ^ 44 then return none
  if (← IO.getEnv "LEAN_NUM_THREADS") == some (toString cfg.threads) then return none
  let exe ← IO.appPath
  let child ← IO.Process.spawn
    { cmd := exe.toString, args := argv.toArray,
      env := #[("LEAN_NUM_THREADS", some (toString cfg.threads))] }
  return some (← child.wait)

private def run (argv : List String) : IO UInt32 := do
  let (args, cfg) := parseOptions argv {}
  match args with
  | [mode, input] =>
    match Algorithm.parse mode, input.toInt? with
    | some algorithm, some z =>
      if let some code ← capWorkers cfg z.natAbs argv then return code
      prepare cfg z.natAbs
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
      if let some code ← capWorkers cfg n argv then return code
      prepare cfg n
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

/-- Runs the CLI and exits explicitly. Parallel searches return as soon as one
task succeeds (the square roots of other GNFS dependencies, other ECM curves),
and such leftover tasks may still spawn and await subtasks. Returning from
`main` shuts the task manager down: it then starts no more workers, yet waits
for every running task, so a leftover task waiting on a subtask would hang the
process forever after the answer has been printed. -/
def main (args : List String) : IO UInt32 := do
  let code ← run args
  (← IO.getStdout).flush
  (← IO.getStderr).flush
  IO.Process.exit code.toUInt8
