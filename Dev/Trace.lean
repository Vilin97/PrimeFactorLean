import PrimeFactorLean.Algorithms

/-! The automatic portfolio (`autoSplitter` under `primeOracle`) stage by stage
with timings: which stage splits each composite, and how long each prime's
certificate takes. A development aid; it mirrors `Algorithms.autoSplitter`. -/

namespace PrimeFactorLean.Trace

/-- Run one stage, print its time and outcome. -/
def stage (depth : Nat) (label : String) (f : Unit → Option Nat) : IO (Option Nat) := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  let ms := (t1 - t0) / 1000000
  if r.isSome || ms ≥ 5 then
    IO.println s!"{"".pushn ' ' (2 * depth)}{label}: {ms} ms -> {r}"
  return r

/-- `autoSplitter` stage by stage. -/
def split (cfg : Config) (depth n : Nat) : IO (Option Nat) := do
  if n < 4 then return none
  let st (label : String) (f : Unit → Option Nat) := stage depth label f
  if let some d ← st "small" fun _ => (smallSplitter 4096 n).map (·.val) then return some d
  if let some d ← st "power" fun _ => (powerSplitter n).map (·.val) then return some d
  if let some d ← st "algebraic" fun _ => (algebraicSplitter n).map (·.val) then return some d
  if n < 2 ^ 62 then
    if let some d ← st "squfof" fun _ => (SQUFOF.split n).map (·.val) then return some d
  if let some d ← st "rho" fun _ => (RhoF.split n 8000 1).map (·.val) then return some d
  if n ≥ 10 ^ 44 then
    if let some d ← st "pm1" fun _ => (PM1F.split n 20000).map (·.val) then return some d
  let snfs := snfsCandidate n
  let pretest := match snfs with
    | some (_, _, _, D) => min (QS.decimalDigits n) ((38 * D + 4430) / 100)
    | none => QS.decimalDigits n
  let levels := ecmSchedule pretest
  for ((b1, curves), i) in levels.zip (List.range levels.length) do
    if let some d ← st s!"ecm B1={b1} curves={curves}" fun _ =>
        (ECMF.split n { b1 := b1, curves := curves, threads := cfg.threads,
                         sigma := 11 + 100003 * i }).map (·.val) then
      return some d
  match snfs with
  | some (b, k, plus, D) =>
    if let some d ← st s!"snfs {b}^{k}{if plus then "+" else "-"}1 (D={D})" fun _ =>
        (GNFS.splitSNFS n b k plus { threads := cfg.threads }).map (·.val) then
      return some d
    st "siqs" fun _ => (SIQS.split n { threads := cfg.threads }).map (·.val)
  | none => st "siqs" fun _ => (SIQS.split n { threads := cfg.threads }).map (·.val)

/-- `factorCoreWith (primeOracle cfg) (autoSplitter cfg)` with the stages traced. -/
def factor (cfg : Config) (depth : Nat) : Nat → Nat → IO (List Nat)
  | 0, n => return [n]
  | fuel + 1, n => do
    if n ≤ 1 then return []
    let pad := "".pushn ' ' (2 * depth)
    let t0 ← IO.monoNanosNow
    let prime ← IO.lazyPure fun _ => primeOracle cfg n
    let t1 ← IO.monoNanosNow
    let ms := (t1 - t0) / 1000000
    if prime then
      if ms ≥ 5 then IO.println s!"{pad}prime {QS.decimalDigits n}d certified: {ms} ms"
      return [n]
    IO.println s!"{pad}composite {QS.decimalDigits n}d (oracle {ms} ms)"
    match ← split cfg depth n with
    | some d =>
      let a ← factor cfg (depth + 1) fuel d
      let b ← factor cfg (depth + 1) fuel (n / d)
      return a ++ b
    | none =>
      let p := minFac n
      if p == n then return [n]
      return p :: (← factor cfg (depth + 1) fuel (n / p))

def main (n threads : Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let fs ← factor { threads } 0 64 n
  let t1 ← IO.monoNanosNow
  IO.println s!"factors {fs.mergeSort} in {(t1 - t0) / 1000000} ms"

end PrimeFactorLean.Trace

