/-!
# Growing the task pool

Lean's task manager starts a new worker thread for a spawned task only when no
worker is idle at that moment, so a burst of tasks spawned while one worker is
idle all queue on that worker and run one after another (measured: after a
single-task batch, a batch of 16 equal tasks took 16 times as long as one). The
executables therefore grow the pool once at startup with `n` tasks that block
until all of them are spawned.
-/

namespace PrimeFactorLean

/-- Grow the task pool to at least `n` workers: the tasks block until all are
spawned, so no worker is idle when the next one is enqueued. -/
def warmPool (n : Nat) : IO Unit := do
  let release ← IO.Promise.new
  let tasks ← (List.range n).mapM fun _ => IO.asTask do
    discard <| IO.wait release.result?
  release.resolve ()
  for t in tasks do discard <| IO.wait t

end PrimeFactorLean
