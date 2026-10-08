import PrimeFactorLean.QS
import PrimeFactorLean.ECMMontgomery
import PrimeFactorLean.Pocklington
open PrimeFactorLean

def timed (label : String) (f : Unit → Option Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  IO.println s!"{label} -> {r} in {(t1 - t0) / 1000000} ms"

def main (args : List String) : IO Unit := do
  match args with
  | ["ecm", b1, curves, ns, ts] =>
    let n := ns.toNat!
    timed s!"ecm B1={b1} n={n}" fun _ =>
      (ECMM.split n { b1 := b1.toNat!, curves := curves.toNat!, threads := ts.toNat! }).map (·.val)
  | [v, ns, ts] =>
    let variant := match v with | "qs" => QS.Variant.qs | "mpqs" => .mpqs | _ => .siqs
    let n := ns.toNat!
    timed s!"{v} n={n} digits={QS.decimalDigits n}" fun _ =>
      (QS.split n { variant := variant, threads := ts.toNat! }).map (·.val)
  | _ => IO.println "usage: dev VARIANT N THREADS | dev ecm B1 CURVES N THREADS"
