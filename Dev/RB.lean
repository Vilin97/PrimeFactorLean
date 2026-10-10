import PrimeFactorLean.SIQS
open PrimeFactorLean
def rbMain : IO Unit := do
  let us : Array Nat := #[8000009 * 9000011, 12000017 * 30000001, 16777259 * 20000003]
  for u in us do
    let t0 ← IO.monoNanosNow
    let mut g1 : UInt64 := 0
    for _ in [0:100] do
      g1 ← IO.lazyPure fun _ => SIQS.rho50 u.toUInt64 1 200000
    let t1 ← IO.monoNanosNow
    let mut g2 : Nat := 0
    for _ in [0:100] do
      g2 ← IO.lazyPure fun _ => SIQS.cofactorFactor u
    let t2 ← IO.monoNanosNow
    IO.println s!"u={u}: rho50 {(t1-t0)/100000} us -> {g1}; cofactorFactor {(t2-t1)/100000} us -> {g2}"
