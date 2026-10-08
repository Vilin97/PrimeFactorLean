import PrimeFactorLean.QS
import PrimeFactorLean.ECMMontgomery
import PrimeFactorLean.Pocklington
import PrimeFactorLean.GNFS
import Dev.NFSDebug
import Dev.QSDebug
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
  | ["nfsdebug", ns, ts, d, fbB, a, lp, fudge, lines, rounds] =>
    let n := ns.toNat!
    let params : NFS.Params := NFS.Params.mk d.toNat! fbB.toNat! fbB.toNat! a.toNat! lp.toNat! lines.toNat! 48 80 fudge.toNat! 40 40 2000 0 256 4
    nfsDebug n ts.toNat! params rounds.toNat!
  | ["nfslattice", ns, ts, d, fbB, a, lp, fudge, li, lj, qpt, rounds] =>
    let n := ns.toNat!
    let params : NFS.Params := { (NFS.Params.mk d.toNat! fbB.toNat! fbB.toNat! a.toNat! lp.toNat! 25 48 80 fudge.toNat! 40 40 2000 li.toNat! lj.toNat! qpt.toNat!) with }
    nfsDebug n ts.toNat! params rounds.toNat!
  | ["nfsdebug", ns, ts] =>
    let n := ns.toNat!
    nfsDebug n ts.toNat! (NFS.chooseParams (QS.decimalDigits n))
  | ["qsdebug", ns, fbs, m, lp, numA] =>
    let n := ns.toNat!
    let params : QS.Params := QS.Params.mk fbs.toNat! m.toNat! lp.toNat! 40 6 0
    qsDebug n params numA.toNat!
  | ["qsdebug", ns, numA] =>
    let n := ns.toNat!
    qsDebug n (QS.chooseParams (QS.decimalDigits n)) numA.toNat!
  | ["siqsp", ns, ts, fbs, m, lp, dlp] =>
    let n := ns.toNat!
    let params : QS.Params := { (QS.Params.mk fbs.toNat! m.toNat! lp.toNat! 40 6 dlp.toNat!) with }
    timed s!"siqs n={n} fb={fbs} M={m} lp={lp} dlp={dlp}" fun _ =>
      (QS.split n { threads := ts.toNat!, params := some params }).map (·.val)
  | ["gnfs", ns, ts] =>
    let n := ns.toNat!
    timed s!"gnfs n={n} digits={QS.decimalDigits n}" fun _ =>
      (GNFS.split n { threads := ts.toNat! }).map (·.val)
  | [v, ns, ts] =>
    let variant := match v with | "qs" => QS.Variant.qs | "mpqs" => .mpqs | _ => .siqs
    let n := ns.toNat!
    timed s!"{v} n={n} digits={QS.decimalDigits n}" fun _ =>
      (QS.split n { variant := variant, threads := ts.toNat! }).map (·.val)
  | _ => IO.println "usage: dev VARIANT N THREADS | dev ecm B1 CURVES N THREADS"
