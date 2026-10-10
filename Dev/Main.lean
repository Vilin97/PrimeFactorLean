import PrimeFactorLean.QS
import PrimeFactorLean.SIQS
import PrimeFactorLean.ECMMontgomery
import PrimeFactorLean.Pocklington
import PrimeFactorLean.GNFS
import Dev.NFSDebug
import Dev.QSDebug
import Dev.Micro
import Dev.RB
import Dev.LasDebug
import Dev.Bench8
import Dev.Stages
import Dev.MontTest
open PrimeFactorLean

def timed (label : String) (f : Unit → Option Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  IO.println s!"{label} -> {r} in {(t1 - t0) / 1000000} ms"

def main (args : List String) : IO Unit := do
  match args with
  | ["micro"] => microMain
  | ["fasttune", ns, fbs, m, lp, dlp, spv, slack, rounds, ts] =>
    let params : SIQS.Params := { fbSize := fbs.toNat!, M := m.toNat!, lpMult := lp.toNat!,
                                  dlpDiv := dlp.toNat!, spv := spv.toNat!, slack := slack.toNat! }
    fastTune ns.toNat! params rounds.toNat! ts.toNat!
  | ["tune2", ns, fbs, m, lp, dlp, spv, slack, fslack, sb, rounds, ts] =>
    let params : SIQS.Params := { fbSize := fbs.toNat!, M := m.toNat!, lpMult := lp.toNat!,
                                  dlpDiv := dlp.toNat!, spv := spv.toNat!, slack := slack.toNat!,
                                  filterSlack := fslack.toNat!, smallBound := sb.toNat! }
    fastTune ns.toNat! params rounds.toNat! ts.toNat!
  | ["siqs3", ns, ts, fbs, m, lp, dlp, spv, slack, fslack, sb, pre] =>
    let n := ns.toNat!
    let params : SIQS.Params := { fbSize := fbs.toNat!, M := m.toNat!, lpMult := lp.toNat!,
                                  dlpDiv := dlp.toNat!, spv := spv.toNat!, slack := slack.toNat!,
                                  filterSlack := fslack.toNat!, smallBound := sb.toNat!,
                                  preSlack := pre.toNat! }
    timed s!"fast siqs n={n} digits={QS.decimalDigits n}" fun _ =>
      (SIQS.split n { threads := ts.toNat!, params := some params }).map (·.val)
  | ["siqs2", ns, ts, fbs, m, lp, dlp, spv, slack, fslack, sb] =>
    let n := ns.toNat!
    let params : SIQS.Params := { fbSize := fbs.toNat!, M := m.toNat!, lpMult := lp.toNat!,
                                  dlpDiv := dlp.toNat!, spv := spv.toNat!, slack := slack.toNat!,
                                  filterSlack := fslack.toNat!, smallBound := sb.toNat! }
    timed s!"fast siqs n={n} digits={QS.decimalDigits n}" fun _ =>
      (SIQS.split n { threads := ts.toNat!, params := some params }).map (·.val)
  | ["fastcheck", ns, fbs, m, lp, spv, seed] =>
    let params : SIQS.Params := { fbSize := fbs.toNat!, M := m.toNat!, lpMult := lp.toNat!,
                                  spv := spv.toNat! }
    fastCheck ns.toNat! params seed.toNat!
  | ["fastcheck", ns, fbs, m, lp, spv, seed, slack, fslack] =>
    let params : SIQS.Params := { fbSize := fbs.toNat!, M := m.toNat!, lpMult := lp.toNat!,
                                  spv := spv.toNat!, slack := slack.toNat!, filterSlack := fslack.toNat! }
    fastCheck ns.toNat! params seed.toNat!
  | ["fastprofile", ns, fbs, m, lp, dlp, spv, slack, seed] =>
    let params : SIQS.Params := { fbSize := fbs.toNat!, M := m.toNat!, lpMult := lp.toNat!,
                                  dlpDiv := dlp.toNat!, spv := spv.toNat!, slack := slack.toNat! }
    fastProfile ns.toNat! params seed.toNat!
  | ["laonly", ns, ts, reps, fbs, m] =>
    let params : SIQS.Params := { fbSize := fbs.toNat!, M := m.toNat!, lpMult := 75, spv := 30,
                                  slack := 16, filterSlack := 12, smallBound := 16384 }
    laOnly ns.toNat! params ts.toNat! reps.toNat!
  | ["graycheck", ns, fbs, m, lp, spv, slack, fslack, seed, steps] =>
    let params : SIQS.Params := { fbSize := fbs.toNat!, M := m.toNat!, lpMult := lp.toNat!,
                                  spv := spv.toNat!, slack := slack.toNat!, filterSlack := fslack.toNat! }
    grayCheck ns.toNat! params seed.toNat! steps.toNat!
  | ["spread", ns, ts, rounds, fbs, m, lp, dlp, spv, slack, fslack, sb] =>
    let params : SIQS.Params := { fbSize := fbs.toNat!, M := m.toNat!, lpMult := lp.toNat!,
                                  dlpDiv := dlp.toNat!, spv := spv.toNat!, slack := slack.toNat!,
                                  filterSlack := fslack.toNat!, smallBound := sb.toNat! }
    taskSpread ns.toNat! params ts.toNat! rounds.toNat!
  | ["ctimed", ns, ts, fbs, m, lp, dlp, spv, slack, fslack, sb] =>
    let params : SIQS.Params := { fbSize := fbs.toNat!, M := m.toNat!, lpMult := lp.toNat!,
                                  dlpDiv := dlp.toNat!, spv := spv.toNat!, slack := slack.toNat!,
                                  filterSlack := fslack.toNat!, smallBound := sb.toNat! }
    collectTimed ns.toNat! params ts.toNat!
  | ["phases2", ns, ts, fbs, m, lp, dlp, spv, slack, fslack, sb] =>
    let params : SIQS.Params := { fbSize := fbs.toNat!, M := m.toNat!, lpMult := lp.toNat!,
                                  dlpDiv := dlp.toNat!, spv := spv.toNat!, slack := slack.toNat!,
                                  filterSlack := fslack.toNat!, smallBound := sb.toNat! }
    fastPhases ns.toNat! params ts.toNat!
  | ["fastphases", ns, ts, fbs, m, lp, dlp, spv, slack] =>
    let params : SIQS.Params := { fbSize := fbs.toNat!, M := m.toNat!, lpMult := lp.toNat!,
                                  dlpDiv := dlp.toNat!, spv := spv.toNat!, slack := slack.toNat! }
    fastPhases ns.toNat! params ts.toNat!
  | ["lanczos", ns, ts, fbs, m, lp] =>
    let params : SIQS.Params := { fbSize := fbs.toNat!, M := m.toNat!, lpMult := lp.toNat!, spv := 20, slack := 3 }
    lanczosDebug ns.toNat! params ts.toNat!
  | ["lanczosunit"] => lanczosUnit
  | ["mulacc"] => mulAccBench
  | ["mula"] => mulABench
  | ["cofactor"] => cofactorBench (70000000 + args.length - 1)
  | ["rb"] => rbMain
  | ["fkunit"] => fkUnit
  | ["las", ns, cnt] => lasDebug ns.toNat! cnt.toNat!
  | ["laspipe", ns, ts, rounds] => lasPipeline ns.toNat! ts.toNat! rounds.toNat!
  | ["fastlong", ns, ts, fbs, m, lp, dlp, spv, slack] =>
    let params : SIQS.Params := { fbSize := fbs.toNat!, M := m.toNat!, lpMult := lp.toNat!,
                                  dlpDiv := dlp.toNat!, spv := spv.toNat!, slack := slack.toNat! }
    fastLong ns.toNat! params ts.toNat!
  | ["fastsiqs", ns, ts] =>
    let n := ns.toNat!
    timed s!"fast siqs n={n} digits={QS.decimalDigits n}" fun _ =>
      (SIQS.split n { threads := ts.toNat! }).map (·.val)
  | ["fastsiqsp", ns, ts, fbs, m, lp, dlp, spv, slack] =>
    let n := ns.toNat!
    let params : SIQS.Params := { fbSize := fbs.toNat!, M := m.toNat!, lpMult := lp.toNat!,
                                  dlpDiv := dlp.toNat!, spv := spv.toNat!, slack := slack.toNat! }
    timed s!"fast siqs n={n} digits={QS.decimalDigits n}" fun _ =>
      (SIQS.split n { threads := ts.toNat!, params := some params }).map (·.val)
  | ["micro2"] => micro2Main
  | ["micro3"] => micro3Main
  | ["micro4"] => micro4Main
  | ["micro5"] => micro5Main
  | ["micro6"] => micro6Main
  | ["micro7"] => micro7Main
  | ["bench8"] => Bench8.bench8Main
  | ["bench9"] => Bench9.bench9Main
  | ["bench10"] => Bench10.bench10Main
  | ["stages", ns, ts] => autoStages ns.toNat! ts.toNat!
  | ["monttest"] => montTestMain
  | ["ecmbench", ns, b1, c, ts] => ecmBench ns.toNat! b1.toNat! c.toNat! ts.toNat!
  | ["ecm", b1, curves, ns, ts] =>
    let n := ns.toNat!
    timed s!"ecm B1={b1} n={n}" fun _ =>
      (ECMM.split n { b1 := b1.toNat!, curves := curves.toNat!, threads := ts.toNat! }).map (·.val)
  | ["nfsdebug", ns, ts, d, fbB, a, lp, fudge, lines, rounds] =>
    let n := ns.toNat!
    let params : NFS.Params := NFS.Params.mk d.toNat! fbB.toNat! fbB.toNat! a.toNat! lp.toNat! lines.toNat! 48 80 fudge.toNat! 40 40 2000 0 256 4 0 0 0 0 0 0
    nfsDebug n ts.toNat! params rounds.toNat!
  | ["nfslattice", ns, ts, d, fbB, a, lp, fudge, li, lj, qpt, rounds] =>
    let n := ns.toNat!
    let params : NFS.Params := { (NFS.Params.mk d.toNat! fbB.toNat! fbB.toNat! a.toNat! lp.toNat! 25 48 80 fudge.toNat! 40 40 2000 li.toNat! lj.toNat! qpt.toNat! 0 0 0 0 0 0) with }
    nfsDebug n ts.toNat! params rounds.toNat!
  | ["nfsdebug", ns, ts] =>
    let n := ns.toNat!
    nfsDebug n ts.toNat! (NFS.chooseParams (QS.decimalDigits n))
  | ["qsdebug", ns, fbs, m, lp, numA] =>
    let n := ns.toNat!
    let params : QS.Params := QS.Params.mk fbs.toNat! m.toNat! lp.toNat! 40 6 0 0
    qsDebug n params numA.toNat!
  | ["qsdebug", ns, numA] =>
    let n := ns.toNat!
    qsDebug n (QS.chooseParams (QS.decimalDigits n)) numA.toNat!
  | ["siqsp", ns, ts, fbs, m, lp, dlp] =>
    let n := ns.toNat!
    let params : QS.Params := { (QS.Params.mk fbs.toNat! m.toNat! lp.toNat! 40 6 dlp.toNat! 0) with }
    timed s!"siqs n={n} fb={fbs} M={m} lp={lp} dlp={dlp}" fun _ =>
      (QS.split n { threads := ts.toNat!, params := some params }).map (·.val)
  | ["qstune", ns, fbs, m, lp, dlp, slack, ss, rounds, ts] =>
    let params : QS.Params := { (QS.Params.mk fbs.toNat! m.toNat! lp.toNat! 40 ss.toNat! dlp.toNat! slack.toNat!) with }
    qsTune ns.toNat! params rounds.toNat! ts.toNat!
  | ["qsphases", ns, fbs, m, lp, dlp, ss, ts] =>
    let params : QS.Params := { (QS.Params.mk fbs.toNat! m.toNat! lp.toNat! 40 ss.toNat! dlp.toNat! 0) with }
    qsPhases ns.toNat! params ts.toNat!
  | ["qslong", ns, fbs, m, lp, dlp, ts] =>
    let params : QS.Params := { (QS.Params.mk fbs.toNat! m.toNat! lp.toNat! 40 6 dlp.toNat! 0) with }
    qsLong ns.toNat! params ts.toNat!
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
