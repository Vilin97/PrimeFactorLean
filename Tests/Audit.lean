import PrimeFactorLean

/-! Kernel axiom audit and deterministic regression tests for the verified core. -/

/- The public correctness theorems, printed for inspection. -/
#print axioms PrimeFactorLean.factor_total_correct
#print axioms PrimeFactorLean.factorSigned_total_correct
#print axioms PrimeFactorLean.Pocklington.pocklington
#print axioms PrimeFactorLean.Pocklington.pocklington_cube
#print axioms PrimeFactorLean.Squares.Relation.toSquares
#print axioms PrimeFactorLean.Squares.SquareCongruence.factor_isSome
#print axioms PrimeFactorLean.GNFS.nfs_square
#print axioms PrimeFactorLean.NFS.eval_mulZ

/- Fail CI on any additional axiom, including sorryAx, in the public specifications. -/
run_cmd do
  let audited : List Lean.Name := [
    ``PrimeFactorLean.factorCoreWith_correct,
    ``PrimeFactorLean.minFac_prime,
    ``PrimeFactorLean.isqrt_spec,
    ``PrimeFactorLean.isqrt_eq_sqrt,
    ``PrimeFactorLean.Pocklington.oracle_sound,
    ``PrimeFactorLean.Squares.modEq_iff_zmod,
    ``PrimeFactorLean.Squares.Relation.valid_zmod,
    ``PrimeFactorLean.factorInt_correct,
    ``PrimeFactorLean.trialCore_correct,
    ``PrimeFactorLean.trialWheelCore_correct,
    ``PrimeFactorLean.factor_correct,
    ``PrimeFactorLean.factor_total_correct,
    ``PrimeFactorLean.factorSigned_correct,
    ``PrimeFactorLean.factorSigned_total_correct,
    ``PrimeFactorLean.rawSearch_sound,
    ``PrimeFactorLean.Arith.powMod_eq,
    ``PrimeFactorLean.Arith.perfectPower_proper,
    ``PrimeFactorLean.Arith.smallPrime_sound,
    ``PrimeFactorLean.Pocklington.prime_pow_dvd_sub_one,
    ``PrimeFactorLean.Pocklington.pocklington,
    ``PrimeFactorLean.Pocklington.pocklington_cube,
    ``PrimeFactorLean.Pocklington.Step.check_sound,
    ``PrimeFactorLean.Pocklington.Certificate.check_sound,
    ``PrimeFactorLean.Pocklington.generate_sound,
    ``PrimeFactorLean.LucasStep.check_sound,
    ``PrimeFactorLean.PrimeCertificate.check_sound,
    ``PrimeFactorLean.Search.modPow_correct,
    ``PrimeFactorLean.Search.brentBlock_product,
    ``PrimeFactorLean.Search.fermat_sound,
    ``PrimeFactorLean.Search.rho_sound,
    ``PrimeFactorLean.Search.brent_sound,
    ``PrimeFactorLean.Search.pMinusOne_sound,
    ``PrimeFactorLean.ECM.inverse_correct,
    ``PrimeFactorLean.ECM.add_preserves_curve,
    ``PrimeFactorLean.ECM.multiply_preserves_curve,
    ``PrimeFactorLean.ECM.stageOne_preserves_curve,
    ``PrimeFactorLean.ECM.split_sound,
    ``PrimeFactorLean.ECMM.xDBL_correct,
    ``PrimeFactorLean.ECMM.xADD_correct,
    ``PrimeFactorLean.ECMM.split_sound,
    ``PrimeFactorLean.Squares.relationHolds_valid,
    ``PrimeFactorLean.Squares.evalExps_mergeRuns,
    ``PrimeFactorLean.Squares.evalExps_half,
    ``PrimeFactorLean.Squares.SquareCongruence.factor_isSome,
    ``PrimeFactorLean.QS.split_sound,
    ``PrimeFactorLean.NFS.eval_mulL,
    ``PrimeFactorLean.NFS.eval_reduce,
    ``PrimeFactorLean.NFS.eval_mulZ,
    ``PrimeFactorLean.NFS.eval_prodTree,
    ``PrimeFactorLean.NFS.evalMod_modEq,
    ``PrimeFactorLean.GNFS.nfs_square,
    ``PrimeFactorLean.GNFS.split_sound,
    ``PrimeFactorLean.SQUFOF.split_sound,
    ``PrimeFactorLean.CFRAC.split_sound,
    ``PrimeFactorLean.PMinusOne.splitPMinusOne_sound,
    ``PrimeFactorLean.PMinusOne.splitPPlusOne_sound]
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in audited do
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unapproved axiom {axiomName} in {declaration}"
  Lean.logInfo m!"Axiom audit passed for {audited.length} public correctness and invariant theorems."

/- Also audit every declaration in the project namespace, including private
declarations and generated helpers. Sharing the visited set avoids repeatedly
traversing the same mathlib dependency closures. -/
run_cmd do
  let env ← Lean.getEnv
  let namespaceRoot : Lean.Name := `PrimeFactorLean
  let declarations : Array Lean.Name := env.constants.fold
    (fun acc name _ =>
      if namespaceRoot.isPrefixOf (Lean.privateToUserName name) then acc.push name else acc) #[]
  let scan : Lean.CollectAxioms.M Unit := declarations.forM Lean.CollectAxioms.collect
  let (_, result) := (scan.run env).run {}
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in result.axioms do
    unless allowed.contains axiomName do
      throwError "Unapproved axiom {axiomName} in the complete PrimeFactorLean declaration closure"
  Lean.logInfo m!"Global axiom audit passed for all {declarations.size} PrimeFactorLean declarations, including private/generated helpers."

open PrimeFactorLean

example : trialFactor 0 = none := by decide
example : trialFactor 1 = some [] := by simp [trialFactor, trialCore]
example : trialWheelFactor 0 = none := by decide
example : trialWheelFactor 1 = some [] := by simp [trialWheelFactor, trialWheelCore]
example : factorInt trialSplitter (-1) = some (-1, []) := by
  simp [factorInt, factorNat, factorCore, factorCoreWith]
example : factorInt trialSplitter 0 = none := by decide

/- Exhaustively compare the independently proved implementations. -/
#eval do
  if trialWheelFactor 360 != some [2, 2, 2, 3, 3, 5] then
    throw (IO.userError "360 edge case failed")
  if factorInt trialSplitter (-360) != some (-1, [2, 2, 2, 3, 3, 5]) then
    throw (IO.userError "signed -360 edge case failed")
  for n in [:10001] do
    let reference := trialFactor n
    let optimized := trialWheelFactor n
    if reference != optimized then
      throw (IO.userError s!"trial/wheel mismatch at {n}: {reference} != {optimized}")
    if n < 501 && trialFactorReference n != reference then
      throw (IO.userError s!"reference/sqrt mismatch at {n}")
    match optimized with
    | none =>
      if n != 0 then throw (IO.userError s!"missing factorization of {n}")
    | some fs =>
      if fs.prod != n || !(fs.all fun p => decide (Nat.Prime p)) then
        throw (IO.userError s!"invalid prime factorization at {n}")
  IO.println "Core audit: trial and 6-wheel agree and factor all inputs 0..10000; signed edge cases pass."

/- Regression guard for a Lean 4.24 compiler bug: `0 - x` is compiled to `x`
(for `Nat` and fixed-width integers alike). Runtime code avoids the pattern
(`scripts/audit_sources.py` rejects it); this records the behavior. -/
@[noinline] def zeroSubProbe (x : Nat) : Nat := 0 - x
@[noinline] def negProbe (x : UInt32) : UInt32 := -x
#eval do
  if negProbe 1 != 4294967295 then throw (IO.userError "UInt32 negation miscompiled")
  if zeroSubProbe 5 != 0 then
    IO.println "note: this Lean compiler rewrites `0 - x` to `x` (known bug); runtime code avoids it"
