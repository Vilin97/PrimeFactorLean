import PrimeFactorLean.Core
import PrimeFactorLean.Trial
import PrimeFactorLean.Algorithms
import PrimeFactorLean.NumberFieldSieve
import PrimeFactorLean.CubicNumberFieldSieve

/-! Kernel axiom audit and deterministic regression tests for the verified core. -/

#print axioms PrimeFactorLean.factorCoreWith_correct
#print axioms PrimeFactorLean.factorCore_correct
#print axioms PrimeFactorLean.factorNat_correct
#print axioms PrimeFactorLean.factorInt_correct
#print axioms PrimeFactorLean.trialSearchAux_none_iff
#print axioms PrimeFactorLean.trialSearch_none_prime
#print axioms PrimeFactorLean.trialCore_correct
#print axioms PrimeFactorLean.trialFactorReference_correct
#print axioms PrimeFactorLean.trialWheelSearch_none_prime
#print axioms PrimeFactorLean.trialWheelCore_correct
#print axioms PrimeFactorLean.trialWheelFactor_correct
#print axioms PrimeFactorLean.factor_correct
#print axioms PrimeFactorLean.factor_total_correct
#print axioms PrimeFactorLean.factorSigned_correct
#print axioms PrimeFactorLean.factorSigned_total_correct
#print axioms PrimeFactorLean.Search.modPow_correct
#print axioms PrimeFactorLean.Search.brentBlock_product
#print axioms PrimeFactorLean.ECM.add_preserves_curve
#print axioms PrimeFactorLean.ECM.split_sound
#print axioms PrimeFactorLean.QuadraticSieve.factorOverBase_factorization
#print axioms PrimeFactorLean.PrimeCertificate.check_sound
#print axioms PrimeFactorLean.NumberFieldSieve.square_roots_congruence
#print axioms PrimeFactorLean.NumberFieldSieve.factorization_correct
#print axioms PrimeFactorLean.QuadraticSieve.splitMPQS_sound
#print axioms PrimeFactorLean.QuadraticSieve.mpqs_relation_congruence
#print axioms PrimeFactorLean.QuadraticSieve.quotientValue_step
#print axioms PrimeFactorLean.CubicNumberFieldSieve.mul_assoc
#print axioms PrimeFactorLean.CubicNumberFieldSieve.norm_mul
#print axioms PrimeFactorLean.CubicNumberFieldSieve.evaluate_mul_mod
#print axioms PrimeFactorLean.CubicNumberFieldSieve.split_correct

/- Fail CI on any additional axiom, including sorryAx, in the public specifications. -/
run_cmd do
  let audited : List Lean.Name := [
    ``PrimeFactorLean.factorCoreWith_correct,
    ``PrimeFactorLean.factorInt_correct,
    ``PrimeFactorLean.trialCore_correct,
    ``PrimeFactorLean.trialWheelCore_correct,
    ``PrimeFactorLean.factor_correct,
    ``PrimeFactorLean.factor_total_correct,
    ``PrimeFactorLean.factorSigned_correct,
    ``PrimeFactorLean.factorSigned_total_correct,
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
    ``PrimeFactorLean.QuadraticSieve.factorOverBase_factorization,
    ``PrimeFactorLean.QuadraticSieve.even_powerProduct_is_square,
    ``PrimeFactorLean.QuadraticSieve.split_sound,
    ``PrimeFactorLean.LucasStep.check_sound,
    ``PrimeFactorLean.PrimeCertificate.check_sound,
    ``PrimeFactorLean.generatePrimeCertificate_sound,
    ``PrimeFactorLean.NumberFieldSieve.square_roots_congruence,
    ``PrimeFactorLean.NumberFieldSieve.split_correct,
    ``PrimeFactorLean.NumberFieldSieve.factorization_correct,
    ``PrimeFactorLean.QuadraticSieve.splitMPQS_sound,
    ``PrimeFactorLean.QuadraticSieve.mpqs_relation_congruence,
    ``PrimeFactorLean.QuadraticSieve.quotientValue_step,
    ``PrimeFactorLean.CubicNumberFieldSieve.mul_assoc,
    ``PrimeFactorLean.CubicNumberFieldSieve.norm_mul,
    ``PrimeFactorLean.CubicNumberFieldSieve.evaluate_mul_mod,
    ``PrimeFactorLean.CubicNumberFieldSieve.split_correct]
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
