import Lake
open Lake DSL

/-- `-march=native` for the generated C (as for the native baselines), except on
continuous integration (`CI` set): its build cache moves between runners with
different instruction sets. -/
def nativeArgs : Array String :=
  run_io do return if (← IO.getEnv "CI").isSome then #[] else #["-march=native"]

package primeFactorLean where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]
  moreLeancArgs := nativeArgs

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"

@[default_target]
lean_lib PrimeFactorLean

lean_lib Tests

lean_exe factor where
  root := `Main

lean_exe factorBench where
  root := `Bench

@[test_driver]
lean_exe factorTests where
  root := `Tests.Main

lean_exe dev where
  root := `Dev.Main

lean_lib Dev
