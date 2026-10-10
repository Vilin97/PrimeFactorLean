import Lake
open Lake DSL

package primeFactorLean where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]
  -- Optimized native build of the generated C (as for the native baselines).
  moreLeancArgs := #["-march=native"]

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
