import PrimeFactorLean.Primality
import PrimeFactorLean.Algorithms
import Mathlib.Data.Nat.Factors

/-!
Adversarial executable tests for the Pratt checker and its untrusted producer.
The callback's outputs are never assumed correct by the soundness theorem.
-/

namespace Tests.Primality
open PrimeFactorLean

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError ("Primality test failed: " ++ label))

private def valid101 : PrimeCertificate :=
  ⟨101, [⟨5, 2, [2, 2]⟩, ⟨101, 2, [2, 2, 5, 5]⟩]⟩

set_option maxRecDepth 10000 in
/-- The kernel also checks a concrete successful certificate, without native_decide. -/
theorem certificate101_prime : Nat.Prime 101 :=
  valid101.check_sound (by decide)

/-- Run independently or invoke from the repository's main test runner. -/
def run : IO Unit := do
  require "valid certificate" valid101.check
  let malformed : List (String × PrimeCertificate) := [
    ("zero", ⟨0, []⟩),
    ("one", ⟨1, []⟩),
    ("unverified requested value", ⟨99, valid101.steps⟩),
    ("incorrect product", ⟨101, [⟨5, 2, [2, 2]⟩, ⟨101, 2, [2, 5, 5]⟩]⟩),
    ("invalid witness", ⟨101, [⟨5, 2, [2, 2]⟩, ⟨101, 1, [2, 2, 5, 5]⟩]⟩),
    ("missing factor proof", ⟨101, [⟨101, 2, [2, 2, 5, 5]⟩]⟩),
    ("reversed dependencies", ⟨101, valid101.steps.reverse⟩),
    ("composite row", ⟨9, [⟨9, 2, [2, 2, 2]⟩]⟩)]
  for (label, certificate) in malformed do
    require label (!certificate.check)
  for n in [2, 3, 5, 7, 13, 101, 1009, 65537, 1000000007] do
    match generatePrimeCertificate Nat.primeFactorsList n with
    | none => throw (IO.userError ("Failed to construct prime certificate: " ++ toString n))
    | some certificate =>
        require ("generated certificate for " ++ toString n)
          (certificate.value == n && certificate.check)
  for n in [0, 1, 4, 9, 15, 561, 1105, 1729, 3215031751] do
    require ("composite rejection " ++ toString n)
      (!(generatePrimeCertificate Nat.primeFactorsList n).isSome)
  let hostileCallbacks : List (Nat → List Nat) := [
    (fun _ => []), (fun _ => [0]), (fun _ => [1]),
    (fun n => [n + 1]), (fun n => [n])]
  for badFactor in hostileCallbacks do
    require "hostile factoring callback"
      (!(generatePrimeCertificate badFactor 101).isSome)
  require "exhausted generation fuel"
    (!(generatePrimeCertificate Nat.primeFactorsList 101 0).isSome)
  require "exhausted witness search"
    (!(generatePrimeCertificate Nat.primeFactorsList 101 64 0).isSome)
  require "base prime independent of budgets"
    (generatePrimeCertificate (fun _ => []) 2 0 0).isSome
  for n in [2, 3, 101, 65537, 1000000007] do
    require ("production oracle prime " ++ toString n) (algorithmPrimeOracle {} n).isSome
  for n in [0, 1, 4, 561, 1105, 1729, 3215031751] do
    require ("production oracle composite " ++ toString n) (!(algorithmPrimeOracle {} n).isSome)
  require "production factor prime" (factor .auto 1000000007 == some [1000000007])
  require "production factor Carmichael" (factor .auto 561 == some [3, 11, 17])
  let hostileOracle : PrimeOracle := prattOracle (fun _ => [0])
  let hostileSplitter : Splitter := checkedSplitter (fun _ => some 1)
  require "hostile oracle and splitter preserve exact fallback"
    (factorCoreWith hostileOracle hostileSplitter 21 == [3, 7])
  IO.println "Primality tests passed (valid, malformed, composite, hostile producer, and 1e9 prime)."

end Tests.Primality

namespace Tests

def checkPrimality : IO Bool := do
  try
    Primality.run
    return true
  catch e =>
    IO.eprintln e.toString
    return false

end Tests
