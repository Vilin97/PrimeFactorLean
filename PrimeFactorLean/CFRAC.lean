import Std.Data.HashMap
import Std.Data.HashSet
import PrimeFactorLean.Squares
import PrimeFactorLean.GF2

/-!
# The continued fraction method (CFRAC)

Morrison and Brillhart (1975) expand `√N`, `N = k n`, as a continued fraction.
With `s = ⌊√N⌋`, `P₀ = 0`, `Q₀ = 1` (and `Q_{-1} = N`):

  `a_i = ⌊(s + P_i) / Q_i⌋`,  `P_{i+1} = a_i Q_i - P_i`,
  `Q_{i+1} = Q_{i-1} + a_i (P_i - P_{i+1})`,

and the convergent numerators `A_i = a_i A_{i-1} + A_{i-2}` (`A_{-1} = 1`,
`A_{-2} = 0`) satisfy `A_{i-1}² - N B_{i-1}² = (-1)^i Q_i` with `0 < Q_i < 2√N`.
Reducing modulo `n ∣ N` gives the relation

  `A_{i-1}² ≡ (-1)^i Q_i  (mod n)`,

whose right-hand side has only about half the digits of `n`. A prime `p ∤ N`
dividing some `Q_i` has `(N/p) = 1`, so the factor base is `2` and the odd
primes with `(N/p) ∈ {0, 1}`. The multiplier `k` is chosen by the
Knuth–Schroeppel score (the expected contribution of small primes to `log Q_i`,
minus `½ log k`); the next-best multipliers are tried in turn when the
expansion of `√N` has a short period or every dependency yields a trivial
congruence (which does happen for some inputs of about ten digits).

*Smoothness test.* Instead of dividing each `Q_i` by every factor-base prime,
`g = gcd(Q_i, ∏ fb)` is the radical of the smooth part, and dividing out
`g, gcd(g, Q_i/g), …` leaves the cofactor `L` (one big remainder and a few
small gcds per `Q_i`). Only when `L = 1` (a full relation), or when `L` is below
the large-prime bound `lpMult · p_max` and a second `Q_j` with the same large
prime `L` has turned up, is the smooth part trial divided to obtain the
exponent vector; two relations sharing `L` are paired into a full one.

**What is proved.** Each relation is a `Squares.Relation`, created only through
`Relation.mk?`, which checks `x² ≡ ± L · ∏ fb[j]^{e_j} (mod n)`; pairing,
multiplication, exponent bookkeeping and the final congruence of squares are
kernel-proved (`Squares.Relation.toSquares`), and the returned factor is a
`ProperFactor n`, so `split_sound` holds by construction. The expansion, the
smoothness test, the multiplier choice and the GF(2) solver are untrusted
search procedures: an error there can only lose a relation, never produce a
wrong factor.
-/

namespace PrimeFactorLean.CFRAC

open Arith Squares

/-! ## Parameters -/

structure Params where
  /-- Number of factor-base primes, including `2`. -/
  fbSize : Nat
  /-- Large-prime bound as a multiple of the largest factor-base prime. -/
  lpMult : Nat
  /-- Continued-fraction terms examined per multiplier before giving up. -/
  maxSteps : Nat
  /-- Relations collected beyond the factor-base size. -/
  extra : Nat := 32
  deriving Repr, Inhabited

/-- `(digits, factor-base size, large-prime multiplier, step budget)`. The sizes
were tuned on balanced semiprimes; the optimum is flat within a factor of two. -/
def paramTable : List (Nat × Nat × Nat × Nat) :=
  [(10, 20, 10, 100000), (15, 35, 20, 300000), (20, 50, 30, 1000000),
   (25, 110, 40, 3000000), (30, 220, 50, 6000000), (35, 420, 60, 12000000),
   (40, 800, 80, 25000000), (45, 1300, 100, 50000000), (50, 2000, 120, 100000000),
   (55, 3000, 150, 200000000)]

def chooseParams (digits : Nat) : Params :=
  let entry := (paramTable.find? fun e => digits ≤ e.1).getD
    (paramTable.getLast?.getD (55, 3000, 150, 200000000))
  { fbSize := entry.2.1, lpMult := entry.2.2.1, maxSteps := entry.2.2.2 }

def decimalDigits (n : Nat) : Nat := (toString n).length

/-! ## Knuth–Schroeppel multipliers -/

def multiplierCandidates : List Nat :=
  [1, 3, 5, 7, 11, 13, 15, 17, 19, 21, 23, 29, 31, 33, 35, 37, 39, 41, 43, 47, 51, 53,
   55, 57, 59, 61, 65, 67, 69, 71, 73]

/-- The Knuth–Schroeppel score of `k`: the expected value of `log` of the part
of `Q_i` made of primes below `1000`, minus `½ log k` for the larger `Q_i`. -/
def score (n k : Nat) (primes : Array Nat) : Float := Id.run do
  let kn := k * n
  let mut s : Float := -0.5 * Float.log k.toFloat
  let r := kn % 8
  if r == 1 then s := s + 2.0 * Float.log 2.0
  else if r == 5 then s := s + Float.log 2.0
  else if r == 3 || r == 7 then s := s + 0.5 * Float.log 2.0
  for p in primes do
    if p == 2 then continue
    if p > 1000 then break
    let lp := Float.log p.toFloat
    if k % p == 0 then s := s + lp / p.toFloat
    else if powMod (kn % p) ((p - 1) / 2) p == 1 then
      s := s + 2.0 * lp / (p.toFloat - 1.0)
  return s

/-- The `count` best multipliers, best first. -/
def chooseMultipliers (n : Nat) (primes : Array Nat) (count : Nat) : Array Nat :=
  let scored := (multiplierCandidates.toArray.map fun k => (score n k primes, k)).qsort
    (fun a b => a.1 > b.1)
  (scored.extract 0 count).map (·.2)

/-! ## Factor base and relations -/

/-- The factor base of `N = k n`: `2` and the odd primes `p` with `(N/p) ≠ -1`,
up to `size` primes. A prime factor of `n` met on the way is returned instead. -/
def buildFactorBase (n N size : Nat) (primes : Array Nat) : Array Nat ⊕ Nat := Id.run do
  let mut fb : Array Nat := #[2]
  for p in primes do
    if fb.size ≥ size then break
    if p == 2 then continue
    if n % p == 0 then
      if p < n then return .inr p else continue
    if N % p == 0 || powMod (N % p) ((p - 1) / 2) p == 1 then fb := fb.push p
  return .inl fb

/-- The cofactor of `Q > 0` left after removing every factor-base prime, where
`fbProd = ∏ fb`: `g` runs through the radicals of what remains of the smooth
part, so a few gcds replace trial division by the whole factor base. -/
def cofactor (fbProd Q : Nat) : Nat := Id.run do
  let mut L := Q
  let mut g := Nat.gcd (fbProd % Q) Q
  while g > 1 && L > 0 do
    L := L / g
    g := Nat.gcd g L
  return L

/-- The exponent vector of `v` over `fb` by trial division, if `v` is smooth. -/
def exponents (fb : Array Nat) (v : Nat) : Option (List (Nat × Nat)) := Id.run do
  let mut v := v
  let mut exps : List (Nat × Nat) := []
  for j in [0:fb.size] do
    if v ≤ 1 then break
    let p := fb[j]!
    if p > 1 && v % p == 0 then
      let mut e := 0
      while v % p == 0 && v > 0 do
        v := v / p
        e := e + 1
      exps := (j, e) :: exps
  return if v == 1 then some exps else none

/-- The checked relation `x² ≡ ±L · ∏ fb[j]^{e_j} (mod n)` for
`Q = L · ∏ fb[j]^{e_j}`. -/
def relationOf (n : Nat) (fb : Array Nat) (x Q L : Nat) (neg : Bool) :
    Option (Relation n fb) := do
  let exps ← exponents fb (Q / L)
  Relation.mk? n fb x 1 L neg exps

/-- Expand `√N` for at most `maxSteps` terms, collecting relations until `needed`
full ones (after pairing large primes) are available or the period of the
expansion ends (`Q_i = 1`). An unmatched large-prime candidate is stored as
`(x, Q, sign)`; its exponent vector is computed only once a second `Q` with the
same large prime turns up. -/
def collect (n : Nat) (fb : Array Nat) (N lpBound needed maxSteps : Nat) :
    Array (Relation n fb) := Id.run do
  let s := isqrt N
  let fbProd := fb.foldl (· * ·) 1
  let mut fulls : Array (Relation n fb) := #[]
  let mut singles : Std.HashMap Nat (Nat × Nat × Bool) := {}
  let mut seen : Std.HashSet Nat := {}
  -- Index `i`: `P = P_i`, `Qprev = Q_{i-1}`, `Q = Q_i`, `A1 = A_{i-1}`, `A2 = A_{i-2}`.
  let mut P := s
  let mut Qprev := 1
  let mut Q := N - s * s
  let mut A1 := s % n
  let mut A2 := 1 % n
  let mut odd := true
  for _ in [0:maxSteps] do
    if fulls.size ≥ needed || Q == 0 then break
    -- `A_{i-1}² ≡ (-1)^i Q_i (mod n)`.
    let L := cofactor fbProd Q
    if L < lpBound && !seen.contains A1 then
      seen := seen.insert A1
      if L == 1 then
        if let some r := relationOf n fb A1 Q 1 odd then fulls := fulls.push r
      else
        match singles.get? L with
        | some (x0, Q0, neg0) =>
          if let some r0 := relationOf n fb x0 Q0 L neg0 then
            if let some r := relationOf n fb A1 Q L odd then
              if h : r0.large = r.large then fulls := fulls.push (r0.pair r h)
        | none => singles := singles.insert L (A1, Q, odd)
    if Q == 1 then break
    let a := (s + P) / Q
    let P' := a * Q - P
    let Q' := if P' ≤ P then Qprev + a * (P - P') else Qprev - a * (P' - P)
    let A := (a * A1 + A2) % n
    P := P'
    Qprev := Q
    Q := Q'
    A2 := A1
    A1 := A
    odd := !odd
  return fulls

/-- Linear algebra and square roots: try each dependency until one splits `n`. -/
def extract (n : Nat) (fb : Array Nat) (rels : Array (Relation n fb)) :
    Option (ProperFactor n) := Id.run do
  let rows := rels.map parityColumns
  let deps := GF2.dependencies (fb.size + 1) rows 64
  for dep in deps do
    match dep.toList.map (fun i => rels[i]!) with
    | [] => continue
    | r :: rest =>
      match (r.prod rest).toSquares with
      | none => continue
      | some sc =>
        match sc.factor with
        | some d => return some d
        | none => continue
  return none

/-! ## Driver -/

/-- CFRAC on an odd `n` that is not a perfect power, trying the `tries` best
multipliers in turn. -/
def splitWith (n : Nat) (params : Params) (tries : Nat := 5) : Option (ProperFactor n) :=
  Id.run do
  let primes := primesUpTo (max 1000 (params.fbSize * 30))
  for k in chooseMultipliers n primes tries do
    let N := k * n
    let s := isqrt N
    if s * s == N then
      -- `n = k m²`: the root shares the factor `k m` with `n`.
      if let some d := checkFactor n (Nat.gcd s n) then return some d
      continue
    match buildFactorBase n N params.fbSize primes with
    | .inr p => return checkFactor n p
    | .inl fb =>
      let lpBound := fb[fb.size - 1]! * params.lpMult
      let rels := collect n fb N lpBound (fb.size + 1 + params.extra) params.maxSteps
      if let some d := extract n fb rels then return some d
  return none

/-- The public splitter: tiny inputs and probable primes are declined, even
numbers and perfect powers are handled first, and the parameters are chosen by
size. -/
def split (n : Nat) : Option (ProperFactor n) :=
  if n < 1000 then none
  else if n % 2 = 0 then checkFactor n 2
  else match perfectPower n with
    | some (r, _) => checkFactor n r
    | none =>
      if isProbablePrime n then none else splitWith n (chooseParams (decimalDigits n))

/-- Every factor returned by CFRAC is a proper divisor. -/
theorem split_sound {n : Nat} {d : ProperFactor n} (_h : split n = some d) :
    1 < d.val ∧ d.val < n ∧ d.val ∣ n := d.property

end PrimeFactorLean.CFRAC
