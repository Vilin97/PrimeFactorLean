import PrimeFactorLean.Core
import PrimeFactorLean.Arith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Lenstra's elliptic curve method with Montgomery curves

This is the modern form of ECM (Montgomery 1987; Brent; Zimmermann–Dodson):

* curves `B y² = x³ + A x² + x` over `ℤ/n` in Suyama's parametrization
  `u = σ² - 5`, `v = 4σ`, `x₀ = u³`, `z₀ = v³`, `(A+2)/4 = (v-u)³(3u+v)/(16u³v)`,
  which guarantees a group order divisible by 12;
* projective x-only arithmetic `(X : Z)`, so no inversions are needed: doubling
  costs 5 multiplications, differential addition 6;
* stage 1 multiplies the starting point by every maximal prime power `≤ B1`
  with the Montgomery ladder;
* stage 2 (standard continuation, baby-step giant-step with `D = 2310`)
  accumulates `X_G Z_j - X_j Z_G` for the pairs `m D ± j` covering every prime
  in `(B1, B2]`, using one batched gcd;
* independent curves run in parallel tasks.

**What is proved.** Every reported factor is `gcd(z, n)` for some computed `z`,
so it divides `n` by `Nat.gcd_dvd_right`; nontriviality is checked
(`gcdFactor`). `split` therefore returns a `ProperFactor n` and `split_sound`
holds for all inputs. In addition, `xDBL_correct` and `xADD_correct` prove
that the projective formulas compute the classical affine x-coordinate
formulas for doubling and differential addition on Montgomery curves, over any
field. The probabilistic success analysis (smooth group orders) is not
formalized.
-/

namespace PrimeFactorLean.ECMM

open Arith

/-- A proper factor obtained from a gcd: divisibility holds by construction. -/
def gcdFactor (n z : Nat) : Option (ProperFactor n) :=
  let g := Nat.gcd z n
  if h : 1 < g ∧ g < n then some ⟨g, h.1, h.2, Nat.gcd_dvd_right z n⟩ else none

/-! ## Projective x-only arithmetic -/

structure Pt where
  x : Nat
  z : Nat
  deriving Inhabited, Repr

/-- Doubling: `X₂ = (X+Z)²(X-Z)²`, `Z₂ = 4XZ((X-Z)² + a24·4XZ)`. -/
@[inline] def dbl (n a24 : Nat) (P : Pt) : Pt :=
  let s := (P.x + P.z) % n
  let d := (P.x + n - P.z % n) % n
  let t1 := s * s % n
  let t2 := d * d % n
  let t3 := (t1 + n - t2) % n
  ⟨t1 * t2 % n, t3 * ((t2 + a24 * t3) % n) % n⟩

/-- Differential addition: `P + Q` from `P`, `Q` and `D = P - Q`. -/
@[inline] def add (n : Nat) (P Q D : Pt) : Pt :=
  let u := (P.x + n - P.z % n) % n * ((Q.x + Q.z) % n) % n
  let w := (P.x + P.z) % n * ((Q.x + n - Q.z % n) % n) % n
  let s := (u + w) % n
  let d := (u + n - w) % n
  ⟨D.z * (s * s % n) % n, D.x * (d * d % n) % n⟩

/-- Montgomery ladder: `[k]P` for `k ≥ 1`. -/
def ladder (n a24 : Nat) (P : Pt) (k : Nat) : Pt := Id.run do
  if k ≤ 1 then return P
  let mut r0 := P
  let mut r1 := dbl n a24 P
  let top := k.log2
  for i' in [0:top] do
    let i := top - 1 - i'
    if k.testBit i then
      r0 := add n r1 r0 P
      r1 := dbl n a24 r1
    else
      r1 := add n r1 r0 P
      r0 := dbl n a24 r0
  return r0

/-! ## Correctness of the formulas over a field

On `B y² = x³ + A x² + x`, the affine x-coordinates satisfy
`x(2P) = (x² - 1)² / (4x(x² + A x + 1))` and, for `P ≠ ±Q`,
`x(P+Q) x(P-Q) = (x_P x_Q - 1)² / (x_P - x_Q)²`. The projective formulas used
by `dbl` and `add` compute exactly these values (with `a24 = (A + 2)/4`). -/

theorem xDBL_correct {K : Type*} [Field K] (A x : K) (h2 : (2 : K) ≠ 0) :
    let a24 := (A + 2) / 4
    let t1 := (x + 1) ^ 2
    let t2 := (x - 1) ^ 2
    let t3 := t1 - t2
    t1 * t2 = (x ^ 2 - 1) ^ 2 ∧ t3 * (t2 + a24 * t3) = 4 * x * (x ^ 2 + A * x + 1) := by
  intro a24 t1 t2 t3
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  constructor
  · simp only [t1, t2]; ring
  · simp only [a24, t1, t2, t3]; field_simp; ring

theorem xADD_correct {K : Type*} [Field K] (xP xQ : K) :
    let u := (xP - 1) * (xQ + 1)
    let w := (xP + 1) * (xQ - 1)
    (u + w) ^ 2 = 4 * (xP * xQ - 1) ^ 2 ∧ (u - w) ^ 2 = 4 * (xP - xQ) ^ 2 := by
  intro u w
  constructor <;> simp only [u, w] <;> ring

/-! ## Curve selection, stage 1 and stage 2 -/

/-- Suyama's curve for parameter `σ`: returns `(a24, P₀)` or a factor. -/
def suyama (n σ : Nat) : Except (Option (ProperFactor n)) (Nat × Pt) :=
  let u := (σ * σ + n - 5 % n) % n
  let v := 4 * σ % n
  let x0 := u * u % n * u % n
  let z0 := v * v % n * v % n
  let vmu := (v + n - u) % n
  let num := vmu * vmu % n * vmu % n * ((3 * u + v) % n) % n
  let den := 16 * x0 % n * v % n
  match invMod den n with
  | some inv => .ok (num * inv % n, ⟨x0, z0⟩)
  | none => .error (gcdFactor n den)

/-- Shared stage data: primes up to `B1` and a primality map up to `B2 + D`. -/
structure Plan where
  b1 : Nat
  b2 : Nat
  powers : Array Nat
  /-- The prime underlying each entry of `powers`. -/
  bases : Array Nat
  isPrime : ByteArray
  d : Nat
  babies : Array Nat

def mkPlan (b1 b2 : Nat) : Plan := Id.run do
  let d := if b2 > 2 * 10 ^ 6 then 2310 else 210
  let limit := b2 + d + 1
  let mut sieve : ByteArray := ByteArray.emptyWithCapacity limit
  for _ in [0:limit] do sieve := sieve.push 1
  sieve := sieve.set! 0 0
  sieve := sieve.set! 1 0
  let mut i := 2
  while i * i < limit do
    if sieve.get! i == 1 then
      let mut j := i * i
      while j < limit do
        sieve := sieve.set! j 0
        j := j + i
    i := i + 1
  let mut powers : Array Nat := #[]
  let mut bases : Array Nat := #[]
  for p in [2:b1 + 1] do
    if sieve.get! p == 1 then
      let mut q := p
      while q * p ≤ b1 do q := q * p
      powers := powers.push q
      bases := bases.push p
  let mut babies : Array Nat := #[]
  for j in [1:d / 2] do
    if j % 2 == 1 && Nat.gcd j d == 1 then babies := babies.push j
  return { b1 := b1, b2 := b2, powers := powers, bases := bases, isPrime := sieve, d := d,
           babies := babies }

/-- Stage 2 by the standard continuation. Returns the accumulated product. -/
def stageTwo (n a24 : Nat) (plan : Plan) (Q : Pt) : Except (Option (ProperFactor n)) Nat := Id.run do
  let d := plan.d
  -- Baby steps [j]Q for odd j < D/2.
  let maxJ := d / 2
  let q2 := dbl n a24 Q
  let mut odd : Array Pt := #[Q, add n q2 Q Q]   -- [1]Q, [3]Q
  let mut j := 5
  while j < maxJ do
    let next := add n odd[odd.size - 1]! q2 odd[odd.size - 2]!
    odd := odd.push next
    j := j + 2
  -- Normalize the selected babies to Z = 1 by one batched inversion.
  let sel := plan.babies.map fun b => odd[(b - 1) / 2]!
  let mut prefixProd : Array Nat := #[]
  let mut acc := 1
  for P in sel do
    acc := acc * P.z % n
    prefixProd := prefixProd.push acc
  match invMod acc n with
  | none => return .error (gcdFactor n acc)
  | some inv =>
    let mut invs : Array Nat := Array.replicate sel.size 0
    let mut running := inv
    for k' in [0:sel.size] do
      let k := sel.size - 1 - k'
      let before := if k == 0 then 1 else prefixProd[k - 1]!
      invs := invs.set! k (running * before % n)
      running := running * sel[k]!.z % n
    let xs := (Array.range sel.size).map fun k => sel[k]!.x * invs[k]! % n
    -- Giant steps G_m = [m D] Q.
    let QD := ladder n a24 Q d
    let m0 := max 1 (plan.b1 / d)
    let mut gPrev := ladder n a24 Q ((m0 - 1) * d)
    let mut g := ladder n a24 Q (m0 * d)
    if m0 == 1 then gPrev := ⟨QD.x, QD.z⟩
    let mut prod := 1
    let mut m := m0
    let mut first := true
    while m * d ≤ plan.b2 + d do
      let c := m * d
      for k in [0:xs.size] do
        let b := plan.babies[k]!
        let hit := (c + b ≤ plan.b2 && plan.isPrime.get! (c + b) == 1) ||
          (c > b && c - b > plan.b1 && plan.isPrime.get! (c - b) == 1)
        if hit then
          prod := prod * ((g.x + n - xs[k]! * g.z % n) % n) % n
      -- advance: G_{m+1} = G_m + QD with difference G_{m-1}
      let gNext := if first && m0 == 1 then dbl n a24 g else add n g QD gPrev
      first := false
      gPrev := g
      g := gNext
      m := m + 1
    return .ok prod

/-- Backtracking when stage 1 annihilated every prime factor at once (`gcd = n`,
typical when all factors are small): replay with a gcd after each prime power,
and inside the guilty power after each single prime. -/
def stageOneReplay (n a24 : Nat) (plan : Plan) (P0 : Pt) : Option (ProperFactor n) := Id.run do
  let mut P := P0
  for i in [0:plan.powers.size] do
    let next := ladder n a24 P plan.powers[i]!
    let g := Nat.gcd next.z n
    if g == 1 then
      P := next
      continue
    if let some f := gcdFactor n next.z then return some f
    -- This prime power killed every factor; step through its prime.
    let p := plan.bases[i]!
    let mut R := P
    let mut k := plan.powers[i]!
    while k > 1 do
      R := ladder n a24 R p
      if let some f := gcdFactor n R.z then return some f
      if Nat.gcd R.z n == n then break
      k := k / p
    return none
  return none

/-- Run one curve: stage 1 (with backtracking), then stage 2. -/
def runCurve (n : Nat) (plan : Plan) (σ : Nat) : Option (ProperFactor n) :=
  match suyama n σ with
  | .error f => f
  | .ok (a24, P0) => Id.run do
    let mut P := P0
    for q in plan.powers do
      P := ladder n a24 P q
    match gcdFactor n P.z with
    | some f => return some f
    | none =>
      if Nat.gcd P.z n == n then return stageOneReplay n a24 plan P0
      if plan.b2 ≤ plan.b1 then return none
      match stageTwo n a24 plan P with
      | .error f => return f
      | .ok prod => return gcdFactor n prod

structure Config where
  b1 : Nat := 2000
  b2 : Nat := 0
  curves : Nat := 32
  threads : Nat := 8
  sigma : Nat := 11
  deriving Repr, Inhabited

/-- Try `curves` curves in parallel batches; the first proper factor wins. -/
def splitWith (n : Nat) (cfg : Config) : Option (ProperFactor n) := Id.run do
  if n < 4 then return none
  let b2 := if cfg.b2 == 0 then 100 * cfg.b1 else cfg.b2
  let plan := mkPlan cfg.b1 b2
  let threads := max 1 cfg.threads
  let mut done := 0
  let mut batch := 0
  while done < cfg.curves do
    let count := min threads (cfg.curves - done)
    let tasks := (List.range count).map fun t =>
      Task.spawn fun _ => runCurve n plan (cfg.sigma + batch * threads + t)
    for task in tasks do
      if let some f := task.get then return some f
    done := done + count
    batch := batch + 1
  return none

/-- GMP-ECM's recommended `(B1, curves)` for factors of 15 to 40 digits. -/
def schedule : List (Nat × Nat) :=
  [(2000, 25), (11000, 90), (50000, 300), (250000, 700), (1000000, 1800), (3000000, 5100)]

/-- Even numbers and perfect powers first, then ECM at fixed `B1`. -/
def split (n : Nat) (cfg : Config := {}) : Option (ProperFactor n) :=
  if n < 4 then none
  else if n % 2 = 0 then checkFactor n 2
  else match perfectPower n with
    | some (r, _) => checkFactor n r
    | none => splitWith n cfg

/-- Every factor returned by ECM is a proper divisor. -/
theorem split_sound {n : Nat} {cfg : Config} {d : ProperFactor n}
    (_h : split n cfg = some d) : 1 < d.val ∧ d.val < n ∧ d.val ∣ n := d.property

end PrimeFactorLean.ECMM
