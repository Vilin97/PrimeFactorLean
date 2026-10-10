import PrimeFactorLean.MontGen
import PrimeFactorLean.ECMMontgomery

/-!
# ECM on fixed-width Montgomery arithmetic

The algorithm of `PrimeFactorLean.ECMM` (Suyama curves, x-only Montgomery
arithmetic, stage 1 and the standard stage-2 continuation), run on the
fixed-width residues of `PrimeFactorLean.MontGen` instead of `Nat`:

* stage 1 is one Montgomery ladder over `k = ∏ q` (all maximal prime powers
  `q ≤ B1`) from a base point normalized to `Z = 1`, so a ladder step costs
  4 squarings and 6 multiplications;
* stage 2 accumulates `X_G - x_j Z_G` over the pairs `m D ± j` that contain a
  prime of `(B1, B2]`, with the baby steps normalized by one batched inversion;
* when stage 1 collapses (`gcd = n`: every factor found at once) the curve is
  replayed prime power by prime power with the `Nat` code of `ECMM`.

Every factor is `gcd(z, n)` for a computed `z` and is checked
(`ECMM.gcdFactor`), so `split` returns a `ProperFactor n` whatever the
arithmetic computes.
-/

namespace PrimeFactorLean.ECMF

open Mont Mont.Arith

structure Pt (α : Type) where
  x : α
  z : α

instance {α : Type} [Inhabited α] : Inhabited (Pt α) := ⟨⟨default, default⟩⟩

section Generic

variable {α μ : Type} [Arith α μ] [Inhabited α]

/-- `[2]P`: `X₂ = (X+Z)²(X-Z)²`, `Z₂ = 4XZ((X-Z)² + a24·4XZ)`. -/
@[specialize] def dbl (m : μ) (a24 : α) (P : Pt α) : Pt α :=
  let s := sqr m (add m P.x P.z)
  let d := sqr m (sub m P.x P.z)
  let t := sub m s d
  ⟨mul m s d, mul m t (add m d (mul m a24 t))⟩

/-- `P + Q` from `P - Q = D`. -/
@[specialize] def addPt (m : μ) (P Q D : Pt α) : Pt α :=
  let u := mul m (sub m P.x P.z) (add m Q.x Q.z)
  let w := mul m (add m P.x P.z) (sub m Q.x Q.z)
  ⟨mul m D.z (sqr m (add m u w)), mul m D.x (sqr m (sub m u w))⟩

/-- `P + Q` when `P - Q = (xD : 1)`. -/
@[specialize] def addNorm (m : μ) (P Q : Pt α) (xD : α) : Pt α :=
  let u := mul m (sub m P.x P.z) (add m Q.x Q.z)
  let w := mul m (add m P.x P.z) (sub m Q.x Q.z)
  ⟨sqr m (add m u w), mul m xD (sqr m (sub m u w))⟩

/-- The Montgomery ladder over `bits[i-1], …, bits[0]` (most significant
first) from `(r0, r1) = ([k']P, [k'+1]P)`, for the base point `(xP : 1)`. -/
@[specialize] def ladderLoop (m : μ) (a24 xP : α) (bits : ByteArray) (r0 r1 : Pt α) :
    Nat → Pt α
  | 0 => r0
  | i + 1 =>
    if bits.get! i == 1 then ladderLoop m a24 xP bits (addNorm m r1 r0 xP) (dbl m a24 r1) i
    else ladderLoop m a24 xP bits (dbl m a24 r0) (addNorm m r1 r0 xP) i

/-- `[k]P` by the general ladder (`k ≥ 1`). -/
@[specialize] def ladderAny (m : μ) (a24 : α) (P : Pt α) (k : Nat) : Pt α := Id.run do
  if k ≤ 1 then return P
  let mut r0 := P
  let mut r1 := dbl m a24 P
  let top := k.log2
  for i' in [0:top] do
    let i := top - 1 - i'
    if k.testBit i then
      r0 := addPt m r1 r0 P
      r1 := dbl m a24 r1
    else
      r1 := addPt m r1 r0 P
      r0 := dbl m a24 r0
  return r0

/-- `[j]Q` for `j = 1, 3, 5, …` (`count` points). -/
@[specialize] def oddMultiples (m : μ) (a24 : α) (Q : Pt α) (count : Nat) : Array (Pt α) :=
  Id.run do
  let q2 := dbl m a24 Q
  let mut out : Array (Pt α) := #[Q]
  if count > 1 then out := out.push (addPt m q2 Q Q)
  for k in [2:count] do
    out := out.push (addPt m out[k - 1]! q2 out[k - 2]!)
  return out

/-- Stage 2 (standard continuation): the product of `X_G - x_j Z_G` over the
giant steps `G = [mD]Q` and the normalized babies `x_j` whose pair `mD ± j`
holds a prime of `(B1, B2]`. `.error z` when a normalization is impossible
(`gcd(z, n) > 1`). -/
@[specialize] def stageTwo (m : μ) (a24 : α) (plan : ECMM.Plan) (Q : Pt α) : Except Nat α :=
  Id.run do
  let n := modulus (α := α) m
  let d := plan.d
  let odd := oddMultiples m a24 Q (d / 4)
  let sel := plan.babies.map fun b => odd[(b - 1) / 2]!
  -- batched inversion of the babies' `Z` (on plain residues)
  let zs := sel.map fun P => fromMont m P.z
  let mut prefixProd : Array Nat := #[]
  let mut acc := 1
  for z in zs do
    acc := acc * z % n
    prefixProd := prefixProd.push acc
  let some inv := Arith.invMod acc n | return .error acc
  let mut xs : Array α := Array.replicate sel.size (ofLimbs m 0)
  let mut running := inv
  for k' in [0:sel.size] do
    let k := sel.size - 1 - k'
    let before := if k == 0 then 1 else prefixProd[k - 1]!
    let zinv := running * before % n
    xs := xs.set! k (toMont m (fromMont m sel[k]!.x * zinv % n))
    running := running * zs[k]! % n
  -- giant steps `G_m = [m D] Q`
  let QD := ladderAny m a24 Q d
  let m0 := max 1 (plan.b1 / d)
  let mut gPrev := if m0 == 1 then QD else ladderAny m a24 Q ((m0 - 1) * d)
  let mut g := if m0 == 1 then QD else ladderAny m a24 Q (m0 * d)
  let mut prod : α := toMont m 1
  let mut mm := m0
  let mut first := true
  while mm * d ≤ plan.b2 + d do
    let c := mm * d
    for k in [0:xs.size] do
      let b := plan.babies[k]!
      let hit := (c + b ≤ plan.b2 && plan.isPrime.get! (c + b) == 1) ||
        (c > b && c - b > plan.b1 && plan.isPrime.get! (c - b) == 1)
      if hit then
        prod := mul m prod (sub m g.x (mul m xs[k]! g.z))
    -- `G_{m+1} = G_m + [D]Q` with difference `G_{m-1}` (`G_2 = [2]G_1` when `m0 = 1`)
    let gNext := if first && m0 == 1 then dbl m a24 g else addPt m g QD gPrev
    first := false
    gPrev := g
    g := gNext
    mm := mm + 1
  return .ok prod

/-- Outcome of one curve. -/
inductive Outcome
  /-- `gcd(z, n)` is the candidate factor. -/
  | value (z : Nat)
  /-- Stage 1 found every factor at once (`gcd = n`). -/
  | collapsed
  | nothing

/-- Stages 1 and 2 of one curve with normalized base point `(x0 : 1)`;
`bits` are the bits of `∏ q` (least significant first, top bit set). -/
@[specialize] def curve (m : μ) (a24 x0 : α) (bits : ByteArray) (plan : ECMM.Plan) : Outcome :=
  let n := modulus (α := α) m
  let one : α := toMont m 1
  let P : Pt α := ⟨x0, one⟩
  let Q := if bits.size ≤ 1 then P else ladderLoop m a24 x0 bits P (dbl m a24 P) (bits.size - 1)
  let g := gcdN m Q.z
  if g == n then .collapsed
  else if g > 1 then .value (limbNat Q.z)
  else if plan.b2 ≤ plan.b1 then .nothing
  else match stageTwo m a24 plan Q with
    | .error z => .value z
    | .ok prod => .value (limbNat prod)

/-- One curve for the Suyama parameter `σ` at width `α`. -/
@[specialize] def runCurveW (m : μ) (n : Nat) (plan : ECMM.Plan) (bits : ByteArray) (σ : Nat) :
    Option (ProperFactor n) :=
  match ECMM.suyama n σ with
  | .error f => f
  | .ok (a24N, P0) =>
    match Arith.invMod (P0.z % n) n with
    | none => ECMM.gcdFactor n P0.z
    | some zinv =>
      let x0 : α := toMont m (P0.x * zinv % n)
      match curve m (toMont m a24N) x0 bits plan with
      | .value z => ECMM.gcdFactor n z
      | .collapsed => ECMM.stageOneReplay n a24N plan P0
      | .nothing => none

end Generic

/-- The bits of `k`, least significant first. -/
def natBits (k : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (k.log2 + 1)
  let mut r := k
  while r > 0 do
    let w := r &&& 4294967295
    r := r >>> 32
    for i in [0:32] do
      out := out.push (if w.testBit i then 1 else 0)
  -- drop leading zeros
  let mut top := out.size
  while top > 0 && out.get! (top - 1) == 0 do top := top - 1
  return out.extract 0 top

/-- Stage data shared by all curves: the plan and the bits of `∏ q`. -/
structure Fast where
  plan : ECMM.Plan
  bits : ByteArray

def mkFast (b1 b2 : Nat) : Fast :=
  let plan := ECMM.mkPlan b1 b2
  { plan, bits := natBits (plan.powers.foldl (· * ·) 1) }

set_option maxHeartbeats 1000000

def curve1 (n : Nat) (fast : Fast) (σ : Nat) : Option (ProperFactor n) :=
  runCurveW (α := N1) (Mod1.ofNat n) n fast.plan fast.bits σ

def curve2 (n : Nat) (fast : Fast) (σ : Nat) : Option (ProperFactor n) :=
  runCurveW (α := N2) (Mod2.ofNat n) n fast.plan fast.bits σ

def curve3 (n : Nat) (fast : Fast) (σ : Nat) : Option (ProperFactor n) :=
  runCurveW (α := N3) (Mod3.ofNat n) n fast.plan fast.bits σ

def curve4 (n : Nat) (fast : Fast) (σ : Nat) : Option (ProperFactor n) :=
  runCurveW (α := N4) (Mod4.ofNat n) n fast.plan fast.bits σ

def curve5 (n : Nat) (fast : Fast) (σ : Nat) : Option (ProperFactor n) :=
  runCurveW (α := N5) (Mod5.ofNat n) n fast.plan fast.bits σ

def curve6 (n : Nat) (fast : Fast) (σ : Nat) : Option (ProperFactor n) :=
  runCurveW (α := N6) (Mod6.ofNat n) n fast.plan fast.bits σ

def curve7 (n : Nat) (fast : Fast) (σ : Nat) : Option (ProperFactor n) :=
  runCurveW (α := N7) (Mod7.ofNat n) n fast.plan fast.bits σ

def curve8 (n : Nat) (fast : Fast) (σ : Nat) : Option (ProperFactor n) :=
  runCurveW (α := N8) (Mod8.ofNat n) n fast.plan fast.bits σ

def curve9 (n : Nat) (fast : Fast) (σ : Nat) : Option (ProperFactor n) :=
  runCurveW (α := N9) (Mod9.ofNat n) n fast.plan fast.bits σ

def curve10 (n : Nat) (fast : Fast) (σ : Nat) : Option (ProperFactor n) :=
  runCurveW (α := N10) (Mod10.ofNat n) n fast.plan fast.bits σ

def curve11 (n : Nat) (fast : Fast) (σ : Nat) : Option (ProperFactor n) :=
  runCurveW (α := N11) (Mod11.ofNat n) n fast.plan fast.bits σ

def curve12 (n : Nat) (fast : Fast) (σ : Nat) : Option (ProperFactor n) :=
  runCurveW (α := N12) (Mod12.ofNat n) n fast.plan fast.bits σ

/-- One curve at the width that fits `n` (the `Nat` code beyond 336 bits). -/
def runCurve (n : Nat) (fast : Fast) (σ : Nat) : Option (ProperFactor n) :=
  match (n.log2 + 28) / 28 with
  | 1 => curve1 n fast σ
  | 2 => curve2 n fast σ
  | 3 => curve3 n fast σ
  | 4 => curve4 n fast σ
  | 5 => curve5 n fast σ
  | 6 => curve6 n fast σ
  | 7 => curve7 n fast σ
  | 8 => curve8 n fast σ
  | 9 => curve9 n fast σ
  | 10 => curve10 n fast σ
  | 11 => curve11 n fast σ
  | 12 => curve12 n fast σ
  | _ => ECMM.runCurve n fast.plan σ

/-- The stage data of the standard levels (`B2 = 100 B1`), built on first use and
shared by every later call (the prime sieve up to `B2` dominates the cost). -/
def standardPlans : Array (Nat × Thunk Fast) :=
  #[2000, 11000, 50000, 250000, 1000000, 3000000].map fun b1 =>
    (b1, Thunk.mk fun _ => mkFast b1 (100 * b1))

def planFor (b1 b2 : Nat) : Fast :=
  if b2 == 100 * b1 then
    match standardPlans.find? (·.1 == b1) with
    | some (_, t) => t.get
    | none => mkFast b1 b2
  else mkFast b1 b2

/-- Try `curves` curves in parallel batches; the first proper factor wins. -/
def splitWith (n : Nat) (cfg : ECMM.Config) : Option (ProperFactor n) := Id.run do
  if n < 4 then return none
  let b2 := if cfg.b2 == 0 then 100 * cfg.b1 else cfg.b2
  let fast := planFor cfg.b1 b2
  let threads := max 1 cfg.threads
  let mut done := 0
  let mut batch := 0
  while done < cfg.curves do
    let count := min threads (cfg.curves - done)
    let tasks := (List.range count).map fun t =>
      Task.spawn fun _ => runCurve n fast (cfg.sigma + batch * threads + t)
    for task in tasks do
      if let some f := task.get then return some f
    done := done + count
    batch := batch + 1
  return none

/-- Even numbers and perfect powers first, then ECM at fixed `B1`. -/
def split (n : Nat) (cfg : ECMM.Config := {}) : Option (ProperFactor n) :=
  if n < 4 then none
  else if n % 2 = 0 then checkFactor n 2
  else match Arith.perfectPower n with
    | some (r, _) => checkFactor n r
    | none => splitWith n cfg

/-- Every factor returned by the fast ECM is a proper divisor. -/
theorem split_sound {n : Nat} {cfg : ECMM.Config} {d : ProperFactor n}
    (_h : split n cfg = some d) : 1 < d.val ∧ d.val < n ∧ d.val ∣ n := d.property

end PrimeFactorLean.ECMF
