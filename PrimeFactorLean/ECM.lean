import PrimeFactorLean.Core
/-!
# A bounded, executable ECM stage one

The computation uses affine elliptic curves over `ℤ/nℤ`.  Every attempted
division first computes a gcd.  A nonunit denominator can expose a proper
factor; a denominator divisible by all of `n` discards that curve.

Curves have a deterministic initial point: choose `x`, `y`, and `a`, then set
`b = y² - x³ - a*x`.  The discriminant is checked before scalar multiplication.
Stage one multiplies by the largest power of each prime at most `bound`, giving
the usual exponent `lcm(1, …, bound)`.  A simpler factorial schedule is retained
as a benchmark reference.  Both schedules are bounded stage one, with no stage two.
-/

namespace PrimeFactorLean.ECM

/-- Extended Euclid, transcribed from mathlib's `Nat.xgcdAux` (the proof layer
shows that the two agree, so mathlib's Bézout identity applies to it). -/
def xgcdAux : Nat → Int → Int → Nat → Int → Int → Nat × Int × Int
  | 0, _, _, r', s', t' => (r', s', t')
  | k + 1, s, t, r', s', t' =>
    let q := r' / (k + 1)
    xgcdAux (r' % (k + 1)) (s' - q * s) (t' - q * t) (k + 1) s t
termination_by k => k
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos _)

/-- The Bézout coefficient of `x` in `gcd x y = x * a + y * b`. -/
def gcdA (x y : Nat) : Int := (xgcdAux x 1 0 y 0 1).2.1

/-- The standard representative of an extended-Euclidean modular inverse. -/
def inverse (n d : Nat) : Nat :=
  (gcdA d n % (n : Int)).toNat

/-- Modular subtraction avoids truncated subtraction by reducing first. -/
def subMod (n x y : Nat) : Nat :=
  (x % n + n - y % n) % n

/-- Modular subtraction really cancels its subtrahend. -/
theorem subMod_add {n : Nat} (hn : 0 < n) (x y : Nat) :
    (subMod n x y + y) % n = x % n := by
  have hy : y % n ≤ x % n + n :=
    Nat.le_trans (Nat.le_of_lt (Nat.mod_lt y hn)) (Nat.le_add_left n (x % n))
  calc
    (subMod n x y + y) % n = (x % n + n - y % n + y % n) % n := by
      simp only [subMod, Nat.add_mod, Nat.mod_mod]
    _ = (x % n + n) % n := by rw [Nat.sub_add_cancel hy]
    _ = x % n := by simp

structure Point where
  x : Nat
  y : Nat
  deriving Repr, DecidableEq

/-- `none` is the point at infinity. -/
abbrev ECPoint := Option Point

/-- The affine Weierstrass curve equation, over residues modulo `n`. -/
def OnCurve (n a b : Nat) (p : Point) : Prop :=
  (p.y * p.y) % n = (p.x * p.x * p.x + a * p.x + b) % n

inductive Step where
  | point (p : ECPoint)
  | factor (d : Nat)
  | discard
  deriving Repr

/-- Divide a slope numerator, or report the gcd that prevents division. -/
def slope (n numerator denominator : Nat) (finish : Nat → Step) : Step :=
  let d := Nat.gcd denominator n
  if 1 < d ∧ d < n then
    .factor d
  else if d = 1 then
    finish ((numerator * inverse n denominator) % n)
  else
    .discard

def resultPoint (n : Nat) (p q : Point) (m : Nat) : Point :=
  let x := subMod n (m * m) (p.x + q.x)
  let y := subMod n (m * subMod n p.x x) p.y
  ⟨x, y⟩

def finishAdd (n : Nat) (p q : Point) (m : Nat) : Step :=
  .point (some (resultPoint n p q m))

/-- Affine chord-and-tangent addition, including the point at infinity. -/
def add (n a : Nat) (p q : ECPoint) : Step :=
  match p, q with
  | none, _ => .point q
  | _, none => .point p
  | some p, some q =>
      if p.x = q.x ∧ (p.y + q.y) % n = 0 then
        .point none
      else if p.x = q.x ∧ p.y = q.y then
        slope n ((3 * p.x * p.x + a) % n) ((2 * p.y) % n)
          (finishAdd n p q)
      else
        slope n (subMod n q.y p.y) (subMod n q.x p.x)
          (finishAdd n p q)

/-- The point at infinity and every affine point satisfying the curve equation. -/
def PointOnCurve (n a b : Nat) : ECPoint → Prop
  | none => True
  | some p => OnCurve n a b p

/-- Binary scalar multiplication.  Fuel decreases even on composite moduli. -/
def multiplyAux (n a : Nat) : Nat → Nat → ECPoint → ECPoint → Step
  | 0, _, accumulator, _ => .point accumulator
  | fuel + 1, k, accumulator, base =>
      if k = 0 then
        .point accumulator
      else
        let accumulated :=
          if k % 2 = 1 then add n a accumulator base else .point accumulator
        match accumulated with
        | .factor d => .factor d
        | .discard => .discard
        | .point accumulator' =>
            if k / 2 = 0 then
              .point accumulator'
            else
              match add n a base base with
              | .factor d => .factor d
              | .discard => .discard
              | .point base' => multiplyAux n a fuel (k / 2) accumulator' base'

def multiply (n a k : Nat) (p : ECPoint) : Step :=
  multiplyAux n a k k none p

/-- Apply successive stage-one scalar multipliers. -/
def stageAux (n a : Nat) : Nat → Nat → ECPoint → Step
  | 0, _, p => .point p
  | remaining + 1, multiplier, p =>
      match p with
      | none => .point none
      | some _ =>
          match multiply n a multiplier p with
          | .factor d => .factor d
          | .discard => .discard
          | .point p' => stageAux n a remaining (multiplier + 1) p'

def stageOneFactorial (n a bound : Nat) (p : ECPoint) : Step :=
  stageAux n a (bound - 1) 2 p

/-- Repeatedly enlarge a prime power while it remains inside the stage bound. -/
def primePowerAux (bound prime : Nat) : Nat → Nat → Nat
  | 0, power => power
  | fuel + 1, power =>
      if power * prime ≤ bound then
        primePowerAux bound prime fuel (power * prime)
      else power

def primePower (bound prime : Nat) : Nat :=
  primePowerAux bound prime bound prime

/-- Prime testing here constructs the scalar schedule; it never splits the input. -/
def stageMultipliers (bound : Nat) : List Nat :=
  (List.range (bound + 1)).filterMap fun prime =>
    if 2 ≤ prime ∧ minFac prime = prime then some (primePower bound prime) else none

def stageList (n a : Nat) : List Nat → ECPoint → Step
  | [], p => .point p
  | multiplier :: rest, p =>
      match p with
      | none => .point none
      | some _ =>
          match multiply n a multiplier p with
          | .factor d => .factor d
          | .discard => .discard
          | .point p' => stageList n a rest p'

def stageOne (n a bound : Nat) (p : ECPoint) : Step :=
  stageList n a (stageMultipliers bound) p

/-- Seed a curve together with a point lying on it by construction. -/
def curveWithStage (stage : Nat → Nat → Nat → ECPoint → Step) (n bound seed : Nat) : Step :=
  let x := (seed + 1) % n
  let y := (seed * seed + 3) % n
  let a := (5 * seed + 1) % n
  let b := subMod n (y * y) (x * x * x + a * x)
  let discriminant := (4 * a * a * a + 27 * b * b) % n
  let d := Nat.gcd discriminant n
  if 1 < d ∧ d < n then
    .factor d
  else if d = 1 then
    stage n a bound (some ⟨x, y⟩)
  else
    .discard

def curve (n bound seed : Nat) : Step := curveWithStage stageOne n bound seed

def curveFactorial (n bound seed : Nat) : Step := curveWithStage stageOneFactorial n bound seed

def curvesAuxWith (tryCurve : Nat → Nat → Nat → Step) (n bound : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | remaining + 1, seed =>
      match tryCurve n bound seed with
      | .factor d => some d
      | _ => curvesAuxWith tryCurve n bound remaining (seed + 1)

def curvesAux (n bound remaining seed : Nat) : Option Nat :=
  curvesAuxWith curve n bound remaining seed

/-- A final inexpensive check makes the public result self-validating. -/
def checkFactor (n : Nat) : Option Nat → Option Nat
  | none => none
  | some d => if 1 < d ∧ d < n ∧ d ∣ n then some d else none

theorem checkFactor_sound {n d : Nat} {candidate : Option Nat}
    (h : checkFactor n candidate = some d) : 1 < d ∧ d < n ∧ d ∣ n := by
  cases candidate with
  | none => simp [checkFactor] at h
  | some c =>
      simp only [checkFactor] at h
      split at h
      next hc => cases Option.some.inj h; exact hc
      next => contradiction

/-- Try a bounded number of deterministic curves using genuine ECM stage one. -/
def split (n : Nat) (bound : Nat := 200) (curves : Nat := 12) : Option Nat :=
  if n < 4 then none else checkFactor n (curvesAux n bound curves 1)

/-- The original factorial stage-one schedule, retained for direct benchmarks. -/
def splitFactorial (n : Nat) (bound : Nat := 200) (curves : Nat := 12) : Option Nat :=
  if n < 4 then none else checkFactor n (curvesAuxWith curveFactorial n bound curves 1)

/-- Every successful ECM split is a strict nontrivial divisor. -/
theorem split_sound {n bound curves d : Nat}
    (h : split n bound curves = some d) : 1 < d ∧ d < n ∧ d ∣ n := by
  unfold split at h
  split at h
  next => contradiction
  next => exact checkFactor_sound h

theorem splitFactorial_sound {n bound curves d : Nat}
    (h : splitFactorial n bound curves = some d) : 1 < d ∧ d < n ∧ d ∣ n := by
  unfold splitFactorial at h
  split at h
  next => contradiction
  next => exact checkFactor_sound h

end PrimeFactorLean.ECM
