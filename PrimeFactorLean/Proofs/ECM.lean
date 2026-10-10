import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import PrimeFactorLean.ECM

/-! Proof layer: see the runtime module for documentation. -/

namespace PrimeFactorLean.ECM

theorem xgcdAux_eq : ∀ (r : Nat) (s t : Int) (r' : Nat) (s' t' : Int),
    xgcdAux r s t r' s' t' = Nat.xgcdAux r s t r' s' t' := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro s t r' s' t'
    cases r with
    | zero => rw [Nat.xgcd_zero_left]; simp [xgcdAux]
    | succ k =>
      rw [xgcdAux, Nat.xgcdAux_rec (Nat.succ_pos k)]
      exact ih _ (Nat.mod_lt _ (Nat.succ_pos k)) _ _ _ _ _

theorem gcdA_eq (x y : Nat) : gcdA x y = Nat.gcdA x y := by
  simp [gcdA, Nat.gcdA, Nat.xgcd, xgcdAux_eq]

/-- The actual executable inverse is correct when its denominator is a unit. -/
theorem inverse_correct {n d : Nat} (hn : 1 < n) (hd : Nat.gcd d n = 1) :
    d * inverse n d % n = 1 := by
  have hn' : (n : Int) ≠ 0 :=
    Int.ofNat_ne_zero.mpr (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))
  have key := congrArg (fun (m : Int) => (m % n).toNat) (Nat.gcd_eq_gcd_ab d n)
  simp only at key
  rw [Int.add_mul_emod_self_left, ← Int.natCast_mod, Int.toNat_natCast,
    hd, Nat.mod_eq_of_lt hn] at key
  refine Eq.trans (Int.ofNat.inj ?_) key.symm
  rw [inverse, gcdA_eq, Int.ofNat_eq_coe, Int.natCast_mod, Int.natCast_mul,
    Int.toNat_of_nonneg (Int.emod_nonneg _ hn'), Int.ofNat_eq_coe,
    Int.toNat_of_nonneg (Int.emod_nonneg _ hn'), Int.mul_emod,
    Int.emod_emod, ← Int.mul_emod]

/-- Constructing `b` from a point actually puts that point on the curve. -/
theorem seeded_point_on_curve {n : Nat} (hn : 0 < n) (a x y : Nat) :
    OnCurve n a (subMod n (y * y) (x * x * x + a * x)) ⟨x, y⟩ := by
  unfold OnCurve
  simpa only [Nat.add_comm] using
    (subMod_add hn (y * y) (x * x * x + a * x)).symm

theorem subMod_cast {n : Nat} (hn : 0 < n) (x y : Nat) :
    (subMod n x y : ZMod n) = (x : ZMod n) - y := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [Nat.cast_add] using
    (ZMod.natCast_eq_natCast_iff' (subMod n x y + y) x n).mpr (subMod_add hn x y)

theorem onCurve_iff_cast (n a b : Nat) (p : Point) :
    OnCurve n a b p ↔
      (p.y : ZMod n) * p.y = p.x * p.x * p.x + (a : ZMod n) * p.x + b := by
  unfold OnCurve
  rw [← ZMod.natCast_eq_natCast_iff']
  simp only [Nat.cast_mul, Nat.cast_add]

/-- The exact tangent formulas used by `finishAdd` preserve a curve equation. -/
theorem tangent_formula_preserves_curve {R : Type*} [CommRing R]
    (a b x y m : R) (hp : y * y = x * x * x + a * x + b)
    (hs : m * (2 * y) = 3 * x * x + a) :
    let X := m * m - (x + x)
    let Y := m * (x - X) - y
    Y * Y = X * X * X + a * X + b := by
  dsimp
  linear_combination hp + (m * m - (x + x) - x) * hs

/-- The exact chord formulas preserve a curve when the chord denominator is a unit. -/
theorem chord_formula_preserves_curve {R : Type*} [CommRing R]
    (a b x₁ y₁ x₂ y₂ m t : R)
    (hp : y₁ * y₁ = x₁ * x₁ * x₁ + a * x₁ + b)
    (hq : y₂ * y₂ = x₂ * x₂ * x₂ + a * x₂ + b)
    (hs : m * (x₂ - x₁) = y₂ - y₁) (hi : t * (x₂ - x₁) = 1) :
    let X := m * m - (x₁ + x₂)
    let Y := m * (x₁ - X) - y₁
    Y * Y = X * X * X + a * X + b := by
  dsimp
  linear_combination
    (1 - (m * m - (x₁ + x₂) - x₁) * t) * hp +
    ((m * m - (x₁ + x₂) - x₁) * t) * hq +
    ((m * m - (x₁ + x₂) - x₁) * t) * (y₁ + y₂ + m * (x₂ - x₁)) * hs -
    (m * m - (x₁ + x₂) - x₁) *
      (m * m * (x₂ - x₁) + 2 * m * y₁ - x₂ * x₂ - x₂ * x₁ - x₁ * x₁ - a) * hi

/-- A unit denominator gives the slope equation needed by chord-and-tangent addition. -/
theorem slope_value_correct {n denominator : Nat} (hn : 1 < n)
    (hd : Nat.gcd denominator n = 1) (numerator : Nat) :
    denominator * ((numerator * inverse n denominator) % n) % n = numerator % n := by
  calc
    denominator * ((numerator * inverse n denominator) % n) % n =
        (numerator * (denominator * inverse n denominator)) % n := by
      simp [Nat.mul_mod, Nat.mul_left_comm]
    _ = ((numerator % n) * ((denominator * inverse n denominator) % n)) % n :=
      Nat.mul_mod _ _ _
    _ = numerator % n := by rw [inverse_correct hn hd]; simp

theorem inverse_cast {n denominator : Nat} (hn : 1 < n)
    (hd : Nat.gcd denominator n = 1) :
    (inverse n denominator : ZMod n) * denominator = 1 := by
  have h : denominator * inverse n denominator % n = 1 % n := by
    rw [inverse_correct hn hd, Nat.mod_eq_of_lt hn]
  simpa only [Nat.cast_mul, Nat.cast_one, mul_comm] using
    (ZMod.natCast_eq_natCast_iff' (denominator * inverse n denominator) 1 n).mpr h

theorem slope_cast {n denominator : Nat} (hn : 1 < n)
    (hd : Nat.gcd denominator n = 1) (numerator : Nat) :
    (((numerator * inverse n denominator) % n : Nat) : ZMod n) * denominator = numerator := by
  have h := (ZMod.natCast_eq_natCast_iff'
    (denominator * ((numerator * inverse n denominator) % n)) numerator n).mpr
    (slope_value_correct hn hd numerator)
  simpa only [Nat.cast_mul, mul_comm] using h

/-- Every successful slope computation used a unit denominator. -/
theorem slope_success {n numerator denominator : Nat} {finish : Nat → Step} {p : ECPoint}
    (h : slope n numerator denominator finish = .point p) :
    Nat.gcd denominator n = 1 ∧
      finish ((numerator * inverse n denominator) % n) = .point p := by
  unfold slope at h
  dsimp only at h
  split at h
  next => contradiction
  next =>
    split at h
    next hd => exact ⟨hd, h⟩
    next => contradiction

theorem resultPoint_tangent_on_curve {n a b : Nat} (hn : 0 < n) (p : Point) (m : Nat)
    (hp : OnCurve n a b p)
    (hs : (m : ZMod n) * (2 * (p.y : ZMod n)) = 3 * p.x * p.x + a) :
    OnCurve n a b (resultPoint n p p m) := by
  apply (onCurve_iff_cast n a b _).mpr
  simpa only [resultPoint, subMod_cast hn, Nat.cast_mul, Nat.cast_add] using
    tangent_formula_preserves_curve (a : ZMod n) b p.x p.y m
      ((onCurve_iff_cast n a b p).mp hp) hs

theorem resultPoint_chord_on_curve {n a b : Nat} (hn : 0 < n) (p q : Point) (m t : Nat)
    (hp : OnCurve n a b p) (hq : OnCurve n a b q)
    (hs : (m : ZMod n) * ((q.x : ZMod n) - p.x) = (q.y : ZMod n) - p.y)
    (hi : (t : ZMod n) * ((q.x : ZMod n) - p.x) = 1) :
    OnCurve n a b (resultPoint n p q m) := by
  apply (onCurve_iff_cast n a b _).mpr
  simpa only [resultPoint, subMod_cast hn, Nat.cast_mul, Nat.cast_add] using
    chord_formula_preserves_curve (a : ZMod n) b p.x p.y q.x q.y m t
      ((onCurve_iff_cast n a b p).mp hp) ((onCurve_iff_cast n a b q).mp hq) hs hi

/-- Successful raw affine addition preserves the actual modular curve equation. -/
theorem add_preserves_curve {n a b : Nat} (hn : 1 < n) {p q r : ECPoint}
    (hp : PointOnCurve n a b p) (hq : PointOnCurve n a b q)
    (h : add n a p q = .point r) : PointOnCurve n a b r := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  cases p with
  | none =>
      have hpoint : Step.point q = Step.point r := by cases q <;> exact h
      have he : q = r := Step.point.inj hpoint
      cases he
      exact hq
  | some p =>
      cases q with
      | none =>
          have he : some p = r := Step.point.inj h
          cases he
          exact hp
      | some q =>
          unfold add at h
          dsimp only at h
          split at h
          next =>
            have he : none = r := Step.point.inj h
            cases he
            trivial
          next =>
            split at h
            next hsame =>
              have hpq : p = q := by
                rcases p with ⟨px, py⟩
                rcases q with ⟨qx, qy⟩
                dsimp only at hsame
                rcases hsame with ⟨hx, hy⟩
                cases hx
                cases hy
                rfl
              subst q
              rcases slope_success h with ⟨hd, hfinish⟩
              let m := (((3 * p.x * p.x + a) % n) * inverse n ((2 * p.y) % n)) % n
              have he : r = some (resultPoint n p p m) := (Step.point.inj hfinish).symm
              rw [he]
              apply resultPoint_tangent_on_curve hn0 p m hp
              simpa only [m, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using
                slope_cast hn hd ((3 * p.x * p.x + a) % n)
            next =>
              rcases slope_success h with ⟨hd, hfinish⟩
              let denominator := subMod n q.x p.x
              let m := (subMod n q.y p.y * inverse n denominator) % n
              have he : r = some (resultPoint n p q m) := (Step.point.inj hfinish).symm
              rw [he]
              apply resultPoint_chord_on_curve hn0 p q m (inverse n denominator) hp hq
              · simpa only [m, denominator, subMod_cast hn0] using
                  slope_cast hn hd (subMod n q.y p.y)
              · simpa only [denominator, subMod_cast hn0] using inverse_cast hn hd

theorem multiplyAux_preserves_curve {n a b : Nat} (hn : 1 < n) :
    ∀ (fuel k : Nat) (accumulator base r : ECPoint),
      PointOnCurve n a b accumulator → PointOnCurve n a b base →
      multiplyAux n a fuel k accumulator base = .point r → PointOnCurve n a b r := by
  intro fuel
  induction fuel with
  | zero =>
      intro k accumulator base r hacc hbase h
      have he : accumulator = r := Step.point.inj h
      cases he
      exact hacc
  | succ fuel ih =>
      intro k accumulator base r hacc hbase h
      simp only [multiplyAux] at h
      split at h
      next =>
        cases Step.point.inj h
        exact hacc
      next =>
        cases hs : (if k % 2 = 1 then add n a accumulator base else Step.point accumulator) with
        | factor d => simp only [hs] at h; contradiction
        | discard => simp only [hs] at h; contradiction
        | point accumulator' =>
            have hacc' : PointOnCurve n a b accumulator' := by
              by_cases hodd : k % 2 = 1
              · simp only [hodd, if_true] at hs
                exact add_preserves_curve hn hacc hbase hs
              · simp only [hodd, if_false] at hs
                cases Step.point.inj hs
                exact hacc
            simp only [hs] at h
            split at h
            next =>
              cases Step.point.inj h
              exact hacc'
            next =>
              cases hb : add n a base base with
              | factor d => simp only [hb] at h; contradiction
              | discard => simp only [hb] at h; contradiction
              | point base' =>
                  simp only [hb] at h
                  exact ih _ _ _ _ hacc' (add_preserves_curve hn hbase hbase hb) h

theorem multiply_preserves_curve {n a b k : Nat} (hn : 1 < n) {p r : ECPoint}
    (hp : PointOnCurve n a b p) (h : multiply n a k p = .point r) :
    PointOnCurve n a b r :=
  multiplyAux_preserves_curve hn k k none p r trivial hp h

theorem stageAux_preserves_curve {n a b : Nat} (hn : 1 < n) :
    ∀ (remaining multiplier : Nat) (p r : ECPoint), PointOnCurve n a b p →
      stageAux n a remaining multiplier p = .point r → PointOnCurve n a b r := by
  intro remaining
  induction remaining with
  | zero =>
      intro multiplier p r hp h
      cases Step.point.inj h
      exact hp
  | succ remaining ih =>
      intro multiplier p r hp h
      cases p with
      | none =>
          cases Step.point.inj h
          trivial
      | some p =>
          simp only [stageAux] at h
          cases hm : multiply n a multiplier (some p) with
          | factor d => simp only [hm] at h; contradiction
          | discard => simp only [hm] at h; contradiction
          | point p' =>
              simp only [hm] at h
              exact ih _ _ _ (multiply_preserves_curve hn hp hm) h

theorem stageOneFactorial_preserves_curve {n a b bound : Nat} (hn : 1 < n) {p r : ECPoint}
    (hp : PointOnCurve n a b p) (h : stageOneFactorial n a bound p = .point r) :
    PointOnCurve n a b r :=
  stageAux_preserves_curve hn (bound - 1) 2 p r hp h

theorem stageList_preserves_curve {n a b : Nat} (hn : 1 < n) :
    ∀ (multipliers : List Nat) (p r : ECPoint), PointOnCurve n a b p →
      stageList n a multipliers p = .point r → PointOnCurve n a b r := by
  intro multipliers
  induction multipliers with
  | nil =>
      intro p r hp h
      cases Step.point.inj h
      exact hp
  | cons multiplier rest ih =>
      intro p r hp h
      cases p with
      | none =>
          cases Step.point.inj h
          trivial
      | some p =>
          simp only [stageList] at h
          cases hm : multiply n a multiplier (some p) with
          | factor d => simp only [hm] at h; contradiction
          | discard => simp only [hm] at h; contradiction
          | point p' =>
              simp only [hm] at h
              exact ih _ _ (multiply_preserves_curve hn hp hm) h

theorem stageOne_preserves_curve {n a b bound : Nat} (hn : 1 < n) {p r : ECPoint}
    (hp : PointOnCurve n a b p) (h : stageOne n a bound p = .point r) :
    PointOnCurve n a b r :=
  stageList_preserves_curve hn (stageMultipliers bound) p r hp h

end PrimeFactorLean.ECM
