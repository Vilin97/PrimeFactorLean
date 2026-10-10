/-!
# A total, verified factorization engine (runtime layer)

Search routines may be incomplete, randomized, or time limited. A successful
split must carry a checked proof that it is a proper divisor. The engine always
terminates and returns a factorization of every positive input; failed searches
fall back to exact trial division (`minFac`). Prime leaves are certified by a
Boolean prime checker whose soundness is a separate theorem.

This file, like every module that the `factor` executable runs, imports only
Lean's core library: proofs that need mathlib (primality of the leaves, the
statement `IsFactorization` with mathlib's `Nat.Prime`) live in
`PrimeFactorLean.Proofs.*` and are stated about these exact definitions.
-/

namespace PrimeFactorLean

/-- A nontrivial divisor, strictly smaller than its input. -/
abbrev ProperFactor (n : Nat) := {d : Nat // 1 < d ∧ d < n ∧ d ∣ n}

/-- A searcher is allowed to give up; every successful result is certified. -/
abbrev Splitter := (n : Nat) → Option (ProperFactor n)

/-- Check an arbitrary proposed factor before trusting a search algorithm. -/
def checkFactor (n d : Nat) : Option (ProperFactor n) :=
  if h : 1 < d ∧ d < n ∧ d ∣ n then some ⟨d, h⟩ else none

/-- Turn any fallible raw divisor search into a certified splitter. -/
def checkedSplitter (search : Nat → Option Nat) : Splitter :=
  fun n => (search n).bind (checkFactor n)

@[simp] theorem checkFactor_some {n d : Nat} (h : 1 < d ∧ d < n ∧ d ∣ n) :
    checkFactor n d = some ⟨d, h⟩ := by simp [checkFactor, h]

@[simp] theorem checkFactor_none {n d : Nat} (h : ¬(1 < d ∧ d < n ∧ d ∣ n)) :
    checkFactor n d = none := by simp [checkFactor, h]

/-! ## Congruences of integers modulo `n` -/

/-- `a ≡ b (mod n)` for integers. -/
def ModEq (n : Nat) (a b : Int) : Prop := (n : Int) ∣ a - b

namespace ModEq

variable {n : Nat} {a b c d : Int}

theorem refl (n : Nat) (a : Int) : ModEq n a a := by
  simp [ModEq]

theorem of_eq (h : a = b) : ModEq n a b := h ▸ refl n a

theorem symm (h : ModEq n a b) : ModEq n b a := by
  unfold ModEq at *
  have : b - a = -(a - b) := by grind
  rw [this]
  exact Int.dvd_neg.mpr h

theorem trans (h1 : ModEq n a b) (h2 : ModEq n b c) : ModEq n a c := by
  unfold ModEq at *
  have : a - c = (a - b) + (b - c) := by grind
  rw [this]
  exact Int.dvd_add h1 h2

theorem add (h1 : ModEq n a b) (h2 : ModEq n c d) : ModEq n (a + c) (b + d) := by
  unfold ModEq at *
  have : a + c - (b + d) = (a - b) + (c - d) := by grind
  rw [this]
  exact Int.dvd_add h1 h2

theorem neg (h : ModEq n a b) : ModEq n (-a) (-b) := by
  unfold ModEq at *
  have : -a - -b = -(a - b) := by grind
  rw [this]
  exact Int.dvd_neg.mpr h

theorem mul (h1 : ModEq n a b) (h2 : ModEq n c d) : ModEq n (a * c) (b * d) := by
  unfold ModEq at *
  have : a * c - b * d = a * (c - d) + d * (a - b) := by grind
  rw [this]
  exact Int.dvd_add (Int.dvd_trans h2 (Int.dvd_mul_left _ _))
    (Int.dvd_trans h1 (Int.dvd_mul_left _ _))

theorem pow (k : Nat) (h : ModEq n a b) : ModEq n (a ^ k) (b ^ k) := by
  induction k with
  | zero => exact refl n 1
  | succ k ih =>
    rw [Int.pow_succ, Int.pow_succ]
    exact ih.mul h

/-- Reduction modulo `n` does not change the class. -/
theorem natCast_mod (a n : Nat) : ModEq n ((a % n : Nat) : Int) (a : Int) := by
  unfold ModEq
  have h := Nat.mod_add_div a n
  refine ⟨-((a / n : Nat) : Int), ?_⟩
  have h' : ((a % n : Nat) : Int) + (n : Int) * ((a / n : Nat) : Int) = (a : Int) := by
    exact_mod_cast h
  grind

theorem zero_of_dvd {x : Int} (h : (n : Int) ∣ x) : ModEq n x 0 := by
  simpa [ModEq] using h

end ModEq

/-! ## Integer square roots -/

/-- Newton iteration from above for `⌊√n⌋` (untrusted; `isqrt` checks it). -/
def sqrtNewton (n : Nat) : Nat := Id.run do
  if n < 2 then return n
  let mut x := 2 ^ (n.log2 / 2 + 1)
  let mut fuel := n.log2 + 8
  while fuel > 0 do
    fuel := fuel - 1
    let y := (x + n / x) / 2
    if y ≥ x then break
    x := y
  return x

/-- Downward linear search: the largest `r ≤ start` with `r * r ≤ n`, provided
`n < (start + 1)²`. Only reached if Newton's iteration were wrong. -/
def sqrtDown (n : Nat) : Nat → Nat
  | 0 => 0
  | r + 1 => if (r + 1) * (r + 1) ≤ n then r + 1 else sqrtDown n r

theorem sqrtDown_spec (n : Nat) : ∀ r, n < (r + 1) * (r + 1) →
    sqrtDown n r * sqrtDown n r ≤ n ∧ n < (sqrtDown n r + 1) * (sqrtDown n r + 1) := by
  intro r
  induction r with
  | zero => intro h; simp [sqrtDown]; omega
  | succ r ih =>
    intro h
    simp only [sqrtDown]
    split
    · exact ⟨by assumption, h⟩
    · exact ih (by omega)

/-- `⌊√n⌋`: Newton's answer, accepted only after checking its defining bounds. -/
def isqrt (n : Nat) : Nat :=
  let r := sqrtNewton n
  if r * r ≤ n ∧ n < (r + 1) * (r + 1) then r else sqrtDown n n

theorem isqrt_spec (n : Nat) : isqrt n * isqrt n ≤ n ∧ n < (isqrt n + 1) * (isqrt n + 1) := by
  unfold isqrt
  dsimp only
  split
  · assumption
  · apply sqrtDown_spec
    have : n ≤ n * n ∨ n = 0 := by
      cases n with
      | zero => exact Or.inr rfl
      | succ k => exact Or.inl (Nat.le_mul_of_pos_left _ (Nat.succ_pos k))
    rcases this with h | h
    · have : n * n < (n + 1) * (n + 1) := Nat.mul_self_lt_mul_self (Nat.lt_succ_self n)
      omega
    · subst h; decide

theorem isqrt_le (n : Nat) : isqrt n * isqrt n ≤ n := (isqrt_spec n).1

theorem lt_succ_isqrt (n : Nat) : n < (isqrt n + 1) * (isqrt n + 1) := (isqrt_spec n).2

/-! ## The least prime factor by trial division -/

/-- Smallest `d' ≥ d` dividing `n`, or `n` once `d² > n` (fuel-bounded). -/
def minFacAux (n d : Nat) : Nat → Nat
  | 0 => n
  | fuel + 1 => if n < d * d then n else if n % d = 0 then d else minFacAux n (d + 1) fuel

/-- The least factor `≥ 2` of `n ≥ 2` (exact trial division). -/
def minFac (n : Nat) : Nat := if n < 2 then n else minFacAux n 2 n

theorem minFacAux_spec (n : Nat) (hn : 2 ≤ n) : ∀ fuel d, 2 ≤ d →
    2 ≤ minFacAux n d fuel ∧ minFacAux n d fuel ∣ n := by
  intro fuel
  induction fuel with
  | zero => intro d _; exact ⟨hn, Nat.dvd_refl n⟩
  | succ fuel ih =>
    intro d hd
    simp only [minFacAux]
    split
    · exact ⟨hn, Nat.dvd_refl n⟩
    · split
      · exact ⟨hd, Nat.dvd_of_mod_eq_zero (by assumption)⟩
      · exact ih (d + 1) (by omega)

theorem minFac_spec {n : Nat} (hn : 2 ≤ n) : 2 ≤ minFac n ∧ minFac n ∣ n := by
  unfold minFac
  rw [if_neg (by omega)]
  exact minFacAux_spec n hn n 2 (Nat.le_refl 2)

theorem minFac_le {n : Nat} (hn : 2 ≤ n) : minFac n ≤ n :=
  Nat.le_of_dvd (by omega) (minFac_spec hn).2

private theorem quotient_lt {n d : Nat} (hn : 0 < n) (hd : 1 < d) :
    n / d < n := Nat.div_lt_self hn hd

/-! ## The engine -/

/-- Search before testing primality: fast methods can split large composites
without paying the cost of exhaustive trial division first. `isPrime` is a
Boolean certificate checker (sound by a separate theorem); when it accepts,
`n` is a leaf. -/
def factorCoreWith (isPrime : Nat → Bool) (splitter : Splitter) (n : Nat) : List Nat :=
  if _hn : n ≤ 1 then []
  else
    if isPrime n then [n]
    else
      match splitter n with
      | some d => factorCoreWith isPrime splitter d.val ++ factorCoreWith isPrime splitter (n / d.val)
      | none =>
        let p := minFac n
        if p = n then [n]
        else p :: factorCoreWith isPrime splitter (n / p)
termination_by n
decreasing_by
  · exact d.property.2.1
  · exact quotient_lt (by omega) d.property.1
  · exact quotient_lt (by omega) (by have := (minFac_spec (n := n) (by omega)).1; omega)

/-- The basic engine uses exact trial division when no divisor search succeeds. -/
abbrev factorCore (splitter : Splitter) (n : Nat) : List Nat :=
  factorCoreWith (fun _ => false) splitter n

/-- Zero has no finite factorization into primes; represent this explicitly. -/
def factorNat (splitter : Splitter) (n : Nat) : Option (List Nat) :=
  if n = 0 then none else some (factorCore splitter n)

@[simp] theorem factorNat_zero (splitter : Splitter) : factorNat splitter 0 = none := by
  simp [factorNat]

/-- Signed integer factorization. The sign is a unit; factors are positive primes. -/
def factorInt (splitter : Splitter) (z : Int) : Option (Int × List Nat) :=
  (factorNat splitter z.natAbs).map fun factors => (z.sign, factors)

end PrimeFactorLean
