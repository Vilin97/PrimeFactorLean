import Std.Data.HashMap
import Std.Data.HashSet
import PrimeFactorLean.NFS.Sieve
import PrimeFactorLean.NFS.Lattice
import PrimeFactorLean.NFS.Sqrt
import PrimeFactorLean.Squares
import PrimeFactorLean.GF2

/-!
# The general number field sieve

The asymptotically fastest known general-purpose factoring algorithm
(Pollard; Buhler–Lenstra–Pomerance; Lenstra–Lenstra–Manasse–Pollard), with
heuristic running time `L_n[1/3, (64/9)^{1/3}]`.

Pipeline (each stage in `PrimeFactorLean.NFS.*`):

1. **Polynomial selection**: `F` of degree `d` with `F(m) = n` (base `m`).
2. **Factor bases** of rational primes, algebraic prime ideals `(p, r)` and
   quadratic characters.
3. **Line sieving** for coprime `(a, b)` with `a - b m` and `F(a, b)` smooth
   (one large prime per side).
4. **Linear algebra** over GF(2) (`GF2.dependencies`) on columns for the sign,
   the parity of the number of relations, the characters, rational primes and
   algebraic ideals.
5. **Square roots**: the rational square root `Y₀` of `∏ (a - b m)` and the
   algebraic square root `β` of `γ = f'(ω)² ∏ (c_d a - b ω)` in `ℤ[ω]`, where
   `f(y) = c_d^{d-1} F(y / c_d)` is monic and `ω = c_d α` (`NFS.sqrtZ`).
6. `X = φ(β)`, `Y = f'(c_d m) · c_d^{|S|/2} · Y₀` with `φ(ω) = c_d m mod n`.

**What is proved.** `nfs_square` proves `X² ≡ Y² (mod n)` from three facts that
are checked at run time on exact integers: `f(c_d m) ≡ 0 (mod n)`,
`β · β = γ` in `ℤ[ω]` (list equality after the executable multiplication),
and `∏ (a - b m) = Y₀²`. It uses the kernel-checked multiplicativity of
evaluation (`NFS.eval_mulZ`, `NFS.eval_prodTree`). Hence every
`SquareCongruence` produced here is genuine, the extracted factor is a
`ProperFactor n`, and `split_sound` holds. Polynomial selection, sieving, the
GF(2) solver and the `p`-adic square-root search are untrusted.
-/

namespace PrimeFactorLean.GNFS

open Arith NFS Squares

/-! ## The congruence of squares -/

private theorem prod_map_elt {n : Nat} (r : Int) (cd m : Nat)
    (hr : ModEq n r ((cd : Int) * (m : Int))) (S : List (Int × Int)) :
    ModEq n (prodL (S.map (fun ab => eval r [(cd : Int) * ab.1, -ab.2])))
      ((cd : Int) ^ S.length * prodL (S.map fun ab => ab.1 - ab.2 * (m : Int))) := by
  induction S with
  | nil => exact ModEq.of_eq (by simp [prodL])
  | cons ab rest ih =>
    simp only [List.map_cons, prodL, List.length_cons]
    have he : ModEq n (eval r [(cd : Int) * ab.1, -ab.2])
        ((cd : Int) * (ab.1 - ab.2 * (m : Int))) := by
      have := (ModEq.refl n ((cd : Int) * ab.1)).add (hr.mul (ModEq.refl n (-ab.2)))
      refine (ModEq.of_eq ?_).trans (this.trans (ModEq.of_eq ?_))
      · simp only [eval_cons, eval_nil]; grind
      · grind
    refine (he.mul ih).trans (ModEq.of_eq ?_)
    rw [Int.pow_succ]
    grind

/-- **The number field sieve congruence.** If `f(r) ≡ 0` with `r ≡ c_d m`,
`β² = γ` in `ℤ[ω]` and the rational product is the square `Y₀²`, then
`φ(β)² ≡ (φ(f') · c_d^k · Y₀)² (mod n)` for `|S| = 2k`. -/
theorem nfs_square {n : Nat} (g fp β : List Int) (cd m : Nat) (S : List (Int × Int))
    (Y0 : Int) (k : Nat) (r : Int) (hroot : ModEq n (eval r g + r ^ g.length) 0)
    (hr : ModEq n r ((cd : Int) * (m : Int)))
    (hβ : mulZ g β β = prodTree g (fp :: fp :: S.map fun ab => [(cd : Int) * ab.1, -ab.2]))
    (hrat : prodL (S.map fun ab => ab.1 - ab.2 * (m : Int)) = Y0 * Y0)
    (hk : S.length = 2 * k) :
    ModEq n ((eval r β) ^ 2) ((eval r fp * (cd : Int) ^ k * Y0) ^ 2) := by
  have h1 : ModEq n ((eval r β) ^ 2) (eval r (mulZ g β β)) :=
    (ModEq.of_eq (by grind)).trans (eval_mulZ r g β β hroot).symm
  rw [hβ] at h1
  refine h1.trans ((eval_prodTree r g hroot _).trans ?_)
  simp only [List.map_cons, prodL, List.map_map]
  have hcomp : (S.map (eval r ∘ fun ab => [(cd : Int) * ab.1, -ab.2])) =
      S.map (fun ab => eval r [(cd : Int) * ab.1, -ab.2]) := rfl
  rw [hcomp]
  refine ((ModEq.refl n (eval r fp)).mul ((ModEq.refl n (eval r fp)).mul
    (prod_map_elt r cd m hr S))).trans (ModEq.of_eq ?_)
  rw [hrat, hk, Squares.pow_two_mul]
  grind

/-! ## Run setup with the proved root equation -/

structure Setup (n : Nat) where
  sel : Selection
  g : List Int
  fp : List Int
  cd : Nat
  r : Nat
  hn : 0 < n
  hroot : ModEq n (eval (r : Int) g + (r : Int) ^ g.length) 0
  hr : ModEq n (r : Int) ((cd : Int) * (sel.m : Int))

def mkSetup (n : Nat) (sel : Selection) : Option (Setup n) :=
  let g := monicLower sel.coeffs
  let cd := sel.lead
  let r := cd * sel.m % n
  if h : 0 < n ∧ evalMod n r (g ++ [1]) = 0 then
    some { sel := sel, g := g, fp := derivative g, cd := cd, r := r, hn := h.1,
           hroot := by
             have hc := evalMod_modEq h.1 r (g ++ [1])
             rw [h.2, eval_append_singleton] at hc
             exact (ModEq.of_eq (by grind)).trans (hc.symm.trans (ModEq.of_eq (by simp))),
           hr := (ModEq.natCast_mod (cd * sel.m) n).trans (ModEq.of_eq (by push_cast; rfl)) }
  else none

/-! ## From a dependency to a congruence of squares -/

/-- Square root of the rational product from the exponent multiset (untrusted;
`congruence` checks the result exactly). -/
def rationalRoot (rels : List Rel) : Option Int := Id.run do
  let mut exps : Std.HashMap Nat Nat := {}
  let mut neg := 0
  for r in rels do
    if r.ratNeg then neg := neg + 1
    for (p, e) in r.rat do
      exps := exps.insert p (exps.getD p 0 + e)
  if neg % 2 == 1 then return none
  let mut y : Int := 1
  for (p, e) in exps.toList do
    if e % 2 == 1 then return none
    y := y * (p : Int) ^ (e / 2)
  return some y

def congruence {n : Nat} (st : Setup n) (rels : List Rel) (p : Nat) :
    Option (SquareCongruence n) :=
  let S : List (Int × Int) := rels.map fun r => (r.a, (r.b : Int))
  let k := S.length / 2
  if hk : S.length = 2 * k then
    match rationalRoot rels with
    | none => none
    | some Y0 =>
      if hrat : prodL (S.map fun ab => ab.1 - ab.2 * (st.sel.m : Int)) = Y0 * Y0 then
        let γ := prodTree st.g (st.fp :: st.fp :: S.map fun ab => [(st.cd : Int) * ab.1, -ab.2])
        match sqrtZ st.g γ p with
        | none => none
        | some β =>
          if hβ : mulZ st.g β β = γ then
            some ⟨evalMod n st.r β,
              evalMod n st.r st.fp * powMod st.cd k n % n * (Y0 % (n : Int)).toNat % n, by
                have key := nfs_square st.g st.fp β st.cd st.sel.m S Y0 k (st.r : Int)
                  st.hroot st.hr hβ hrat hk
                have hx := (evalMod_modEq st.hn st.r β).pow 2
                have hpow : ModEq n ((powMod st.cd k n : Nat) : Int) ((st.cd : Int) ^ k) := by
                  rw [powMod_eq]
                  exact (ModEq.natCast_mod _ n).trans (ModEq.of_eq (by push_cast; rfl))
                have hab : ModEq n ((evalMod n st.r st.fp * powMod st.cd k n % n : Nat) : Int)
                    (eval (st.r : Int) st.fp * (st.cd : Int) ^ k) := by
                  refine (ModEq.natCast_mod _ n).trans ?_
                  rw [Int.natCast_mul]
                  exact (evalMod_modEq st.hn st.r st.fp).mul hpow
                have hy : ModEq n
                    ((evalMod n st.r st.fp * powMod st.cd k n % n * (Y0 % (n : Int)).toNat % n : Nat) : Int)
                    (eval (st.r : Int) st.fp * (st.cd : Int) ^ k * Y0) := by
                  refine (ModEq.natCast_mod _ n).trans ?_
                  rw [Int.natCast_mul]
                  exact hab.mul (toNat_emod_modEq st.hn Y0)
                exact hx.trans (key.trans (hy.pow 2).symm)⟩
          else none
      else none
  else none

/-! ## Matrix construction -/

/-- Column layout: `0` sign of `a - b m`, `1` parity of the relation count,
`2 …` quadratic characters, then rational primes and algebraic ideals as they
occur (large primes included). -/
def buildRows (fb : FactorBase) (rels : Array Rel) : Array (Array Nat) × Nat := Id.run do
  let mut ratCol : Std.HashMap Nat Nat := {}
  let mut algCol : Std.HashMap (Nat × Nat) Nat := {}
  let mut next := 2 + fb.chars.size
  let mut rows : Array (Array Nat) := Array.mkEmpty rels.size
  for rel in rels do
    let mut row : Array Nat := #[1]
    if rel.ratNeg then row := row.push 0
    for k in [0:fb.chars.size] do
      let (q, s) := fb.chars[k]!
      let x := ((rel.a - (rel.b : Int) * (s : Int)) % (q : Int)).toNat
      if x != 0 && powMod x ((q - 1) / 2) q == q - 1 then row := row.push (2 + k)
    for (p, e) in rel.rat do
      if e % 2 == 1 then
        match ratCol.get? p with
        | some c => row := row.push c
        | none =>
          ratCol := ratCol.insert p next
          row := row.push next
          next := next + 1
    for (p, r, e) in rel.alg do
      if e % 2 == 1 then
        match algCol.get? (p, r) with
        | some c => row := row.push c
        | none =>
          algCol := algCol.insert (p, r) next
          row := row.push next
          next := next + 1
    rows := rows.push row
  return (rows, next)

/-- Number of distinct columns used by the surviving rows. -/
def activeColumns (numCols : Nat) (rows : Array (Array Nat)) (kept : Array Nat) : Nat := Id.run do
  let mut used : Array Bool := Array.replicate numCols false
  let mut count := 0
  for i in kept do
    for c in rows[i]! do
      if c < numCols && !used[c]! then
        used := used.set! c true
        count := count + 1
  return count

/-! ## Driver -/

structure Config where
  threads : Nat := 8
  params : Option Params := none
  /-- Collection rounds before giving up (each round is `threads` tasks). -/
  maxRounds : Nat := 3000
  deriving Inhabited

def decimalDigits (n : Nat) : Nat := (toString n).length

/-- Relation collection state. -/
structure Collection where
  rels : Array Rel := #[]
  seen : Std.HashSet (Int × Nat) := {}
  nextB : Nat := 1
  nextQ : Nat := 0
  deriving Inhabited

/-- One parallel round of line sieving or special-`q` lattice sieving. -/
def collectRound (ctx : Ctx) (params : Params) (threads : Nat) (st : Collection) :
    Collection := Id.run do
  let mut st := st
  let batches : List (Array Rel) :=
    if params.latticeI == 0 then
      let start := st.nextB
      let lines := params.linesPerTask
      let tasks := (List.range threads).map fun t =>
        Task.spawn fun _ => sieveLines ctx (start + t * lines) lines
      tasks.map Task.get
    else
      let qs := specialQs ctx.sel (max st.nextQ params.algBound) (threads * params.qPerTask)
      let skew := skewness ctx.sel
      let tasks := (List.range threads).map fun t =>
        Task.spawn fun _ => Id.run do
          let mut out : Array Rel := #[]
          for k in [t * params.qPerTask:(t + 1) * params.qPerTask] do
            if h : k < qs.size then
              let (q, ρ) := qs[k]
              out := out ++ sieveSpecialQ ctx q ρ params.latticeI params.latticeJ skew
          return out
      tasks.map Task.get
  if params.latticeI == 0 then
    st := { st with nextB := st.nextB + threads * params.linesPerTask }
  else
    let qs := specialQs ctx.sel (max st.nextQ params.algBound) (threads * params.qPerTask)
    st := { st with nextQ := (qs.back?.map (·.1)).getD st.nextQ }
  -- Update the containers through local variables so each stays uniquely
  -- referenced (a structure update would copy them on every insertion).
  let mut rels := st.rels
  let mut seen := st.seen
  st := { st with rels := #[], seen := {} }
  for batch in batches do
    for rel in batch do
      if !seen.contains (rel.a, rel.b) then
        seen := seen.insert (rel.a, rel.b)
        rels := rels.push rel
  return { st with rels := rels, seen := seen }

/-- Whether the matrix has enough excess after singleton removal. -/
def matrixReady (ctx : Ctx) (params : Params) (rels : Array Rel) : Bool :=
  let base := ctx.fb.ratPrimes.size + ctx.fb.algPrimes.size + ctx.fb.chars.size + 2
  if rels.size < base + params.extra then false
  else
    let (rows, numCols) := buildRows ctx.fb rels
    let kept := GF2.removeSingletons numCols rows
    kept.size ≥ activeColumns numCols rows kept + params.extra

/-- Sieve until the matrix has a healthy excess of relations, then try dependencies. -/
def splitCore (n : Nat) (cfg : Config := {}) : Option (ProperFactor n) := Id.run do
  let params := cfg.params.getD (chooseParams (decimalDigits n))
  let some sel := selectPolynomial n params.degree params.polyTries params.halfWidth
    params.expectedLines | return none
  let some st := mkSetup n sel | return none
  let ctx := mkCtx n sel params
  -- A factor-base prime dividing n is a factor.
  for q in ctx.fb.ratPrimes do
    if n % q == 0 && q < n then return checkFactor n q
  let some p := inertPrime st.g 1000003 | return none
  let threads := max 1 cfg.threads
  let mut coll : Collection := {}
  let mut round := 0
  let mut ready := false
  -- The readiness test rebuilds the matrix (single-threaded), so it runs only
  -- after the relation count has grown by a tenth since the previous test.
  let mut lastCheck := 0
  while !ready && round < cfg.maxRounds do
    round := round + 1
    coll := collectRound ctx params threads coll
    if coll.rels.size * 10 ≥ lastCheck * 11 then
      lastCheck := coll.rels.size
      ready := matrixReady ctx params coll.rels
  if !ready then return none
  let rels := coll.rels
  let (rows, numCols) := buildRows ctx.fb rels
  let deps := GF2.dependencies numCols rows 64
  for dep in deps do
    match congruence st (dep.toList.map fun i => rels[i]!) p with
    | none => continue
    | some sc =>
      match sc.factor with
      | some d => return some d
      | none => continue
  return none

/-- The public splitter: even numbers and perfect powers are handled first. -/
def split (n : Nat) (cfg : Config := {}) : Option (ProperFactor n) :=
  if n < 1000 then none
  else if n % 2 = 0 then checkFactor n 2
  else match perfectPower n with
    | some (r, _) => checkFactor n r
    | none => splitCore n cfg

/-- Every factor returned by the number field sieve is a proper divisor. -/
theorem split_sound {n : Nat} {cfg : Config} {d : ProperFactor n}
    (_h : split n cfg = some d) : 1 < d.val ∧ d.val < n ∧ d.val ∣ n := d.property

end PrimeFactorLean.GNFS
