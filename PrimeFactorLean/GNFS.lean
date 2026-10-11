import Std.Data.HashMap
import Std.Data.HashSet
import PrimeFactorLean.NFS.Sieve
import PrimeFactorLean.NFS.Lattice
import PrimeFactorLean.NFS.Las
import PrimeFactorLean.NFS.Sqrt
import PrimeFactorLean.Squares
import PrimeFactorLean.GF2
import PrimeFactorLean.Merge
import PrimeFactorLean.NFS.PolySelect

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

**What is proved.** Every `SquareCongruence` produced here is genuine: the
congruence `X² ≡ Y² (mod n)` is checked modulo `n` when it is created
(`SquareCongruence.ofCheck`), so the extracted factor is a `ProperFactor n` and
`split_sound` holds. The check is also complete: `nfs_square` and
`nfs_square_lin` prove `X² ≡ Y² (mod n)` whenever `f(c_d m) ≡ 0 (mod n)`,
`β · β = γ` in `ℤ[ω]` and `∏ (a - b m) = Y₀²`, using the kernel-checked
multiplicativity of evaluation (`NFS.eval_mulZ`, `NFS.eval_prodTree`), so a
true square root always passes the check. Polynomial selection, sieving, the
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

/-- `∏ eval r [c_d a, -b] ≡ c_d^{|S|} ∏ (a - b x₀)` for an integer `x₀` with `r ≡ c_d x₀`. -/
private theorem prod_map_elt_int {n : Nat} (r : Int) (cd : Nat) (x0 : Int)
    (hr : ModEq n r ((cd : Int) * x0)) (S : List (Int × Int)) :
    ModEq n (prodL (S.map (fun ab => eval r [(cd : Int) * ab.1, -ab.2])))
      ((cd : Int) ^ S.length * prodL (S.map fun ab => ab.1 - ab.2 * x0)) := by
  induction S with
  | nil => exact ModEq.of_eq (by simp [prodL])
  | cons ab rest ih =>
    simp only [List.map_cons, prodL, List.length_cons]
    have he : ModEq n (eval r [(cd : Int) * ab.1, -ab.2]) ((cd : Int) * (ab.1 - ab.2 * x0)) := by
      have := (ModEq.refl n ((cd : Int) * ab.1)).add (hr.mul (ModEq.refl n (-ab.2)))
      refine (ModEq.of_eq ?_).trans (this.trans (ModEq.of_eq ?_))
      · simp only [eval_cons, eval_nil]; grind
      · grind
    refine (he.mul ih).trans (ModEq.of_eq ?_)
    rw [Int.pow_succ]
    grind

/-- `∏ (Y₁ a - m b) ≡ Y₁^{|S|} ∏ (a - b x₀)` when `Y₁ x₀ ≡ m (mod n)`. -/
private theorem prod_lin {n : Nat} (y1 m : Nat) (x0 : Int)
    (hx : ModEq n ((y1 : Int) * x0) (m : Int)) (S : List (Int × Int)) :
    ModEq n (prodL (S.map fun ab => (y1 : Int) * ab.1 - (m : Int) * ab.2))
      ((y1 : Int) ^ S.length * prodL (S.map fun ab => ab.1 - ab.2 * x0)) := by
  induction S with
  | nil => exact ModEq.of_eq (by simp [prodL])
  | cons ab rest ih =>
    simp only [List.map_cons, prodL, List.length_cons]
    have he : ModEq n ((y1 : Int) * ab.1 - (m : Int) * ab.2) ((y1 : Int) * (ab.1 - ab.2 * x0)) := by
      have := (ModEq.refl n ((y1 : Int) * ab.1)).add ((hx.symm.mul (ModEq.refl n ab.2)).neg)
      refine (ModEq.of_eq ?_).trans (this.trans (ModEq.of_eq ?_))
      · grind
      · grind
    refine (he.mul ih).trans (ModEq.of_eq ?_)
    rw [Int.pow_succ]
    grind

/-- **The number field sieve congruence for a rational polynomial `Y₁ x - m`.**
If `f(r) ≡ 0` with `r ≡ c_d x₀` and `Y₁ x₀ ≡ m`, `β² = γ` in `ℤ[ω]` and the
rational product `∏ (Y₁ a - m b)` is the square `Z²`, then
`(φ(β) Y₁^k)² ≡ (φ(f') · c_d^k · Z)² (mod n)` for `|S| = 2k`. With `Y₁ = 1`,
`x₀ = m` this is `nfs_square`. -/
theorem nfs_square_lin {n : Nat} (g fp β : List Int) (cd y1 m : Nat) (x0 : Int)
    (S : List (Int × Int)) (Z : Int) (k : Nat) (r : Int)
    (hroot : ModEq n (eval r g + r ^ g.length) 0)
    (hr : ModEq n r ((cd : Int) * x0)) (hx : ModEq n ((y1 : Int) * x0) (m : Int))
    (hβ : mulZ g β β = prodTree g (fp :: fp :: S.map fun ab => [(cd : Int) * ab.1, -ab.2]))
    (hrat : prodL (S.map fun ab => (y1 : Int) * ab.1 - (m : Int) * ab.2) = Z * Z)
    (hk : S.length = 2 * k) :
    ModEq n ((eval r β * (y1 : Int) ^ k) ^ 2) ((eval r fp * (cd : Int) ^ k * Z) ^ 2) := by
  have h1 : ModEq n ((eval r β) ^ 2) (eval r (mulZ g β β)) :=
    (ModEq.of_eq (by grind)).trans (eval_mulZ r g β β hroot).symm
  rw [hβ] at h1
  have h2 := h1.trans (eval_prodTree r g hroot _)
  simp only [List.map_cons, prodL, List.map_map] at h2
  have hcomp : (S.map (eval r ∘ fun ab => [(cd : Int) * ab.1, -ab.2])) =
      S.map (fun ab => eval r [(cd : Int) * ab.1, -ab.2]) := rfl
  rw [hcomp] at h2
  -- (φ β)² ≡ φ(f')² · c_d^{|S|} · ∏ (a - b x₀)
  have h3 := h2.trans ((ModEq.refl n (eval r fp)).mul ((ModEq.refl n (eval r fp)).mul
    (prod_map_elt_int r cd x0 hr S)))
  -- multiply by Y₁^{|S|}: ∏ (a - b x₀) · Y₁^{|S|} ≡ ∏ (Y₁ a - m b) = Z²
  have h4 := h3.mul (ModEq.refl n ((y1 : Int) ^ S.length))
  have hl := prod_lin y1 m x0 hx S
  rw [hrat] at hl
  refine (ModEq.of_eq ?_).trans (h4.trans ?_)
  · rw [hk, Squares.pow_two_mul]; grind
  · have := (ModEq.refl n (eval r fp * (eval r fp * (cd : Int) ^ S.length))).mul hl.symm
    refine (ModEq.of_eq ?_).trans (this.trans (ModEq.of_eq ?_))
    · grind
    · rw [hk, Squares.pow_two_mul]; grind

/-! ## Run setup with the proved root equation -/

structure Setup (n : Nat) where
  sel : Selection
  g : List Int
  fp : List Int
  cd : Nat
  /-- The common root of `F` and `Y₁ x - m` modulo `n`. -/
  x0 : Nat
  r : Nat
  hn : 0 < n
  hroot : ModEq n (eval (r : Int) g + (r : Int) ^ g.length) 0
  hr : ModEq n (r : Int) ((cd : Int) * (x0 : Int))
  hx : ModEq n ((sel.y1 : Int) * (x0 : Int)) (sel.m : Int)

/-- The run setup: `x₀ = m / Y₁ mod n`, `r = c_d x₀ mod n`, with the root
equation `f(r) ≡ 0` and `Y₁ x₀ ≡ m` checked exactly. -/
def mkSetup (n : Nat) (sel : Selection) : Option (Setup n) :=
  let g := monicLower sel.coeffs
  let cd := sel.lead
  let x0 := match Arith.invMod (sel.y1 % n) n with
    | some inv => sel.m % n * inv % n
    | none => 0
  let r := cd * x0 % n
  if h : 0 < n ∧ evalMod n r (g ++ [1]) = 0 ∧ sel.y1 * x0 % n = sel.m % n then
    some { sel := sel, g := g, fp := derivative g, cd := cd, x0 := x0, r := r, hn := h.1,
           hroot := by
             have hc := evalMod_modEq h.1 r (g ++ [1])
             rw [h.2.1, eval_append_singleton] at hc
             exact (ModEq.of_eq (by grind)).trans (hc.symm.trans (ModEq.of_eq (by simp))),
           hr := (ModEq.natCast_mod (cd * x0) n).trans (ModEq.of_eq (by push_cast; rfl)),
           hx := by
             have h1 := (ModEq.natCast_mod (sel.y1 * x0) n).symm
             have h2 := ModEq.natCast_mod sel.m n
             rw [h.2.2] at h1
             exact (ModEq.of_eq (by push_cast; rfl)).trans (h1.trans h2) }
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

/-- The rational square root modulo `n`: `∏ p^{e/2} mod n` over the rational
factorizations of `rels` (`none` if the sign or an exponent is odd). Untrusted:
`congruence` checks the congruence it leads to. -/
def rationalRootMod (n : Nat) (rels : List Rel) : Option Nat := Id.run do
  let mut exps : Std.HashMap Nat Nat := {}
  let mut neg := 0
  for r in rels do
    if r.ratNeg then neg := neg + 1
    for (p, e) in r.rat do
      exps := exps.insert p (exps.getD p 0 + e)
  if neg % 2 == 1 then return none
  let mut y : Nat := 1 % n
  for (p, e) in exps.toList do
    if e % 2 == 1 then return none
    y := y * powMod p (e / 2) n % n
  return some y

/-- The congruence of squares of a dependency `rels` (`|S| = 2k` pairs `(a, b)`):
`X = φ(β) Y₁^k` for a candidate square root `β` of `γ = f'(ω)² ∏ (c_d a - b ω)`
(`NFS.sqrtFind`) and `Y = φ(f') c_d^k Z` for the rational square root `Z`
modulo `n`. The congruence `X² ≡ Y² (mod n)` itself is checked modulo `n`
(`SquareCongruence.ofCheck`), which is what soundness needs: no exact square in
`ℤ[ω]` or `ℤ` has to be formed or verified. `nfs_square_lin` shows the check
accepts every true square root. -/
def congruence {n : Nat} (st : Setup n) (rels : List Rel) (p : Nat) :
    Option (SquareCongruence n) :=
  let S : List (Int × Int) := rels.map fun r => (r.a, (r.b : Int))
  let k := S.length / 2
  if S.length % 2 == 1 then none else
  match rationalRootMod n rels with
  | none => none
  | some z =>
    let y := evalMod n st.r st.fp * powMod st.cd k n % n * z % n
    let yk := powMod st.sel.y1 k n
    let xOf (β : List Int) : Nat := evalMod n st.r β * yk % n
    let γ := prodTreePar st.g 3 (st.fp :: st.fp :: S.map fun ab => [(st.cd : Int) * ab.1, -ab.2])
    match sqrtFind st.g γ p (fun β => xOf β * xOf β % n == y * y % n) with
    | some β => SquareCongruence.ofCheck n (xOf β) y
    | none => none

/-! ## Matrix construction -/

/-! Column layout: `0` sign of `a - b m`, `1` parity of the relation count,
`2 …` quadratic characters, then rational primes and algebraic ideals as they
occur (large primes included). -/

/-- The Jacobi symbol `(a / n)` for odd `n > 0` (binary algorithm on machine
words): `1`, `-1` or `0`. Used for the quadratic characters (untrusted: a wrong
character only spoils a dependency, which the square root then rejects). -/
def jacobi (a n : UInt64) : Int := go (a % n) n 1 8192
where
  go (a n : UInt64) (t : Int) : Nat → Int
    | 0 => 0
    | fuel + 1 =>
      if a == 0 then (if n == 1 then t else 0)
      else if a &&& 1 == 0 then
        -- a factor 2 of `a` flips the sign when n ≡ ±3 (mod 8) (one shift per
        -- step: `Nat.log2` of the low bit would be a run-time call)
        let r := n % 8
        go (a >>> 1) n (if r == 3 || r == 5 then -t else t) fuel
      else
        -- reciprocity
        let t := if a % 4 == 3 && n % 4 == 3 then -t else t
        go (n % a) a t fuel

/-- Incrementally maintained matrix rows: the odd-exponent ideal columns of each
relation. The factor base has fixed columns (`2 + chars + k` for the rational
prime of index `k`, then the algebraic ideals), found through tables indexed by
the prime; only the large primes beyond it are numbered on first occurrence (a
hash-map lookup per prime of every relation made this a serial bottleneck). The
dense columns (the parity column `1`, the sign `0` and the characters) are added
only when the final matrix is built. -/
structure Rows where
  /-- `ratIdx[p]` is one more than the index of the rational factor-base prime `p`
  (`0`: not in the factor base). -/
  ratIdx : Array Nat := #[]
  /-- `algFirst[p]` is one more than the index of the first algebraic ideal
  above `p`. -/
  algFirst : Array Nat := #[]
  algPrimes : Array Nat := #[]
  algRoots : Array Nat := #[]
  ratBase : Nat := 0
  algBase : Nat := 0
  ratCol : Std.HashMap Nat Nat := {}
  /-- Large ideals `(p, r)` keyed by `2^32 p + r`. -/
  algCol : Std.HashMap Nat Nat := {}
  next : Nat
  sparse : Array (Array Nat) := #[]
  deriving Inhabited

def Rows.empty (fb : FactorBase) : Rows := Id.run do
  let ratLim := fb.ratPrimes.back?.getD 0
  let algLim := fb.algPrimes.back?.getD 0
  let mut ratIdx : Array Nat := Array.replicate (ratLim + 1) 0
  for k in [0:fb.ratPrimes.size] do ratIdx := ratIdx.set! fb.ratPrimes[k]! (k + 1)
  let mut algFirst : Array Nat := Array.replicate (algLim + 1) 0
  for k' in [0:fb.algPrimes.size] do
    let k := fb.algPrimes.size - 1 - k'
    algFirst := algFirst.set! fb.algPrimes[k]! (k + 1)
  let ratBase := 2 + fb.chars.size
  let algBase := ratBase + fb.ratPrimes.size
  return { ratIdx, algFirst, algPrimes := fb.algPrimes, algRoots := fb.algRoots, ratBase, algBase,
           next := algBase + fb.algPrimes.size }

/-- The column of the algebraic factor-base ideal `(p, r)` if it is one. -/
def algColumnOf (algFirst algPrimes algRoots : Array Nat) (algBase p r : Nat) : Option Nat := Id.run do
  let k0 := algFirst.getD p 0
  if k0 == 0 then return none
  let mut k := k0 - 1
  while k < algPrimes.size && algPrimes[k]! == p do
    if algRoots[k]! == r then return some (algBase + k)
    k := k + 1
  return none

def Rows.add (rs : Rows) (rel : Rel) : Rows := Id.run do
  -- every field taken apart once, so that the arrays and maps stay unshared
  let ⟨ratIdx, algFirst, algPrimes, algRoots, ratBase, algBase, ratCol0, algCol0, next0, sparse⟩ := rs
  let mut ratCol := ratCol0
  let mut algCol := algCol0
  let mut next := next0
  let mut row : Array Nat := #[]
  for (p, e) in rel.rat do
    if e % 2 == 1 then
      let k := ratIdx.getD p 0
      if k != 0 then row := row.push (ratBase + k - 1)
      else
        match ratCol.get? p with
        | some c => row := row.push c
        | none =>
          ratCol := ratCol.insert p next
          row := row.push next
          next := next + 1
  for (p, r, e) in rel.alg do
    if e % 2 == 1 then
      match algColumnOf algFirst algPrimes algRoots algBase p r with
      | some c => row := row.push c
      | none =>
        let key := ((p.toUInt64 <<< 32) ||| r.toUInt64).toNat
        match algCol.get? key with
        | some c => row := row.push c
        | none =>
          algCol := algCol.insert key next
          row := row.push next
          next := next + 1
  return ⟨ratIdx, algFirst, algPrimes, algRoots, ratBase, algBase, ratCol, algCol, next,
    sparse.push row⟩

/-- The full row of relation `rel` (with sparse part `sparse`): parity column,
sign, quadratic characters and ideals. -/
def fullRow (fb : FactorBase) (rel : Rel) (sparse : Array Nat) : Array Nat := Id.run do
  let mut row : Array Nat := #[1]
  if rel.ratNeg then row := row.push 0
  for k in [0:fb.chars.size] do
    let (q, s) := fb.chars[k]!
    let x := ((rel.a - (rel.b : Int) * (s : Int)) % (q : Int)).toNat
    if x != 0 && jacobi x.toUInt64 q.toUInt64 == -1 then row := row.push (2 + k)
  return row ++ sparse

def buildRows (fb : FactorBase) (rels : Array Rel) : Array (Array Nat) × Nat := Id.run do
  let mut rs := Rows.empty fb
  for rel in rels do rs := rs.add rel
  let mut rows : Array (Array Nat) := Array.mkEmpty rels.size
  for k in [0:rels.size] do rows := rows.push (fullRow fb rels[k]! rs.sparse[k]!)
  return (rows, rs.next)

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

/-- One parallel round of special-`q` lattice sieving over the next `count`
special-`q` ideals from `st.nextQ`: they are dealt round-robin to twice as many
tasks as threads (so that every task gets a similar mix), and each task keeps
its sieve buffers from one round to the next (`scratch`, consumed and
returned). -/
def collectRoundLas (las : Las.LasCtx) (params : Params) (threads count : Nat) (st : Collection)
    (scratch : List Las.Scratch) : Collection × List Las.Scratch := Id.run do
  let lo := max st.nextQ params.qmin
  let mut qs : Array (Nat × Nat) := #[]
  let mut hi := lo
  while qs.size < count do
    qs := qs ++ specialQsIn las.base.sel hi (hi + 512)
    hi := hi + 512
  -- twice as many tasks as threads: a round waits for its slowest task, and
  -- the pool rebalances smaller tasks
  let T := max 1 (2 * threads)
  let scs := scratch ++ (List.range (T - min T scratch.length)).map fun _ => Las.Scratch.new las
  let tasks := (scs.zip (List.range T)).map fun (sc0, t) =>
    Task.spawn fun _ => Id.run do
      if las.params.variant == 14 then
        let mine := (Array.range ((qs.size + T - 1 - t) / T)).map fun k => qs[t + k * T]!
        return Las.processQs14 las las.params.gapSlack mine sc0
      let mut out : Array Rel := #[]
      let mut sc := sc0
      for k in [0:(qs.size + T - 1 - t) / T] do
        let (q, ρ) := qs[t + k * T]!
        let (rels, sc') := if las.params.variant == 0 then Las.processQWith las q ρ sc
          else if las.params.variant == 11 then Las.processQ11 las q ρ sc
          else if las.params.variant == 12 then Las.processQ12 las q ρ sc
          else if las.params.variant == 13 then Las.processQ13 las las.params.gapSlack q ρ sc
          else Las.processQ10 las las.params.gapSlack q ρ sc
        sc := sc'
        out := out ++ rels
      return (out, sc)
  let results := tasks.map Task.get
  let mut rels := st.rels
  let mut seen := st.seen
  for (batch, _) in results do
    for rel in batch do
      if !seen.contains (rel.a, rel.b) then
        seen := seen.insert (rel.a, rel.b)
        rels := rels.push rel
  return ({ rels := rels, seen := seen, nextB := st.nextB, nextQ := hi }, results.map (·.2))

/-- Whether the matrix has enough excess after singleton removal (on the sparse
rows; the dense columns are accounted for by `dense`). -/
def rowsReady (rs : Rows) (dense extra : Nat) : Bool :=
  let kept := GF2.removeSingletons rs.next rs.sparse
  kept.size ≥ activeColumns rs.next rs.sparse kept + dense + extra

/-- The excess (rows minus active columns and `dense`) after singleton removal,
and whether it reaches `extra`. -/
def rowsExcess (rs : Rows) (dense extra : Nat) : Int × Bool × Nat :=
  let kept := GF2.removeSingletons rs.next rs.sparse
  let e : Int := (kept.size : Int) - (activeColumns rs.next rs.sparse kept + dense : Nat)
  (e, e ≥ extra, kept.size)

/-- Whether the matrix of `rels` has enough excess after singleton removal. -/
def matrixReady (ctx : Ctx) (params : Params) (rels : Array Rel) : Bool :=
  let base := ctx.fb.ratPrimes.size + ctx.fb.algPrimes.size + ctx.fb.chars.size + 2
  if rels.size < base + params.extra then false
  else
    let rs := rels.foldl Rows.add (Rows.empty ctx.fb)
    rowsReady rs (2 + ctx.fb.chars.size) params.extra

/-- Readiness bookkeeping after a check `(excess, ok, kept)` of `size` relations:
whether the matrix is ready, the last measurement (none while nothing survives
singleton removal) and the extrapolated relation target (`0`: none). The target
extrapolates the last two excesses, with a tenth more since the excess grows
faster than linearly. -/
def readiness (extra size : Nat) (prev : Option (Nat × Int)) (chk : Int × Bool × Nat) :
    Bool × Option (Nat × Int) × Nat :=
  let (excess, ok, kept) := chk
  if kept == 0 then (ok, none, 0)
  else
    let target := match prev with
      | some (r0, e0) =>
        if excess > e0 && size > r0 then
          let need := ((extra : Int) - excess) * ((size - r0 : Nat) : Int) / (excess - e0)
          size + (11 * need.toNat) / 10
        else 0
      | none => 0
    (ok, some (size, excess), target)

/-- Sieve until the matrix has a healthy excess of relations, then try dependencies. -/
def splitWith (n : Nat) (sel : Selection) (params : Params) (cfg : Config := {}) :
    Option (ProperFactor n) := Id.run do
  -- with the lattice siever, large primes reach `2^lpb`: the quadratic
  -- characters (chosen above `lpMult · bound`) must lie above them
  let params := if params.lasLogI > 0 then
      { params with lpMult := 2 ^ (max params.lpbR params.lpbA) /
          (min params.ratBound params.algBound) + 1 }
    else params
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
  let lasParams : Las.LasParams :=
    { logI := params.lasLogI, lpbR := params.lpbR, lpbA := params.lpbA, mfbR := params.mfbR,
      mfbA := params.mfbA, fudge := params.lasFudge, variant := params.lasVariant }
  let las := Las.mkLasCtx ctx lasParams
  -- special-q per round: at least six per task, and about a tenth of the
  -- relations collected so far once the yield is known
  let mut count := 8 * threads
  let mut scratch : List Las.Scratch := []
  let mut prev : Option (Nat × Int) := none
  let mut rows := Rows.empty ctx.fb
  let base := ctx.fb.ratPrimes.size + ctx.fb.algPrimes.size + ctx.fb.chars.size + 2
  let dense := 2 + ctx.fb.chars.size
  while !ready && round < cfg.maxRounds do
    round := round + 1
    let before := coll.rels.size
    -- Readiness is a full singleton removal: once the relation count can
    -- suffice and after every tenth of growth, then after every round once an
    -- excess has been measured (it grows fast near the end). Far from ready
    -- (no excess measured yet), the rows of the relations so far are built and
    -- checked in a task while this round sieves; near the end the check
    -- follows the round, since one a round late would oversieve.
    let due := coll.rels.size ≥ base && coll.rels.size * 10 ≥ lastCheck * 11
    let mut bg : Option (Task (Rows × Option (Int × Bool × Nat))) := none
    if prev.isNone && params.lasLogI > 0 then
      let fresh := coll.rels.extract rows.sparse.size coll.rels.size
      let r0 := rows
      rows := default
      bg := some (Task.spawn fun _ =>
        let r := fresh.foldl Rows.add r0
        (r, if due then some (rowsExcess r dense params.extra) else none))
    if params.lasLogI > 0 then
      let (c, sc) := collectRoundLas las params threads count coll scratch
      coll := c
      scratch := sc
    else coll := collectRound ctx params threads coll
    let mut target := 0
    if let some t := bg then
      let (r, chk) := t.get
      rows := r
      if let some c := chk then
        lastCheck := before
        let (ok, p', tg) := readiness params.extra before prev c
        ready := ok
        prev := p'
        target := tg
    -- (far from ready, the next round's task adds this round's rows)
    if bg.isNone then
      for k in [rows.sparse.size:coll.rels.size] do rows := rows.add coll.rels[k]!
    if !ready && bg.isNone && coll.rels.size ≥ base &&
        (prev.isSome || coll.rels.size * 10 ≥ lastCheck * 11) then
      lastCheck := coll.rels.size
      let (ok, p', tg) := readiness params.extra coll.rels.size prev
        (rowsExcess rows dense params.extra)
      ready := ok
      prev := p'
      target := tg
    let gained := coll.rels.size - before
    if params.lasLogI > 0 && gained > 0 then
      count := max (6 * threads) (count * (coll.rels.size / 10 + 1) / gained)
      if target > coll.rels.size then
        count := max (6 * threads) (min count ((target - coll.rels.size) * count / gained + 1))
      else if prev.isSome then
        -- an excess was measured but cannot be extrapolated yet: a short round
        -- (a twenty-fifth of growth) for the second measurement
        count := max (6 * threads) (min count (count * (coll.rels.size / 25 + 1) / gained))
  if !ready then return none
  let rels := coll.rels
  for k in [rows.sparse.size:rels.size] do rows := rows.add rels[k]!
  let numCols := rows.next
  -- filtering on the sparse rows (the dense sign, parity and character columns
  -- that `fullRow` adds are never removed): singletons, then cliques down to
  -- an excess of `purgeExcess`, which beyond that only enlarges the matrix
  let kept := GF2.removeSingletons numCols rows.sparse
  let kept := if params.purgeExcess == 0 then kept
    else Merge.purge numCols dense rows.sparse kept params.purgeExcess
  -- full rows of the survivors only (a Jacobi symbol per character), in
  -- parallel chunks
  let chunk := (kept.size + threads - 1) / threads
  let rowTasks := (List.range threads).map fun t => Task.spawn fun _ =>
    (Array.range (min kept.size ((t + 1) * chunk) - min kept.size (t * chunk))).map fun i =>
      let k := kept[t * chunk + i]!
      fullRow ctx.fb rels[k]! rows.sparse[k]!
  let keptRows := rowTasks.foldl (fun acc tk => acc ++ tk.get) #[]
  -- merge light columns into a smaller, denser matrix
  let (mrows, hist, mcols) := Merge.merge numCols dense keptRows params.mergeDensity 32
  let mdeps := Lanczos.dependencies mcols mrows 64 threads
  let deps := Merge.unmerge kept.size hist mdeps
  let deps := if deps.isEmpty then GF2.dependencies numCols keptRows 64 else deps
  let deps := deps.map fun dep => dep.map fun i => kept[i]!
  -- each dependency splits `n` with probability about 1/2: square roots in
  -- parallel batches of four
  let mut i := 0
  while i < deps.size do
    let batch := (deps.extract i (i + 4)).toList.map fun dep => Task.spawn fun _ =>
      (congruence st (dep.toList.map fun j => rels[j]!) p).bind (·.factor)
    for tk in batch do
      if let some d := tk.get then return some d
    i := i + 4
  return none

/-- The number field sieve with a selected polynomial pair: Kleinjung-style
polynomials (rational side `Y₁ x - m`) for the lattice siever, base-`m`
polynomials for the line sievers. -/
def splitCore (n : Nat) (cfg : Config := {}) : Option (ProperFactor n) :=
  let params := cfg.params.getD (chooseParams (decimalDigits n))
  let sel? := if params.lasLogI > 0 then
      if params.psP > 0 then
        PolySelect.selectCollision n params.degree params.psP params.psNq params.psIncr
          params.psAdMax params.psKeep 16 100000 params.lpbR params.lpbA
          (Float.exp2 (2 * params.lasLogI - 1).toFloat * params.qmin.toFloat) (max 1 cfg.threads)
      else
        PolySelect.select n params.degree params.psAdStep params.psAdCount 2 params.psQlo
          params.psQhi 3 params.psRotV (max 1 cfg.threads)
    else none
  match sel?.orElse fun _ =>
      selectPolynomial n params.degree params.polyTries params.halfWidth params.expectedLines with
  | some sel => splitWith n sel params cfg
  | none => none

/-! ## The special number field sieve

For a divisor `n` of `N = b^k ± 1` the pair `f = b^r x^d ± 1`, `g = x - b^t`
(`k = d t + r`) has `f(b^t) = N ≡ 0 (mod n)`; alternatively `f = x^d ± b^(d-r)`
with `m = b^(t+1)` has `f(m) = b^(d-r) N`. Both coefficients are tiny, so the
norms are those of a number field sieve on a number of about half the digits
of `N`: the parameters are chosen for `7/10` of its digits. The polynomial is
not trusted: `mkSetup` checks `f(m) ≡ 0 (mod n)` like any other. -/

/-- The SNFS pair of degree `d` for `b^k + 1` (`plus`) or `b^k - 1`, with the
smaller leading or constant coefficient. -/
def snfsSelection (b k d : Nat) (plus : Bool) : Selection :=
  let t := k / d
  let r := k % d
  let one : Int := if plus then 1 else -1
  if r ≤ d - r || r == 0 then
    -- b^r x^d ± 1, m = b^t
    let cs : Array Int := ((Array.replicate (d + 1) (0 : Int)).set! d ((b ^ r : Nat) : Int)).set! 0 one
    { coeffs := cs, m := b ^ t }
  else
    -- x^d ± b^(d-r), m = b^(t+1): f(m) = b^(d-r) (b^k ± 1)
    let cs : Array Int := ((Array.replicate (d + 1) (0 : Int)).set! d 1).set! 0
      (one * ((b ^ (d - r) : Nat) : Int))
    { coeffs := cs, m := b ^ (t + 1) }

/-- The degree and parameters of the special number field sieve for `b^k ± 1`
with `digits` decimal digits: degree 4 below 70 digits, 5 below 125, 6 beyond
(degree 5 measured faster from 78 digits: 2^257 - 1 3.9 s -> 3.5 s,
2^293 - 1 20.2 s -> 8.2 s), with the parameters of the general number field
sieve at `7/10` of the digits plus two (at least 60). -/
def snfsParams (digits : Nat) : Params :=
  let d := if digits < 70 then 4 else if digits < 125 then 5 else 6
  { chooseParams (max 60 (7 * digits / 10 + 2)) with degree := d }

/-- The special number field sieve for a divisor `n` of `b^k ± 1`. -/
def splitSNFS (n b k : Nat) (plus : Bool) (cfg : Config := {}) : Option (ProperFactor n) :=
  let params := cfg.params.getD (snfsParams (decimalDigits (b ^ k)))
  splitWith n (snfsSelection b k params.degree plus) params cfg

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
