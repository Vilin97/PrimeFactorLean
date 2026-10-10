import Std.Data.HashMap
import Std.Data.HashSet
import PrimeFactorLean.NFS.Sieve
import PrimeFactorLean.NFS.Lattice
import PrimeFactorLean.NFS.Las
import PrimeFactorLean.NFS.Sqrt
import PrimeFactorLean.Squares
import PrimeFactorLean.GF2
import PrimeFactorLean.Merge

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

def congruence {n : Nat} (st : Setup n) (rels : List Rel) (p : Nat) :
    Option (SquareCongruence n) :=
  let S : List (Int × Int) := rels.map fun r => (r.a, (r.b : Int))
  let k := S.length / 2
  if hk : S.length = 2 * k then
    match rationalRoot rels with
    | none => none
    | some Z =>
      if hrat : prodL (S.map fun ab => (st.sel.y1 : Int) * ab.1 - (st.sel.m : Int) * ab.2) =
          Z * Z then
        let γ := prodTree st.g (st.fp :: st.fp :: S.map fun ab => [(st.cd : Int) * ab.1, -ab.2])
        match sqrtZ st.g γ p with
        | none => none
        | some β =>
          if hβ : mulZ st.g β β = γ then
            some ⟨evalMod n st.r β * powMod st.sel.y1 k n % n,
              evalMod n st.r st.fp * powMod st.cd k n % n * (Z % (n : Int)).toNat % n, by
                have key := nfs_square_lin st.g st.fp β st.cd st.sel.y1 st.sel.m (st.x0 : Int) S Z k
                  (st.r : Int) st.hroot st.hr st.hx hβ hrat hk
                have hpow (b : Nat) : ModEq n ((powMod b k n : Nat) : Int) ((b : Int) ^ k) := by
                  rw [powMod_eq]
                  exact (ModEq.natCast_mod _ n).trans (ModEq.of_eq (by push_cast; rfl))
                have hxx : ModEq n ((evalMod n st.r β * powMod st.sel.y1 k n % n : Nat) : Int)
                    (eval (st.r : Int) β * (st.sel.y1 : Int) ^ k) := by
                  refine (ModEq.natCast_mod _ n).trans ?_
                  rw [Int.natCast_mul]
                  exact (evalMod_modEq st.hn st.r β).mul (hpow st.sel.y1)
                have hab : ModEq n ((evalMod n st.r st.fp * powMod st.cd k n % n : Nat) : Int)
                    (eval (st.r : Int) st.fp * (st.cd : Int) ^ k) := by
                  refine (ModEq.natCast_mod _ n).trans ?_
                  rw [Int.natCast_mul]
                  exact (evalMod_modEq st.hn st.r st.fp).mul (hpow st.cd)
                have hy : ModEq n
                    ((evalMod n st.r st.fp * powMod st.cd k n % n * (Z % (n : Int)).toNat % n : Nat) : Int)
                    (eval (st.r : Int) st.fp * (st.cd : Int) ^ k * Z) := by
                  refine (ModEq.natCast_mod _ n).trans ?_
                  rw [Int.natCast_mul]
                  exact hab.mul (toNat_emod_modEq st.hn Z)
                exact (hxx.pow 2).trans (key.trans (hy.pow 2).symm)⟩
          else none
      else none
  else none

/-! ## Matrix construction -/

/-! Column layout: `0` sign of `a - b m`, `1` parity of the relation count,
`2 …` quadratic characters, then rational primes and algebraic ideals as they
occur (large primes included). -/

/-- The Jacobi symbol `(a / n)` for odd `n > 0` (binary algorithm on machine
words): `1`, `-1` or `0`. Used for the quadratic characters (untrusted: a wrong
character only spoils a dependency, which the square root then rejects). -/
def jacobi (a n : UInt64) : Int := go (a % n) n 1 128
where
  go (a n : UInt64) (t : Int) : Nat → Int
    | 0 => 0
    | fuel + 1 =>
      if a == 0 then (if n == 1 then t else 0)
      else
        -- remove the factors of 2 of `a`: each flips the sign when n ≡ ±3 (mod 8)
        let tz := (a &&& (-a)).toNat.log2
        let a := a >>> tz.toUInt64
        let r := n % 8
        let t := if tz % 2 == 1 && (r == 3 || r == 5) then -t else t
        -- reciprocity
        let t := if a % 4 == 3 && n % 4 == 3 then -t else t
        go (n % a) a t fuel

/-- Incrementally maintained matrix rows: the odd-exponent ideal columns of each
relation (numbered from `2 + chars` in order of first appearance). The dense
columns (the parity column `1`, the sign `0` and the characters) are added only
when the final matrix is built. -/
structure Rows where
  ratCol : Std.HashMap Nat Nat := {}
  algCol : Std.HashMap (Nat × Nat) Nat := {}
  next : Nat
  sparse : Array (Array Nat) := #[]
  deriving Inhabited

def Rows.empty (fb : FactorBase) : Rows := { next := 2 + fb.chars.size }

def Rows.add (rs : Rows) (rel : Rel) : Rows := Id.run do
  let mut ratCol := rs.ratCol
  let mut algCol := rs.algCol
  let mut next := rs.next
  let mut row : Array Nat := #[]
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
  return { ratCol, algCol, next, sparse := rs.sparse.push row }

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

/-- One parallel round of Franke–Kleinjung lattice sieving over the special-`q`
primes of `[st.nextQ, st.nextQ + threads · width)`: each task takes an
interval of width `width`, finds its special-`q` ideals itself and reuses its
sieve buffers from one special-`q` to the next. -/
def collectRoundLas (las : Las.LasCtx) (params : Params) (threads width : Nat) (st : Collection) :
    Collection := Id.run do
  let lo := max st.nextQ params.qmin
  let tasks := (List.range threads).map fun t =>
    Task.spawn fun _ => Id.run do
      let a := lo + t * width
      let qs := specialQsIn las.base.sel a (a + width)
      let mut out : Array Rel := #[]
      let mut sc := Las.Scratch.new las
      for (q, ρ) in qs do
        let (rels, sc') := Las.processQWith las q ρ sc
        sc := sc'
        out := out ++ rels
      return out
  let batches := tasks.map Task.get
  let mut rels := st.rels
  let mut seen := st.seen
  for batch in batches do
    for rel in batch do
      if !seen.contains (rel.a, rel.b) then
        seen := seen.insert (rel.a, rel.b)
        rels := rels.push rel
  return { rels := rels, seen := seen, nextB := st.nextB, nextQ := lo + threads * width }

/-- Whether the matrix has enough excess after singleton removal (on the sparse
rows; the dense columns are accounted for by `dense`). -/
def rowsReady (rs : Rows) (dense extra : Nat) : Bool :=
  let kept := GF2.removeSingletons rs.next rs.sparse
  kept.size ≥ activeColumns rs.next rs.sparse kept + dense + extra

/-- Whether the matrix of `rels` has enough excess after singleton removal. -/
def matrixReady (ctx : Ctx) (params : Params) (rels : Array Rel) : Bool :=
  let base := ctx.fb.ratPrimes.size + ctx.fb.algPrimes.size + ctx.fb.chars.size + 2
  if rels.size < base + params.extra then false
  else
    let rs := rels.foldl Rows.add (Rows.empty ctx.fb)
    rowsReady rs (2 + ctx.fb.chars.size) params.extra

/-- Sieve until the matrix has a healthy excess of relations, then try dependencies. -/
def splitCore (n : Nat) (cfg : Config := {}) : Option (ProperFactor n) := Id.run do
  let params := cfg.params.getD (chooseParams (decimalDigits n))
  -- with the lattice siever, large primes reach `2^lpb`: the quadratic
  -- characters (chosen above `lpMult · bound`) must lie above them
  let params := if params.lasLogI > 0 then
      { params with lpMult := 2 ^ (max params.lpbR params.lpbA) /
          (min params.ratBound params.algBound) + 1 }
    else params
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
  let lasParams : Las.LasParams :=
    { logI := params.lasLogI, lpbR := params.lpbR, lpbA := params.lpbA, mfbR := params.mfbR,
      mfbA := params.mfbA, fudge := params.lasFudge }
  let las := Las.mkLasCtx ctx lasParams
  -- special-q interval per task: grows with the measured yield so that rounds
  -- stay long (a round waits for its slowest task)
  let mut width := 200
  let mut rows := Rows.empty ctx.fb
  let base := ctx.fb.ratPrimes.size + ctx.fb.algPrimes.size + ctx.fb.chars.size + 2
  while !ready && round < cfg.maxRounds do
    round := round + 1
    let before := coll.rels.size
    coll := if params.lasLogI > 0 then collectRoundLas las params threads width coll
      else collectRound ctx params threads coll
    -- readiness is a full singleton removal: run it only once the relation
    -- count can suffice, and then after every tenth of growth
    for k in [rows.sparse.size:coll.rels.size] do rows := rows.add coll.rels[k]!
    if coll.rels.size ≥ base && coll.rels.size * 10 ≥ lastCheck * 11 then
      lastCheck := coll.rels.size
      ready := rowsReady rows (2 + ctx.fb.chars.size) params.extra
    -- aim the next round at about a fifth of the relations still missing
    let gained := coll.rels.size - before
    if params.lasLogI > 0 && gained > 0 then
      let want := (base + base / 2 - min (base + base / 2) coll.rels.size) / 5
      width := max 100 (min 20000 (width * max 1 want / gained))
  if !ready then return none
  let rels := coll.rels
  for k in [rows.sparse.size:rels.size] do rows := rows.add rels[k]!
  let numCols := rows.next
  let matRows := (Array.range rels.size).map fun k => fullRow ctx.fb rels[k]! rows.sparse[k]!
  -- filtering: merge light columns into a smaller, denser matrix (the sign,
  -- parity and character columns are dense and never eliminated)
  let kept := GF2.removeSingletons numCols matRows
  let (mrows, hist, mcols) := Merge.merge numCols (2 + ctx.fb.chars.size)
    (kept.map fun i => matRows[i]!) params.mergeDensity 32
  let mdeps := Lanczos.dependencies mcols mrows 64 threads
  let deps := (Merge.unmerge kept.size hist mdeps).map fun dep => dep.map fun i => kept[i]!
  let deps := if deps.isEmpty then GF2.dependencies numCols matRows 64 else deps
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
