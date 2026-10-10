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
      -- products by balanced trees, the top levels in parallel (`prodL` and
      -- `prodTree` are what the congruence theorem speaks about)
      if hrat0 : prodTreeInt 3 (S.map fun ab => (st.sel.y1 : Int) * ab.1 - (st.sel.m : Int) * ab.2) =
          Z * Z then
        have hrat := (prodTreeInt_eq 3 _).symm.trans hrat0
        let γ := prodTreePar st.g 3 (st.fp :: st.fp :: S.map fun ab => [(st.cd : Int) * ab.1, -ab.2])
        match sqrtZ st.g γ p with
        | none => none
        | some ⟨β, hβ0⟩ =>
          if hγ : normalize γ = γ then
            have hβ := hβ0.trans (hγ.trans (prodTreePar_eq _ _ _))
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

/-- One parallel round of special-`q` lattice sieving over the next `count`
special-`q` ideals from `st.nextQ`: they are dealt round-robin to the tasks (so
that every task gets a similar mix), and each task keeps its sieve buffers
from one round to the next (`scratch`, consumed and returned). -/
def collectRoundLas (las : Las.LasCtx) (params : Params) (threads count : Nat) (st : Collection)
    (scratch : List Las.Scratch) : Collection × List Las.Scratch := Id.run do
  let lo := max st.nextQ params.qmin
  let mut qs : Array (Nat × Nat) := #[]
  let mut hi := lo
  while qs.size < count do
    qs := qs ++ specialQsIn las.base.sel hi (hi + 512)
    hi := hi + 512
  let T := max 1 threads
  let scs := scratch ++ (List.range (T - min T scratch.length)).map fun _ => Las.Scratch.new las
  let tasks := (scs.zip (List.range T)).map fun (sc0, t) =>
    Task.spawn fun _ => Id.run do
      let mut out : Array Rel := #[]
      let mut sc := sc0
      for k in [0:(qs.size + T - 1 - t) / T] do
        let (q, ρ) := qs[t + k * T]!
        let (rels, sc') := Las.processQWith las q ρ sc
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
      mfbA := params.mfbA, fudge := params.lasFudge }
  let las := Las.mkLasCtx ctx lasParams
  -- special-q per round: at least six per task, and about a tenth of the
  -- relations collected so far once the yield is known
  let mut count := 8 * threads
  let mut scratch : List Las.Scratch := []
  let mut prev : Option (Nat × Int) := none
  let mut rows := Rows.empty ctx.fb
  let base := ctx.fb.ratPrimes.size + ctx.fb.algPrimes.size + ctx.fb.chars.size + 2
  while !ready && round < cfg.maxRounds do
    round := round + 1
    let before := coll.rels.size
    if params.lasLogI > 0 then
      let (c, sc) := collectRoundLas las params threads count coll scratch
      coll := c
      scratch := sc
    else coll := collectRound ctx params threads coll
    -- readiness is a full singleton removal: run it once the relation count
    -- can suffice and after every tenth of growth, then after every round once
    -- an excess has been measured (it grows fast near the end)
    for k in [rows.sparse.size:coll.rels.size] do rows := rows.add coll.rels[k]!
    let mut target := 0
    if coll.rels.size ≥ base && (prev.isSome || coll.rels.size * 10 ≥ lastCheck * 11) then
      lastCheck := coll.rels.size
      let (excess, ok, kept) := rowsExcess rows (2 + ctx.fb.chars.size) params.extra
      ready := ok
      if kept == 0 then
        -- nothing survives singleton removal yet: far from ready, check again
        -- after two fifths more relations
        prev := none
        lastCheck := coll.rels.size * 14 / 11
      else
        -- the relations still needed, extrapolated from the last two checks
        -- (with a tenth more: the excess grows faster than linearly)
        if let some (r0, e0) := prev then
          if excess > e0 && coll.rels.size > r0 then
            let need := ((params.extra : Int) - excess) * ((coll.rels.size - r0 : Nat) : Int) /
              (excess - e0)
            target := coll.rels.size + (11 * need.toNat) / 10
        prev := some (coll.rels.size, excess)
    let gained := coll.rels.size - before
    if params.lasLogI > 0 && gained > 0 then
      count := max (6 * threads) (count * (coll.rels.size / 10 + 1) / gained)
      if target > coll.rels.size then
        count := max (6 * threads) (min count ((target - coll.rels.size) * count / gained + 1))
  if !ready then return none
  let rels := coll.rels
  for k in [rows.sparse.size:rels.size] do rows := rows.add rels[k]!
  let numCols := rows.next
  -- the character columns cost a Jacobi symbol each: rows in parallel chunks
  let chunk := (rels.size + threads - 1) / threads
  let rowTasks := (List.range threads).map fun t => Task.spawn fun _ =>
    (Array.range (min rels.size ((t + 1) * chunk) - min rels.size (t * chunk))).map fun i =>
      let k := t * chunk + i
      fullRow ctx.fb rels[k]! rows.sparse[k]!
  let matRows := rowTasks.foldl (fun acc tk => acc ++ tk.get) #[]
  -- filtering: merge light columns into a smaller, denser matrix (the sign,
  -- parity and character columns are dense and never eliminated)
  let kept := GF2.removeSingletons numCols matRows
  let (mrows, hist, mcols) := Merge.merge numCols (2 + ctx.fb.chars.size)
    (kept.map fun i => matRows[i]!) params.mergeDensity 32
  let mdeps := Lanczos.dependencies mcols mrows 64 threads
  let deps := (Merge.unmerge kept.size hist mdeps).map fun dep => dep.map fun i => kept[i]!
  let deps := if deps.isEmpty then GF2.dependencies numCols matRows 64 else deps
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

/-- The special number field sieve for a divisor `n` of `b^k ± 1`: degree 4
below 90 digits of `b^k`, 5 below 125, 6 beyond; parameters of the general
number field sieve at `7/10` of the digits (at least 60), with that degree. -/
def splitSNFS (n b k : Nat) (plus : Bool) (cfg : Config := {}) : Option (ProperFactor n) :=
  let digits := decimalDigits (b ^ k)
  let d := if digits < 90 then 4 else if digits < 125 then 5 else 6
  let params := { (cfg.params.getD (chooseParams (max 60 (7 * digits / 10)))) with degree := d }
  splitWith n (snfsSelection b k d plus) params cfg

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
