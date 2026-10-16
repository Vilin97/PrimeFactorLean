import PrimeFactorLean.Arith

/-!
# PRAC programs for ECM stage 1

Stage 1 of ECM multiplies a point by every prime power `p^k ≤ B1`. Along
Montgomery's PRAC Lucas chains (as in GMP-ECM) a multiplication by `p` costs
doublings (5 field operations on `x`-only Montgomery coordinates) and
differential additions with a non-normalized difference (6): 8.9 operations per
bit of `∏ p^k` at `B1 = 50000` and 8.2 at `B1 = 70`, against 10 for the binary
ladder with a normalized base point. The chains depend only on `B1`: they are
computed once, as a byte program that every curve runs (`ECMF.pracRun`,
`SIQS.uecmPrac`).

Opcodes: `0` swaps `A` and `B`; `1 … 9` are the conditions of PRAC; `10` starts
a chain (`B ← A`, `C ← A`, `A ← 2A`) and `11` ends it (`A ← A + B`); `12`
doubles (`p = 2`), `13` triples (`p = 3`); `14 ℓ b₁ … b_ℓ` multiplies by the
number with these bits below its top bit (a prime without a chain; none below
three million). Everything here is untrusted search code.
-/

namespace PrimeFactorLean.Prac

/-- The ten candidate ratios of PRAC (the golden ratio and its neighbours, as in
GMP-ECM). -/
def vals : Array Float := #[0.61803398874989485, 0.72360679774997897,
  0.58017872829546410, 0.63283980608870629, 0.61242994950949500, 0.62018198080741576,
  0.61721461653440386, 0.61834711965622806, 0.61791440652881789, 0.61807966846989581]

/-- One PRAC step on `(d, e)`, `d ≥ e`: the condition taken (`1 … 9`) and the new pair. -/
def step (d e : Nat) : Nat × Nat × Nat :=
  if 4 * d ≤ 5 * e && (d + e) % 3 == 0 then
    let d' := (2 * d - e) / 3
    (1, d', (e - d') / 2)
  else if 4 * d ≤ 5 * e && (d - e) % 6 == 0 then (2, (d - e) / 2, e)
  else if d ≤ 4 * e then (3, d - e, e)
  else if (d + e) % 2 == 0 then (4, (d - e) / 2, e)
  else if d % 2 == 0 then (5, d / 2, e)
  else if d % 3 == 0 then (6, d / 3 - e, e)
  else if (d + e) % 3 == 0 then (7, (d - 2 * e) / 3, e)
  else if (d - e) % 3 == 0 then (8, (d - e) / 3, e)
  else (9, d, e / 2)

/-- Field operations of a condition (6 per addition, 5 per doubling). -/
def cost (k : Nat) : Nat :=
  if k == 1 then 18 else if k == 3 then 6 else if k == 6 || k == 7 || k == 8 then 23 else 11

/-- The start `(d, e) = (n - r, 2r - n)` of the chain for `n` with ratio `v`
(`none` if `r = round(n v)` is out of range). -/
def start (n : Nat) (v : Float) : Option (Nat × Nat) :=
  let r := (n.toFloat * v + 0.5).toUInt64.toNat
  if r ≥ n || 2 * r < n then none else some (n - r, 2 * r - n)

/-- The cost of the chain from `(d, e)` (`c` so far; `none` if it does not reach
`d = e` within its fuel). Tail recursive: no loop state is allocated. -/
def chainCost : Nat → Nat → Nat → Nat → Option Nat
  | 0, _, _, _ => none
  | fuel + 1, d, e, c =>
    if d == e then some c
    else if e == 0 then none
    else
      let (d, e) := if d < e then (e, d) else (d, e)
      let (k, d', e') := step d e
      chainCost fuel d' e' (c + cost k)

/-- The opcodes of the chain from `(d, e)` appended to `out` (`0` a swap, `1 … 9` a
condition). -/
def chainOps : Nat → Nat → Nat → ByteArray → ByteArray
  | 0, _, _, out => out
  | fuel + 1, d, e, out =>
    if d == e || e == 0 then out
    else
      let (d, e, out) := if d < e then (e, d, out.push 0) else (d, e, out)
      let (k, d', e') := step d e
      chainOps fuel d' e' (out.push k.toUInt8)

/-- The stage-1 program for `B1` (one multiplication by `p` per prime power
`p^k ≤ B1`, primes in increasing order). -/
def program (b1 : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for p in Arith.primesUpTo b1 do
    let mut q := p
    while q ≤ b1 do
      if p == 2 then out := out.push 12
      else if p == 3 then out := out.push 13
      else
        let fuel := 4 * p.log2 + 64
        let mut best : Option (Nat × Nat × Nat) := none
        for v in vals do
          if let some (d, e) := start p v then
            if let some c := chainCost fuel d e 11 then
              if best.all (c < ·.1) then best := some (d, c, e)
        match best with
        | some (d, _, e) =>
          out := chainOps fuel d e (out.push 10)
          out := out.push 11
        | none =>
          out := out.push 14
          out := out.push p.log2.toUInt8
          for i in [0:p.log2] do out := out.push (if p.testBit (p.log2 - 1 - i) then 1 else 0)
      q := q * p
  return out

end PrimeFactorLean.Prac
