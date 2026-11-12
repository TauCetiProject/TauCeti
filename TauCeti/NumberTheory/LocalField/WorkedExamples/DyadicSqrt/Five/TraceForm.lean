/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.QuadraticExtension
public import TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.Five.Basic

/-!
# A table of twisted trace forms over `ℚ₂(√5)`

The coefficients `1`, `2 + √5`, `3 + 2√5`, and `16 + 7√5`, and their negatives, give the
following diagonalizations of the forms `y ↦ Tr(a y²)` over `ℚ₂`:

| `a` | `Tr_*⟨a⟩` |
| --- | --- |
| `1` | `⟨2, 10⟩` |
| `2 + √5` | `⟨4, −20⟩` |
| `3 + 2√5` | `⟨6, −30/11⟩` |
| `16 + 7√5` | `⟨32, 160/11⟩` |

Negating `a` negates both diagonal entries. The last positive coefficient is
`(2 + √5)(3 + 2√5)`, so these are precisely the products of subsets of those two
coefficients, with an optional factor `−1`. This table supplies explicit presentations for
computing the discriminants and Stiefel–Whitney classes of their trace transfers.

The diagonalization uses Kahn's orthogonal basis `(1, √5/a)`, through
`TauCeti.equivalent_traceTransfer_smul_sq_weightedSumSquares_of_sq`. Its entries are
`Tr a` and `5 · Tr a / N a`; every coefficient in the table has nonzero trace.

## References

* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations
  galoisiennes réelles*, Invent. Math. 78 (1984), 223–256, Lemme II.2.1 and Théorème 2.
-/

public section

noncomputable section

namespace TauCeti.DyadicSqrtFive

open _root_.QuadraticMap

/-- The diagonal entries of the trace transfers of `1`, `2 + √5`, `3 + 2√5`, and
`16 + 7√5`, in that order. If `negative = true`, both entries are negated. -/
def traceTransferDiagonal (i : Fin 4) (negative : Bool) : Fin 2 → ℚ_[2]ˣ :=
  let w : Fin 4 → Fin 2 → ℚ_[2]ˣ :=
    ![![Units.mk0 2 (by norm_num), Units.mk0 10 (by norm_num)],
      ![Units.mk0 4 (by norm_num), Units.mk0 (-20) (by norm_num)],
      ![Units.mk0 6 (by norm_num), Units.mk0 (-30 / 11) (by norm_num)],
      ![Units.mk0 32 (by norm_num), Units.mk0 (160 / 11) (by norm_num)]]
  if negative then -(w i) else w i

/-- Evaluation of the diagonal table in `ℚ₂`, with an optional simultaneous sign change. -/
@[simp]
theorem coe_traceTransferDiagonal (i : Fin 4) (negative : Bool) (j : Fin 2) :
    (traceTransferDiagonal i negative j : ℚ_[2]) =
      if negative then -(![![2, 10], ![4, -20], ![6, -30 / 11], ![32, 160 / 11]] i j)
      else ![![2, 10], ![4, -20], ![6, -30 / 11], ![32, 160 / 11]] i j := by
  fin_cases i <;> cases negative <;> fin_cases j <;> simp [traceTransferDiagonal]

/-- The eight coefficients obtained from `1`, `2 + √5`, `3 + 2√5`, and `16 + 7√5`,
with either sign, have the trace-transfer diagonalizations in `traceTransferDiagonal`.
The statement applies to the transferred forms themselves, without a chosen presentation. -/
theorem equivalent_traceTransfer_table (a : DyadicSqrtFive) (i : Fin 4) (negative : Bool)
    (ha : a = if negative then -(![1, 2 + sqrtFive, 3 + 2 * sqrtFive,
      16 + 7 * sqrtFive] i) else ![1, 2 + sqrtFive, 3 + 2 * sqrtFive,
      16 + 7 * sqrtFive] i) :
    ((a • QuadraticMap.sq (R := DyadicSqrtFive) (A := DyadicSqrtFive)).traceTransfer
      ℚ_[2]).Equivalent
      (weightedSumSquares ℚ_[2] fun j => (traceTransferDiagonal i negative j : ℚ_[2])) := by
  let u : ℚ_[2] := if negative then -(![1, 2, 3, 16] i) else ![1, 2, 3, 16] i
  let v : ℚ_[2] := if negative then -(![0, 1, 2, 7] i) else ![0, 1, 2, 7] i
  have ha' : a = algebraMap ℚ_[2] DyadicSqrtFive u +
      algebraMap ℚ_[2] DyadicSqrtFive v * sqrtFive := by
    rw [ha]
    fin_cases i <;> cases negative <;> simp [u, v, map_ofNat, add_comm]
  have hx2 : sqrtFive ^ 2 = algebraMap ℚ_[2] DyadicSqrtFive (5 : ℚ_[2]) := by
    simp [map_ofNat]
  have ht : Algebra.trace ℚ_[2] DyadicSqrtFive a = 2 * u := by
    rw [ha', Algebra.IsQuadraticExtension.trace_algebraMap_add_algebraMap_mul_of_sq_eq
      sqrtFive_not_mem hx2]
  have hn : Algebra.norm ℚ_[2] a = u ^ 2 - 5 * v ^ 2 := by
    rw [ha', norm_add_mul_sqrtFive]
  have ht0 : Algebra.trace ℚ_[2] DyadicSqrtFive a ≠ 0 := by
    rw [ht]
    fin_cases i <;> cases negative <;> norm_num [u]
  convert equivalent_traceTransfer_smul_sq_weightedSumSquares_of_sq finrank_eq_two
    sqrtFive_not_mem hx2 ht0 using 2
  ext j
  rw [ht, hn]
  fin_cases i <;> cases negative <;> fin_cases j <;>
    norm_num [u, v]

end TauCeti.DyadicSqrtFive
