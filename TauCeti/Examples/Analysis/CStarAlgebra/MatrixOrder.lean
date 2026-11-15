/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MatrixOrder
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
public import TauCeti.Analysis.Matrix.PosSemidef.FinTwo
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# Two-dimensional examples of the spectral order

For the self-adjoint flip matrix `a = [[0,1],[1,0]]`, its positive part is the
rank-one averaging projection `q = [[1/2,1/2],[1/2,1/2]]`. Exact parameter regions
for diagonal matrices above `a` and `q` exhibit the failure of operator monotonicity
of the positive part and of squaring. Square roots remain operator monotone.

All matrices here live in `CStarMatrix (Fin 2) (Fin 2) ℂ`, with its C⋆-norm and
spectral order, rather than the entrywise order or norm.

The positive-part calculation uses Mathlib's `CFC.posPart_negPart_unique`;
the parameter regions use the eigenvalue criterion for positive semidefiniteness.
-/

public section

noncomputable section

open scoped ComplexOrder

namespace TauCeti.MatrixOrderExample

/-- The self-adjoint flip matrix, with eigenvalues `1` and `-1`. -/
def flip : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix !![0, 1; 1, 0]

/-- The orthogonal projection onto the line spanned by `(1,1)`. -/
def averagingProjection : CStarMatrix (Fin 2) (Fin 2) ℂ :=
  CStarMatrix.ofMatrix !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

/-- A real diagonal matrix, regarded as an element of the matrix C⋆-algebra. -/
def diagonal (s t : ℝ) : CStarMatrix (Fin 2) (Fin 2) ℂ :=
  CStarMatrix.ofMatrix (Matrix.diagonal ![(s : ℂ), (t : ℂ)])

/-- Entries of the flip matrix. -/
@[simp]
theorem flip_apply (i j : Fin 2) : flip i j = if i = j then 0 else 1 := by
  fin_cases i <;> fin_cases j <;> simp [flip]

/-- All entries of the averaging projection are one half. -/
@[simp]
theorem averagingProjection_apply (i j : Fin 2) : averagingProjection i j = 1 / 2 := by
  fin_cases i <;> fin_cases j <;> simp [averagingProjection]

/-- Entries of a real diagonal matrix. -/
@[simp]
theorem diagonal_apply (s t : ℝ) (i j : Fin 2) :
    diagonal s t i j = if i = j then ((![s, t] i : ℝ) : ℂ) else 0 := by
  fin_cases i <;> fin_cases j <;> simp [diagonal]

/-- The averaging matrix is a star projection. -/
theorem isStarProjection_averagingProjection : IsStarProjection averagingProjection := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [averagingProjection, CStarMatrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [averagingProjection, CStarMatrix.star_apply]

/-- The positive part of the flip is the averaging projection, rather than the identity. -/
@[simp]
theorem posPart_flip : flip⁺ = averagingProjection := by
  have h : flip = averagingProjection - (1 - averagingProjection) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [flip, averagingProjection]
  exact (CFC.posPart_negPart_unique h
    isStarProjection_averagingProjection.mul_one_sub_self
    isStarProjection_averagingProjection.nonneg
    isStarProjection_averagingProjection.one_sub.nonneg).1

/-- A real diagonal matrix is positive exactly when its two entries are nonnegative. -/
@[simp]
theorem diagonal_nonneg_iff (s t : ℝ) : 0 ≤ diagonal s t ↔ 0 ≤ s ∧ 0 ≤ t := by
  simp [diagonal, CStarMatrix.nonneg_iff_posSemidef, Matrix.posSemidef_diagonal_iff,
    Fin.forall_fin_two]

/-- Squaring a diagonal matrix squares its entries. -/
@[simp]
theorem diagonal_sq (s t : ℝ) : diagonal s t ^ 2 = diagonal (s ^ 2) (t ^ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal, pow_two, CStarMatrix.mul_apply, Fin.sum_univ_two]

/-- The exact region of positive diagonal matrices that dominate the flip. -/
theorem flip_le_diagonal_iff {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    flip ≤ diagonal s t ↔ 1 ≤ s * t := by
  have h : diagonal s t - flip =
      CStarMatrix.ofMatrix !![(s : ℂ), -1; -1, (t : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonal, flip]
  rw [← sub_nonneg, h, CStarMatrix.nonneg_iff_posSemidef,
    Equiv.symm_apply_apply]
  simpa [hs, ht] using (Matrix.posSemidef_fin_two_ofReal_iff (𝕜 := ℂ) s (-1) t)

/-- Both diagonal-minor conditions are necessary for a diagonal matrix to dominate the
averaging projection. The product inequality alone does not characterize this region. -/
theorem averagingProjection_le_diagonal_iff (s t : ℝ) :
    averagingProjection ≤ diagonal s t ↔
      1 / 2 ≤ s ∧ 1 / 2 ≤ t ∧ 1 / 4 ≤ (s - 1 / 2) * (t - 1 / 2) := by
  have h : diagonal s t - averagingProjection = CStarMatrix.ofMatrix
      !![((s - 1 / 2 : ℝ) : ℂ), ((-1 / 2 : ℝ) : ℂ);
        ((-1 / 2 : ℝ) : ℂ), ((t - 1 / 2 : ℝ) : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonal, averagingProjection] <;> ring
  rw [← sub_nonneg, h, CStarMatrix.nonneg_iff_posSemidef, Equiv.symm_apply_apply]
  convert Matrix.posSemidef_fin_two_ofReal_iff (𝕜 := ℂ) (s - 1 / 2) (-1 / 2)
    (t - 1 / 2) using 1
  norm_num

/-- The exact region in which the square of a diagonal matrix dominates the projection. -/
theorem averagingProjection_le_diagonal_sq_iff (s t : ℝ) :
    averagingProjection ≤ diagonal s t ^ 2 ↔
      1 / 2 ≤ s ^ 2 ∧ 1 / 2 ≤ t ^ 2 ∧
        1 / 4 ≤ (s ^ 2 - 1 / 2) * (t ^ 2 - 1 / 2) := by
  rw [diagonal_sq, averagingProjection_le_diagonal_iff]

/-- Taking a square root fixes the averaging projection. -/
@[simp]
theorem sqrt_averagingProjection : CFC.sqrt averagingProjection = averagingProjection :=
  CFC.sqrt_unique isStarProjection_averagingProjection.isIdempotentElem.eq
    isStarProjection_averagingProjection.nonneg

/-- Square roots preserve the order above the averaging projection. -/
theorem averagingProjection_le_sqrt_diagonal {s t : ℝ}
    (h : averagingProjection ≤ diagonal s t) :
    averagingProjection ≤ CFC.sqrt (diagonal s t) := by
  calc averagingProjection = CFC.sqrt averagingProjection := sqrt_averagingProjection.symm
    _ ≤ CFC.sqrt (diagonal s t) := CFC.sqrt_le_sqrt _ _ h

/-- A positive diagonal matrix can dominate the flip without dominating its positive part. -/
theorem flip_le_diagonal_not_posPart :
    flip ≤ diagonal (1 / 2) 3 ∧ ¬flip⁺ ≤ diagonal (1 / 2) 3 := by
  rw [flip_le_diagonal_iff (by norm_num) (by norm_num), posPart_flip,
    averagingProjection_le_diagonal_iff]
  norm_num

/-- Squaring does not preserve the order above a positive projection. -/
theorem averagingProjection_le_diagonal_not_sq :
    averagingProjection ≤ diagonal (5 / 8) 5 ∧
      ¬averagingProjection ^ 2 ≤ diagonal (5 / 8) 5 ^ 2 := by
  rw [isStarProjection_averagingProjection.pow_eq (by decide),
    averagingProjection_le_diagonal_iff, averagingProjection_le_diagonal_sq_iff]
  norm_num

/-- Compression by the first coordinate projection need not decrease a positive matrix. -/
theorem not_compression_averagingProjection_le :
    ¬diagonal 1 0 * averagingProjection * diagonal 1 0 ≤ averagingProjection := by
  have h : averagingProjection - diagonal 1 0 * averagingProjection * diagonal 1 0 =
      CStarMatrix.ofMatrix !![0, 1 / 2; 1 / 2, 1 / 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [diagonal, averagingProjection, CStarMatrix.mul_apply, Fin.sum_univ_two]
  rw [← sub_nonneg, h, CStarMatrix.nonneg_iff_posSemidef, Equiv.symm_apply_apply]
  have hcrit := Matrix.posSemidef_fin_two_ofReal_iff (𝕜 := ℂ) 0 (1 / 2) (1 / 2)
  norm_num at hcrit ⊢
  exact hcrit

end TauCeti.MatrixOrderExample
