/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Matrix.Order
public import TauCeti.LinearAlgebra.Matrix.PosSemidef

/-!
# Kernel and range constraints for positive-semidefinite block matrices

For a positive-semidefinite matrix `S` on a sum of two finite coordinate types, the kernel of
each diagonal block is contained in the kernel of the off-diagonal block in the same column.
Dually, the range of each off-diagonal block is contained in the range of the diagonal block
in the same row. These constraints allow singular covariance blocks in Schur complements
and Gaussian conditioning.

The kernel and range statements use `Matrix.toEuclideanLin` and apply over both real and
complex scalars. All statements include zero blocks and empty coordinate types.

A block diagonal matrix `fromBlocks A 0 0 D` is positive semidefinite exactly when both of its
diagonal blocks are, `Matrix.posSemidef_fromBlocks_zero₁₂_zero₂₁_iff`; this holds over any
partially ordered star ring. Hence, in the Loewner order, two block matrices with the same
off-diagonal blocks compare exactly when their diagonal blocks do,
`Matrix.fromBlocks_le_fromBlocks_iff`.

## References

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., 2003,
  Chapter 2 (partitioned covariance matrices and conditional Gaussian distributions).
-/

public section

open Matrix
open scoped ComplexOrder

namespace Matrix.PosSemidef

variable {ι κ 𝕜 : Type*} [RCLike 𝕜] {S : Matrix (ι ⊕ κ) (ι ⊕ κ) 𝕜}

/-- In a positive-semidefinite block matrix, the kernel of the lower-right block is
contained in the kernel of the upper-right block. No invertibility is required. -/
theorem ker_toEuclideanLin_toBlocks₂₂_le [Fintype κ] [DecidableEq κ]
    (hS : S.PosSemidef) :
    LinearMap.ker S.toBlocks₂₂.toEuclideanLin ≤ LinearMap.ker S.toBlocks₁₂.toEuclideanLin := by
  intro x hx
  simp only [LinearMap.mem_ker, toEuclideanLin, toLpLin_apply, WithLp.toLp_eq_zero] at hx ⊢
  exact hS.toBlocks₁₂_mulVec_eq_zero hx

/-- In a positive-semidefinite block matrix, the kernel of the upper-left block is
contained in the kernel of the lower-left block. -/
theorem ker_toEuclideanLin_toBlocks₁₁_le [Fintype ι] [DecidableEq ι]
    (hS : S.PosSemidef) :
    LinearMap.ker S.toBlocks₁₁.toEuclideanLin ≤ LinearMap.ker S.toBlocks₂₁.toEuclideanLin := by
  intro x hx
  simp only [LinearMap.mem_ker, toEuclideanLin, toLpLin_apply, WithLp.toLp_eq_zero] at hx ⊢
  exact hS.toBlocks₂₁_mulVec_eq_zero hx

/-- In a positive-semidefinite block matrix, the range of the lower-left block is
contained in the range of the lower-right block, including when that block is singular. -/
theorem range_toEuclideanLin_toBlocks₂₁_le [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (hS : S.PosSemidef) :
    LinearMap.range S.toBlocks₂₁.toEuclideanLin ≤ LinearMap.range S.toBlocks₂₂.toEuclideanLin := by
  have hD : S.toBlocks₂₂.IsHermitian := hS.isHermitian.submatrix Sum.inr
  have hB : S.toBlocks₁₂ᴴ = S.toBlocks₂₁ := by
    ext i j
    exact hS.isHermitian.apply _ _
  -- Taking orthogonal complements reverses the kernel inclusion; adjoints exchange the blocks.
  simpa only [LinearMap.orthogonal_ker, ← toEuclideanLin_conjTranspose_eq_adjoint,
    hD.eq, hB] using Submodule.orthogonal_le hS.ker_toEuclideanLin_toBlocks₂₂_le

/-- In a positive-semidefinite block matrix, the range of the upper-right block is
contained in the range of the upper-left block. -/
theorem range_toEuclideanLin_toBlocks₁₂_le [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (hS : S.PosSemidef) :
    LinearMap.range S.toBlocks₁₂.toEuclideanLin ≤ LinearMap.range S.toBlocks₁₁.toEuclideanLin := by
  have h := (hS.submatrix Sum.swap).range_toEuclideanLin_toBlocks₂₁_le
  rw [← fromBlocks_toBlocks S, fromBlocks_submatrix_sum_swap_sum_swap,
    toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂] at h
  exact h

end Matrix.PosSemidef

namespace Matrix

variable {ι κ R : Type*} [Ring R] [PartialOrder R] [StarRing R] [AddLeftMono R] [Finite ι]
  [Finite κ]

/-- A block diagonal matrix `fromBlocks A 0 0 D` is positive semidefinite if and only if both
diagonal blocks `A` and `D` are. -/
theorem posSemidef_fromBlocks_zero₁₂_zero₂₁_iff {A : Matrix ι ι R} {D : Matrix κ κ R} :
    (fromBlocks A 0 0 D).PosSemidef ↔ A.PosSemidef ∧ D.PosSemidef := by
  -- The diagonal blocks are the submatrices along `Sum.inl` and `Sum.inr`, by definition.
  refine ⟨fun h ↦ ⟨h.submatrix Sum.inl, h.submatrix Sum.inr⟩, fun ⟨hA, hD⟩ ↦ ?_⟩
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  rw [posSemidef_iff_dotProduct_mulVec] at hA hD ⊢
  refine ⟨?_, fun x ↦ ?_⟩
  · simp [IsHermitian, fromBlocks_conjTranspose, hA.1.eq, hD.1.eq]
  · have := add_nonneg (hA.2 (x ∘ Sum.inl)) (hD.2 (x ∘ Sum.inr))
    simpa [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type] using this

open scoped MatrixOrder in
/-- In the Loewner order, two block matrices with the same off-diagonal blocks `B` and `C`
compare exactly when their diagonal blocks do:
`fromBlocks A B C D ≤ fromBlocks A' B C D' ↔ A ≤ A' ∧ D ≤ D'`. -/
theorem fromBlocks_le_fromBlocks_iff {𝕜 : Type*} [RCLike 𝕜] {A A' : Matrix ι ι 𝕜}
    {B : Matrix ι κ 𝕜} {C : Matrix κ ι 𝕜} {D D' : Matrix κ κ 𝕜} :
    fromBlocks A B C D ≤ fromBlocks A' B C D' ↔ A ≤ A' ∧ D ≤ D' := by
  have h : fromBlocks A' B C D' - fromBlocks A B C D = fromBlocks (A' - A) 0 0 (D' - D) := by
    simp [sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  rw [le_iff, le_iff, le_iff, h, posSemidef_fromBlocks_zero₁₂_zero₂₁_iff]

end Matrix
