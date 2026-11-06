/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Block

/-!
# Leading block minors under triangular multiplication

An invertible block triangular matrix has invertible leading blocks, over any commutative
ring. Consequently, multiplying a matrix on the left by an invertible block lower triangular
matrix and on the right by an invertible block upper triangular matrix preserves the condition
that its leading block minors are units.

This is the matrix step that reduces the leading-minor test on a Bruhat expression `L * W * U`
to the test on its Weyl representative `W`. The middle matrix need not be invertible, the outer
matrices need not be unitriangular, and blocks may have arbitrary multiplicities. We work on
any down-closed set of block indices, including the empty set, before specializing to all
initial segments. In particular, the result applies to weight-space blocks rather than only
to one-dimensional weight spaces.

## Main results

* `Matrix.BlockTriangular.isUnit_det_toSquareBlockProp`: leading blocks of an invertible
  block upper triangular matrix have unit determinants.
* `Matrix.BlockTriangular.isUnit_det_toSquareBlockProp_of_toDual`: the lower triangular version.
* `Matrix.isUnit_det_toSquareBlockProp_mul_mul_iff`: the unit-minor test on a down-closed set
  is unchanged by invertible triangular outer factors.
* `Matrix.forall_isUnit_det_toSquareBlockProp_le_mul_mul_iff`: preservation of the test on
  every leading block.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 5, Theorem 7.
* J. C. Jantzen, *Representations of Algebraic Groups*, second edition, AMS (2003),
  Part II, Chapter 1.
-/

public section

open OrderDual

namespace Matrix

variable {m R α : Type*} [Fintype m] [DecidableEq m] [CommRing R] [LinearOrder α]
  {b : m → α} {A L M U : Matrix m m R} {p : m → Prop} [DecidablePred p]

/-- A leading block of a block upper triangular matrix with unit determinant also has unit
determinant. The set of indices may be any down-closed union of blocks. -/
theorem BlockTriangular.isUnit_det_toSquareBlockProp (hA : A.BlockTriangular b)
    (hdet : IsUnit A.det) (hp : ∀ ⦃i j⦄, b j ≤ b i → p i → p j) :
    IsUnit (A.toSquareBlockProp p).det := by
  rw [twoBlockTriangular_det A p fun i hi j hj =>
    hA (lt_of_not_ge fun hij => hi (hp hij hj))] at hdet
  exact isUnit_of_mul_isUnit_left hdet

/-- A leading block of a block lower triangular matrix with unit determinant also has unit
determinant. The set of indices may be any down-closed union of blocks. -/
theorem BlockTriangular.isUnit_det_toSquareBlockProp_of_toDual
    (hA : A.BlockTriangular (toDual ∘ b)) (hdet : IsUnit A.det)
    (hp : ∀ ⦃i j⦄, b j ≤ b i → p i → p j) :
    IsUnit (A.toSquareBlockProp p).det := by
  rw [twoBlockTriangular_det' A p fun i hi j hj =>
    hA (toDual_lt_toDual.mpr (lt_of_not_ge fun hij => hj (hp hij hi)))] at hdet
  exact isUnit_of_mul_isUnit_left hdet

/-- Invertible block lower triangular left factors and invertible block upper triangular right
factors preserve the unit-determinant test on every down-closed union of blocks. No hypothesis
on the middle matrix is required. -/
theorem isUnit_det_toSquareBlockProp_mul_mul_iff
    (hL : L.BlockTriangular (toDual ∘ b)) (hU : U.BlockTriangular b)
    (hLdet : IsUnit L.det) (hUdet : IsUnit U.det)
    (hp : ∀ ⦃i j⦄, b j ≤ b i → p i → p j) :
    IsUnit ((L * M * U).toSquareBlockProp p).det ↔
      IsUnit (M.toSquareBlockProp p).det := by
  rw [hU.toSquareBlockProp_mul hp, hL.toSquareBlockProp_mul_of_toDual hp]
  simp only [det_mul, IsUnit.mul_iff,
    hL.isUnit_det_toSquareBlockProp_of_toDual hLdet hp,
    hU.isUnit_det_toSquareBlockProp hUdet hp, true_and, and_true]

/-- All leading block minors of `L * M * U` are units exactly when those of `M` are, if `L`
is invertible block lower triangular and `U` is invertible block upper triangular. This is the
leading-minor criterion for the block matrix big cell, invariant under its triangular factors. -/
theorem forall_isUnit_det_toSquareBlockProp_le_mul_mul_iff
    (hL : L.BlockTriangular (toDual ∘ b)) (hU : U.BlockTriangular b)
    (hLdet : IsUnit L.det) (hUdet : IsUnit U.det) :
    (∀ i, IsUnit ((L * M * U).toSquareBlockProp fun j => b j ≤ b i).det) ↔
      ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det := by
  exact forall_congr' fun _ => isUnit_det_toSquareBlockProp_mul_mul_iff hL hU hLdet hUdet
    fun _ _ hji hi => hji.trans hi

end Matrix
