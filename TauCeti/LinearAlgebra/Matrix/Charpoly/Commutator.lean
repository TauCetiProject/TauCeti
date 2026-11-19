/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.Algebra.Lie.AdjointAction.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Algebra.Polynomial.Splits
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Characteristic polynomial of a triangular commutator operator

For an upper-triangular matrix `X` over any commutative ring, the characteristic polynomial of
`Y ↦ X * Y - Y * X` is the product of the linear factors with roots `X i i - X j j` over all
pairs `(i, j)`. Ordering the matrix units lexicographically by row and by reversed column makes
this operator upper triangular.

## Main results

* `Matrix.IsUpperTriangular.charpoly_ad`: the exact product of the diagonal differences.
* `Matrix.IsUpperTriangular.splits_charpoly_ad`: splitting over the original coefficient ring.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition (1996), Chapter I, §5,
  pp.21–22, for triangular adjoint operators and split solvability.
-/

public noncomputable section

open Module Polynomial
attribute [local instance 100] LieRing.ofAssociativeRing

namespace Matrix
variable {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]

private def adIndex : (ι × ι) ≃ (ι ×ₗ ιᵒᵈ) :=
  (Equiv.prodCongr (Equiv.refl _) OrderDual.toDual).trans toLex

private def adBasis : Basis (ι ×ₗ ιᵒᵈ) K (Matrix ι ι K) :=
  (Matrix.stdBasis K ι ι).reindex adIndex

private theorem adBasis_apply (i j : ι) :
    adBasis (toLex (i, OrderDual.toDual j)) = Matrix.single i j (1 : K) := by
  simp [adBasis, adIndex, Matrix.stdBasis_eq_single]

omit [DecidableEq ι] in
private theorem adBasis_repr (M : Matrix ι ι K) (i j : ι) :
    adBasis.repr M (toLex (i, OrderDual.toDual j)) = M i j := by
  rw [adBasis, Basis.repr_reindex_apply]
  simp [adIndex, Matrix.stdBasis]

private theorem ad_matrix_apply (X : Matrix ι ι K) (i j k l : ι) :
    LinearMap.toMatrix adBasis adBasis (LieAlgebra.ad K (Matrix ι ι K) X)
        (toLex (i, OrderDual.toDual j)) (toLex (k, OrderDual.toDual l)) =
      X i k * (if l = j then 1 else 0) - (if i = k then 1 else 0) * X l j := by
  rw [LinearMap.toMatrix_apply, adBasis_apply, adBasis_repr, LieAlgebra.ad_apply]
  by_cases hik : i = k <;> by_cases hlj : l = j <;>
    simp_all [Ring.lie_def, Matrix.mul_apply, Matrix.single, eq_comm]

private theorem ad_matrix_upper [LinearOrder ι] (X : Matrix ι ι K)
    (hX : X.IsUpperTriangular) :
    (LinearMap.toMatrix adBasis adBasis (LieAlgebra.ad K (Matrix ι ι K) X)).IsUpperTriangular := by
  intro a b hba
  obtain ⟨⟨i, j⟩, rfl⟩ := toLex.surjective a
  obtain ⟨⟨k, l⟩, rfl⟩ := toLex.surjective b
  refine (ad_matrix_apply X i (OrderDual.ofDual j) k (OrderDual.ofDual l)).trans ?_
  rcases Prod.Lex.toLex_lt_toLex.mp hba with hki | ⟨hki, hjl⟩
  · have hz : X i k = 0 := hX hki
    simp [hz, ne_of_gt hki]
  · dsimp only at hki hjl
    have hjl' : OrderDual.ofDual j < OrderDual.ofDual l :=
      OrderDual.ofDual_lt_ofDual.mpr hjl
    have hz : X (OrderDual.ofDual l) (OrderDual.ofDual j) = 0 := hX hjl'
    simp [hz, ne_of_gt hjl']

/-- The characteristic polynomial of the adjoint of an upper-triangular matrix is the product
of the linear factors with roots its diagonal differences, over all pairs of indices. -/
theorem IsUpperTriangular.charpoly_ad [LinearOrder ι] {X : Matrix ι ι K}
    (hX : X.IsUpperTriangular) :
    (LieAlgebra.ad K (Matrix ι ι K) X).charpoly =
      ∏ p : ι × ι, (Polynomial.X - C (X p.1 p.1 - X p.2 p.2)) := by
  rw [← LinearMap.charpoly_toMatrix _ adBasis,
    Matrix.charpoly_of_isUpperTriangular _ (ad_matrix_upper X hX)]
  refine Fintype.prod_equiv adIndex.symm _ _ ?_
  intro p
  obtain ⟨⟨i, j⟩, rfl⟩ := toLex.surjective p
  apply congrArg (fun a : K ↦ Polynomial.X - C a)
  simpa [adIndex] using ad_matrix_apply X i (OrderDual.ofDual j) i (OrderDual.ofDual j)

/-- The adjoint characteristic polynomial of an upper-triangular matrix splits over its ring
of coefficients. -/
theorem IsUpperTriangular.splits_charpoly_ad [LinearOrder ι] {X : Matrix ι ι K}
    (hX : X.IsUpperTriangular) :
    (LieAlgebra.ad K (Matrix ι ι K) X).charpoly.Splits := by
  rw [hX.charpoly_ad]
  exact Polynomial.Splits.prod (fun _ _ ↦ Polynomial.Splits.X_sub_C _)

end Matrix
