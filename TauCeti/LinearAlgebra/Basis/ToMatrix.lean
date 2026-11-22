/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Trace.Basic

/-!
# The coordinate matrix of a family as a linear map

For a basis `b` of `M` indexed by a finite type `ι` and a finite family `y : κ → M`, the matrix
`b.toMatrix y` has the coordinates of `y a` as its `a`-th column. Multiplying a coefficient vector
`c : κ → R` by it gives the coordinates of the linear combination `∑ a, c a • y a`. So the kernel of
the matrix is the space of linear relations among the `y a`, and, over a field, its rows are
linearly independent exactly when the `y a` span `M`.

This identifies the relations among finitely many vectors of a finite-dimensional space with the
solutions of a linear system whose rows are independent precisely in the spanning case, the
situation in which lattices of integral relations have a covolume formula. Two compatibilities
let the coordinate matrix be computed elsewhere: localizing the scalars of `b` maps its entries
to the localized ring, and for an algebra `B` over `A` the matrix of the values `σ (y a)` under
the algebra maps `σ : B →ₐ[A] C` factors through the coordinate matrix and the values `σ (b i)`.

## Main results

* `Module.Basis.mulVecLin_toMatrix`: multiplication by `b.toMatrix y` is the linear combination
  map of `y` followed by the coordinates in `b`.
* `Module.Basis.ker_mulVecLin_toMatrix`: its kernel is the space of linear relations among `y`.
* `Module.Basis.linearIndependent_row_toMatrix_iff`: over a field, its rows are linearly
  independent if and only if `y` spans `M`.
* `Module.Basis.toMatrix_localizationLocalization`: coordinates in a localized basis.
* `Module.Basis.embeddingsMatrix_eq_transpose_mul`: the embeddings matrix of `y` is the transposed
  coordinate matrix times the embeddings matrix of `b`.
-/

public section

open Matrix Submodule

namespace Module.Basis

variable {R M ι κ : Type*}

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- The coordinates of a family in the basis obtained from `b` by localizing are the coordinates
in `b`, mapped to the localized scalars. -/
theorem toMatrix_localizationLocalization {A Rₛ Aₛ : Type*} [CommRing A] [Algebra R A]
    [CommRing Rₛ] [Algebra R Rₛ] (S : Submonoid R) [IsLocalization S Rₛ] [CommRing Aₛ]
    [Algebra A Aₛ] [Algebra Rₛ Aₛ] [Algebra R Aₛ] [IsScalarTower R Rₛ Aₛ] [IsScalarTower R A Aₛ]
    [IsLocalization (Algebra.algebraMapSubmonoid A S) Aₛ] (b : Basis ι R A) (y : κ → A) :
    (b.localizationLocalization Rₛ S Aₛ).toMatrix (algebraMap A Aₛ ∘ y) =
      (b.toMatrix y).map (algebraMap R Rₛ) := by
  ext i a
  simp [toMatrix_apply]

/-- The matrix of the values `σ (y a)` of a family `y` under the `A`-algebra maps `σ : B →ₐ[A] C`
is the transpose of its coordinate matrix in a basis `b`, mapped to `C`, times the matrix of the
values `σ (b i)`. -/
theorem embeddingsMatrix_eq_transpose_mul [Fintype ι] {A B : Type*} (C : Type*) [CommRing A]
    [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] (b : Basis ι A B) (y : κ → B) :
    Algebra.embeddingsMatrix A C y =
      ((b.toMatrix y).map (algebraMap A C))ᵀ * Algebra.embeddingsMatrix A C b := by
  ext a σ
  conv_lhs => rw [Algebra.embeddingsMatrix_apply, ← b.sum_repr (y a)]
  simp [Matrix.mul_apply, toMatrix_apply, Algebra.smul_def]

variable [Finite ι] [Fintype κ]

/-- Multiplication by the coordinate matrix `b.toMatrix y` sends a coefficient vector `c` to the
coordinates in `b` of the linear combination `∑ a, c a • y a`. -/
theorem mulVecLin_toMatrix (b : Basis ι R M) (y : κ → M) :
    (b.toMatrix y).mulVecLin = b.equivFun.toLinearMap ∘ₗ Fintype.linearCombination R y := by
  ext c i
  simp [mulVec, dotProduct, toMatrix_apply, Fintype.linearCombination_apply, mul_comm]

/-- The kernel of the coordinate matrix `b.toMatrix y` is the space of linear relations among
the vectors `y a`. -/
@[simp]
theorem ker_mulVecLin_toMatrix (b : Basis ι R M) (y : κ → M) :
    LinearMap.ker (b.toMatrix y).mulVecLin = LinearMap.ker (Fintype.linearCombination R y) := by
  rw [mulVecLin_toMatrix, LinearEquiv.ker_comp]

end CommRing

/-- Over a field, the rows of the coordinate matrix `b.toMatrix y` are linearly independent if and
only if the vectors `y a` span the whole space. -/
theorem linearIndependent_row_toMatrix_iff [Finite ι] [Finite κ] [Field R] [AddCommGroup M]
    [Module R M] (b : Basis ι R M) (y : κ → M) :
    LinearIndependent R (b.toMatrix y).row ↔ span R (Set.range y) = ⊤ := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, finrank_span_range_row, eq_comm,
    ← mulVec_surjective_iff_rank_eq_card, ← coe_mulVecLin, ← LinearMap.range_eq_top,
    mulVecLin_toMatrix, LinearMap.range_comp, ← Fintype.range_linearCombination]
  exact Submodule.map_eq_top_iff

end Module.Basis
