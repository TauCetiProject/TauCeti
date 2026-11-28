/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# Entry and trace linear maps on `CStarMatrix`

This file packages entry extraction (`CStarMatrix.entryLinearMap`) and the matrix trace
(`CStarMatrix.traceLinearMap`) on `CStarMatrix` as `R`-linear maps.
-/

public section

namespace CStarMatrix

/-- Extracting the `(i, j)`-th entry of a `CStarMatrix` as an `R`-linear map. -/
def entryLinearMap (R A : Type*) {m n : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    (i : m) (j : n) : CStarMatrix m n A →ₗ[R] A :=
  (Matrix.entryLinearMap R A i j).comp (ofMatrixₗ (R := R)).symm.toLinearMap

/-- Applying `CStarMatrix.entryLinearMap` yields the `(i, j)`-th entry. -/
@[simp]
theorem entryLinearMap_apply {R A m n : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    (i : m) (j : n) (M : CStarMatrix m n A) : entryLinearMap R A i j M = M i j := (rfl)

/-- The matrix trace of a C⋆-matrix bundled as a linear map. -/
def traceLinearMap (n R A : Type*) [Fintype n] [AddCommMonoid A] [Semiring R] [Module R A] :
    CStarMatrix n n A →ₗ[R] A :=
  (Matrix.traceLinearMap n R A).comp (ofMatrixₗ (R := R)).symm.toLinearMap

/-- Applying `CStarMatrix.traceLinearMap` yields the matrix trace of the underlying matrix. -/
@[simp]
theorem traceLinearMap_apply {n R A : Type*} [Fintype n] [AddCommMonoid A] [Semiring R]
    [Module R A] (M : CStarMatrix n n A) :
    traceLinearMap n R A M = Matrix.trace (ofMatrix.symm M) := (rfl)

end CStarMatrix
