/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Rank
import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# Action of complex matrix C⋆-algebras on finite-dimensional Euclidean space

`CStarMatrix.toEuclideanCLM` packages the canonical `⋆`-algebra isomorphism
`CStarMatrix n n ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)` obtained by composing
`CStarMatrix.ofMatrixStarAlgEquiv.symm` with `Matrix.toEuclideanCLM`, together with its evaluation,
inverse, underlying linear map, and operator-range dimension (`Matrix.rank`) lemmas.
-/

public section

noncomputable section

namespace CStarMatrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The canonical `⋆`-algebra isomorphism identifying `CStarMatrix n n ℂ` with bounded linear
operators on `EuclideanSpace ℂ n`. -/
def toEuclideanCLM (n : Type*) [Fintype n] [DecidableEq n] :
    CStarMatrix n n ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
  ofMatrixStarAlgEquiv.symm.trans (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ))

/-- Applying `CStarMatrix.toEuclideanCLM` applies `Matrix.toEuclideanCLM` to `ofMatrix.symm A`. -/
@[simp]
theorem toEuclideanCLM_apply (A : CStarMatrix n n ℂ) :
    toEuclideanCLM n A = Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (ofMatrix.symm A) := by
  rw [toEuclideanCLM, StarAlgEquiv.trans_apply]
  exact congrArg (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) <|
    ofMatrixStarAlgEquiv.symm_apply_eq.mpr <| by
      rw [← ofMatrix_eq_ofMatrixStarAlgEquiv, Equiv.apply_symm_apply]

/-- Applying `(CStarMatrix.toEuclideanCLM n).symm` wraps `(Matrix.toEuclideanCLM).symm` in
`CStarMatrix.ofMatrix`. -/
@[simp]
theorem toEuclideanCLM_symm_apply (T : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    (toEuclideanCLM n).symm T = ofMatrix ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm T) := by
  rw [toEuclideanCLM, StarAlgEquiv.symm_trans_apply, StarAlgEquiv.symm_symm,
    ← ofMatrix_eq_ofMatrixStarAlgEquiv]

/-- The linear map underlying `CStarMatrix.toEuclideanCLM n A` is
`Matrix.toEuclideanLin (ofMatrix.symm A)`. -/
theorem coe_toEuclideanCLM_eq_toEuclideanLin (A : CStarMatrix n n ℂ) :
    (toEuclideanCLM n A).toLinearMap = Matrix.toEuclideanLin (ofMatrix.symm A) := by
  rw [toEuclideanCLM_apply, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]

/-- The dimension of the range of `CStarMatrix.toEuclideanCLM n A` equals
`Matrix.rank (ofMatrix.symm A)`. -/
theorem finrank_range_toEuclideanCLM (A : CStarMatrix n n ℂ) :
    Module.finrank ℂ (LinearMap.range (toEuclideanCLM n A).toLinearMap) =
      Matrix.rank (ofMatrix.symm A) := by
  rw [coe_toEuclideanCLM_eq_toEuclideanLin, ← Matrix.rank_eq_finrank_range_toEuclideanLin]

end CStarMatrix

end
