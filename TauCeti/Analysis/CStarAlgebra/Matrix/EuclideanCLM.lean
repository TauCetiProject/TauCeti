/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.Hom
import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# Scalar C⋆-matrices as operators on `EuclideanSpace`

`CStarMatrix.toEuclideanCLM` is the star algebra isomorphism between `CStarMatrix n n ℂ` and the
operators on `EuclideanSpace ℂ n`, through Mathlib's `Matrix.toEuclideanCLM`. It preserves norms
(`CStarMatrix.norm_toEuclideanCLM`), traces (`CStarMatrix.trace_toEuclideanCLM`) and the order
(`CStarMatrix.toEuclideanCLM_le_toEuclideanCLM_iff`), and sends the matrix product `x⋆y` to the
composition `x† ∘L y` of operators (`CStarMatrix.toEuclideanCLM_symm_adjoint_comp`).
-/

public section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace CStarMatrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The star algebra isomorphism between `CStarMatrix n n ℂ` and the operators on
`EuclideanSpace ℂ n`, through `Matrix.toEuclideanCLM`. -/
def toEuclideanCLM : CStarMatrix n n ℂ ≃⋆ₐ[ℂ]
    (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
  (ofMatrixStarAlgEquiv (n := n) (A := ℂ)).symm.trans Matrix.toEuclideanCLM

/-- `toEuclideanCLM` is `Matrix.toEuclideanCLM` on the underlying matrix. -/
theorem toEuclideanCLM_apply (x : CStarMatrix n n ℂ) :
    toEuclideanCLM x = Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (ofMatrix.symm x) :=
  (rfl)

/-- `toEuclideanCLM.symm` is `Matrix.toEuclideanCLM.symm`, as a `CStarMatrix`. -/
theorem toEuclideanCLM_symm_apply (Z : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    toEuclideanCLM.symm Z = ofMatrix ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm Z) :=
  (rfl)

/-- The entries of a matrix are the matrix coefficients of its operator in the standard basis. -/
theorem inner_single_toEuclideanCLM_single (x : CStarMatrix n n ℂ) (i j : n) :
    ⟪EuclideanSpace.single i 1, toEuclideanCLM x (EuclideanSpace.single j 1)⟫_ℂ = x i j := by
  simp [toEuclideanCLM_apply, EuclideanSpace.inner_single_left]

/-- The trace of the operator of a matrix is the trace of the matrix. -/
@[simp]
theorem trace_toEuclideanCLM (x : CStarMatrix n n ℂ) :
    LinearMap.trace ℂ _ (toEuclideanCLM x).toLinearMap = (ofMatrix.symm x).trace := by
  rw [toEuclideanCLM_apply, Matrix.trace_toEuclideanCLM]

/-- `toEuclideanCLM` preserves norms. -/
@[simp]
theorem norm_toEuclideanCLM (x : CStarMatrix n n ℂ) : ‖toEuclideanCLM x‖ = ‖x‖ :=
  NonUnitalStarAlgHom.norm_map toEuclideanCLM toEuclideanCLM.injective x

/-- `toEuclideanCLM` preserves and reflects the order. -/
@[simp]
theorem toEuclideanCLM_le_toEuclideanCLM_iff {x y : CStarMatrix n n ℂ} :
    toEuclideanCLM x ≤ toEuclideanCLM y ↔ x ≤ y :=
  NonUnitalStarAlgHom.map_le_map_iff toEuclideanCLM toEuclideanCLM.injective

/-- `toEuclideanCLM` turns adjoints of operators into adjoints of matrices. -/
theorem toEuclideanCLM_symm_adjoint_comp (U W : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    toEuclideanCLM.symm (U.adjoint ∘L W) =
      star (toEuclideanCLM.symm U) * toEuclideanCLM.symm W := by
  rw [StarAlgEquiv.symm_apply_eq, map_mul, map_star, StarAlgEquiv.apply_symm_apply,
    StarAlgEquiv.apply_symm_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.mul_def]

end CStarMatrix
