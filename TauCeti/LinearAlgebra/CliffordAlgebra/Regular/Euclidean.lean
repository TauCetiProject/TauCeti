/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Regular.Norm
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.InnerProductSpace.QuadraticForm.SquaredNorm
public import TauCeti.Analysis.InnerProductSpace.ExteriorAlgebra.HermitianMetric
import Mathlib.LinearAlgebra.BilinearForm.Hom

/-!
# Euclidean metric on the negative Clifford algebra

The Clifford algebra of a real inner product space, with generators squaring to minus the squared
length, carries the scalar-part Euclidean metric. The scoped instances use
`CliffordAlgebra.regularInnerProductCore`. An isometry of the generating spaces induces an
isometry for these metrics, so orthogonal changes of frame preserve the model fibre metric.
-/

public noncomputable section

open TauCeti

namespace CliffordAlgebra.NegativeMetric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The Euclidean norm of the real negative Clifford model. -/
scoped instance instNormedAddCommGroup : NormedAddCommGroup (CliffordAlgebra (negNormSqForm V)) :=
  (regularInnerProductCore _ (posDef_neg_negNormSqForm V)).toNormedAddCommGroup

/-- The Euclidean inner product is the scalar part of `star x * y`. -/
scoped instance instInnerProductSpace : InnerProductSpace ℝ (CliffordAlgebra (negNormSqForm V)) :=
  InnerProductSpace.ofCore (regularInnerProductCore _ (posDef_neg_negNormSqForm V)).toCore

open scoped RealInnerProductSpace in
/-- The Euclidean inner product is the intrinsic scalar-part pairing. -/
theorem inner_eq_regularBilinForm (x y : CliffordAlgebra (negNormSqForm V)) :
    ⟪x, y⟫ = regularBilinForm (negNormSqForm V) x y :=
  regularInnerProductCore_inner _ (posDef_neg_negNormSqForm V) x y

/-- The norm agrees with the intrinsic scalar-part norm. -/
theorem norm_eq_regularNorm (x : CliffordAlgebra (negNormSqForm V)) :
    ‖x‖ = regularNorm _ x :=
  (regularNorm_eq_norm_core _ (posDef_neg_negNormSqForm V) x).symm

open scoped RealInnerProductSpace in
/-- The Chevalley map carries the Euclidean Clifford metric to the exterior Gram form. -/
theorem regularBilinForm_eq_gramForm (x y : CliffordAlgebra (negNormSqForm V)) :
    regularBilinForm (negNormSqForm V) x y =
      ExteriorAlgebra.gramForm V (equivExterior (negNormSqForm V) x)
        (equivExterior (negNormSqForm V) y) := by
  classical
  let e := stdOrthonormalBasis ℝ V
  let Q := negNormSqForm V
  let f := (equivExterior Q).toLinearMap
  have hQ : (QuadraticMap.associated Q).IsOrthoᵢ e.toBasis := by
    rw [associated_negNormSqForm]
    intro i j hij
    simpa using e.orthonormal.2 hij
  have heq : regularBilinForm Q = (ExteriorAlgebra.gramForm V).compl₁₂ f f := by
    apply LinearMap.BilinForm.ext_basis (basis Q e.toBasis)
    intro i j
    rw [regularBilinForm_basis_of_neg_one Q hQ (fun i ↦ by simp [Q, e]),
      LinearMap.compl₁₂_apply]
    simp only [f, LinearEquiv.coe_coe, equivExterior_basis, ExteriorAlgebra.gramForm_basis_basis]
  rw [heq, LinearMap.compl₁₂_apply]
  rfl

variable (V)

/-- Multiplication of the real negative Clifford algebra as a continuous bilinear map. -/
def mulCLM : CliffordAlgebra (negNormSqForm V) →L[ℝ] CliffordAlgebra (negNormSqForm V) →L[ℝ]
    CliffordAlgebra (negNormSqForm V) :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp
    (LinearMap.mul ℝ (CliffordAlgebra (negNormSqForm V)))).toContinuousLinearMap

@[simp]
theorem mulCLM_apply (x y : CliffordAlgebra (negNormSqForm V)) :
    mulCLM V x y = x * y := (rfl)

end CliffordAlgebra.NegativeMetric
