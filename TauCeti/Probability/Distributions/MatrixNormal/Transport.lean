/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.MatrixNormal.Basic

/-!
# Random-variable transport for matrix normal laws

This file gives the `HasLaw` forms of the transport identities for matrix normal laws.
Vectorization, entry evaluation, transposition, row and column extraction, and two-sided affine
maps preserve the corresponding Gaussian or matrix normal families. The covariance hypotheses
are positive semidefiniteness, so the results include singular laws and zero covariance.

## Main results

* `ProbabilityTheory.HasLaw.matrixNormal_of_multivariateGaussian`: reshaping a Gaussian vector
  gives a matrix normal random matrix.
* `ProbabilityTheory.HasLaw.matrixNormal_vec`: vectorization gives a multivariate Gaussian.
* `ProbabilityTheory.HasLaw.matrixNormal_apply`: each entry is a scalar Gaussian.
* `ProbabilityTheory.HasLaw.matrixNormal_transpose`: transposition exchanges row and column
  covariances.
* `ProbabilityTheory.HasLaw.matrixNormal_row` and
  `ProbabilityTheory.HasLaw.matrixNormal_col`: rows and columns are multivariate Gaussian.
* `ProbabilityTheory.HasLaw.matrixNormal_mul_mul_add`: two-sided affine maps preserve matrix
  normal laws.
-/

public section

noncomputable section

open MeasureTheory
open scoped Kronecker Matrix NNReal

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {ι κ ι' κ' Ω : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ι'] [DecidableEq κ'] [MeasurableSpace Ω]
  {P : Measure Ω} {X : Ω → Matrix ι κ ℝ} {M : Matrix ι κ ℝ} {U : Matrix ι ι ℝ}
  {V : Matrix κ κ ℝ}

/-- Reshaping a multivariate Gaussian with Kronecker covariance gives a random matrix with the
corresponding matrix normal law. -/
theorem matrixNormal_of_multivariateGaussian
    {Z : Ω → EuclideanSpace ℝ (κ × ι)}
    (hZ : HasLaw Z (multivariateGaussian (WithLp.toLp 2 M.vec) (V ⊗ₖ U)) P)
    (hU : U.PosSemidef) (hV : V.PosSemidef) :
    HasLaw (fun ω ↦ (TauCeti.matrixVecMeasurableEquiv 2).symm (Z ω))
      (matrixNormalMeasure M U V) P := by
  rw [matrixNormalMeasure_of_posSemidef M hU hV]
  exact (hasLaw_map (MeasurableEquiv.measurable _).aemeasurable).comp hZ

/-- Vectorizing a random matrix with a matrix normal law gives the corresponding multivariate
Gaussian law with Kronecker covariance. -/
theorem matrixNormal_vec (hX : HasLaw X (matrixNormalMeasure M U V) P)
    (hU : U.PosSemidef) (hV : V.PosSemidef) :
    HasLaw (fun ω ↦ WithLp.toLp 2 (X ω).vec)
      (multivariateGaussian (WithLp.toLp 2 M.vec) (V ⊗ₖ U)) P :=
  (HasLaw.mk (by fun_prop) (map_vec_matrixNormalMeasure M hU hV)).comp hX

/-- Evaluating an entry of a random matrix with a matrix normal law gives the corresponding
scalar Gaussian law. -/
theorem matrixNormal_apply (hX : HasLaw X (matrixNormalMeasure M U V) P)
    (hU : U.PosSemidef) (hV : V.PosSemidef) (i : ι) (j : κ) :
    HasLaw (fun ω ↦ X ω i j) (gaussianReal (M i j) (U i i * V j j).toNNReal) P :=
  (HasLaw.mk Matrix.measurable_apply.aemeasurable
    (map_apply_matrixNormalMeasure M hU hV i j)).comp hX

/-- Transposing a random matrix with a matrix normal law exchanges its row and column
covariances. This includes the point-mass fallback at invalid covariance parameters. -/
theorem matrixNormal_transpose (hX : HasLaw X (matrixNormalMeasure M U V) P) :
    HasLaw (fun ω ↦ (X ω)ᵀ) (matrixNormalMeasure Mᵀ V U) P :=
  (HasLaw.mk (by fun_prop) (map_transpose_matrixNormalMeasure M U V)).comp hX

/-- A row of a random matrix with a matrix normal law is multivariate Gaussian, with the column
covariance scaled by the corresponding diagonal entry of the row covariance. -/
theorem matrixNormal_row (hX : HasLaw X (matrixNormalMeasure M U V) P)
    (hU : U.PosSemidef) (hV : V.PosSemidef) (i : ι) :
    HasLaw (fun ω ↦ WithLp.toLp 2 (X ω i))
      (multivariateGaussian (WithLp.toLp 2 (M i)) (U i i • V)) P :=
  (HasLaw.mk ((WithLp.measurable_toLp 2 _).comp
    (measurable_pi_iff.mpr fun _ ↦ Matrix.measurable_apply)).aemeasurable
    (map_row_matrixNormalMeasure M hU hV i)).comp hX

/-- A column of a random matrix with a matrix normal law is multivariate Gaussian, with the row
covariance scaled by the corresponding diagonal entry of the column covariance. -/
theorem matrixNormal_col (hX : HasLaw X (matrixNormalMeasure M U V) P)
    (hU : U.PosSemidef) (hV : V.PosSemidef) (j : κ) :
    HasLaw (fun ω ↦ WithLp.toLp 2 fun i ↦ X ω i j)
      (multivariateGaussian (WithLp.toLp 2 fun i ↦ M i j) (V j j • U)) P :=
  (HasLaw.mk ((WithLp.measurable_toLp 2 _).comp
    (measurable_pi_iff.mpr fun _ ↦ Matrix.measurable_apply)).aemeasurable
    (map_col_matrixNormalMeasure M hU hV j)).comp hX

/-- A two-sided affine image of a random matrix with a matrix normal law is matrix normal.
The left and right matrices may be rectangular and singular. -/
theorem matrixNormal_mul_mul_add (hX : HasLaw X (matrixNormalMeasure M U V) P)
    (hU : U.PosSemidef) (hV : V.PosSemidef) (A : Matrix ι' ι ℝ) (B : Matrix κ κ' ℝ)
    (C : Matrix ι' κ' ℝ) :
    HasLaw (fun ω ↦ A * X ω * B + C)
      (matrixNormalMeasure (A * M * B + C) (A * U * Aᵀ) (Bᵀ * V * B)) P :=
  (HasLaw.mk (by fun_prop) (map_mul_mul_add_matrixNormalMeasure M hU hV A B C)).comp hX

end ProbabilityTheory.HasLaw
