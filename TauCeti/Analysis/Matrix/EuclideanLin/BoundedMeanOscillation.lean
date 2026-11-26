/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.MeasureTheory.Function.BoundedMeanOscillation.Adjoint

/-!
# Mean oscillation of the conjugate transpose of a matrix field

For a field `a` of square matrices, the operator of the conjugate transpose `(a x)ᴴ` on Euclidean
space is the adjoint of the operator of `a x` (`Matrix.adjoint_toEuclideanCLM`), and taking adjoints
is a conjugate-linear, hence real linear, isometry. So the VMO modulus and the BMO seminorm of the
field of operators of `aᴴ` equal those of `a` (`ContinuousLinearMap.vmoModulus_adjoint`,
`ContinuousLinearMap.bmoSeminorm_adjoint`). For real matrices `aᴴ = aᵀ`: this is how the
transposed coefficients of an adjoint divergence-form equation inherit small mean oscillation.

## Main declarations

* `Matrix.vmoModulus_toEuclideanCLM_conjTranspose`: the equality for the VMO modulus.
* `Matrix.bmoSeminorm_toEuclideanCLM_conjTranspose`: the equality for the BMO seminorm.
* `Matrix.vmoModulus_toEuclideanCLM_transpose`, `Matrix.bmoSeminorm_toEuclideanCLM_transpose`:
  the same equalities for the transpose, over a field with trivial star such as `ℝ`, where
  `aᴴ` simplifies to `aᵀ`.
-/

public section

namespace Matrix

open MeasureTheory TauCeti

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
  {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X} {a : X → Matrix ι ι 𝕜}

/-- Taking conjugate transposes does not change the VMO modulus of the field of operators of a
matrix field: the operator of `Aᴴ` is the adjoint of the operator of `A`, and taking adjoints is a
real linear isometry. -/
@[simp]
theorem vmoModulus_toEuclideanCLM_conjTranspose (r : ℝ) :
    vmoModulus (fun x => toEuclideanCLM (𝕜 := 𝕜) (a x)ᴴ) μ r =
      vmoModulus (fun x => toEuclideanCLM (𝕜 := 𝕜) (a x)) μ r := by
  simp only [← adjoint_toEuclideanCLM, ContinuousLinearMap.vmoModulus_adjoint]

/-- Taking conjugate transposes does not change the BMO seminorm of the field of operators of a
matrix field: the operator of `Aᴴ` is the adjoint of the operator of `A`, and taking adjoints is a
real linear isometry. -/
@[simp]
theorem bmoSeminorm_toEuclideanCLM_conjTranspose :
    bmoSeminorm (fun x => toEuclideanCLM (𝕜 := 𝕜) (a x)ᴴ) μ =
      bmoSeminorm (fun x => toEuclideanCLM (𝕜 := 𝕜) (a x)) μ := by
  simp only [← adjoint_toEuclideanCLM, ContinuousLinearMap.bmoSeminorm_adjoint]

/-- Over a field with trivial star, such as `ℝ`, taking transposes does not change the VMO modulus
of the field of operators of a matrix field. -/
@[simp]
theorem vmoModulus_toEuclideanCLM_transpose [TrivialStar 𝕜] (r : ℝ) :
    vmoModulus (fun x => toEuclideanCLM (𝕜 := 𝕜) (a x)ᵀ) μ r =
      vmoModulus (fun x => toEuclideanCLM (𝕜 := 𝕜) (a x)) μ r := by
  simp only [← conjTranspose_eq_transpose_of_trivial, vmoModulus_toEuclideanCLM_conjTranspose]

/-- Over a field with trivial star, such as `ℝ`, taking transposes does not change the BMO
seminorm of the field of operators of a matrix field. -/
@[simp]
theorem bmoSeminorm_toEuclideanCLM_transpose [TrivialStar 𝕜] :
    bmoSeminorm (fun x => toEuclideanCLM (𝕜 := 𝕜) (a x)ᵀ) μ =
      bmoSeminorm (fun x => toEuclideanCLM (𝕜 := 𝕜) (a x)) μ := by
  simp only [← conjTranspose_eq_transpose_of_trivial, bmoSeminorm_toEuclideanCLM_conjTranspose]

end Matrix
