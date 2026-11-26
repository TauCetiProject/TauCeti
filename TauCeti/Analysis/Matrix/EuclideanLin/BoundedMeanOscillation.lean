/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import Mathlib.Analysis.Normed.Affine.MazurUlam
import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# Mean oscillation of the conjugate transpose of a matrix field

For a field `a` of square matrices, the operator of the conjugate transpose `(a x)ᴴ` on Euclidean
space is the adjoint of the operator of `a x` (`Matrix.adjoint_toEuclideanCLM`), and taking adjoints
is a conjugate-linear, hence real linear, isometry. So the VMO modulus and the BMO seminorm of the
field of operators of `aᴴ` equal those of `a`. For real matrices `aᴴ = aᵀ`: this is how the
transposed coefficients of an adjoint divergence-form equation inherit small mean oscillation.

## Main declarations

* `Matrix.vmoModulus_toEuclideanCLM_conjTranspose`: the equality for the VMO modulus.
* `Matrix.bmoSeminorm_toEuclideanCLM_conjTranspose`: the equality for the BMO seminorm.
-/

public section

namespace Matrix

open MeasureTheory TauCeti

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]

/-- The adjoint on the operators of `EuclideanSpace 𝕜 ι`, as a real linear isometric equivalence:
taking adjoints is conjugate-linear, hence real linear, and isometric. -/
private noncomputable def adjointRealLinearIsometryEquiv :
    (EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) ≃ₗᵢ[ℝ]
      (EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) :=
  (ContinuousLinearMap.adjoint (𝕜 := 𝕜)).toIsometryEquiv.toRealLinearIsometryEquivOfMapZero
    (map_zero ContinuousLinearMap.adjoint)

private theorem comp_toEuclideanCLM_eq_toEuclideanCLM_conjTranspose {X : Type*}
    (a : X → Matrix ι ι 𝕜) :
    adjointRealLinearIsometryEquiv (𝕜 := 𝕜) (ι := ι) ∘ (fun x => toEuclideanCLM (𝕜 := 𝕜) (a x)) =
      fun x => toEuclideanCLM (𝕜 := 𝕜) (a x)ᴴ :=
  funext fun x => adjoint_toEuclideanCLM (a x)

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X}
  {a : X → Matrix ι ι 𝕜}

/-- Taking conjugate transposes does not change the VMO modulus of the field of operators of a
matrix field: the operator of `Aᴴ` is the adjoint of the operator of `A`, and taking adjoints is a
real linear isometry. -/
@[simp]
theorem vmoModulus_toEuclideanCLM_conjTranspose (r : ℝ) :
    vmoModulus (fun x => toEuclideanCLM (𝕜 := 𝕜) (a x)ᴴ) μ r =
      vmoModulus (fun x => toEuclideanCLM (𝕜 := 𝕜) (a x)) μ r := by
  rw [← comp_toEuclideanCLM_eq_toEuclideanCLM_conjTranspose]
  exact (adjointRealLinearIsometryEquiv (𝕜 := 𝕜) (ι := ι)).toLinearIsometry.vmoModulus_comp r

/-- Taking conjugate transposes does not change the BMO seminorm of the field of operators of a
matrix field: the operator of `Aᴴ` is the adjoint of the operator of `A`, and taking adjoints is a
real linear isometry. -/
@[simp]
theorem bmoSeminorm_toEuclideanCLM_conjTranspose :
    bmoSeminorm (fun x => toEuclideanCLM (𝕜 := 𝕜) (a x)ᴴ) μ =
      bmoSeminorm (fun x => toEuclideanCLM (𝕜 := 𝕜) (a x)) μ := by
  rw [← comp_toEuclideanCLM_eq_toEuclideanCLM_conjTranspose]
  exact (adjointRealLinearIsometryEquiv (𝕜 := 𝕜) (ι := ι)).toLinearIsometry.bmoSeminorm_comp

end Matrix
