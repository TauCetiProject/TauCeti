/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import TauCeti.Analysis.InnerProductSpace.Adjoint

/-!
# Mean oscillation of the conjugate transpose of a matrix field

The operator of the conjugate transpose of a square matrix is the adjoint of its operator on
Euclidean space, and taking adjoints is an `ℝ`-linear isometry. Postcomposition with such an
isometry does not change mean oscillation (`LinearIsometry.vmoModulus_comp`,
`LinearIsometry.bmoSeminorm_comp`). So passing to the conjugate transpose does not change the
VMO modulus (`TauCeti.vmoModulus_toEuclideanCLM_conjTranspose`) or the BMO seminorm
(`TauCeti.bmoSeminorm_toEuclideanCLM_conjTranspose`) of a field of operators. Over `ℝ` the
conjugate transpose is the transpose, which is the simp normal form for real matrices; the real
forms are `TauCeti.vmoModulus_toEuclideanCLM_transpose` and
`TauCeti.bmoSeminorm_toEuclideanCLM_transpose`. They control the adjoint of a real coefficient
field.
-/

public section

namespace TauCeti

open Matrix MeasureTheory

variable {𝕜 ι X : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]
  [MeasurableSpace X] {μ : Measure X}

/-- Passing to the conjugate transpose does not change the VMO modulus of a field of operators of
matrices. -/
@[simp]
theorem vmoModulus_toEuclideanCLM_conjTranspose {a : X → Matrix ι ι 𝕜} (r : ℝ) :
    vmoModulus (fun x => toEuclideanCLM (n := ι) (𝕜 := 𝕜) (a x)ᴴ) μ r =
      vmoModulus (fun x => toEuclideanCLM (n := ι) (𝕜 := 𝕜) (a x)) μ r := by
  -- Taking adjoints is an `ℝ`-linear isometry of operators.
  let L : (EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) →ₗᵢ[ℝ]
      (EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) :=
    ⟨(starL' ℝ).toLinearEquiv.toLinearMap, norm_star⟩
  simp only [← star_eq_conjTranspose, map_star]
  exact L.vmoModulus_comp _ r

/-- Passing to the conjugate transpose does not change the BMO seminorm of a field of operators of
matrices. -/
@[simp]
theorem bmoSeminorm_toEuclideanCLM_conjTranspose {a : X → Matrix ι ι 𝕜} :
    bmoSeminorm (fun x => toEuclideanCLM (n := ι) (𝕜 := 𝕜) (a x)ᴴ) μ =
      bmoSeminorm (fun x => toEuclideanCLM (n := ι) (𝕜 := 𝕜) (a x)) μ := by
  simp only [← iSup_vmoModulus, vmoModulus_toEuclideanCLM_conjTranspose]

/-- Transposing does not change the VMO modulus of a field of operators of real matrices. -/
@[simp]
theorem vmoModulus_toEuclideanCLM_transpose {a : X → Matrix ι ι ℝ} (r : ℝ) :
    vmoModulus (fun x => toEuclideanCLM (n := ι) (𝕜 := ℝ) (a x)ᵀ) μ r =
      vmoModulus (fun x => toEuclideanCLM (n := ι) (𝕜 := ℝ) (a x)) μ r := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    vmoModulus_toEuclideanCLM_conjTranspose (μ := μ) (a := a) r

/-- Transposing does not change the BMO seminorm of a field of operators of real matrices. -/
@[simp]
theorem bmoSeminorm_toEuclideanCLM_transpose {a : X → Matrix ι ι ℝ} :
    bmoSeminorm (fun x => toEuclideanCLM (n := ι) (𝕜 := ℝ) (a x)ᵀ) μ =
      bmoSeminorm (fun x => toEuclideanCLM (n := ι) (𝕜 := ℝ) (a x)) μ := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    bmoSeminorm_toEuclideanCLM_conjTranspose (μ := μ) (a := a)

end TauCeti
