/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import TauCeti.Analysis.Matrix.EuclideanLin.Measurable

/-!
# Mean oscillation of the conjugate transpose of a matrix field

The operator of the conjugate transpose of a square matrix is the adjoint of its operator on
Euclidean space, and taking adjoints is an isometry. So passing to the conjugate transpose at most
doubles the mean oscillation of a field of operators: its VMO modulus
(`TauCeti.vmoModulus_toEuclideanCLM_conjTranspose_le`) and its BMO seminorm
(`TauCeti.bmoSeminorm_toEuclideanCLM_conjTranspose_le`). Over `ℝ` the conjugate transpose is the
transpose, which is how the adjoint of a real coefficient field is controlled.
-/

public section

namespace TauCeti

open Matrix MeasureTheory

variable {𝕜 ι X : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]
  [MeasurableSpace X] {μ : Measure X} {a : X → Matrix ι ι 𝕜}

/-- Passing to the conjugate transpose at most doubles the VMO modulus of a field of operators of
matrices. -/
theorem vmoModulus_toEuclideanCLM_conjTranspose_le (ha : AEStronglyMeasurable a μ) (r : ℝ) :
    vmoModulus (fun x => toEuclideanCLM (n := ι) (𝕜 := 𝕜) (a x)ᴴ) μ r ≤
      2 * vmoModulus (fun x => toEuclideanCLM (n := ι) (𝕜 := 𝕜) (a x)) μ r := by
  simpa [← star_eq_conjTranspose, map_star, Function.comp_def] using
    star_isometry.lipschitzWith.vmoModulus_comp_le (aestronglyMeasurable_toEuclideanCLM_iff.2 ha) r

/-- Passing to the conjugate transpose at most doubles the BMO seminorm of a field of operators of
matrices. -/
theorem bmoSeminorm_toEuclideanCLM_conjTranspose_le (ha : AEStronglyMeasurable a μ) :
    bmoSeminorm (fun x => toEuclideanCLM (n := ι) (𝕜 := 𝕜) (a x)ᴴ) μ ≤
      2 * bmoSeminorm (fun x => toEuclideanCLM (n := ι) (𝕜 := 𝕜) (a x)) μ := by
  simpa [← star_eq_conjTranspose, map_star, Function.comp_def] using
    star_isometry.lipschitzWith.bmoSeminorm_comp_le (aestronglyMeasurable_toEuclideanCLM_iff.2 ha)

end TauCeti
