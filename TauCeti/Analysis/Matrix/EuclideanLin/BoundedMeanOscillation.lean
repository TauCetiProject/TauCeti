/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Analysis.Matrix.EuclideanLin.Measurable

/-!
# Mean oscillation of the conjugate transpose of a matrix field

For a field `a` of square matrices, the operator of the conjugate transpose `(a x)ᴴ` on Euclidean
space is the adjoint of the operator of `a x` (`Matrix.adjoint_toEuclideanCLM`), and taking adjoints
is a conjugate-linear isometry. So the VMO modulus and the BMO seminorm of the field of operators of
`aᴴ` are at most twice those of `a`. For real matrices `aᴴ = aᵀ`: this is how the transposed
coefficients of an adjoint divergence-form equation inherit small mean oscillation.

## Main declarations

* `Matrix.vmoModulus_toEuclideanCLM_conjTranspose_le`: the bound for the VMO modulus.
* `Matrix.bmoSeminorm_toEuclideanCLM_conjTranspose_le`: the bound for the BMO seminorm.
-/

public section

namespace Matrix

open MeasureTheory TauCeti

variable {𝕜 ι X : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]
  [MeasurableSpace X] {μ : Measure X} {a : X → Matrix ι ι 𝕜}

/-- Taking conjugate transposes at most doubles the VMO modulus of the field of operators of a
matrix field: the operator of `Aᴴ` is the adjoint of the operator of `A`, and taking adjoints is an
isometry. -/
theorem vmoModulus_toEuclideanCLM_conjTranspose_le (ha : AEStronglyMeasurable a μ) (r : ℝ) :
    vmoModulus (fun x => toEuclideanCLM (𝕜 := 𝕜) (a x)ᴴ) μ r ≤
      2 * vmoModulus (fun x => toEuclideanCLM (𝕜 := 𝕜) (a x)) μ r := by
  have h := (ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := EuclideanSpace 𝕜 ι)
    (F := EuclideanSpace 𝕜 ι)).lipschitzWith.vmoModulus_comp_le
      (aestronglyMeasurable_toEuclideanCLM_iff.2 ha) r
  simpa only [Function.comp_def, adjoint_toEuclideanCLM, ENNReal.coe_one, mul_one] using h

/-- Taking conjugate transposes at most doubles the BMO seminorm of the field of operators of a
matrix field: the operator of `Aᴴ` is the adjoint of the operator of `A`, and taking adjoints is an
isometry. -/
theorem bmoSeminorm_toEuclideanCLM_conjTranspose_le (ha : AEStronglyMeasurable a μ) :
    bmoSeminorm (fun x => toEuclideanCLM (𝕜 := 𝕜) (a x)ᴴ) μ ≤
      2 * bmoSeminorm (fun x => toEuclideanCLM (𝕜 := 𝕜) (a x)) μ := by
  have h := (ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := EuclideanSpace 𝕜 ι)
    (F := EuclideanSpace 𝕜 ι)).lipschitzWith.bmoSeminorm_comp_le
      (aestronglyMeasurable_toEuclideanCLM_iff.2 ha)
  simpa only [Function.comp_def, adjoint_toEuclideanCLM, ENNReal.coe_one, mul_one] using h

end Matrix
