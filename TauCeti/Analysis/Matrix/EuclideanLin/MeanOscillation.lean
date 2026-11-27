/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.MeasureTheory.Integral.Bochner.Star

/-!
# Mean oscillation of the conjugate transpose of a matrix field

The operator of the conjugate transpose of a square matrix is the adjoint of its operator on
Euclidean space, and taking adjoints is an `ℝ`-linear isometry, so it commutes with averages. So
passing to the conjugate transpose does not change the mean oscillation of a field of operators:
its VMO modulus (`TauCeti.vmoModulus_toEuclideanCLM_conjTranspose`) and its BMO seminorm
(`TauCeti.bmoSeminorm_toEuclideanCLM_conjTranspose`). Over `ℝ` the conjugate transpose is the
transpose, which is how the adjoint of a real coefficient field is controlled.
-/

public section

namespace TauCeti

open Matrix MeasureTheory

variable {𝕜 ι X : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]
  [MeasurableSpace X] {μ : Measure X} {a : X → Matrix ι ι 𝕜}

/-- Passing to the conjugate transpose does not change the VMO modulus of a field of operators of
matrices. -/
@[simp]
theorem vmoModulus_toEuclideanCLM_conjTranspose (r : ℝ) :
    vmoModulus (fun x => toEuclideanCLM (n := ι) (𝕜 := 𝕜) (a x)ᴴ) μ r =
      vmoModulus (fun x => toEuclideanCLM (n := ι) (𝕜 := 𝕜) (a x)) μ r := by
  -- Taking adjoints is `ℝ`-linear, so it commutes with averages, and it is an isometry.
  have hint (ν : Measure X) (f : X → EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) :
      ∫ z, star (f z) ∂ν = star (∫ z, f z ∂ν) :=
    integral_star f
  have hn (A B : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι) :
      ‖star A - star B‖ₑ = ‖A - B‖ₑ := by
    simpa only [eDist_eq_eNorm_sub] using star_isometry.edist_eq A B
  -- So the mean oscillations on every ball agree.
  have hball (c : X) (s : ℝ) :
      ⨍⁻ y in Metric.ball c s, ‖star (toEuclideanCLM (n := ι) (𝕜 := 𝕜) (a y)) -
          ⨍ z in Metric.ball c s, star (toEuclideanCLM (n := ι) (𝕜 := 𝕜) (a z)) ∂μ‖ₑ ∂μ =
        ⨍⁻ y in Metric.ball c s, ‖toEuclideanCLM (n := ι) (𝕜 := 𝕜) (a y) -
          ⨍ z in Metric.ball c s, toEuclideanCLM (n := ι) (𝕜 := 𝕜) (a z) ∂μ‖ₑ ∂μ := by
    rw [setAverage_eq', setAverage_eq', hint]
    congr 1 with y
    exact hn _ _
  simp only [← star_eq_conjTranspose, map_star]
  exact le_antisymm
    (vmoModulus_le fun c s hs => (hball c s).trans_le
      (setLAverage_enorm_sub_setAverage_le_vmoModulus _ μ c hs))
    (vmoModulus_le fun c s hs => (hball c s).symm.trans_le
      (setLAverage_enorm_sub_setAverage_le_vmoModulus _ μ c hs))

/-- Passing to the conjugate transpose does not change the BMO seminorm of a field of operators of
matrices. -/
@[simp]
theorem bmoSeminorm_toEuclideanCLM_conjTranspose :
    bmoSeminorm (fun x => toEuclideanCLM (n := ι) (𝕜 := 𝕜) (a x)ᴴ) μ =
      bmoSeminorm (fun x => toEuclideanCLM (n := ι) (𝕜 := 𝕜) (a x)) μ := by
  simp only [← iSup_vmoModulus, vmoModulus_toEuclideanCLM_conjTranspose]

end TauCeti
