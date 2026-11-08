/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrability of the applied derivative and of derivative energy densities

The derivative of a `C¹` function with compact support is continuous and compactly supported,
hence bounded. So along a strongly measurable family of points `G`, the derivative applied to an
integrable family of vectors `Z` is integrable: it is dominated by a constant times `‖Z‖`. No
finiteness of the measure is needed.

Over any nontrivially normed field, squared norms of the derivative of a `C¹` map in two given
directions, and cutoff-weighted versions of them, are integrable when the map or the cutoff has
compact support. A weighted squared defect `c z * ‖fderiv w z e₁ + A z (fderiv w z e₂)‖ ^ 2` is
integrable when it vanishes off a compact set on which `c` and `A` are continuous, so they need
not be continuous elsewhere.

## Main results

* `TauCeti.integrable_fderiv_apply`: for `f` of class `C¹` with compact support, an a.e. strongly
  measurable `G` and an integrable `Z`, the map `x ↦ fderiv 𝕜 f (G x) (Z x)` is integrable.
* `TauCeti.integrable_cutoff_fderiv_sq_mul_norm_sq`,
  `TauCeti.integrable_norm_fderiv_sq_add`, `TauCeti.integrable_cutoff_sq_mul_norm_fderiv_sq`,
  `TauCeti.integrable_mul_norm_defect_sq`: integrability of the derivative energy densities
  in two directions.
-/

public section

open MeasureTheory

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of a `C¹` compactly supported function, evaluated along an a.e. strongly
measurable family of points `G` and applied to an integrable family of vectors `Z`, is integrable:
it is bounded by a constant times `‖Z‖`. -/
theorem integrable_fderiv_apply {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : E → F}
    (hf : ContDiff 𝕜 1 f) (hfc : HasCompactSupport f) {G : α → E} (hG : AEStronglyMeasurable G μ)
    {Z : α → E} (hZ : Integrable Z μ) :
    Integrable (fun x ↦ fderiv 𝕜 f (G x) (Z x)) μ := by
  have hDf := hf.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hDf.bounded_above_of_compact_support (hfc.fderiv 𝕜)
  exact (hZ.norm.const_mul C).mono'
    (Continuous.comp_aestronglyMeasurable₂ (g := fun (L : E →L[𝕜] F) w ↦ L w)
      (by fun_prop) (hDf.comp_aestronglyMeasurable hG) hZ.1)
    (.of_forall fun x ↦ (fderiv 𝕜 f _).le_of_opNorm_le (hC _) _)

section Energy

variable [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E}
  [IsFiniteMeasureOnCompacts μ]

/-- The cutoff-derivative error density of a `C¹` cutoff with compact support is integrable
against the squared norm of a continuous map. -/
theorem integrable_cutoff_fderiv_sq_mul_norm_sq [NormedSpace ℝ E] {u : E → F} {χ : E → ℝ}
    (hu : Continuous u) (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (e₁ e₂ : E) :
    Integrable (fun z ↦ (fderiv ℝ χ z e₁ ^ 2 + fderiv ℝ χ z e₂ ^ 2) * ‖u z‖ ^ 2) μ := by
  have := hχ.continuous_fderiv one_ne_zero
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) <|
    (hc.fderiv ℝ).mono <| Function.support_subset_iff'.2 fun z hz ↦ by
      simp [Function.notMem_support.1 hz]

/-- The derivative energy of a compactly supported `C¹` map is integrable, in two directions. -/
theorem integrable_norm_fderiv_sq_add {w : E → F} (hw : ContDiff 𝕜 1 w) (hc : HasCompactSupport w)
    (e₁ e₂ : E) :
    Integrable (fun z ↦ ‖fderiv 𝕜 w z e₁‖ ^ 2 + ‖fderiv 𝕜 w z e₂‖ ^ 2) μ := by
  have := hw.continuous_fderiv one_ne_zero
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) <|
    (hc.fderiv 𝕜).mono <| Function.support_subset_iff'.2 fun z hz ↦ by
      simp [Function.notMem_support.1 hz]

/-- A cutoff-weighted derivative energy density of a `C¹` map is integrable when the weight has
compact support. -/
theorem integrable_cutoff_sq_mul_norm_fderiv_sq {u : E → F} {χ : E → ℝ} (hu : ContDiff 𝕜 1 u)
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (e₁ e₂ : E) :
    Integrable (fun z ↦ χ z ^ 2 * (‖fderiv 𝕜 u z e₁‖ ^ 2 + ‖fderiv 𝕜 u z e₂‖ ^ 2)) μ := by
  have := hu.continuous_fderiv one_ne_zero
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) <|
    hc.mono <| Function.support_subset_iff'.2 fun z hz ↦ by simp [Function.notMem_support.1 hz]

/-- A weighted squared defect `c z * ‖fderiv 𝕜 w z e₁ + A z (fderiv 𝕜 w z e₂)‖ ^ 2` of a `C¹` map
is integrable once it vanishes off a compact set on which the coefficients are continuous. -/
theorem integrable_mul_norm_defect_sq (e₁ e₂ : E) {w : E → F} {c : E → ℝ} {A : E → F →L[𝕜] F}
    {S : Set E} (hw : ContDiff 𝕜 1 w) (hc : ContinuousOn c S) (hS : IsCompact S)
    (hA : ContinuousOn A S)
    (hsub : Function.support
      (fun z ↦ c z * ‖fderiv 𝕜 w z e₁ + A z (fderiv 𝕜 w z e₂)‖ ^ 2) ⊆ S) :
    Integrable (fun z ↦ c z * ‖fderiv 𝕜 w z e₁ + A z (fderiv 𝕜 w z e₂)‖ ^ 2) μ := by
  have hdw := (hw.continuous_fderiv one_ne_zero).continuousOn (s := S)
  exact (integrableOn_iff_integrable_of_support_subset hsub).mp <|
    (hc.mul (((hdw.clm_apply continuousOn_const).add
      (hA.clm_apply (hdw.clm_apply continuousOn_const))).norm.pow 2)).integrableOn_compact hS

end Energy

end TauCeti
