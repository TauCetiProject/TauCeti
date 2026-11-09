/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
import TauCeti.Analysis.Fourier.ChangeOfVariables

/-!
# Dilations of Schwartz functions

For `c ≠ 0`, the dilate `ξ ↦ σ (c⁻¹ • ξ)` of a Schwartz function `σ` is again a Schwartz
function. Viewing `σ` as the symbol of a Fourier multiplier, dilation does not change the `L¹`
norm of its kernel `𝓕⁻ σ`; this is what makes the `Lᵖ` bounds of frequency-localized multipliers
uniform in the scale.

## Main declarations

* `SchwartzMap.dilate`: the dilate `ξ ↦ σ (c⁻¹ • ξ)` of a Schwartz function.
* `SchwartzMap.integral_norm_fourierInv_dilate`: `∫ ‖𝓕⁻ (dilate c σ)‖ = ∫ ‖𝓕⁻ σ‖`.
-/

public section

open MeasureTheory
open scoped SchwartzMap FourierTransform

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

section NormedSpace

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

/-- The dilate `ξ ↦ σ (c⁻¹ • ξ)` of a Schwartz function `σ` by a nonzero factor `c`. -/
noncomputable def dilate {c : ℝ} (hc : c ≠ 0) (σ : 𝓢(E, F)) : 𝓢(E, F) :=
  compCLMOfContinuousLinearEquiv ℝ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 c⁻¹ (inv_ne_zero hc))) σ

@[simp]
theorem dilate_apply {c : ℝ} (hc : c ≠ 0) (σ : 𝓢(E, F)) (ξ : E) :
    dilate hc σ ξ = σ (c⁻¹ • ξ) := by
  simp [dilate, Units.smul_def]

end NormedSpace

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℂ F]

/-- Dilating a symbol does not change the `L¹` norm of its kernel:
`∫ ‖𝓕⁻ (σ (c⁻¹ • ·))‖ = ∫ ‖𝓕⁻ σ‖`. -/
theorem integral_norm_fourierInv_dilate {c : ℝ} (hc : c ≠ 0) (σ : 𝓢(E, F)) :
    ∫ x, ‖𝓕⁻ (dilate hc σ : E → F) x‖ = ∫ x, ‖𝓕⁻ (σ : E → F) x‖ := by
  rw [show (dilate hc σ : E → F) = fun ξ ↦ σ (c⁻¹ • ξ) from funext (dilate_apply hc σ)]
  exact TauCeti.integral_norm_fourierInv_comp_smul _ (inv_ne_zero hc)

end SchwartzMap
