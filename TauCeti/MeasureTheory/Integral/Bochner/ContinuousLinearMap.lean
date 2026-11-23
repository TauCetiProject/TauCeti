/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Evaluating integrals of continuous bilinear and alternating maps

Integration of a curried continuous bilinear map commutes with evaluation in both arguments,
without a completeness assumption on the codomain
(`ContinuousLinearMap.integral_apply_apply`). Evaluation at a family of vectors passes under
the Bochner integral of continuous alternating maps with values in a complete space
(`ContinuousAlternatingMap.integral_apply`), as Mathlib's `ContinuousMultilinearMap.integral_apply`
does for multilinear maps.

Applying a continuous linear map `L` to a function multiplies the integral of its squared norm by
at most `‖L‖²` (`ContinuousLinearMap.integral_norm_apply_sq_le`), as for the energy of a map
composed with a linear change of coordinates.
-/

public section

open MeasureTheory

namespace ContinuousLinearMap

variable {X H₁ H₂ E 𝕜 : Type*} [MeasurableSpace X] {μ : Measure X}
  [RCLike 𝕜] [NormedAddCommGroup H₁] [NormedSpace 𝕜 H₁]
  [NormedAddCommGroup H₂] [NormedSpace 𝕜 H₂] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace 𝕜 E]

/-- The integral of an integrable family of curried continuous bilinear maps can be evaluated
in two directions by integrating its pointwise evaluation. -/
theorem integral_apply_apply {φ : X → H₁ →L[𝕜] H₂ →L[𝕜] E}
    (hφ : Integrable φ μ) (v : H₁) (w : H₂) :
    (∫ x, φ x ∂μ) v w = ∫ x, φ x v w ∂μ := by
  rw [integral_apply hφ v, integral_apply (hφ.apply_continuousLinearMap v) w]

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {X 𝕜 F G : Type*} [MeasurableSpace X] {μ : Measure X} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Applying a continuous linear map `L` to a function `f` multiplies the integral of its squared
norm by at most `‖L‖²`: `∫ ‖L ∘ f‖² ≤ ‖L‖² ∫ ‖f‖²`. -/
theorem integral_norm_apply_sq_le (L : F →L[𝕜] G) {f : X → F}
    (hf : Integrable (fun x ↦ ‖f x‖ ^ 2) μ) :
    ∫ x, ‖L (f x)‖ ^ 2 ∂μ ≤ ‖L‖ ^ 2 * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun x ↦ by positivity) (hf.const_mul _)
    (ae_of_all _ fun x ↦ ?_)
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm (f x)) 2

end ContinuousLinearMap

namespace ContinuousAlternatingMap

variable {X E F ι 𝕜 : Type*} [MeasurableSpace X] {μ : Measure X} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace 𝕜 F] [CompleteSpace F] [Fintype ι]

/-- Evaluation of continuous alternating maps with values in a complete space passes under the
Bochner integral. -/
theorem integral_apply {φ : X → E [⋀^ι]→L[𝕜] F} (hφ : Integrable φ μ) (v : ι → E) :
    (∫ x, φ x ∂μ) v = ∫ x, φ x v ∂μ :=
  (((ContinuousMultilinearMap.apply 𝕜 (fun _ : ι ↦ E) F v).comp
    (toContinuousMultilinearMapCLM 𝕜)).integral_comp_comm hφ).symm

end ContinuousAlternatingMap
