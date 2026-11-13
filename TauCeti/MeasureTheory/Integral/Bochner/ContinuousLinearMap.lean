/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Evaluating integrals of continuous bilinear maps

Integration of a curried continuous bilinear map commutes with evaluation in both arguments,
without a completeness assumption on the codomain.
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
