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
without a completeness assumption on the codomain. Evaluation at a family of vectors passes under
the Bochner integral of continuous alternating maps with values in a complete space
(`ContinuousAlternatingMap.integral_apply`), as Mathlib's `ContinuousMultilinearMap.integral_apply`
does for multilinear maps.
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
