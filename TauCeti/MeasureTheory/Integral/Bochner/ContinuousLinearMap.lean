/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

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

-- Pin the standard extended norm: inference through the two operator topologies is ambiguous.
/-- The standard extended norm on the space of curried continuous bilinear maps. -/
noncomputable local instance instContinuousENormBilinear :
    ContinuousENorm (H₁ →L[𝕜] H₂ →L[𝕜] E) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid (H₁ →L[𝕜] H₂ →L[𝕜] E) inferInstance).toContinuousENorm

/-- The integral of an integrable family of curried continuous bilinear maps can be evaluated
in two directions by integrating its pointwise evaluation. -/
theorem integral_apply_apply {φ : X → H₁ →L[𝕜] H₂ →L[𝕜] E}
    (hφ : Integrable φ μ) (v : H₁) (w : H₂) :
    (∫ x, φ x ∂μ) v w = ∫ x, φ x v w ∂μ := by
  rw [integral_apply hφ v]
  let L : (H₁ →L[𝕜] H₂ →L[𝕜] E) →L[𝕜] H₂ →L[𝕜] E :=
    ContinuousLinearMap.apply 𝕜 (H₂ →L[𝕜] E) v
  exact integral_apply (φ := fun x ↦ φ x v) (L.integrable_comp (𝕜 := 𝕜) (𝕜' := 𝕜) (φ := φ) hφ) w

end ContinuousLinearMap
