/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Scalar multiplication as a change of measure in Lᵖ

For a finite exponent, multiplying a function by a measurable scalar coefficient
is equivalent in Lᵖ seminorm to weighting the measure by the coefficient's extended norm
to that exponent. This permits approximation in weighted spaces without dividing
by a coefficient, including on its zero set.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {α 𝕜 ε : Type*} [MeasurableSpace α]
  [TopologicalSpace 𝕜] [ContinuousENorm 𝕜] [TopologicalSpace ε] [ContinuousENorm ε]
  [SMul 𝕜 ε] [ContinuousSMul 𝕜 ε] [ENormSMulClass 𝕜 ε]
  {μ : Measure α} {p : ℝ≥0∞}

/-- Scalar multiplication by a coefficient `w` is a change of measure with density `‖w‖ₑ^p`.
The coefficient may vanish; neither function needs finite Lᵖ norm. For multiplication in a
normed division ring, take `ε = 𝕜` and rewrite `w • f` with `smul_eq_mul`. -/
theorem eLpNorm_smul_eq_eLpNorm_withDensity {w : α → 𝕜} {f : α → ε}
    (hw : AEStronglyMeasurable w μ) (hf : AEStronglyMeasurable f μ) (hp : p ≠ ∞) :
    eLpNorm (w • f) p μ =
      eLpNorm f p (μ.withDensity fun x ↦ ‖w x‖ₑ ^ p.toReal) := by
  have hfw := hf.mono_ac (withDensity_absolutelyContinuous μ fun x ↦ ‖w x‖ₑ ^ p.toReal)
  rcases eq_or_ne p 0 with rfl | hp₀
  · rw [eLpNorm_exponent_zero (hw.smul hf), eLpNorm_exponent_zero hfw]
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp₀ hp (hw.smul hf),
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp₀ hp hfw,
    lintegral_withDensity_eq_lintegral_mul₀ (hw.eNorm.pow_const _) (hf.eNorm.pow_const _)]
  congr 1
  apply lintegral_congr
  intro x
  simp [eNorm_smul, ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]

end MeasureTheory
