/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Multiplication as a change of measure in Lᵖ

For a finite positive exponent, multiplying a function by a measurable coefficient
is equivalent in Lᵖ seminorm to weighting the measure by the coefficient's absolute
value to that exponent. This permits approximation in weighted spaces without dividing
by a coefficient, including on its zero set.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {α 𝕜 : Type*} [MeasurableSpace α] [NormedDivisionRing 𝕜]
  {μ : Measure α} {p : ℝ≥0∞}

/-- Multiplication by a coefficient in a normed division ring is a change of measure
with density `‖w‖^p`.
The coefficient may vanish; neither function needs finite Lᵖ norm. -/
theorem eLpNorm_mul_eq_withDensity {w f : α → 𝕜} (hw : AEStronglyMeasurable w μ)
    (hf : AEStronglyMeasurable f μ) (hp₀ : p ≠ 0) (hp : p ≠ ∞) :
    eLpNorm (w * f) p μ =
      eLpNorm f p (μ.withDensity fun x ↦ ‖w x‖ₑ ^ p.toReal) := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp₀ hp (hw.mul hf),
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp₀ hp
      (hf.mono_ac (withDensity_absolutelyContinuous _ _)),
    lintegral_withDensity_eq_lintegral_mul₀ (hw.eNorm.pow_const _) (hf.eNorm.pow_const _)]
  congr 1
  apply lintegral_congr
  intro x
  simp [Pi.mul_apply, ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]

end MeasureTheory
