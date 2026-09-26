/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# `Lᵖ` seminorms and Markov kernels

The pointwise `Lᵖ` seminorm of a measurable function against a kernel is measurable. Taking
its `Lᵖ` seminorm against a measure gives the seminorm against the mixture measure.

## Main statements

* `TauCeti.measurable_eLpNorm_kernel`: measurability of the pointwise seminorm;
* `TauCeti.eLpNorm_eLpNorm_kernel`: the seminorm of pointwise seminorms equals the seminorm
  against the mixture.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y] {p : ℝ≥0∞}

/-- The pointwise `L^p` seminorm `x ↦ ‖f‖_{L^p (κ x)}` of a measurable function against a kernel is
measurable. -/
theorem measurable_eLpNorm_kernel (hp0 : p ≠ 0) (hp : p ≠ ∞) (κ : Kernel X Y)
    {f : Y → ℝ≥0∞} (hf : Measurable f) : Measurable fun x ↦ eLpNorm f p (κ x) := by
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hf.aestronglyMeasurable]
  exact ((hf.enorm.pow_const _).lintegral_kernel).pow_const _

/-- Averaging the pointwise `L^p` seminorms `x ↦ ‖f‖_{L^p (κ x)}` over `μ` in `L^p` gives the
`L^p` seminorm of `f` against the mixture `κ ∘ₘ μ`. -/
theorem eLpNorm_eLpNorm_kernel (hp0 : p ≠ 0) (hp : p ≠ ∞) (κ : Kernel X Y)
    (μ : Measure X) {f : Y → ℝ≥0∞} (hf : Measurable f) :
    eLpNorm (fun x ↦ eLpNorm f p (κ x)) p μ = eLpNorm f p (κ ∘ₘ μ) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp
      (measurable_eLpNorm_kernel hp0 hp κ hf).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hf.aestronglyMeasurable,
    Measure.lintegral_bind κ.aemeasurable (hf.enorm.pow_const _).aemeasurable]
  congr 1
  refine lintegral_congr fun x ↦ ?_
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hf.aestronglyMeasurable,
    enorm_eq_self, one_div, ENNReal.rpow_inv_rpow hr.ne']

end TauCeti
