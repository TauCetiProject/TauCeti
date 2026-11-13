/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Lower integrals over a measurable hull

For an s-finite measure `μ`, the measurable hull `toMeasurable μ s` of a set `s` carries the same
restricted measure as `s` (`MeasureTheory.Measure.restrict_toMeasurable_of_sfinite`). Hence cutting
a nonnegative extended real function off outside the hull and integrating a positive power of the
result gives the integral of the power of the function over `s`
(`MeasureTheory.lintegral_indicator_toMeasurable_pow`). The cut-off function is measurable
whenever the original function is, whatever the measurability of `s`.

## Main results

* `MeasureTheory.lintegral_indicator_toMeasurable_pow`: the lower integral of a positive power of
  the function cut off outside the measurable hull of `s` is that of the power over `s`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]

/-- **A positive power of a function cut off outside a measurable hull.** For an s-finite measure
`μ`, an extended nonnegative function `g` and a positive exponent `n`, the lower integral of
`((toMeasurable μ s).indicator g) ^ n` over `μ` is the lower integral of `g ^ n` over `s`: the
indicator commutes with the power since `0 ^ n = 0`, and the hull has the same restricted measure
as `s`. No measurability of `s` or `g` is needed. -/
theorem lintegral_indicator_toMeasurable_pow (g : α → ℝ≥0∞) (s : Set α) {n : ℕ} (hn : n ≠ 0) :
    ∫⁻ z, (toMeasurable μ s).indicator g z ^ n ∂μ = ∫⁻ z in s, g z ^ n ∂μ := by
  rw [← Measure.restrict_toMeasurable_of_sfinite s,
    ← lintegral_indicator (measurableSet_toMeasurable μ s)]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ toMeasurable μ s <;> simp [hz, hn]

end MeasureTheory
