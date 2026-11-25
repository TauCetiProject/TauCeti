/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Interval integrals of indicator functions

For a locally finite measure `μ` on `ℝ` and a null-measurable set `s`, the indicator `1_s` is
interval integrable (`TauCeti.intervalIntegrable_indicator_one`), and for `a ≤ b` its integral
over `a..b` is the measure of `s ∩ (a, b]` (`TauCeti.intervalIntegral.integral_indicator_one`).
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {μ : Measure ℝ} {s : Set ℝ}

/-- The indicator of a null-measurable set is interval integrable for a locally finite
measure. -/
theorem intervalIntegrable_indicator_one [IsLocallyFiniteMeasure μ] (hs : NullMeasurableSet s μ)
    (a b : ℝ) : IntervalIntegrable (s.indicator (1 : ℝ → ℝ)) μ a b :=
  (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
    (aestronglyMeasurable_const.indicator₀ (hs.mono Measure.restrict_le_self))
    (Filter.Eventually.of_forall fun y => by by_cases hy : y ∈ s <;> simp [hy])

namespace intervalIntegral

/-- For `a ≤ b`, the integral of the indicator `1_s` of a null-measurable set over `a..b` is the
measure of `s ∩ (a, b]`. -/
theorem integral_indicator_one (hs : NullMeasurableSet s μ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, s.indicator (1 : ℝ → ℝ) t ∂μ = μ.real (s ∩ Ioc a b) := by
  have h : NullMeasurableSet s (μ.restrict (Ioc a b)) := hs.mono Measure.restrict_le_self
  simp [_root_.intervalIntegral.integral_of_le hab, integral_indicator₀ h,
    measureReal_restrict_apply₀ h]

end intervalIntegral

end TauCeti
