/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Norm
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Lebesgue integrals of differences of indicators

On a null-measurable set `K`, the lower Lebesgue integral of `‖1_s - 1_t‖ₑ` is at most the
measure of `(s ∆ t) ∩ K`: the integrand is the indicator of the symmetric difference.

## Main statements

* `MeasureTheory.Measure.setLIntegral_enorm_indicator_one_sub_le`: on `K`, the `L¹` distance
  between the indicators of `s` and `t` is at most the measure of `(s ∆ t) ∩ K`.
-/

public section

namespace MeasureTheory.Measure

open Set
open scoped symmDiff

/-- On a null-measurable set `K`, the `L¹` distance between the indicators of `s` and `t` is at
most the measure of `(s ∆ t) ∩ K`. -/
theorem setLIntegral_enorm_indicator_one_sub_le {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (s t : Set α) {K : Set α} (hK : NullMeasurableSet K ν) :
    ∫⁻ x in K, ‖s.indicator (1 : α → ℝ) x - t.indicator 1 x‖ₑ ∂ν ≤ ν ((s ∆ t) ∩ K) := by
  simp_rw [← apply_indicator_symmDiff eNorm_neg, eNorm_indicator_eq_indicator_eNorm, Pi.one_apply,
    eNorm_one]
  exact (lintegral_indicator_one_le _).trans (restrict_apply₀' hK).le

end MeasureTheory.Measure
