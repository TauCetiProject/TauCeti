/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Norm
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Lebesgue integrals of differences of indicators

On a measurable set `K`, the lower Lebesgue integral of `‖1_s - 1_t‖ₑ` is at most the measure of
`(s ∆ t) ∩ K`: the integrand is the indicator of the symmetric difference.

## Main statements

* `TauCeti.setLIntegral_enorm_indicator_one_sub_le`: on `K`, the `L¹` distance between the
  indicators of `s` and `t` is at most the measure of `(s ∆ t) ∩ K`.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped symmDiff

/-- On a measurable set `K`, the `L¹` distance between the indicators of `s` and `t` is at most
the measure of `(s ∆ t) ∩ K`. -/
theorem setLIntegral_enorm_indicator_one_sub_le {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (s t : Set α) {K : Set α} (hK : MeasurableSet K) :
    ∫⁻ x in K, ‖s.indicator (1 : α → ℝ) x - t.indicator 1 x‖ₑ ∂ν ≤ ν ((s ∆ t) ∩ K) := by
  have hpt : ∀ x, ‖s.indicator (1 : α → ℝ) x - t.indicator 1 x‖ₑ = (s ∆ t).indicator 1 x :=
    fun x => by by_cases h₁ : x ∈ s <;> by_cases h₂ : x ∈ t <;> simp [mem_symmDiff, h₁, h₂]
  simp_rw [hpt]
  exact (lintegral_indicator_one_le _).trans (Measure.restrict_apply' hK).le

end TauCeti
