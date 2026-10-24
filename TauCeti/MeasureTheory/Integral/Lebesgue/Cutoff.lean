/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Lebesgue integrals of cut-off functions

Multiplying a real function `u` by a cutoff `χ` with `|χ| ≤ 1` and support in a set `s` does not
increase the Lebesgue integral of its extended norm beyond that of `u` over `s`.

## Main statements

* `TauCeti.lintegral_enorm_mul_le_setLIntegral_of_support_subset`: `∫ |χ u| ≤ ∫_s |u|`.
-/

public section

namespace TauCeti

open MeasureTheory Function Set

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α} {χ : α → ℝ}

/-- Multiplying by a cutoff `χ` with `|χ| ≤ 1` and `support χ ⊆ s` does not increase the `L¹`
norm on `s`: `∫ |χ u| ≤ ∫_s |u|`. Neither `s` nor the functions need be measurable. -/
theorem lintegral_enorm_mul_le_setLIntegral_of_support_subset (hχ1 : ∀ x, |χ x| ≤ 1)
    (hχs : support χ ⊆ s) (u : α → ℝ) :
    ∫⁻ x, ‖(χ * u) x‖ₑ ∂μ ≤ ∫⁻ x in s, ‖u x‖ₑ ∂μ := by
  refine (lintegral_mono fun x => ?_).trans (lintegral_indicator_le _ s)
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, Pi.mul_apply, enorm_mul]
    exact mul_le_of_le_one_left' (by simpa [← ofReal_norm] using hχ1 x)
  · simp [notMem_support.mp fun hmem => hx (hχs hmem)]

end TauCeti
