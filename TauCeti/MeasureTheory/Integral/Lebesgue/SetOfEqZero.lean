/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# The lower Lebesgue integral of a function vanishing on a set of full measure

On a finite measure space, a function into `ℝ≥0∞` that vanishes on a set having the measure of the
whole space has zero lower Lebesgue integral. The set need not be measurable, nor the function
(a.e.-)measurable: the lower integral is the supremum over measurable minorants, each of which
vanishes almost everywhere.

## Main statements

* `TauCeti.lintegral_eq_zero_of_measure_setOf_eq_zero_eq_measure_univ`: the lower integral of a
  function vanishing on a set of full measure is zero.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- For a finite measure, if a function into `ℝ≥0∞` vanishes on a set (not necessarily measurable)
whose measure equals that of the whole space, then its lower Lebesgue integral is zero. -/
theorem lintegral_eq_zero_of_measure_setOf_eq_zero_eq_measure_univ [IsFiniteMeasure μ]
    {f : Ω → ℝ≥0∞} (h : μ {ω | f ω = 0} = μ univ) : ∫⁻ ω, f ω ∂μ = 0 := by
  obtain ⟨g, hg, hgle, hge⟩ := exists_measurable_le_lintegral_eq μ f
  have hs : MeasurableSet {ω | g ω ≠ 0} := hg (measurableSet_singleton (0 : ℝ≥0∞)).compl
  have hsub : {ω | f ω = 0} ⊆ {ω | g ω ≠ 0}ᶜ := fun ω h0 hg0 ↦
    hg0 (le_antisymm (h0 ▸ hgle ω) zero_le)
  have hc : μ {ω | g ω ≠ 0}ᶜ = μ univ :=
    le_antisymm (measure_mono (subset_univ _)) (h ▸ measure_mono hsub)
  have hnull : μ {ω | g ω ≠ 0} = 0 := by
    have := measure_add_measure_compl (μ := μ) hs
    rw [hc] at this
    simpa [measure_ne_top μ] using this
  rw [hge, lintegral_congr_ae (ae_iff.2 hnull : g =ᵐ[μ] 0)]
  simp

end TauCeti
