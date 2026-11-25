/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan Braams, Claude
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Integrals of functions of a finitely valued random variable

Under a finite measure `μ`, the integral of `F ∘ Y` for a random variable `Y` with values in a
finite type is the finite sum `∑ b, μ (Y = b) • F b`. No integrability hypothesis is needed:
every function on a finite type is integrable against a finite measure.

## Main results

* `MeasureTheory.integral_comp_eq_sum_measureReal_preimage_singleton`.

The statement is adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>),
file `CKSD/Bayes/Basic.lean`.
-/

public section

open MeasureTheory

namespace MeasureTheory

/-- The integral of a function of a random variable with finitely many values is the sum of its
values weighted by their probabilities. -/
theorem integral_comp_eq_sum_measureReal_preimage_singleton {Ω β E : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] [Fintype β] [MeasurableSpace β]
    [MeasurableSingletonClass β] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Y : Ω → β}
    (hY : AEMeasurable Y μ) (F : β → E) :
    ∫ ω, F (Y ω) ∂μ = ∑ b, μ.real (Y ⁻¹' {b}) • F b := by
  rw [← integral_map hY StronglyMeasurable.of_discrete.aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  simp_rw [measureReal_def, Measure.map_apply_of_aemeasurable hY (measurableSet_singleton _)]

end MeasureTheory
