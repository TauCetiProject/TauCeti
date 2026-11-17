/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Measure.Count

/-!
# Bochner integrals with respect to counting measure

Mathlib's `Mathlib.MeasureTheory.Integral.Bochner.SumMeasure` evaluates Bochner integrals against
`Measure.count` only on finite types (`MeasureTheory.integral_count`) and against general measures
only on countable spaces with measurable singletons (`MeasureTheory.integral_countable`).

This file provides `MeasureTheory.hasSum_integral_count` and `MeasureTheory.integral_count_eq_tsum`
for any `Measure.count`-integrable Banach-space-valued function on an arbitrary measurable space,
with no countability or `MeasurableSingletonClass` assumption (used for counting-measure `L²`
Parseval identities and uncountable discrete group von Neumann algebras).
-/

public section

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {f : α → E}

/-- If `f` is integrable with respect to `Measure.count`, then `f` is unconditionally summable with
sum `∫ a, f a ∂Measure.count`. No countability or `MeasurableSingletonClass` assumption on `α` is
required. -/
theorem hasSum_integral_count (hf : Integrable f (Measure.count : Measure α)) :
    HasSum f (∫ a, f a ∂(Measure.count : Measure α)) := by
  have hmk : f = hf.aestronglyMeasurable.mk f :=
    funext (Measure.ae_count_iff.1 hf.aestronglyMeasurable.ae_eq_mk)
  have hsm : StronglyMeasurable f := by
    rw [hmk]
    exact hf.aestronglyMeasurable.stronglyMeasurable_mk
  rw [Measure.count] at hf ⊢
  exact (hasSum_integral_measure hf).congr_fun fun a => (integral_dirac' _ a hsm).symm

/-- The Bochner integral of a `Measure.count`-integrable function equals its `tsum`, with no
countability or `MeasurableSingletonClass` assumption on `α`. -/
theorem integral_count_eq_tsum (hf : Integrable f (Measure.count : Measure α)) :
    ∫ a, f a ∂(Measure.count : Measure α) = ∑' a, f a :=
  (hasSum_integral_count hf).tsum_eq.symm

end MeasureTheory
