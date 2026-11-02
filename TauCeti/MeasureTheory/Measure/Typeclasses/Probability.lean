/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # Probability measure support lemmas

For a probability measure, `1 - μ sᶜ ≤ μ s` for an **arbitrary** set `s`.

Mathlib's `prob_compl_eq_one_sub₀` requires `NullMeasurableSet s` and
`prob_compl_le_one_sub_of_le_prob` requires `MeasurableSet s`; this lemma needs
nothing, because subadditivity `1 = μ (s ∪ sᶜ) ≤ μ s + μ sᶜ` holds for outer
measures.  This is the form in which high-probability events are consumed when
converting vanishing failure probabilities into convergence statements, where
the event sets are often not (easily) measurable.

The zero measure is not a probability measure. The simp lemma for this fact also
simplifies totalized distribution laws that reduce to zero outside their parameter range.

## Main results

* `MeasureTheory.Measure.one_sub_measure_compl_le`
* `MeasureTheory.not_isProbabilityMeasure_zero`

## Source

The complement bound is adapted from the Davis--Kahan/DKPS formalization,
`ForMathlib/MeasureTheory/Measure/Typeclasses/Probability.lean` at `fc38eb4`,
by Claude Fable 5 (Kitware, Inc., Apache-2.0); the public theorem is
exposed in `MeasureTheory.Measure`.
-/

public section

namespace MeasureTheory

/-- The zero measure is not a probability measure. It is a simp lemma so that simp, after
rewriting a law to `0` off its parameter range, can still decide `IsProbabilityMeasure` of that
law. -/
@[simp]
theorem not_isProbabilityMeasure_zero {α : Type*} [MeasurableSpace α] :
    ¬ IsProbabilityMeasure (0 : Measure α) :=
  fun _ ↦ IsProbabilityMeasure.ne_zero (0 : Measure α) rfl

end MeasureTheory

namespace MeasureTheory.Measure

open MeasureTheory
open scoped ENNReal

/--
For a probability measure, `1 - μ sᶜ ≤ μ s`, with no measurability assumption
on `s`: subadditivity gives `1 = μ (s ∪ sᶜ) ≤ μ s + μ sᶜ`.
-/
theorem one_sub_measure_compl_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : Set Ω) : 1 - μ sᶜ ≤ μ s :=
  tsub_le_iff_right.mpr <| by
    calc (1 : ℝ≥0∞) = μ (s ∪ sᶜ) := by rw [Set.union_compl_self, measure_univ]
      _ ≤ μ s + μ sᶜ := measure_union_le _ _

end MeasureTheory.Measure
