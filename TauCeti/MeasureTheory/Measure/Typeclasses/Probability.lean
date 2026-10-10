/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # Measurability-free complement bound for probability measures

For a probability measure, `1 - μ sᶜ ≤ μ s` for an **arbitrary** set `s`.

Mathlib's `prob_compl_eq_one_sub₀` requires `NullMeasurableSet s` and
`prob_compl_le_one_sub_of_le_prob` requires `MeasurableSet s`; this lemma needs
nothing, because subadditivity `1 = μ (s ∪ sᶜ) ≤ μ s + μ sᶜ` holds for outer
measures.  This is the form in which high-probability events are consumed when
converting vanishing failure probabilities into convergence statements, where
the event sets are often not (easily) measurable.

## Main result

* `TauCeti.one_sub_measure_compl_le`

## Staging notes

Staged for Tau Ceti, roadmap topic T19.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to
`Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib/MeasureTheory/Measure/Typeclasses/Probability.lean`
  at Davis--Kahan commit `fc38eb4`.
* Original declaration: `ForMathlib.one_sub_measure_compl_le`
  (namespace renamed here `ForMathlib` → `TauCeti`).
* Original authorship: formalized by Claude Fable 5 (`claude-fable-5[1m]`);
  staged for Mathlib (no separate copyright line in the source header), released
  under Apache 2.0.
* Extraction class: **copied**, converted to the Tau Ceti module system.
* Spectra influence: **none** (imports only Mathlib).
-/

public section

namespace TauCeti

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

end TauCeti
