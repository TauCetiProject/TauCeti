/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Pushing forward measures

Restricting a measure before pushing it forward along an almost everywhere measurable map can only
decrease the pushforward. This complements Mathlib's
`MeasureTheory.Measure.map_mono_of_aemeasurable`. Pushing a measure forward along a measurable
equivalence `e` and then along any function `g` is pushing it forward along `g ∘ e`, even for a
function `g` that is not almost everywhere measurable. In that case Mathlib's pushforward of a
nonzero measure is a fallback Dirac measure, the same for `g` and for `g ∘ e`, and for the zero
measure both pushforwards are zero.

## Main results

* `MeasureTheory.Measure.map_restrict_le_map` — `(μ.restrict s).map f ≤ μ.map f` for an
  almost everywhere measurable `f`, with no hypothesis on `s`.
* `MeasurableEquiv.map_map_measure` — `(μ.map e).map g = μ.map (g ∘ e)` for a measurable
  equivalence `e`, with no measurability assumption on `g`.
-/

public section

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {f : α → β}

/-- Pushing forward the part of `μ` carried by `s` gives a measure below the pushforward of `μ`.
No hypothesis on `s` is needed. -/
theorem map_restrict_le_map (hf : AEMeasurable f μ) (s : Set α) :
    (μ.restrict s).map f ≤ μ.map f :=
  map_mono_of_aemeasurable restrict_le_self hf

end MeasureTheory.Measure

namespace MeasurableEquiv

open MeasureTheory

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Pushing a measure forward along a measurable equivalence `e` and then along any function `g`
is pushing it forward along `g ∘ e`, with no measurability assumption on `g`. -/
theorem map_map_measure (e : α ≃ᵐ β) (μ : Measure α) (g : β → γ) :
    (μ.map e).map g = μ.map (g ∘ e) := by
  have hiff : AEMeasurable g (μ.map e) ↔ AEMeasurable (g ∘ e) μ :=
    e.measurableEmbedding.aemeasurable_map_iff
  by_cases hg : AEMeasurable g (μ.map e)
  · exact AEMeasurable.map_map_of_aemeasurable hg e.measurable.aemeasurable
  · by_cases hμ : μ = 0
    · simp [hμ]
    · have hμ' : μ.map e ≠ 0 := fun h ↦
        hμ ((Measure.map_eq_zero_iff e.measurable.aemeasurable).1 h)
      rw [Measure.map_of_not_aemeasurable_of_ne_zero hg hμ',
        Measure.map_of_not_aemeasurable_of_ne_zero (hiff.not.1 hg) hμ]

end MeasurableEquiv
