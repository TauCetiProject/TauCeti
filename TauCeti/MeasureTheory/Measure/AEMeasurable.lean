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
`MeasureTheory.Measure.map_mono_of_aemeasurable`. Precomposing a function with a measure-preserving
measurable equivalence does not change its law, even for a function that is not almost everywhere
measurable. In that case Mathlib's pushforward of a nonzero measure is a fallback Dirac measure,
the same for the function and for its precomposition, and for the zero measure both pushforwards
are zero.

## Main results

* `MeasureTheory.Measure.map_restrict_le_map` — `(μ.restrict s).map f ≤ μ.map f` for an
  almost everywhere measurable `f`, with no hypothesis on `s`.
* `MeasureTheory.Measure.map_comp_measurableEquiv_of_map_eq` — precomposing with a
  measure-preserving measurable equivalence does not change the law, with no measurability
  assumption on the function.
-/

public section

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {f : α → β}

/-- Pushing forward the part of `μ` carried by `s` gives a measure below the pushforward of `μ`.
No hypothesis on `s` is needed. -/
theorem map_restrict_le_map (hf : AEMeasurable f μ) (s : Set α) :
    (μ.restrict s).map f ≤ μ.map f :=
  map_mono_of_aemeasurable restrict_le_self hf

/-- The law of a function is unchanged by a measure-preserving measurable equivalence of its
domain, with no measurability assumption on the function. -/
theorem map_comp_measurableEquiv_of_map_eq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {e : X ≃ᵐ X} (he : μ.map e = μ) (g : X → β) : μ.map (g ∘ e) = μ.map g := by
  have hpres : MeasurePreserving e μ μ := ⟨e.measurable, he⟩
  by_cases hg : AEMeasurable g μ
  · rw [← AEMeasurable.map_map_of_aemeasurable (by rwa [he]) e.measurable.aemeasurable, he]
  · have hge : ¬ AEMeasurable (g ∘ e) μ := by
      rwa [hpres.aemeasurable_comp_iff e.measurableEmbedding]
    by_cases hμ : μ = 0
    · simp [hμ]
    · rw [Measure.map_of_not_aemeasurable_of_ne_zero hge hμ,
        Measure.map_of_not_aemeasurable_of_ne_zero hg hμ]

end MeasureTheory.Measure
