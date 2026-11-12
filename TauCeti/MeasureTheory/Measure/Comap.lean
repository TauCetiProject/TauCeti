/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Comap

import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Composing pullbacks of measures along a measurable embedding

Pulling a measure back along a measurable embedding `g` and then along an arbitrary map `f` is the
same as pulling it back along `g ∘ f`.

## Main declarations

* `MeasurableEmbedding.comap_comap`: `(μ.comap g).comap f = μ.comap (g ∘ f)` for a measurable
  embedding `g` and any `f`.
-/

public section

open MeasureTheory Set

namespace MeasurableEmbedding

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {g : β → γ}

/-- Pulling a measure back along a measurable embedding `g` and then along an arbitrary map `f`
agrees with pulling it back along `g ∘ f`: no measurability assumption on `f` is needed, since both
sides vanish unless the relevant images are null-measurable. -/
theorem comap_comap (hg : MeasurableEmbedding g) (f : α → β) (μ : Measure γ) :
    (μ.comap g).comap f = μ.comap (g ∘ f) := by
  have himg : ∀ A : Set β, MeasurableSet A → NullMeasurableSet (g '' A) μ :=
    fun A hA => (hg.measurableSet_image' hA).nullMeasurableSet
  have hqmp : QuasiMeasurePreserving g (μ.comap g) μ :=
    ⟨hg.measurable, by
      rw [hg.map_comap]
      exact Measure.restrict_le_self.absolutelyContinuous⟩
  by_cases hR : Function.Injective f ∧
      ∀ A : Set α, MeasurableSet A → NullMeasurableSet ((g ∘ f) '' A) μ
  · have hL : ∀ A : Set α, MeasurableSet A → NullMeasurableSet (f '' A) (μ.comap g) := by
      intro A hA
      have : f '' A = g ⁻¹' ((g ∘ f) '' A) := by
        rw [image_comp, preimage_image_eq _ hg.injective]
      rw [this]
      exact (hR.2 A hA).preimage hqmp
    ext A hA
    rw [Measure.comap_apply₀ _ _ hR.1 hL hA.nullMeasurableSet,
      Measure.comap_apply₀ _ _ (hg.injective.comp hR.1) hR.2 hA.nullMeasurableSet,
      Measure.comap_apply₀ _ _ hg.injective himg (hL A hA), image_comp]
  · rw [Measure.comap_undef (f := g ∘ f) fun h => hR ⟨h.1.of_comp, h.2⟩]
    refine Measure.comap_undef fun h => hR ⟨h.1, fun A hA => ?_⟩
    have := Measure.NullMeasurableSet.image _ _ hg.injective himg (h.2 A hA)
    rwa [image_comp]

end MeasurableEmbedding
