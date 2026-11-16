/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Comap
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Pullbacks of measures

This file records general properties of `MeasureTheory.Measure.comap`:

* Pulling a measure back along a measurable embedding `g` and then along an arbitrary map `f` is
  the same as pulling it back along `g ∘ f` (`MeasurableEmbedding.comap_comap`). Mathlib's
  `MeasureTheory.Measure.comap_comap` needs a measurable-image hypothesis on `f`; strengthening `g`
  to a measurable embedding removes every hypothesis on `f`, which allows iterated pullbacks along
  maps such as arbitrary subtype inclusions.
* For any measurable map `f`, `(μ.comap f) (f ⁻¹' v) ≤ μ v` with no measurability assumption on `v`
  or injectivity assumption on `f` (`MeasureTheory.Measure.comap_preimage_le`), and consequently
  pulling a σ-finite measure back along a measurable map gives a σ-finite measure
  (`Measurable.sigmaFinite_comap`).

## Main declarations

* `MeasurableEmbedding.comap_comap`: `(μ.comap g).comap f = μ.comap (g ∘ f)` for a measurable
  embedding `g` and any `f`.
* `MeasureTheory.Measure.comap_preimage_le`: `(μ.comap f) (f ⁻¹' v) ≤ μ v` for measurable `f`.
* `Measurable.sigmaFinite_comap`: σ-finiteness of `μ.comap f` for a measurable map `f` and
  σ-finite `μ`.
-/

public section

open MeasureTheory Set

namespace MeasurableEmbedding

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {g : β → γ}

/-- Pulling a measure back along a measurable embedding `g` and then along an arbitrary map `f`
agrees with pulling it back along `g ∘ f`, with no injectivity or measurable-image assumption on
`f` (unlike `MeasureTheory.Measure.comap_comap`). -/
theorem comap_comap (hg : MeasurableEmbedding g) (f : α → β) (μ : Measure γ) :
    (μ.comap g).comap f = μ.comap (g ∘ f) := by
  have himg : ∀ A : Set β, MeasurableSet A → NullMeasurableSet (g '' A) μ :=
    fun A hA => (hg.measurableSet_image' hA).nullMeasurableSet
  have hqmp : QuasiMeasurePreserving g (μ.comap g) μ :=
    ⟨hg.measurable.aemeasurable, by
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

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- For any measurable map `f`, the pullback measure of `f ⁻¹' v` is bounded by `μ v`, with no
measurability assumption on `v` or injectivity assumption on `f`. -/
theorem comap_preimage_le {f : α → β} (hf : Measurable f) (μ : Measure β) (v : Set β) :
    (μ.comap f) (f ⁻¹' v) ≤ μ v := by
  have hT : MeasurableSet (f ⁻¹' toMeasurable μ v) := hf (measurableSet_toMeasurable μ v)
  exact (measure_mono (preimage_mono (subset_toMeasurable μ v))).trans <|
    ((comap_apply_le f μ hT.nullMeasurableSet).trans
      (measure_mono (image_preimage_subset f _))).trans_eq (measure_toMeasurable v)

/-- Pulling a σ-finite measure back along a measurable map gives a σ-finite measure. -/
theorem _root_.Measurable.sigmaFinite_comap {f : α → β} (hf : Measurable f) (μ : Measure β)
    [SigmaFinite μ] : SigmaFinite (μ.comap f) :=
  ⟨⟨{ set n := f ⁻¹' spanningSets μ n
      set_mem _ := trivial
      finite n := (comap_preimage_le hf μ _).trans_lt (measure_spanningSets_lt_top μ n)
      spanning := by rw [← preimage_iUnion, iUnion_spanningSets, preimage_univ] }⟩⟩

end MeasureTheory.Measure
