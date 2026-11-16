/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Null-singleton measure lemmas

For a measure with null singletons, removing countably many inputs changes the image of an
arbitrary map only on a null set (`Set.Countable.image_sdiff_ae_eq`), without measurability or
injectivity of the map. Moreover, on a metric space any bounded set of diameter zero is a
subsingleton and therefore has zero restricted measure
(`MeasureTheory.Measure.restrict_eq_zero_of_diam_eq_zero`).
-/

public section

open MeasureTheory Set

/-- Removing countably many inputs preserves an arbitrary image almost everywhere for a
measure with null singletons. -/
theorem Set.Countable.image_sdiff_ae_eq {α β : Type*} [MeasurableSpace β]
    {Z : Set α} (hZ : Z.Countable) (f : α → β) (s : Set α)
    (μ : Measure β) [NullSingletonClass μ] : f '' (s \ Z) =ᵐ[μ] f '' s := by
  refine (ae_eq_set.mpr ?_).symm
  constructor
  · apply measure_mono_null ?_ ((hZ.image f).measure_zero μ)
    rintro y ⟨⟨x, hx, rfl⟩, hn⟩
    exact ⟨x, by by_contra hne; exact hn ⟨x, ⟨hx, hne⟩, rfl⟩, rfl⟩
  · rw [sdiff_eq_empty.mpr (image_mono sdiff_subset), measure_empty]

/-- For a measure with null singletons on a metric space, a bounded set of diameter zero has zero
restricted measure. -/
theorem MeasureTheory.Measure.restrict_eq_zero_of_diam_eq_zero {α : Type*} [MetricSpace α]
    [MeasurableSpace α] {μ : Measure α} [NullSingletonClass μ] {s : Set α}
    (hs : Bornology.IsBounded s) (hd : Metric.diam s = 0) : μ.restrict s = 0 :=
  Measure.restrict_eq_zero.2 <|
    (Set.not_nontrivial_iff.1 fun hn => (Metric.diam_pos hn hs).ne' hd).measure_zero μ
