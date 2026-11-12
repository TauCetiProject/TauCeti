/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Images after removing finitely many inputs

For a measure with null singletons, removing finitely many inputs changes the image of an
arbitrary map only on a null set. Neither measurability nor injectivity of the map is needed.
-/

public section

open MeasureTheory Set

/-- Removing finitely many inputs preserves an arbitrary image almost everywhere for a
measure with null singletons. -/
theorem Set.Finite.image_sdiff_ae_eq {α β : Type*} [MeasurableSpace β]
    {Z : Set α} (hZ : Z.Finite) (f : α → β) (s : Set α)
    (μ : Measure β) [NullSingletonClass μ] : f '' s =ᵐ[μ] f '' (s \ Z) := by
  apply ae_eq_set.mpr
  constructor
  · apply measure_mono_null ?_ ((hZ.image f).measure_zero μ)
    rintro y ⟨⟨x, hx, rfl⟩, hn⟩
    exact ⟨x, by by_contra hne; exact hn ⟨x, ⟨hx, hne⟩, rfl⟩, rfl⟩
  · rw [sdiff_eq_empty.mpr (image_mono sdiff_subset), measure_empty]
