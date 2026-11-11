/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Images after removing countably many inputs

For a measure with null singletons, removing countably many inputs changes the image of an
arbitrary map only on a null set. Neither measurability nor injectivity of the map is needed.

Dually, a map injective on a set meets a countable set at a null set of points of that set.
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

/-- A map injective on `A` meets a countable set `S` at a null set of points of `A`, for a
measure with null singletons: those points form a countable set, at most one per point of `S`. -/
theorem Set.InjOn.measure_setOf_mem_eq_zero {α β : Type*} [MeasurableSpace α] {f : α → β}
    {A : Set α} (hf : InjOn f A) {S : Set β} (hS : S.Countable) {μ : Measure α}
    [NullSingletonClass μ] : μ {x ∈ A | f x ∈ S} = 0 :=
  (MapsTo.countable_of_injOn (s := {x ∈ A | f x ∈ S}) (fun _ hx => hx.2)
    (hf.mono (sep_subset A _)) hS).measure_zero μ
