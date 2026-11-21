/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable

/-!
# Generated sigma algebras modulo a filter

Eventually equal maps generate the same sigma algebra modulo a countably complete filter.
For an almost-everywhere filter, this compares observation sigma algebras after adjoining
ambient null sets, even when the observations themselves are not ambient measurable.
-/

public section

open MeasurableSpace

namespace TauCeti

/-- Eventually equal maps generate the same sigma algebra modulo the given filter. -/
theorem eventuallyMeasurableSpace_comap_congr {α β : Type*} [MeasurableSpace β]
    (X Y : α → β) {l : Filter α} [CountableInterFilter l] (hXY : X =ᶠ[l] Y) :
    eventuallyMeasurableSpace (MeasurableSpace.comap X inferInstance) l =
      eventuallyMeasurableSpace (MeasurableSpace.comap Y inferInstance) l := by
  -- An eventually measurable set has a measurable representative; comap representatives
  -- are preimages, and eventual equality of maps gives eventual equality of these preimages.
  apply le_antisymm <;> rintro s ⟨t, ht, hst⟩
  · obtain ⟨u, hu, rfl⟩ := measurableSet_comap.mp ht
    exact ⟨Y ⁻¹' u, measurableSet_comap.mpr ⟨u, hu, rfl⟩, hst.trans (hXY.preimage u)⟩
  · obtain ⟨u, hu, rfl⟩ := measurableSet_comap.mp ht
    exact ⟨X ⁻¹' u, measurableSet_comap.mpr ⟨u, hu, rfl⟩, hst.trans (hXY.symm.preimage u)⟩

end TauCeti
