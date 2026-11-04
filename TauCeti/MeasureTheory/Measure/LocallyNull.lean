/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.Basic

/-!
# Locally null images

This file provides a local-to-global criterion for the image of a set to have measure zero.

## Main results

* `TauCeti.measure_image_null_of_locally_null`: an image is null as soon as it is locally null.
-/

public section

open MeasureTheory Set

open scoped Topology

namespace TauCeti

variable {E F G : Type*} [TopologicalSpace E]
  [FunLike G (Set F) ENNReal] [OuterMeasureClass G F] {ν : G} {f : E → F} {s : Set E}

/-- If `s` is Lindelöf and every point of `s` has a neighbourhood within `s` whose image under
`f` is null, then the image of `s` is null. A countable subcover, available because `s` is
Lindelöf (for instance, any set in a hereditarily Lindelöf or second-countable space, via
`HereditarilyLindelofSpace.isLindelof`), reduces the global statement to the local ones; this is
the image version of `MeasureTheory.measure_null_of_locally_null`. -/
theorem measure_image_null_of_locally_null (hs : IsLindelof s)
    (h : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, ν (f '' u) = 0) : ν (f '' s) = 0 := by
  choose! u hu hu₀ using h
  choose! v hv hvu using fun x hx ↦ mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hu x hx)
  obtain ⟨t, htc, hts, hst⟩ := hs.elim_nhds_subcover v hv
  refine measure_mono_null ?_ ((measure_biUnion_null_iff htc).2 fun x hx ↦ hu₀ x (hts x hx))
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (hst hy)
  exact mem_iUnion₂.2 ⟨x, hx, mem_image_of_mem f (hvu x (hts x hx) ⟨hyx, hy⟩)⟩

end TauCeti

end
