/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Locally null images

This file provides local-to-global criteria for sets to have measure zero: for the image of a set,
and for the failure of a property outside a closed set of a second-countable locally compact space,
which is null as soon as it is null on every compact set disjoint from the closed set.

## Main results

* `TauCeti.measure_image_null_of_locally_null`: an image is null as soon as it is locally null.
* `TauCeti.ae_notMem_imp_of_forall_isCompact`: a property holding almost everywhere on every compact
  set disjoint from a closed set `s` holds almost everywhere outside `s`.
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

/-- **Almost everywhere outside a closed set, from compact pieces.** In a second-countable locally
compact space, a property that holds almost everywhere on every compact set disjoint from a closed
set `s` holds almost everywhere outside `s`. Each point outside `s` has a compact neighbourhood
disjoint from `s`, and countably many of these neighbourhoods cover the complement of `s`. -/
theorem ae_notMem_imp_of_forall_isCompact {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] {μ : Measure X} {s : Set X} (hs : IsClosed s)
    {p : X → Prop} (h : ∀ K, IsCompact K → Disjoint K s → ∀ᵐ x ∂μ.restrict K, p x) :
    ∀ᵐ x ∂μ, x ∉ s → p x := by
  rw [ae_iff]
  refine measure_null_of_locally_null _ fun x hx ↦ ?_
  obtain ⟨K, hK, hxK, hKs⟩ := exists_compact_subset hs.isOpen_compl (not_imp.1 hx).1
  have hK₀ : μ ({y | ¬p y} ∩ K) = 0 := nonpos_iff_eq_zero.1 <| (Measure.le_restrict_apply _ _).trans
    (ae_iff.1 (h K hK (subset_compl_iff_disjoint_right.1 hKs))).le
  refine ⟨_ ∩ K, inter_mem_nhdsWithin _ (mem_interior_iff_mem_nhds.1 hxK), ?_⟩
  refine measure_mono_null (fun y hy ↦ ?_) hK₀
  exact ⟨fun hp ↦ hy.1 fun _ ↦ hp, hy.2⟩

end TauCeti

end
