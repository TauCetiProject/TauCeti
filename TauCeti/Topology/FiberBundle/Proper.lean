/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Topology.FiberBundle.Trivialization

/-!
# Proper projections of bundles with compact fibre

A map `p : Z → B` that is locally trivial with compact fibre `F`, in the sense that every point of
`B` lies in the base set of some trivialization of `p` with fibre `F`, is a proper map. In
particular the projection of a fibre bundle with compact fibre is proper, so preimages of compact
sets of the base are compact. No separation axiom and no compactness of the base are assumed.

## Main results

* `TauCeti.isProperMap_of_forall_exists_trivialization`: a locally trivial map with compact fibre is
  proper.
* `FiberBundle.isProperMap_proj`: the projection of a fibre bundle with compact fibre is proper.
-/

public section

open Bundle Filter Set Topology

variable {B F Z : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace Z]

namespace TauCeti

/-- A map that is locally trivial with compact fibre is proper. -/
theorem isProperMap_of_forall_exists_trivialization [CompactSpace F] {p : Z → B}
    (ht : ∀ x, ∃ e : Trivialization F p, x ∈ e.baseSet) : IsProperMap p := by
  refine isProperMap_iff_ultrafilter.2 ⟨continuous_of_forall_exists_trivialization ht,
    fun U x hx ↦ ?_⟩
  obtain ⟨e, hxe⟩ := ht x
  have hsource : e.source ∈ U := e.source_eq ▸ hx (e.open_baseSet.mem_nhds hxe)
  obtain ⟨v, -, hv⟩ := isCompact_univ.ultrafilter_le_nhds' (U.map fun z ↦ (e z).2) univ_mem
  have he : Tendsto e U (𝓝 (x, v)) := by
    refine (hx.prodMk_nhds hv).congr' ?_
    filter_upwards [hsource] with z hz using Prod.ext (e.coe_fst hz).symm rfl
  refine ⟨e.toOpenPartialHomeomorph.symm (x, v), e.proj_symm_apply' hxe, tendsto_id'.1 ?_⟩
  exact ((e.continuousAt_symm (e.mem_target.2 hxe)).tendsto.comp he).congr'
    (mem_of_superset hsource fun z hz ↦ e.left_inv hz)

end TauCeti

variable (F) in
/-- The projection of a fibre bundle with compact fibre is proper. -/
theorem FiberBundle.isProperMap_proj [CompactSpace F] (E : B → Type*)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] :
    IsProperMap (π F E) :=
  TauCeti.isProperMap_of_forall_exists_trivialization (exists_trivialization_mem_baseSet F E)
