/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Profinite groups are nonarchimedean

A topological group is *nonarchimedean* when every neighbourhood of the identity contains an open
subgroup. In a compact totally disconnected topological group every open neighbourhood of the
identity contains an open normal subgroup, which is Mathlib's
`ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`; this file records the consequence
as the `NonarchimedeanGroup` instance, so that everything Mathlib and Tau Ceti prove about
nonarchimedean groups — the basis of open subgroups at the identity, the transport to quotients
and subgroups, total separatedness of Hausdorff nonarchimedean groups — applies to profinite
groups and to compact totally disconnected topological modules without further argument.

## Main results

* `TauCeti.IsTopologicalGroup.nonarchimedeanGroup_of_compactSpace`, and its additive form
  `TauCeti.IsTopologicalAddGroup.nonarchimedeanAddGroup_of_compactSpace`: a compact totally
  disconnected topological group is nonarchimedean.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- A compact totally disconnected topological group is nonarchimedean: every neighbourhood of
the identity contains an open subgroup. -/
@[to_additive IsTopologicalAddGroup.nonarchimedeanAddGroup_of_compactSpace /-- A compact totally
disconnected topological additive group is nonarchimedean: every neighbourhood of zero contains an
open additive subgroup. -/]
instance (priority := 100) IsTopologicalGroup.nonarchimedeanGroup_of_compactSpace :
    NonarchimedeanGroup G where
  is_nonarchimedean U hU := by
    obtain ⟨V, hVU, hV, h1V⟩ := mem_nhds_iff.mp hU
    obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV h1V
    exact ⟨H.toOpenSubgroup, fun x hx ↦ hVU (hH hx)⟩

end TauCeti
