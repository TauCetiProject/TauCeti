/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.Basic

/-!
# Compact totally disconnected open subgroups as profinite groups

An open subgroup `K : OpenSubgroup G` of a topological group `G` inherits a topological group
structure (`OpenSubgroup.instIsTopologicalGroup`). When `K` is compact as a subset of `G` and
totally disconnected in the subspace topology (`[TotallyDisconnectedSpace K]`), it is a profinite
group and bundles as an object of `ProfiniteGrp` via `OpenSubgroup.toProfiniteGrp` (with additive
counterpart `OpenAddSubgroup.toProfiniteAddGrp`).

When the ambient group `G` is itself totally disconnected (in particular, when `G` is locally
profinite), `TotallyDisconnectedSpace K` is synthesized automatically by
`Subtype.totallyDisconnectedSpace`.

## Main definitions

* `OpenSubgroup.toProfiniteGrp` (and `OpenAddSubgroup.toProfiniteAddGrp`): bundle a compact totally
  disconnected open subgroup of a topological group as an object of `ProfiniteGrp`.
* `OpenSubgroup.coe_toProfiniteGrp` (and `OpenAddSubgroup.coe_toProfiniteAddGrp`): the underlying
  type of `K.toProfiniteGrp hK` is `K`.
-/

public section

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- View a compact totally disconnected open subgroup of a topological group as a bundled
profinite group `ProfiniteGrp`. When the ambient group is totally disconnected,
`TotallyDisconnectedSpace K` is supplied automatically by `Subtype.totallyDisconnectedSpace`. -/
@[to_additive /-- View a compact totally disconnected open additive subgroup of a topological
additive group as a bundled profinite additive group `ProfiniteAddGrp`. When the ambient group is
totally disconnected, `TotallyDisconnectedSpace K` is supplied automatically by
`Subtype.totallyDisconnectedSpace`. -/]
def toProfiniteGrp (K : OpenSubgroup G) [TotallyDisconnectedSpace K]
    (hK : IsCompact (K : Set G)) : ProfiniteGrp :=
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  ProfiniteGrp.of K

/-- The underlying type of `K.toProfiniteGrp hK` is `K`. -/
@[to_additive (attr := simp) /-- The underlying type of `K.toProfiniteAddGrp hK` is `K`. -/]
theorem coe_toProfiniteGrp (K : OpenSubgroup G) [TotallyDisconnectedSpace K]
    (hK : IsCompact (K : Set G)) :
    (K.toProfiniteGrp hK : Type _) = K :=
  (rfl)

end OpenSubgroup

end
