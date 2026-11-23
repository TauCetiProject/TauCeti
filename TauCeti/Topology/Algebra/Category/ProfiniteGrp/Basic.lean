/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# Compact subgroups as profinite groups

A compact subgroup of a totally disconnected topological group is compact and totally
disconnected in the subspace topology, hence a profinite group. This applies in particular to the
compact open subgroups of a locally profinite group.

## Main definitions

* `ProfiniteGrp.ofCompactSubgroup`: a compact subgroup of a totally disconnected topological
  group, as a profinite group.
* `ProfiniteGrp.coe_ofCompactSubgroup`: its underlying type is the subgroup.

Both have additive versions.
-/

@[expose] public section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TotallyDisconnectedSpace G]

/-- A compact subgroup of a totally disconnected topological group, as a profinite group. This
applies to every compact open subgroup of a locally profinite group. -/
@[to_additive /-- A compact additive subgroup of a totally disconnected topological additive
group, as a profinite additive group. -/]
def ProfiniteGrp.ofCompactSubgroup (H : Subgroup G) (hH : IsCompact (H : Set G)) : ProfiniteGrp :=
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hH
  ProfiniteGrp.of H

/-- The underlying type of `ProfiniteGrp.ofCompactSubgroup H hH` is `H`. -/
@[to_additive (attr := simp) /-- The underlying type of
`ProfiniteAddGrp.ofCompactAddSubgroup H hH` is `H`. -/]
lemma ProfiniteGrp.coe_ofCompactSubgroup (H : Subgroup G) (hH : IsCompact (H : Set G)) :
    (ProfiniteGrp.ofCompactSubgroup H hH : Type _) = H :=
  rfl
