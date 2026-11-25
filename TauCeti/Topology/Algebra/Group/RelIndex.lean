/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Open subgroups have finite index in compact subgroups

In a topological group, an open subgroup `U'` has finite index in every compact subgroup `U`
(`TauCeti.relIndex_ne_zero_of_isOpen_of_isCompact`): `U' ∩ U` is an open subgroup of the compact
group `U`, and the cosets of an open subgroup form an open cover by disjoint sets.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **An open subgroup has finite index in a compact subgroup.** -/
theorem relIndex_ne_zero_of_isOpen_of_isCompact {U U' : Subgroup G}
    (hU' : IsOpen (U' : Set G)) (hU : IsCompact (U : Set G)) : U'.relIndex U ≠ 0 := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have := Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen U U' hU')
  exact Subgroup.index_ne_zero_of_finite

end TauCeti
