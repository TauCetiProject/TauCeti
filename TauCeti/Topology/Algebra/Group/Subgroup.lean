/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Topological closure and additive subgroups

Converting a subgroup to an additive subgroup commutes with topological closure. This
connects topological generation in a group with additive generation on its `Additive` type tag.
-/

public section

namespace Subgroup

/-- Converting a subgroup to an additive subgroup commutes with topological closure. -/
@[simp]
theorem toAddSubgroup_topologicalClosure {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (S : Subgroup G) :
    S.topologicalClosure.toAddSubgroup = S.toAddSubgroup.topologicalClosure :=
  -- `Additive G` inherits the topology of `G`, and both subgroup closures use the
  -- set-theoretic closure of the same carrier. The definitional reduction is confined
  -- to this bridge so consumers can rewrite without unfolding these representations.
  (rfl)

end Subgroup
