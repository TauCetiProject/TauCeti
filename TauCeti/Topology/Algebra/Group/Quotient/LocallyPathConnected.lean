/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Quotients of locally path-connected groups are locally path-connected

The quotient `G ⧸ S` of a locally path-connected topological group by a subgroup carries the
quotient topology, so it is locally path-connected by Mathlib's
`Quotient.locallyPathConnectedSpace` (`QuotientGroup.instLocallyPathConnectedSpace`, and
`QuotientAddGroup.instLocallyPathConnectedSpace` for additive groups). Instance search does not
find that instance on `G ⧸ S` by itself, because the quotient setoid is not syntactically visible.
-/

public section

namespace QuotientGroup

/-- The quotient of a locally path-connected group by a subgroup is locally path-connected. -/
@[to_additive /-- The quotient of a locally path-connected additive group by a subgroup is
locally path-connected. -/]
instance instLocallyPathConnectedSpace {G : Type*} [Group G] [TopologicalSpace G]
    [LocallyPathConnectedSpace G] (S : Subgroup G) : LocallyPathConnectedSpace (G ⧸ S) :=
  Quotient.locallyPathConnectedSpace

end QuotientGroup
