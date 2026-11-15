/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Complete regularity of topological groups

The right uniformity of a topological group induces its original topology. Uniformizability
therefore makes every topological group completely regular, and a T0 topological group is T35.
The additive counterparts use the corresponding right uniformity.

## References

* Mathlib, `Topology/Algebra/IsUniformGroup/Defs.lean`, the right uniformity.
* Mathlib, `Topology/UniformSpace/Uniformizable.lean`, complete regularity of uniform spaces.
-/

public section

namespace IsTopologicalGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A topological group is completely regular for its given topology. -/
@[to_additive /-- A topological additive group is completely regular for its given topology. -/]
instance completelyRegularSpace : CompletelyRegularSpace G :=
  .of_exists_uniformSpace ⟨IsTopologicalGroup.rightUniformSpace G, rfl⟩

/-- A T0 topological group is a T35 space. -/
@[to_additive /-- A T0 topological additive group is a T35 space. -/]
instance t35Space [T0Space G] : T35Space G := ⟨⟩

end IsTopologicalGroup
