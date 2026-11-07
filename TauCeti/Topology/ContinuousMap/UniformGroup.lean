/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Algebra.UniformConvergence
public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions

/-!
# The compact-convergence uniformity on continuous maps into an additive group

The native compact-convergence uniformity makes continuous maps into a uniform additive group
a uniform additive group. This allows continuous additive embeddings of function spaces to
transport completeness without changing their compact-open topologies.
-/

public section

namespace ContinuousMap

variable {X G : Type*} [TopologicalSpace X] [UniformSpace G] [AddGroup G]
  [IsUniformAddGroup G]

/-- Compact convergence of continuous maps respects the uniform additive group structure. -/
instance instIsUniformAddGroup : IsUniformAddGroup C(X, G) := by
  let f : C(X, G) →+ UniformOnFun X G {K | IsCompact K} :=
    { toFun := toUniformOnFunIsCompact
      map_zero' := rfl
      map_add' _ _ := rfl }
  exact isUniformEmbedding_toUniformOnFunIsCompact.isUniformInducing.isUniformAddGroup f

end ContinuousMap
