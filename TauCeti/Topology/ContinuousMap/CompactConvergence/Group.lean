/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
public import Mathlib.Topology.Algebra.UniformConvergence
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Compact convergence is a uniform group structure

For a uniform group `G`, the uniformity of compact convergence on the continuous maps `C(α, G)`
is a uniform group structure for pointwise multiplication. Indeed, it is induced by the
multiplicative embedding of `C(α, G)` into the maps `α → G` with uniform convergence on compact
sets (`ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact`), which form a uniform group.

In particular, continuous homomorphisms of topological groups into `C(α, G)` are uniformly
continuous, so they map Cauchy filters to Cauchy filters; this is how completeness of `C(α, G)`
for compact convergence is used in limits of spaces of maps.
-/

public section

namespace ContinuousMap

variable {α G : Type*} [TopologicalSpace α] [UniformSpace G] [Group G] [IsUniformGroup G]

/-- The uniformity of compact convergence on `C(α, G)` is a uniform group structure. -/
@[to_additive /-- The uniformity of compact convergence on `C(α, G)` is a uniform additive group
structure. -/]
instance instIsUniformGroup : IsUniformGroup C(α, G) :=
  isUniformEmbedding_toUniformOnFunIsCompact.isUniformInducing.isUniformGroup
    (MonoidHom.mk' (toUniformOnFunIsCompact : C(α, G) → _) fun _ _ ↦ rfl)

end ContinuousMap
