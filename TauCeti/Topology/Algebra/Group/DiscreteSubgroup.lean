/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Topology.Constructions

/-!
# Traces of discrete subgroups

The trace `Γ ∩ N` of a discrete subgroup `Γ` on a subgroup `N`, presented as `Γ.subgroupOf N`, is
discrete in `N` (`Subgroup.discreteTopology_subgroupOf`). This is registered as an instance, so that
instance search finds discreteness of `Γ ∩ N` for statements about the action of `Γ ∩ N` on `N`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]

/-- The trace `Γ ∩ N` of a discrete subgroup on a subgroup `N` is discrete in `N`. -/
instance discreteTopology_subgroupOf (N : Subgroup G) : DiscreteTopology (Γ.subgroupOf N) :=
  .preimage_of_continuous_injective (Γ : Set G) continuous_subtypeVal Subtype.val_injective

end Subgroup
