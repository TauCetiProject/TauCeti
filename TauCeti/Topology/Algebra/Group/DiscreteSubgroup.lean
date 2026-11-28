/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Traces of discrete subgroups

The trace `Γ ∩ N` of a discrete subgroup `Γ` on a subgroup `N`, presented as `Γ.subgroupOf N`, is
discrete in `N` (`Subgroup.discreteTopology_subgroupOf`). This is registered as an instance, so that
instance search finds discreteness of `Γ ∩ N` for statements about the action of `Γ ∩ N` on `N`.

Conversely, discreteness of a subgroup `K` of a topological group can be read on an open piece:
if `f : G →* G'` is an open embedding, for instance the inclusion of an open subgroup, and the
preimage of `K` under `f` is discrete, then `K` is discrete
(`Subgroup.discreteTopology_of_comap`). Only a neighbourhood of the identity matters, and `f`
carries one onto a neighbourhood of the identity of `G'`. This passes discreteness of a subgroup of
`PSL(2, ℝ)` to subgroups of `PGL(2, ℝ)` that meet the open image of `PSL(2, ℝ)` in its image.
-/

public section

open Topology

namespace Subgroup

section Trace

variable {G : Type*} [Group G] [TopologicalSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]

/-- The trace `Γ ∩ N` of a discrete subgroup on a subgroup `N` is discrete in `N`. -/
instance discreteTopology_subgroupOf (N : Subgroup G) : DiscreteTopology (Γ.subgroupOf N) :=
  .preimage_of_continuous_injective (Γ : Set G) continuous_subtypeVal Subtype.val_injective

end Trace

variable {G G' : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G']

/-- A subgroup `K` of a topological group is discrete as soon as its preimage under an open
embedding `f` is discrete: the image under `f` of a neighbourhood isolating the identity in the
preimage isolates the identity in `K`. -/
theorem discreteTopology_of_comap {f : G →* G'} (hf : IsOpenEmbedding f) {K : Subgroup G'}
    [hK : DiscreteTopology (K.comap f)] : DiscreteTopology K := by
  obtain ⟨O, hO, hO1⟩ := isOpen_induced_iff.mp ((discreteTopology_iff_isOpen_singleton_one
    (G := K.comap f)).mp hK)
  refine discreteTopology_of_isOpen_singleton_one (isOpen_induced_iff.mpr
    ⟨f '' O, hf.isOpenMap O hO, Set.ext fun ⟨k, hk⟩ ↦ ⟨?_, ?_⟩⟩)
  · rintro ⟨o, ho, rfl⟩
    have ho1 : (⟨o, hk⟩ : K.comap f) ∈ ({1} : Set (K.comap f)) := hO1 ▸ ho
    obtain rfl : o = 1 := congrArg Subtype.val ho1
    simp
  · intro h1
    obtain rfl : k = 1 := by simpa using h1
    have h1O : (1 : K.comap f) ∈ Subtype.val ⁻¹' O := hO1 ▸ rfl
    exact ⟨1, h1O, map_one f⟩

end Subgroup
