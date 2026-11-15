/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Defs

/-!
# Open quotient maps

An open quotient map `π : X → Y` commutes with taking frontiers of saturated sets: if `A` is the
full preimage of its image, the frontier of `π '' A` is the image of the frontier of `A`. This is
what lets a decomposition of `X` into pieces meeting along their frontiers descend to a quotient.

Every homeomorphism is an open quotient map (`IsHomeomorph.isOpenQuotientMap`), and discrete
topologies descend along coinducing, quotient, and open quotient maps
(`Topology.IsCoinducing.discreteTopology`, `Topology.IsQuotientMap.discreteTopology`,
`IsOpenQuotientMap.discreteTopology`).
-/

public section

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {π : X → Y}

/-- The frontier of the image of a saturated set under an open quotient map is the image of its
frontier. -/
theorem IsOpenQuotientMap.frontier_image_of_preimage_image_eq (hπ : IsOpenQuotientMap π)
    {A : Set X} (hA : π ⁻¹' (π '' A) = A) : frontier (π '' A) = π '' frontier A := by
  rw [← image_preimage_eq (frontier (π '' A)) hπ.surjective,
    hπ.isOpenMap.preimage_frontier_eq_frontier_preimage hπ.continuous, hA]

/-- A homeomorphism is an open quotient map. -/
theorem IsHomeomorph.isOpenQuotientMap (hπ : IsHomeomorph π) : IsOpenQuotientMap π :=
  ⟨hπ.surjective, hπ.continuous, hπ.isOpenMap⟩

/-- A coinducing map out of a discrete space has discrete codomain. -/
theorem Topology.IsCoinducing.discreteTopology [DiscreteTopology X]
    (hπ : Topology.IsCoinducing π) : DiscreteTopology Y := by
  rw [discreteTopology_iff_forall_isOpen]
  exact fun s ↦ hπ.isOpen_preimage.mp (isOpen_discrete _)

/-- A quotient map out of a discrete space has discrete codomain. -/
theorem Topology.IsQuotientMap.discreteTopology [DiscreteTopology X]
    (hπ : Topology.IsQuotientMap π) : DiscreteTopology Y :=
  hπ.isCoinducing.discreteTopology

/-- An open quotient map out of a discrete space has discrete codomain. -/
theorem IsOpenQuotientMap.discreteTopology [DiscreteTopology X]
    (hπ : IsOpenQuotientMap π) : DiscreteTopology Y :=
  hπ.isQuotientMap.discreteTopology
