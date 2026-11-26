/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.UniformSpace.DiscreteUniformity
public import Mathlib.Topology.UniformSpace.Pi
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs

/-!
# Complements to the discrete uniformity

Complements to Mathlib's `DiscreteUniformity`: a right-uniform group whose topology is discrete
has the discrete uniformity, since its uniformity is the comap of the (discrete) neighbourhood
filter of the identity; and on a product of spaces with the discrete uniformity, agreement on
finite sets of coordinates gives a basis of the product uniformity.

## Main results

* `IsRightUniformGroup.discreteUniformity`, `IsRightUniformAddGroup.discreteUniformity` : a
  right-uniform (additive) group with the discrete topology has the discrete uniformity. Stated
  as a theorem, not an instance: together with Mathlib's `DiscreteUniformity → DiscreteTopology`
  instance it would form a resolution cycle.
* `Pi.hasBasis_uniformity_of_discreteUniformity` : on a product of spaces with the discrete
  uniformity, the relations "agree on a finite set of coordinates" form a basis of the
  uniformity.
-/

public section

open Filter
open scoped Uniformity

/-- A right-uniform group whose topology is discrete has the discrete uniformity.

A theorem rather than an instance: Mathlib's `DiscreteUniformity → DiscreteTopology`
instance points the other way, and registering both directions would loop. -/
@[to_additive /-- A right-uniform additive group whose topology is discrete has the discrete
uniformity.

A theorem rather than an instance: Mathlib's `DiscreteUniformity → DiscreteTopology`
instance points the other way, and registering both directions would loop. -/]
theorem IsRightUniformGroup.discreteUniformity {G : Type*} [Group G] [UniformSpace G]
    [IsRightUniformGroup G] [DiscreteTopology G] : DiscreteUniformity G := by
  rw [discreteUniformity_iff_eq_principal_setRelId, uniformity_eq_comap_nhds_one G, nhds_discrete,
    comap_pure]
  simp [SetRel.id, Set.ext_iff, div_eq_one, eq_comm]

/-- On a product of spaces with the discrete uniformity, the relations "agree on the finite set
`S` of coordinates" form a basis of the product uniformity. -/
theorem Pi.hasBasis_uniformity_of_discreteUniformity {ι : Type*} {α : ι → Type*}
    [∀ i, UniformSpace (α i)] [∀ i, DiscreteUniformity (α i)] :
    (𝓤 (∀ i, α i)).HasBasis Set.Finite fun S ↦ {p | ∀ i ∈ S, p.1 i = p.2 i} := by
  simp only [Pi.uniformity, DiscreteUniformity.eq_principal_setRelId, comap_principal]
  exact (hasBasis_iInf_principal_finite _).congr (fun _ ↦ Iff.rfl) fun S _ ↦ by ext; simp

namespace UniformSpace.Completion

/-- **The completion of a space with the discrete uniformity is discrete.** Such a space is complete
and Hausdorff, so the canonical map into its completion is a homeomorphism. -/
instance discreteTopology_of_discreteUniformity {α : Type*} [UniformSpace α]
    [DiscreteUniformity α] : DiscreteTopology (Completion α) :=
  (UniformCompletion.completeEquivSelf (α := α)).toHomeomorph.symm.discreteTopology

end UniformSpace.Completion
