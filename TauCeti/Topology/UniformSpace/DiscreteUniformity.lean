/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.UniformSpace.DiscreteUniformity
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.UniformSpace.Completion

/-!
# Discrete topological groups have the discrete uniformity

A complement to Mathlib's `DiscreteUniformity`: a right-uniform additive group whose topology is
discrete has the discrete uniformity, since its uniformity is the comap of the (discrete)
neighbourhood filter of zero. The separated completion of a space with the discrete uniformity is
discrete, since such a space is already complete and Hausdorff.

## Main results

* `DiscreteUniformity.of_discreteTopology` : a right-uniform additive group with discrete topology
  has the discrete uniformity. Stated as a theorem, not an instance: together with Mathlib's
  `DiscreteUniformity → DiscreteTopology` instance it would form a resolution cycle. It lives
  in the root `DiscreteUniformity` namespace it extends, following this repository's
  convention for lemmas about external types.
* `UniformSpace.Completion.discreteTopology_of_discreteUniformity` : the completion of a space with
  the discrete uniformity is discrete, registered as an instance.
-/

public section

namespace DiscreteUniformity

open Filter

/-- A right-uniform additive group whose topology is discrete has the discrete uniformity.

A theorem rather than an instance: Mathlib's `DiscreteUniformity → DiscreteTopology`
instance points the other way, and registering both directions would loop. -/
theorem of_discreteTopology {G : Type*} [AddGroup G] [UniformSpace G]
    [IsRightUniformAddGroup G] [DiscreteTopology G] : DiscreteUniformity G := by
  rw [discreteUniformity_iff_setRelId_mem_uniformity, uniformity_eq_comap_nhds_zero G]
  refine Filter.mem_comap.mpr ⟨{0}, (isOpen_discrete _).mem_nhds rfl, fun p hp ↦ ?_⟩
  simpa [SetRel.id, sub_eq_zero, eq_comm] using hp

end DiscreteUniformity

namespace UniformSpace.Completion

/-- **The completion of a space with the discrete uniformity is discrete.** Such a space is complete
and Hausdorff, so the canonical map into its completion is a homeomorphism. -/
instance discreteTopology_of_discreteUniformity {α : Type*} [UniformSpace α]
    [DiscreteUniformity α] : DiscreteTopology (Completion α) :=
  (UniformCompletion.completeEquivSelf (α := α)).toHomeomorph.symm.discreteTopology

end UniformSpace.Completion
