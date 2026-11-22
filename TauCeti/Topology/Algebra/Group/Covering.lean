/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.Maps.Strict.Group
public import TauCeti.Topology.Algebra.Group.Preconnected

/-!
# Covering homomorphisms of topological groups

A surjective homomorphism that is a local homeomorphism is a covering map.
These criteria turn local information about a group homomorphism into a global covering.

The kernel of a homomorphism that is a local homeomorphism is discrete, hence central when the
source is preconnected. The quotient of the source of a continuous open homomorphism by its kernel
embeds onto the range, an open and hence closed subgroup of the target, so it is compact when the
target is. So a homomorphism to a compact group which is a local homeomorphism, such as the
universal covering group of a compact group, exhibits its source as a central extension of a
compact group by a discrete group.

## Main results

* `MonoidHom.isDiscrete_ker_of_isLocalHomeomorph`: the kernel of a local homeomorphism is discrete.
* `MonoidHom.ker_le_center_of_isLocalHomeomorph`: it is central when the source is preconnected.
* `MonoidHom.compactSpace_quotient_ker_of_isOpenMap`: the quotient by the kernel of a continuous
  open homomorphism is compact when the target is.
* `MonoidHom.isCoveringMap_of_isLocalHomeomorph_of_surjective`: a surjective homomorphism
  which is a local homeomorphism is a covering map, with its additive counterpart
  `AddMonoidHom.isCoveringMap_of_isLocalHomeomorph_of_surjective`.

## References

* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113 (2008), Exercise 2.3, for the covering-map assertion for Lie groups.
* Mathlib's `IsQuotientMap.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom`.
-/

public section

open Function Topology Set

namespace MonoidHom

variable {G K : Type*} [Group G] [TopologicalSpace G] [Group K] [TopologicalSpace K]

/-- The kernel of a homomorphism that is a local homeomorphism is discrete. -/
@[to_additive /-- The kernel of an additive homomorphism that is a local homeomorphism is
discrete. -/]
theorem isDiscrete_ker_of_isLocalHomeomorph (f : G →* K) (hf : IsLocalHomeomorph f) :
    IsDiscrete (f.ker : Set G) := by
  apply (hf.isLocalHomeomorphOn.mono (subset_univ _)).isDiscrete_of_image
  rw [← Subgroup.coe_map, Subgroup.map_ker_self, Subgroup.coe_bot]
  exact (subsingleton_singleton : ({1} : Set K).Subsingleton).isDiscrete

/-- The quotient of the source of a continuous open homomorphism to a compact group by its kernel is
compact. -/
@[to_additive /-- The quotient of the source of a continuous open additive homomorphism to a compact
additive group by its kernel is compact. -/]
theorem compactSpace_quotient_ker_of_isOpenMap [SeparatelyContinuousMul K] [CompactSpace K]
    (f : G →* K) (hc : Continuous f) (ho : IsOpenMap f) : CompactSpace (G ⧸ f.ker) := by
  -- The quotient is the range, an open and hence closed subgroup of `K`.
  have : CompactSpace f.range :=
    isCompact_iff_compactSpace.mp (f.range.isClosed_of_isOpen ho.isOpen_range).isCompact
  exact (ContinuousMulEquiv.quotientKerEquivRange (ho.isStrictMap hc)).symm.toHomeomorph
    |>.compactSpace

variable [IsTopologicalGroup G]

/-- A surjective local-homeomorphism homomorphism is a covering map. -/
@[to_additive /-- A surjective local-homeomorphism additive homomorphism is a covering map. -/]
theorem isCoveringMap_of_isLocalHomeomorph_of_surjective (f : G →* K)
    (hlocal : IsLocalHomeomorph f) (hsurj : Surjective f) : IsCoveringMap f := by
  have hq : IsOpenQuotientMap f := ⟨hsurj, hlocal.continuous, hlocal.isOpenMap⟩
  exact (hq.isQuotientMap.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
    (f.isDiscrete_ker_of_isLocalHomeomorph hlocal)).isCoveringMap

/-- The kernel of a homomorphism that is a local homeomorphism is central when the source is
preconnected. -/
@[to_additive /-- The kernel of an additive homomorphism that is a local homeomorphism is central
when the source is preconnected. -/]
theorem ker_le_center_of_isLocalHomeomorph [PreconnectedSpace G] (f : G →* K)
    (hf : IsLocalHomeomorph f) : f.ker ≤ Subgroup.center G :=
  have := SetLike.isDiscrete_iff_discreteTopology.mp (f.isDiscrete_ker_of_isLocalHomeomorph hf)
  f.ker.le_center_of_discreteTopology

end MonoidHom
