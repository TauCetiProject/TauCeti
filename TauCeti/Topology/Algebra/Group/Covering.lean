/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Quotient

/-!
# Covering homomorphisms of topological groups

A surjective homomorphism that is a local homeomorphism is a covering map.
These criteria turn local information about a group homomorphism into a global covering.

## Main results

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

variable {G K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group K] [TopologicalSpace K]

/-- A surjective local-homeomorphism homomorphism is a covering map. -/
@[to_additive /-- A surjective local-homeomorphism additive homomorphism is a covering map. -/]
theorem isCoveringMap_of_isLocalHomeomorph_of_surjective (f : G →* K)
    (hlocal : IsLocalHomeomorph f) (hsurj : Surjective f) : IsCoveringMap f := by
  have hq : IsOpenQuotientMap f := ⟨hsurj, hlocal.continuous, hlocal.isOpenMap⟩
  have hdiscrete : IsDiscrete (f.ker : Set G) := by
    apply (hlocal.isLocalHomeomorphOn.mono (subset_univ _)).isDiscrete_of_image
    rw [← Subgroup.coe_map, Subgroup.map_ker_self, Subgroup.coe_bot]
    exact (subsingleton_singleton : ({1} : Set K).Subsingleton).isDiscrete
  exact (hq.isQuotientMap.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
    hdiscrete).isCoveringMap

end MonoidHom
