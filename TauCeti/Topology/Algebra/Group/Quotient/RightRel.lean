/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Right cosets and left cosets as topological spaces

For a subgroup `K` of a group `G` with continuous inversion, inversion `g ↦ g⁻¹` sends the right
coset `K g` to the left coset `g⁻¹ K`. Mathlib's bijection
`QuotientGroup.quotientRightRelEquivQuotientLeftRel` between the two coset spaces is therefore a
homeomorphism for their quotient topologies
(`QuotientGroup.quotientRightRelHomeomorphQuotientLeftRel`). The right coset space is the orbit
space of the action of `K` on `G` by left multiplication, so this transfers results about orbit
spaces of group actions to the coset space `G ⧸ K`.
-/

public section

namespace QuotientGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G] (K : Subgroup G)

/-- The bijection `[g] ↦ [g⁻¹]` between right and left cosets, as a homeomorphism of the
quotient topologies. -/
@[to_additive /-- The bijection `[g] ↦ [-g]` between right and left cosets, as a homeomorphism of
the quotient topologies. -/]
def quotientRightRelHomeomorphQuotientLeftRel : Quotient (rightRel K) ≃ₜ G ⧸ K where
  toEquiv := quotientRightRelEquivQuotientLeftRel K
  continuous_toFun := continuous_inv.quotient_map' fun _ _ h ↦ by
    rw [rightRel_apply] at h
    rw [leftRel_apply, inv_inv]
    simpa using K.inv_mem h
  continuous_invFun := continuous_inv.quotient_map' fun _ _ h ↦ by
    rw [leftRel_apply] at h
    rw [rightRel_apply, inv_inv]
    simpa using K.inv_mem h

@[to_additive (attr := simp)]
theorem quotientRightRelHomeomorphQuotientLeftRel_mk (g : G) :
    quotientRightRelHomeomorphQuotientLeftRel K (Quotient.mk _ g) = (g⁻¹ : G) :=
  (rfl)

@[to_additive (attr := simp)]
theorem quotientRightRelHomeomorphQuotientLeftRel_symm_mk (g : G) :
    (quotientRightRelHomeomorphQuotientLeftRel K).symm (g : G ⧸ K) = Quotient.mk _ g⁻¹ :=
  (rfl)

end QuotientGroup
