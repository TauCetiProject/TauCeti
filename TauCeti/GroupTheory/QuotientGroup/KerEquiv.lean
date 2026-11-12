/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Evaluating the first isomorphism theorem on a class

Mathlib packages the first isomorphism theorem for a surjective homomorphism `φ : G →* M` as
`QuotientGroup.quotientKerEquivOfSurjective φ hφ : G ⧸ φ.ker ≃* M`. It is defined through
`QuotientGroup.quotientKerEquivOfRightInverse` applied to a right inverse extracted from `hφ`
by choice, so evaluating it on a class otherwise means unfolding that noncomputable
implementation. Likewise, `QuotientGroup.quotientKerEquivRange φ : G ⧸ φ.ker ≃* φ.range` is
built with `MulEquiv.ofBijective` from `QuotientGroup.rangeKerLift`, and Mathlib states no
evaluation rule for it.

This file records these computation rules on classes, so that users never have to unfold the
definitions. The first two are the group-theoretic counterparts of Mathlib's
`RingHom.quotientKerEquivOfSurjective_apply_mk` and
`RingHom.quotientKerEquivOfSurjective_symm_apply`; all three belong beside their definitions in
Mathlib.

## Main statements

* `TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk`: the isomorphism
  `G ⧸ φ.ker ≃* M` sends the class of `g` to `φ g`; its additive counterpart is
  `TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_apply_mk`.
* `TauCeti.QuotientGroup.quotientKerEquivOfSurjective_symm_apply`: the inverse sends
  `φ g` back to the class of `g`; its additive counterpart is
  `TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_symm_apply`.
* `TauCeti.QuotientGroup.quotientKerEquivRange_apply_mk`: the isomorphism
  `G ⧸ φ.ker ≃* φ.range` sends the class of `g` to `φ g`; its additive counterpart is
  `TauCeti.QuotientAddGroup.quotientKerEquivRange_apply_mk`.

The first isomorphism theorem for the composite `H → G → G ⧸ N` of the inclusion of a subgroup
and a quotient map identifies `H ⧸ N.subgroupOf H` with the image of `H` in `G ⧸ N`; this is
`Subgroup.quotientSubgroupOfMulEquivMap`, with evaluation rule
`Subgroup.coe_quotientSubgroupOfMulEquivMap_mk`.
-/

public section

namespace TauCeti

namespace QuotientGroup

variable {G M : Type*} [Group G] [Group M] (φ : G →* M) (hφ : Function.Surjective φ)

/-- The first isomorphism theorem for a surjective homomorphism sends the class of `g` to
`φ g`. -/
@[to_additive (attr := simp) TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_apply_mk
  /-- The first isomorphism theorem for a surjective additive homomorphism sends the class of
  `g` to `φ g`. -/]
theorem quotientKerEquivOfSurjective_apply_mk (g : G) :
    QuotientGroup.quotientKerEquivOfSurjective φ hφ g = φ g :=
  rfl

/-- The inverse of the first isomorphism theorem sends `φ g` to the class of `g`. -/
@[to_additive (attr := simp)
  TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_symm_apply
  /-- The inverse of the additive first isomorphism theorem sends `φ g` to the class of `g`. -/]
theorem quotientKerEquivOfSurjective_symm_apply (g : G) :
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ g) = (g : G ⧸ φ.ker) :=
  (MulEquiv.symm_apply_eq _).2 (quotientKerEquivOfSurjective_apply_mk φ hφ g).symm

/-- The first isomorphism theorem onto the range sends the class of `g` to `φ g`. -/
@[to_additive (attr := simp) TauCeti.QuotientAddGroup.quotientKerEquivRange_apply_mk
  /-- The first isomorphism theorem onto the range of an additive homomorphism sends the class
  of `g` to `φ g`. -/]
theorem quotientKerEquivRange_apply_mk (g : G) :
    QuotientGroup.quotientKerEquivRange φ g = ⟨φ g, g, rfl⟩ :=
  rfl

end QuotientGroup

end TauCeti

namespace Subgroup

/-- For a normal subgroup `N` and any subgroup `H` of `G`, the quotient `H ⧸ N.subgroupOf H` is
isomorphic to the image `H.map (mk' N)` of `H` in `G ⧸ N`: this is the first isomorphism theorem
for the composite `H → G → G ⧸ N`, whose kernel is `N.subgroupOf H`. -/
noncomputable def quotientSubgroupOfMulEquivMap {G : Type*} [Group G] (N H : Subgroup G)
    [N.Normal] : H ⧸ N.subgroupOf H ≃* H.map (QuotientGroup.mk' N) :=
  QuotientGroup.liftEquiv (N.subgroupOf H) ((QuotientGroup.mk' N).subgroupMap_surjective H)
    (by rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])

/-- `quotientSubgroupOfMulEquivMap` sends the class of `h : H` to the class of `h` in `G ⧸ N`. -/
@[simp]
theorem coe_quotientSubgroupOfMulEquivMap_mk {G : Type*} [Group G] (N H : Subgroup G) [N.Normal]
    (h : H) :
    (quotientSubgroupOfMulEquivMap N H (h : H ⧸ N.subgroupOf H) : G ⧸ N) = (h : G) :=
  (rfl)

end Subgroup
