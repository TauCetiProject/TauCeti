/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Hom
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

This file records these computation rules on classes, together with the evaluation rule of the
underlying kernel lift `QuotientGroup.rangeKerLift`, so that users never have to unfold the
definitions. The first two are the group-theoretic counterparts of Mathlib's
`RingHom.quotientKerEquivOfSurjective_apply_mk` and
`RingHom.quotientKerEquivOfSurjective_symm_apply`; all of them belong beside their definitions in
Mathlib.

## Main statements

* `TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk`: the isomorphism
  `G ⧸ φ.ker ≃* M` sends the class of `g` to `φ g`; its additive counterpart is
  `TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_apply_mk`.
* `TauCeti.QuotientGroup.quotientKerEquivOfSurjective_symm_apply`: the inverse sends
  `φ g` back to the class of `g`; its additive counterpart is
  `TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_symm_apply`.
* `TauCeti.QuotientGroup.rangeKerLift_mk`: the kernel lift `G ⧸ φ.ker →* φ.range` sends the
  class of `g` to `φ.rangeRestrict g`; its additive counterpart is
  `TauCeti.QuotientAddGroup.rangeKerLift_mk`.
* `TauCeti.QuotientGroup.quotientKerEquivRange_apply_mk`: the isomorphism
  `G ⧸ φ.ker ≃* φ.range` sends the class of `g` to `φ g`; its additive counterpart is
  `TauCeti.QuotientAddGroup.quotientKerEquivRange_apply_mk`.
* `TauCeti.QuotientGroup.quotientKerEquivRange_symm_apply`: the inverse sends `φ g` back to the
  class of `g`; its additive counterpart is
  `TauCeti.QuotientAddGroup.quotientKerEquivRange_symm_apply`.
* `AddSubgroup.kerCompHomSubtypeMulEquiv` and `AddSubgroup.kerCompHomInclusionMulEquiv`:
  characters of an abelian group trivial on a subgroup correspond multiplicatively to characters of
  the quotient, transferred from Mathlib's `AddMonoidHom.domRestrictHomKerEquiv`.

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

/-- The kernel lift onto the range sends the class of `g` to `φ.rangeRestrict g`. -/
@[to_additive (attr := simp) TauCeti.QuotientAddGroup.rangeKerLift_mk
  /-- The kernel lift onto the range of an additive homomorphism sends the class of `g` to
  `φ.rangeRestrict g`. -/]
theorem rangeKerLift_mk (g : G) : QuotientGroup.rangeKerLift φ g = φ.rangeRestrict g :=
  rfl

/-- The first isomorphism theorem onto the range sends the class of `g` to `φ g`. -/
@[to_additive (attr := simp) TauCeti.QuotientAddGroup.quotientKerEquivRange_apply_mk
  /-- The first isomorphism theorem onto the range of an additive homomorphism sends the class
  of `g` to `φ g`. -/]
theorem quotientKerEquivRange_apply_mk (g : G) :
    QuotientGroup.quotientKerEquivRange φ g = ⟨φ g, g, rfl⟩ :=
  rfl

/-- The inverse of the first isomorphism theorem onto the range sends `φ g` to the class of
`g`. -/
@[to_additive (attr := simp) TauCeti.QuotientAddGroup.quotientKerEquivRange_symm_apply
  /-- The inverse of the first isomorphism theorem onto the range of an additive homomorphism
  sends `φ g` to the class of `g`. -/]
theorem quotientKerEquivRange_symm_apply (g : G) :
    (QuotientGroup.quotientKerEquivRange φ).symm (φ.rangeRestrict g) = (g : G ⧸ φ.ker) :=
  (MulEquiv.symm_apply_eq _).2 (quotientKerEquivRange_apply_mk φ g).symm

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

namespace AddSubgroup

/-- Characters of an abelian group `G` into `U` that vanish on an additive subgroup `N`
correspond multiplicatively to characters of the quotient `G ⧸ N`, via
`AddMonoidHom.domRestrictHomKerEquiv`. -/
def kerCompHomSubtypeMulEquiv {G : Type*} [AddCommGroup G] (N : AddSubgroup G)
    (U : Type*) [CommGroup U] :
    (MonoidHom.compHom' (P := U) N.subtype.toMultiplicative).ker ≃*
      (Multiplicative (G ⧸ N) →* U) where
  toFun ψ := AddMonoidHom.toMultiplicativeLeft <|
    AddMonoidHom.domRestrictHomKerEquiv (Additive U) N
      ⟨ψ.val.toAdditiveRight, AddMonoidHom.mem_ker.2 <| AddMonoidHom.ext fun x ↦
        congrArg Additive.ofMul (DFunLike.congr_fun ψ.property (.ofAdd x))⟩
  invFun η :=
    ⟨((AddMonoidHom.domRestrictHomKerEquiv (Additive U) N).symm
        η.toAdditiveRight).val.toMultiplicativeLeft,
      MonoidHom.mem_ker.2 <| MonoidHom.ext fun x ↦ by
        simpa using congrArg Additive.toMul <| DFunLike.congr_fun
          ((AddMonoidHom.domRestrictHomKerEquiv (Additive U) N).symm
            η.toAdditiveRight).property x.toAdd⟩
  left_inv ψ := Subtype.ext <| MonoidHom.ext fun x ↦ by
    have := (AddMonoidHom.domRestrictHomKerEquiv (Additive U) N).symm_apply_apply
      ⟨ψ.val.toAdditiveRight, AddMonoidHom.mem_ker.2 <| AddMonoidHom.ext fun y ↦
        congrArg Additive.ofMul (DFunLike.congr_fun ψ.property (.ofAdd y))⟩
    exact congrArg Additive.toMul (DFunLike.congr_fun (congrArg Subtype.val this) x.toAdd)
  right_inv η := MonoidHom.ext fun q ↦ by
    have := (AddMonoidHom.domRestrictHomKerEquiv (Additive U) N).apply_symm_apply
      η.toAdditiveRight
    exact congrArg Additive.toMul (DFunLike.congr_fun this q.toAdd)
  map_mul' ψ₁ ψ₂ := MonoidHom.ext fun q ↦ by
    have hmap : AddMonoidHom.domRestrictHomKerEquiv (Additive U) N
          ⟨(ψ₁ * ψ₂).val.toAdditiveRight, AddMonoidHom.mem_ker.2 <| AddMonoidHom.ext fun x ↦
            congrArg Additive.ofMul (DFunLike.congr_fun (ψ₁ * ψ₂).property (.ofAdd x))⟩ =
        AddMonoidHom.domRestrictHomKerEquiv (Additive U) N
          ⟨ψ₁.val.toAdditiveRight, AddMonoidHom.mem_ker.2 <| AddMonoidHom.ext fun x ↦
            congrArg Additive.ofMul (DFunLike.congr_fun ψ₁.property (.ofAdd x))⟩ +
        AddMonoidHom.domRestrictHomKerEquiv (Additive U) N
          ⟨ψ₂.val.toAdditiveRight, AddMonoidHom.mem_ker.2 <| AddMonoidHom.ext fun x ↦
            congrArg Additive.ofMul (DFunLike.congr_fun ψ₂.property (.ofAdd x))⟩ :=
      (AddMonoidHom.domRestrictHomKerEquiv (Additive U) N).map_add
        ⟨ψ₁.val.toAdditiveRight, _⟩ ⟨ψ₂.val.toAdditiveRight, _⟩
    exact congrArg Additive.toMul (DFunLike.congr_fun hmap q.toAdd)

/-- `kerCompHomSubtypeMulEquiv` evaluates on the class of `x : G` as `ψ.val (.ofAdd x)`. -/
@[simp]
theorem kerCompHomSubtypeMulEquiv_apply {G : Type*} [AddCommGroup G] (N : AddSubgroup G)
    (U : Type*) [CommGroup U]
    (ψ : (MonoidHom.compHom' (P := U) N.subtype.toMultiplicative).ker) (x : G) :
    kerCompHomSubtypeMulEquiv N U ψ (.ofAdd (QuotientAddGroup.mk x)) = ψ.val (.ofAdd x) := (rfl)

/-- The inverse of `kerCompHomSubtypeMulEquiv` precomposes with the quotient map. -/
@[simp]
theorem kerCompHomSubtypeMulEquiv_symm_apply_coe {G : Type*} [AddCommGroup G] (N : AddSubgroup G)
    (U : Type*) [CommGroup U] (η : Multiplicative (G ⧸ N) →* U) :
    ((kerCompHomSubtypeMulEquiv N U).symm η : Multiplicative G →* U) =
      η.comp (QuotientAddGroup.mk' N).toMultiplicative := by
  ext x
  rfl

/-- For nested additive subgroups `H ≤ M` and a commutative group `U`, characters of `M` trivial on
`H` correspond multiplicatively to characters of `M ⧸ H.addSubgroupOf M`. -/
def kerCompHomInclusionMulEquiv {L : Type*} [AddCommGroup L] {H M : AddSubgroup L} (hHM : H ≤ M)
    (U : Type*) [CommGroup U] :
    (MonoidHom.compHom' (P := U) (AddSubgroup.inclusion hHM).toMultiplicative).ker ≃*
      (Multiplicative (M ⧸ H.addSubgroupOf M) →* U) :=
  (MulEquiv.subgroupCongr (by
    ext ψ
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    refine ⟨fun h ↦ MonoidHom.ext fun a ↦
        DFunLike.congr_fun h (.ofAdd ⟨a.toAdd.val, a.toAdd.property⟩),
      fun h ↦ MonoidHom.ext fun a ↦
        DFunLike.congr_fun h
          (.ofAdd ⟨⟨a.toAdd.val, hHM a.toAdd.property⟩, a.toAdd.property⟩)⟩)).trans
    ((H.addSubgroupOf M).kerCompHomSubtypeMulEquiv U)

/-- `kerCompHomInclusionMulEquiv` evaluates on the class of `x : M` as `ψ.val (.ofAdd x)`. -/
@[simp]
theorem kerCompHomInclusionMulEquiv_apply {L : Type*} [AddCommGroup L] {H M : AddSubgroup L}
    (hHM : H ≤ M) (U : Type*) [CommGroup U]
    (ψ : (MonoidHom.compHom' (P := U) (AddSubgroup.inclusion hHM).toMultiplicative).ker)
    (x : M) :
    kerCompHomInclusionMulEquiv hHM U ψ (.ofAdd (QuotientAddGroup.mk x)) = ψ.val (.ofAdd x) := (rfl)

/-- The inverse of `kerCompHomInclusionMulEquiv` precomposes with the quotient map. -/
@[simp]
theorem kerCompHomInclusionMulEquiv_symm_apply_coe {L : Type*} [AddCommGroup L]
    {H M : AddSubgroup L} (hHM : H ≤ M) (U : Type*) [CommGroup U]
    (η : Multiplicative (M ⧸ H.addSubgroupOf M) →* U) :
    ((kerCompHomInclusionMulEquiv hHM U).symm η : Multiplicative M →* U) =
      η.comp (QuotientAddGroup.mk' (H.addSubgroupOf M)).toMultiplicative := by
  ext x
  rfl

end AddSubgroup
