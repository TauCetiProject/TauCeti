/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# Transporting closed subgroups and quotients along topological group isomorphisms

An isomorphism of topological groups carries closed subgroups to closed subgroups.  This file
packages that operation as an order isomorphism and records its compatibility with normality and
quotients.  In particular, a normal closed subgroup can be transported without changing the
topological quotient it defines.

## Main definitions

* `ContinuousMulEquiv.closedSubgroupOrderIso`: transport of closed subgroups along an isomorphism
  of topological groups.
* `ContinuousMulEquiv.quotient`: the induced isomorphism of topological quotient groups.
-/

public section

namespace TauCeti

universe u v

variable {G : Type u} {H : Type v} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

/-- A topological group isomorphism transports closed subgroups, preserving inclusion. -/
def _root_.ContinuousMulEquiv.closedSubgroupOrderIso (e : G ≃ₜ* H) :
    ClosedSubgroup G ≃o ClosedSubgroup H where
  toFun K :=
    { toSubgroup := K.toSubgroup.map e.toMulEquiv.toMonoidHom
      isClosed' := by
        -- The carrier of `Subgroup.map` is stored as an existential rather than an image.
        change IsClosed (e '' (K : Set G))
        exact e.toHomeomorph.isClosed_image.mpr K.isClosed' }
  invFun L :=
    { toSubgroup := L.toSubgroup.map e.symm.toMulEquiv.toMonoidHom
      isClosed' := by
        -- The carrier of `Subgroup.map` is stored as an existential rather than an image.
        change IsClosed (e.symm '' (L : Set H))
        exact e.symm.toHomeomorph.isClosed_image.mpr L.isClosed' }
  left_inv K := ClosedSubgroup.toSubgroup_injective <| by
    -- Expose the two maps hidden by the `ClosedSubgroup` structure fields.
    change Subgroup.map e.symm.toMulEquiv.toMonoidHom
      (Subgroup.map e.toMulEquiv.toMonoidHom K.toSubgroup) = K.toSubgroup
    rw [Subgroup.map_map]
    rw [show e.symm.toMulEquiv.toMonoidHom.comp e.toMulEquiv.toMonoidHom =
      MonoidHom.id G by
        apply MonoidHom.ext
        exact e.symm_apply_apply, K.toSubgroup.map_id]
  right_inv L := ClosedSubgroup.toSubgroup_injective <| by
    -- Expose the two maps hidden by the `ClosedSubgroup` structure fields.
    change Subgroup.map e.toMulEquiv.toMonoidHom
      (Subgroup.map e.symm.toMulEquiv.toMonoidHom L.toSubgroup) = L.toSubgroup
    rw [Subgroup.map_map]
    rw [show e.toMulEquiv.toMonoidHom.comp e.symm.toMulEquiv.toMonoidHom =
      MonoidHom.id H by
        apply MonoidHom.ext
        exact e.apply_symm_apply, L.toSubgroup.map_id]
  map_rel_iff' := Subgroup.map_le_map_iff_of_injective e.injective

/-- The underlying subgroup transported by `ContinuousMulEquiv.closedSubgroupOrderIso` is the
image of the original subgroup. -/
@[simp]
theorem _root_.ContinuousMulEquiv.closedSubgroupOrderIso_apply_toSubgroup
    (e : G ≃ₜ* H) (K : ClosedSubgroup G) :
    (e.closedSubgroupOrderIso K).toSubgroup =
      K.toSubgroup.map e.toMulEquiv.toMonoidHom :=
  (rfl)

/-- The inverse transport of a closed subgroup is its image under the inverse topological group
isomorphism. -/
@[simp]
theorem _root_.ContinuousMulEquiv.closedSubgroupOrderIso_symm_apply_toSubgroup
    (e : G ≃ₜ* H) (L : ClosedSubgroup H) :
    (e.closedSubgroupOrderIso.symm L).toSubgroup =
      L.toSubgroup.map e.symm.toMulEquiv.toMonoidHom :=
  (rfl)

/-- Normality is preserved when a closed subgroup is transported along a topological group
isomorphism. -/
instance _root_.ContinuousMulEquiv.instNormalClosedSubgroupOrderIso
    (e : G ≃ₜ* H) (K : ClosedSubgroup G) [K.toSubgroup.Normal] :
    (e.closedSubgroupOrderIso K).toSubgroup.Normal :=
  Subgroup.Normal.map inferInstance e.toMulEquiv.toMonoidHom e.surjective

/-- The group isomorphism on quotients induced by a topological group isomorphism. -/
private def quotientMulEquiv (e : G ≃ₜ* H) (N : ClosedSubgroup G)
    [N.toSubgroup.Normal] :
    G ⧸ N.toSubgroup ≃* H ⧸ (e.closedSubgroupOrderIso N).toSubgroup where
  toFun := QuotientGroup.map N.toSubgroup (e.closedSubgroupOrderIso N).toSubgroup
    e.toMulEquiv.toMonoidHom (Subgroup.le_comap_map e.toMulEquiv.toMonoidHom N.toSubgroup)
  invFun := QuotientGroup.map (e.closedSubgroupOrderIso N).toSubgroup N.toSubgroup
    e.symm.toMulEquiv.toMonoidHom <| by
      rintro _ ⟨g, hg, rfl⟩
      -- Reduce membership in the comap to membership of the inverse image.
      change e.symm (e g) ∈ N.toSubgroup
      rwa [e.symm_apply_apply]
  left_inv q := Quotient.inductionOn' q fun g ↦ by
    -- Quotient induction leaves equality of the two represented classes.
    change ((e.symm (e g) : G) : G ⧸ N.toSubgroup) = (g : G ⧸ N.toSubgroup)
    rw [e.symm_apply_apply]
  right_inv q := Quotient.inductionOn' q fun h ↦ by
    -- Quotient induction leaves equality of the two represented classes.
    change ((e (e.symm h) : H) : H ⧸ (e.closedSubgroupOrderIso N).toSubgroup) =
      (h : H ⧸ (e.closedSubgroupOrderIso N).toSubgroup)
    rw [e.apply_symm_apply]
  map_mul' _ _ := map_mul _ _ _

/-- A topological group isomorphism induces an isomorphism between the quotients by corresponding
normal closed subgroups. -/
def _root_.ContinuousMulEquiv.quotient (e : G ≃ₜ* H) (N : ClosedSubgroup G)
    [N.toSubgroup.Normal] :
    G ⧸ N.toSubgroup ≃ₜ* H ⧸ (e.closedSubgroupOrderIso N).toSubgroup :=
  ContinuousMulEquiv.mk (quotientMulEquiv e N)
    ((QuotientGroup.isQuotientMap_mk N.toSubgroup).continuous_iff.mpr <| by
      exact (QuotientGroup.continuous_mk.comp e.continuous).congr fun g ↦
        (QuotientGroup.map_mk N.toSubgroup (e.closedSubgroupOrderIso N).toSubgroup
          e.toMulEquiv.toMonoidHom _ g).symm)
    ((QuotientGroup.isQuotientMap_mk
      (e.closedSubgroupOrderIso N).toSubgroup).continuous_iff.mpr <| by
        exact (QuotientGroup.continuous_mk.comp e.symm.continuous).congr fun h ↦
          (QuotientGroup.map_mk (e.closedSubgroupOrderIso N).toSubgroup N.toSubgroup
            e.symm.toMulEquiv.toMonoidHom _ h).symm)

/-- The quotient isomorphism sends the class of an element to the class of its image. -/
@[simp]
theorem _root_.ContinuousMulEquiv.quotient_mk (e : G ≃ₜ* H) (N : ClosedSubgroup G)
    [N.toSubgroup.Normal] (g : G) :
    e.quotient N (g : G ⧸ N.toSubgroup) =
      (e g : H ⧸ (e.closedSubgroupOrderIso N).toSubgroup) :=
  (rfl)

/-- The inverse quotient isomorphism sends the class of an element to the class of its inverse
image. -/
@[simp]
theorem _root_.ContinuousMulEquiv.quotient_symm_mk (e : G ≃ₜ* H) (N : ClosedSubgroup G)
    [N.toSubgroup.Normal] (h : H) :
    (e.quotient N).symm (h : H ⧸ (e.closedSubgroupOrderIso N).toSubgroup) =
      (e.symm h : G ⧸ N.toSubgroup) :=
  (rfl)

end TauCeti
