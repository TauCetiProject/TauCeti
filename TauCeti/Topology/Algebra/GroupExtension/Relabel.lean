/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.GroupExtension.Profinite

/-!
# Relabelling profinite group extensions

An extension is unchanged when its kernel and quotient are replaced by continuously isomorphic
groups, provided the two prescribed actions correspond. This file packages that transport for
`ProfiniteGroupExtension`, retaining the same profinite total group.

The construction is useful when a quotient presented by a free profinite group and a Galois group
are canonically isomorphic but not definitionally the same type.

-/

public section

namespace TauCeti.ProfiniteGroupExtension

universe u v

variable {G : Type u} {M : Type v} [Group G] [TopologicalSpace G]
  [CommGroup M] [TopologicalSpace M] [MulDistribMulAction G M]

/-- Relabel the kernel and quotient of a profinite extension along continuous multiplicative
equivalences which identify the prescribed actions. The total group is unchanged. -/
@[expose] def relabel (X : ProfiniteGroupExtension G M)
    {G' : Type u} {M' : Type v} [Group G'] [TopologicalSpace G']
    [CommGroup M'] [TopologicalSpace M'] [MulDistribMulAction G' M']
    (eG : G ≃ₜ* G') (eM : M' ≃ₜ* M)
    (hsmul : ∀ (g : G) (m : M'), eM (eG g • m) = g • eM m) :
    ProfiniteGroupExtension G' M' where
  E := X.E
  toGroupExtension := _root_.GroupExtension.relabel X.toGroupExtension
    eM.toMulEquiv eG.toMulEquiv
  continuous_inl := by
    rw [GroupExtension.relabel_inl]
    exact X.continuous_inl.comp eM.continuous
  continuous_rightHom := by
    rw [GroupExtension.relabel_rightHom]
    exact eG.continuous.comp X.continuous_rightHom
  inducesAction := GroupExtension.inducesAction_iff.mpr <| by
    intro (x : X.E) (m : M')
    apply (_root_.GroupExtension.relabel X.toGroupExtension
      eM.toMulEquiv eG.toMulEquiv).inl_injective
    rw [GroupExtension.inl_conjAct_comm]
    simp only [GroupExtension.relabel_inl, GroupExtension.relabel_rightHom,
      MonoidHom.comp_apply]
    -- Expose the coercions of the two equivalences so the action-compatibility equation matches.
    change x * X.toGroupExtension.inl (eM m) * x⁻¹ =
      X.toGroupExtension.inl (eM (eG (X.toGroupExtension.rightHom x) • m))
    rw [hsmul]
    rw [← (GroupExtension.inducesAction_iff.mp X.inducesAction) x (eM m),
      GroupExtension.inl_conjAct_comm]

/-- Relabelling composes the old inclusion with the kernel equivalence. -/
@[simp]
theorem relabel_inl (X : ProfiniteGroupExtension G M)
    {G' : Type u} {M' : Type v} [Group G'] [TopologicalSpace G']
    [CommGroup M'] [TopologicalSpace M'] [MulDistribMulAction G' M']
    (eG : G ≃ₜ* G') (eM : M' ≃ₜ* M)
    (hsmul : ∀ (g : G) (m : M'), eM (eG g • m) = g • eM m) :
    (X.relabel eG eM hsmul).toGroupExtension.inl =
      X.toGroupExtension.inl.comp eM.toMulEquiv.toMonoidHom :=
  GroupExtension.relabel_inl _ _ _

/-- Relabelling composes the old projection with the quotient equivalence. -/
@[simp]
theorem relabel_rightHom (X : ProfiniteGroupExtension G M)
    {G' : Type u} {M' : Type v} [Group G'] [TopologicalSpace G']
    [CommGroup M'] [TopologicalSpace M'] [MulDistribMulAction G' M']
    (eG : G ≃ₜ* G') (eM : M' ≃ₜ* M)
    (hsmul : ∀ (g : G) (m : M'), eM (eG g • m) = g • eM m) :
    (X.relabel eG eM hsmul).toGroupExtension.rightHom =
      eG.toMulEquiv.toMonoidHom.comp X.toGroupExtension.rightHom :=
  GroupExtension.relabel_rightHom _ _ _

end TauCeti.ProfiniteGroupExtension
