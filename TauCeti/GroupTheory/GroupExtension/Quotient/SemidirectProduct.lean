/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupExtension.Basic
public import TauCeti.GroupTheory.SemidirectProduct
public import TauCeti.GroupTheory.GroupExtension.Quotient.Basic

/-!
# Quotient extensions, splittings, and semidirect products

A complement `D` of a normal subgroup `N` in `G` determines two semidirect-product models of `G`:
`SemidirectProduct.mulEquivSubgroup` on `N ⋊ D` and
`GroupExtension.Splitting.semidirectProductMulEquiv` on `N ⋊ (G ⧸ N)` attached to
`Subgroup.IsComplement'.quotientSplitting`. Their identification along `G ⧸ N ≃* D` is
`Subgroup.IsComplement'.quotientSplittingSemidirectProductMulEquiv_trans_mulEquivSubgroup` in
`TauCeti.GroupTheory.GroupExtension.Quotient.Basic`. This file promotes
`SemidirectProduct.mulEquivSubgroup` to an equivalence of group extensions onto the quotient
extension `N.quotientExtension`.

## Main definitions

* `Subgroup.IsComplement'.toGroupExtensionEquiv`: `SemidirectProduct.mulEquivSubgroup` promoted to
  an equivalence of group extensions from `SemidirectProduct.toGroupExtension` to
  `N.quotientExtension` relabelled along `G ⧸ N ≃* D`.

## Main results

* `Subgroup.IsComplement'.subtype_comp_rightHom_comp_mulEquivSubgroup_symm`: projecting
  `(SemidirectProduct.mulEquivSubgroup h).symm` to `D` is `Subgroup.IsComplement'.quotientSplitting`
  after the quotient map.
* `Subgroup.IsComplement'.toMonoidHom_splittingEquiv_toGroupExtensionEquiv_inr_splitting`:
  transporting `SemidirectProduct.inr_splitting` along `toGroupExtensionEquiv` yields `D.subtype`.
-/

public section

namespace Subgroup.IsComplement'

variable {G : Type*} [Group G] {N D : Subgroup G} [N.Normal] (h : N.IsComplement' D)

/-- Projecting `(SemidirectProduct.mulEquivSubgroup h).symm` to `D` and including into `G` agrees
with `Subgroup.IsComplement'.quotientSplitting` composed with the quotient map `G →* G ⧸ N`. -/
theorem subtype_comp_rightHom_comp_mulEquivSubgroup_symm :
    D.subtype.comp (SemidirectProduct.rightHom.comp
        (SemidirectProduct.mulEquivSubgroup h).symm.toMonoidHom) =
      h.quotientSplitting.toMonoidHom.comp (QuotientGroup.mk' N) := by
  ext g
  exact h.coe_mulEquivSubgroup_symm_right g

/-- `SemidirectProduct.mulEquivSubgroup` as an equivalence from the semidirect-product extension
`1 → N → N ⋊ D → D → 1` to `N.quotientExtension` with quotient relabelled along `G ⧸ N ≃* D`. -/
noncomputable def toGroupExtensionEquiv :
    (SemidirectProduct.toGroupExtension
      ((N.normalizerMonoidHom).comp (inclusion (N.normalizer_eq_top ▸ le_top)))).Equiv
      (N.quotientExtension.relabelQuotient h.symm.QuotientMulEquiv) where
  toMulEquiv := SemidirectProduct.mulEquivSubgroup h
  inl_comm := by
    ext n
    simp [SemidirectProduct.toGroupExtension_inl]
  rightHom_comm := by
    ext x
    simpa [SemidirectProduct.toGroupExtension_rightHom,
      -SemidirectProduct.mulEquivSubgroup_apply,
      -SemidirectProduct.rightHom_comp_mulEquivSubgroup_symm] using
      (DFunLike.congr_fun (SemidirectProduct.rightHom_comp_mulEquivSubgroup_symm h)
        (SemidirectProduct.mulEquivSubgroup h x)).symm

/-- The underlying isomorphism of `Subgroup.IsComplement'.toGroupExtensionEquiv` is
`SemidirectProduct.mulEquivSubgroup`. -/
theorem toMulEquiv_toGroupExtensionEquiv :
    h.toGroupExtensionEquiv.toMulEquiv = SemidirectProduct.mulEquivSubgroup h :=
  (rfl)

/-- Evaluating `Subgroup.IsComplement'.toGroupExtensionEquiv` applies
`SemidirectProduct.mulEquivSubgroup`. -/
@[simp]
theorem toGroupExtensionEquiv_apply
    (x : N ⋊[(N.normalizerMonoidHom).comp (inclusion (N.normalizer_eq_top ▸ le_top))] D) :
    h.toGroupExtensionEquiv x = SemidirectProduct.mulEquivSubgroup h x :=
  (rfl)

/-- Evaluating the inverse of `Subgroup.IsComplement'.toGroupExtensionEquiv` applies the inverse of
`SemidirectProduct.mulEquivSubgroup`. -/
@[simp]
theorem toGroupExtensionEquiv_symm_apply (g : G) :
    h.toGroupExtensionEquiv.symm g = (SemidirectProduct.mulEquivSubgroup h).symm g :=
  (rfl)

/-- Transporting the canonical splitting `SemidirectProduct.inr_splitting` along
`Subgroup.IsComplement'.toGroupExtensionEquiv` gives the subgroup inclusion `D →* G`. -/
@[simp]
theorem toMonoidHom_splittingEquiv_toGroupExtensionEquiv_inr_splitting :
    (h.toGroupExtensionEquiv.splittingEquiv
      (SemidirectProduct.inr_splitting _)).toMonoidHom = D.subtype := by
  ext d
  simp

end Subgroup.IsComplement'
