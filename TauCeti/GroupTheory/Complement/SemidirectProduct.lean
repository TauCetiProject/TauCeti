/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupExtension.Basic
public import TauCeti.GroupTheory.SemidirectProduct
public import TauCeti.GroupTheory.GroupExtension.Quotient.Local

/-!
# Complements, quotient splittings, and semidirect products

A complement `D` of a normal subgroup `N` in `G` determines two semidirect-product models of `G`:
`SemidirectProduct.mulEquivSubgroup` on `N ⋊ D` and
`GroupExtension.Splitting.semidirectProductMulEquiv` on `N ⋊ (G ⧸ N)` attached to
`Subgroup.IsComplement'.quotientSplitting`. This file connects both models to the quotient
extension `N.quotientExtension` and extends the semidirect-product decomposition to local
complements `N.IsLocalComplement K H` inside an intermediate subgroup `H` in which `N` is normal.

## Main definitions

* `Subgroup.IsComplement'.toGroupExtensionEquiv`: `SemidirectProduct.mulEquivSubgroup` promoted to
  an equivalence of group extensions from `SemidirectProduct.toGroupExtension` to
  `N.quotientExtension` relabelled along `G ⧸ N ≃* D`.
* `Subgroup.IsLocalComplement.semidirectProductMulEquiv`: the internal semidirect-product
  isomorphism `N ⋊ K ≃* H` determined by a local complement `K` of `N` in `H` when `N` is normal
  in `H`.

## Main results

* `Subgroup.IsComplement'.congr_quotientMulEquiv_trans_mulEquivSubgroup`:
  `SemidirectProduct.mulEquivSubgroup` agrees with the semidirect-product isomorphism of
  `Subgroup.IsComplement'.quotientSplitting` along `G ⧸ N ≃* D`.
* `Subgroup.IsComplement'.toMonoidHom_splittingEquiv_toGroupExtensionEquiv_inr_splitting`:
  transporting `SemidirectProduct.inr_splitting` along `toGroupExtensionEquiv` yields `D.subtype`.
* `Subgroup.IsLocalComplement.toEquiv_semidirectProductMulEquiv`,
  `Subgroup.IsLocalComplement.toEquiv_semidirectProductMulEquiv_symm`:
  `semidirectProductMulEquiv` and `Subgroup.IsLocalComplement.equiv` are mutually inverse up to
  `SemidirectProduct.equivProd`.
* `Subgroup.IsLocalComplement.semidirectProductMulEquiv_symm_left`,
  `Subgroup.IsLocalComplement.semidirectProductMulEquiv_symm_right`: the components of
  `semidirectProductMulEquiv.symm` are `leftProjection` and `rightProjection`.
* `Subgroup.IsLocalComplement.congr_subgroupOfEquivOfLe_trans_semidirectProductMulEquiv`:
  `semidirectProductMulEquiv` agrees with `SemidirectProduct.mulEquivSubgroup` on `H` along the
  identifications `N.subgroupOf H ≃* N` and `K.subgroupOf H ≃* K`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

namespace IsComplement'

variable {N D : Subgroup G} [N.Normal] (h : N.IsComplement' D)

/-- Coercing the `D`-component of `(SemidirectProduct.mulEquivSubgroup h).symm g` to `G` recovers
the quotient splitting of `D` evaluated at the coset of `g`. -/
theorem coe_mulEquivSubgroup_symm_right_eq_quotientSplitting (g : G) :
    (((SemidirectProduct.mulEquivSubgroup h).symm g).right : G) =
      h.quotientSplitting (g : G ⧸ N) := by
  rw [SemidirectProduct.mulEquivSubgroup_symm_right, h.quotientSplitting_mk_eq_coe_equiv_snd]

/-- Projecting `(SemidirectProduct.mulEquivSubgroup h).symm` to `D` and including into `G` agrees
with `Subgroup.IsComplement'.quotientSplitting` composed with the quotient map `G →* G ⧸ N`. -/
theorem subtype_comp_rightHom_comp_mulEquivSubgroup_symm :
    D.subtype.comp (SemidirectProduct.rightHom.comp
        (SemidirectProduct.mulEquivSubgroup h).symm.toMonoidHom) =
      h.quotientSplitting.toMonoidHom.comp (QuotientGroup.mk' N) := by
  ext g
  exact h.coe_mulEquivSubgroup_symm_right_eq_quotientSplitting g

/-- Conjugation by `Subgroup.IsComplement'.quotientSplitting` on `N` intertwines with the
normalizer action of `D` along `G ⧸ N ≃* D`. -/
theorem quotientSplitting_conjAct_comm (q : G ⧸ N) :
    (h.quotientSplitting.conjAct q).trans (MulEquiv.refl N) =
      (MulEquiv.refl N).trans
        (((N.normalizerMonoidHom).comp (inclusion (N.normalizer_eq_top ▸ le_top)))
          (h.symm.QuotientMulEquiv q)) := by
  ext n
  have hconj := N.quotientExtension.inl_conjAct_comm (e := h.quotientSplitting q) (n := n)
  rw [quotientExtension_inl, subtype_apply, quotientSplitting_apply] at hconj
  simpa [GroupExtension.Splitting.conjAct, quotientSplitting_apply] using hconj

/-- Transporting the acting factor along `G ⧸ N ≃* D` identifies
`SemidirectProduct.mulEquivSubgroup` with the semidirect-product isomorphism attached to
`Subgroup.IsComplement'.quotientSplitting`. -/
theorem congr_quotientMulEquiv_trans_mulEquivSubgroup :
    (SemidirectProduct.congr (MulEquiv.refl N) h.symm.QuotientMulEquiv
        h.quotientSplitting_conjAct_comm).trans (SemidirectProduct.mulEquivSubgroup h) =
      h.quotientSplitting.semidirectProductMulEquiv := by
  ext x
  rw [GroupExtension.Splitting.semidirectProductMulEquiv,
    GroupExtension.Splitting.semidirectProductToGroupExtensionEquiv]
  simp [quotientSplitting_apply]

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
    have hx := DFunLike.congr_fun
      (SemidirectProduct.rightHom_comp_mulEquivSubgroup_symm h).symm
      (SemidirectProduct.mulEquivSubgroup h x)
    simpa only [Function.comp_apply, GroupExtension.relabelQuotient_rightHom,
      quotientExtension_rightHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MonoidHom.coe_ofClass, MulEquiv.symm_apply_apply,
      SemidirectProduct.toGroupExtension_rightHom] using congrArg Subtype.val hx

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
  have hinr : SemidirectProduct.inr_splitting
      ((N.normalizerMonoidHom).comp (inclusion (N.normalizer_eq_top ▸ le_top))) d =
      SemidirectProduct.inr d := by
    rw [← GroupExtension.Splitting.toMonoidHom_apply, SemidirectProduct.inr_splitting]
  simp [hinr]

end IsComplement'

namespace IsLocalComplement

variable {N K H : Subgroup G} [(N.subgroupOf H).Normal] (h : N.IsLocalComplement K H)

/-- The internal semidirect-product isomorphism `N ⋊ K ≃* H` determined by a local complement `K`
of `N` in `H`, when `N` is normal in `H`. -/
noncomputable def semidirectProductMulEquiv :
    N ⋊[(N.normalizerMonoidHom).comp (inclusion h.right_le_normalizer)] K ≃* H :=
  { SemidirectProduct.equivProd.trans h.equiv.symm with
    map_mul' x y := by
      apply Subtype.ext
      simp only [Equiv.toFun_as_coe, Equiv.trans_apply, SemidirectProduct.equivProd_apply,
        coe_mul, coe_equiv_symm_apply, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
        MonoidHom.comp_apply]
      simp [mul_assoc] }

/-- Evaluating `Subgroup.IsLocalComplement.semidirectProductMulEquiv` multiplies the two subgroup
components inside `G`. -/
@[simp]
theorem coe_semidirectProductMulEquiv_apply
    (x : N ⋊[(N.normalizerMonoidHom).comp (inclusion h.right_le_normalizer)] K) :
    (h.semidirectProductMulEquiv x : G) = (x.left : G) * x.right :=
  h.coe_equiv_symm_apply (x.left, x.right)

/-- Composing `Subgroup.IsLocalComplement.semidirectProductMulEquiv` with `H.subtype` recovers the
external multiplication homomorphism `SemidirectProduct.monoidHomSubgroup`. -/
@[simp]
theorem subtype_comp_semidirectProductMulEquiv :
    H.subtype.comp (h.semidirectProductMulEquiv :
      N ⋊[(N.normalizerMonoidHom).comp (inclusion h.right_le_normalizer)] K →* H) =
      SemidirectProduct.monoidHomSubgroup h.right_le_normalizer := by
  ext x
  exact h.coe_semidirectProductMulEquiv_apply x

/-- As an equivalence of types, `Subgroup.IsLocalComplement.semidirectProductMulEquiv` is
`SemidirectProduct.equivProd` followed by the inverse of `Subgroup.IsLocalComplement.equiv`. -/
theorem toEquiv_semidirectProductMulEquiv :
    h.semidirectProductMulEquiv.toEquiv = SemidirectProduct.equivProd.trans h.equiv.symm :=
  (rfl)

/-- As an equivalence of types, `(Subgroup.IsLocalComplement.semidirectProductMulEquiv h).symm` is
`Subgroup.IsLocalComplement.equiv` followed by `SemidirectProduct.equivProd.symm`. -/
theorem toEquiv_semidirectProductMulEquiv_symm :
    h.semidirectProductMulEquiv.symm.toEquiv = h.equiv.trans SemidirectProduct.equivProd.symm :=
  (rfl)

/-- `Subgroup.IsLocalComplement.semidirectProductMulEquiv` sends `inl` to the inclusion `N →* H`. -/
@[simp]
theorem semidirectProductMulEquiv_inl (n : N) :
    h.semidirectProductMulEquiv (SemidirectProduct.inl n) = inclusion h.left_le n := by
  apply Subtype.ext
  simp

/-- `Subgroup.IsLocalComplement.semidirectProductMulEquiv` sends `inr` to the inclusion `K →* H`. -/
@[simp]
theorem semidirectProductMulEquiv_inr (k : K) :
    h.semidirectProductMulEquiv (SemidirectProduct.inr k) = inclusion h.right_le k := by
  apply Subtype.ext
  simp

/-- Restricting `Subgroup.IsLocalComplement.semidirectProductMulEquiv` along `inl` gives
`Subgroup.inclusion h.left_le`. -/
@[simp]
theorem semidirectProductMulEquiv_comp_inl :
    (h.semidirectProductMulEquiv :
      N ⋊[(N.normalizerMonoidHom).comp (inclusion h.right_le_normalizer)] K →* H).comp
        SemidirectProduct.inl = inclusion h.left_le := by
  ext n
  exact congrArg Subtype.val (h.semidirectProductMulEquiv_inl n)

/-- Restricting `Subgroup.IsLocalComplement.semidirectProductMulEquiv` along `inr` gives
`Subgroup.inclusion h.right_le`. -/
@[simp]
theorem semidirectProductMulEquiv_comp_inr :
    (h.semidirectProductMulEquiv :
      N ⋊[(N.normalizerMonoidHom).comp (inclusion h.right_le_normalizer)] K →* H).comp
        SemidirectProduct.inr = inclusion h.right_le := by
  ext k
  exact congrArg Subtype.val (h.semidirectProductMulEquiv_inr k)

/-- The left component of `h.semidirectProductMulEquiv.symm x` is `h.leftProjection x`. -/
@[simp]
theorem semidirectProductMulEquiv_symm_left (x : H) :
    (h.semidirectProductMulEquiv.symm x).left = h.leftProjection x :=
  (h.leftProjection_apply x).symm

/-- The right component of `h.semidirectProductMulEquiv.symm x` is `h.rightProjection x`. -/
@[simp]
theorem semidirectProductMulEquiv_symm_right (x : H) :
    (h.semidirectProductMulEquiv.symm x).right = h.rightProjection x :=
  (h.rightProjection_apply x).symm

/-- `h.semidirectProductMulEquiv.symm` decomposes an element of `H` into the product of its left
and right projections inside `N ⋊ K`. -/
theorem semidirectProductMulEquiv_symm_apply (x : H) :
    h.semidirectProductMulEquiv.symm x =
      SemidirectProduct.inl (h.leftProjection x) * SemidirectProduct.inr (h.rightProjection x) := by
  rw [← SemidirectProduct.inl_left_mul_inr_right (h.semidirectProductMulEquiv.symm x),
    semidirectProductMulEquiv_symm_left, semidirectProductMulEquiv_symm_right]

/-- Projecting `h.semidirectProductMulEquiv.symm` to `K` recovers
`Subgroup.IsLocalComplement.rightProjection`. -/
@[simp]
theorem rightHom_comp_semidirectProductMulEquiv_symm :
    SemidirectProduct.rightHom.comp (h.semidirectProductMulEquiv.symm :
      H →* N ⋊[(N.normalizerMonoidHom).comp (inclusion h.right_le_normalizer)] K) =
      h.rightProjection := by
  ext x
  exact congrArg Subtype.val (h.semidirectProductMulEquiv_symm_right x)

/-- `h.semidirectProductMulEquiv.symm` maps included elements of `N` to `inl`. -/
@[simp]
theorem semidirectProductMulEquiv_symm_inclusion_left (n : N) :
    h.semidirectProductMulEquiv.symm (inclusion h.left_le n) = SemidirectProduct.inl n := by
  apply h.semidirectProductMulEquiv.injective
  simp

/-- `h.semidirectProductMulEquiv.symm` maps included elements of `K` to `inr`. -/
@[simp]
theorem semidirectProductMulEquiv_symm_inclusion_right (k : K) :
    h.semidirectProductMulEquiv.symm (inclusion h.right_le k) = SemidirectProduct.inr k := by
  apply h.semidirectProductMulEquiv.injective
  simp

/-- Restricting `h.semidirectProductMulEquiv.symm` along `inclusion h.left_le` gives `inl`. -/
@[simp]
theorem semidirectProductMulEquiv_symm_comp_inclusion_left :
    (h.semidirectProductMulEquiv.symm :
      H →* N ⋊[(N.normalizerMonoidHom).comp (inclusion h.right_le_normalizer)] K).comp
        (inclusion h.left_le) = SemidirectProduct.inl := by
  apply MonoidHom.ext
  intro n
  exact h.semidirectProductMulEquiv_symm_inclusion_left n

/-- Restricting `h.semidirectProductMulEquiv.symm` along `inclusion h.right_le` gives `inr`. -/
@[simp]
theorem semidirectProductMulEquiv_symm_comp_inclusion_right :
    (h.semidirectProductMulEquiv.symm :
      H →* N ⋊[(N.normalizerMonoidHom).comp (inclusion h.right_le_normalizer)] K).comp
        (inclusion h.right_le) = SemidirectProduct.inr := by
  apply MonoidHom.ext
  intro k
  exact h.semidirectProductMulEquiv_symm_inclusion_right k

/-- For any local complement `K` of a subgroup `N` normal in `H` (not necessarily abelian), the
left projection of a product twists the second factor by conjugation by the right projection of the
first. -/
theorem leftProjection_mul_apply (x y : H) :
    h.leftProjection (x * y) =
      h.leftProjection x *
        ((N.normalizerMonoidHom).comp (inclusion h.right_le_normalizer)
          (h.rightProjection x) (h.leftProjection y)) := by
  simpa only [semidirectProductMulEquiv_symm_left, semidirectProductMulEquiv_symm_right,
    SemidirectProduct.mul_left] using
    congrArg SemidirectProduct.left (h.semidirectProductMulEquiv.symm.map_mul x y)

/-- Identifying `N.subgroupOf H` with `N` and `K.subgroupOf H` with `K` intertwines their
normalizer actions. -/
theorem subgroupOfEquivOfLe_normalizer_comm (k : K.subgroupOf H) :
    (((N.subgroupOf H).normalizerMonoidHom).comp
        (inclusion ((N.subgroupOf H).normalizer_eq_top ▸ le_top)) k).trans
        (N.subgroupOfEquivOfLe h.left_le) =
      (N.subgroupOfEquivOfLe h.left_le).trans
        (((N.normalizerMonoidHom).comp (inclusion h.right_le_normalizer))
          (K.subgroupOfEquivOfLe h.right_le k)) := by
  ext n
  rfl

/-- Under `N.subgroupOf H ≃* N` and `K.subgroupOf H ≃* K`, the local isomorphism
`Subgroup.IsLocalComplement.semidirectProductMulEquiv` agrees with
`SemidirectProduct.mulEquivSubgroup` applied inside `H`. -/
theorem congr_subgroupOfEquivOfLe_trans_semidirectProductMulEquiv :
    (SemidirectProduct.congr (N.subgroupOfEquivOfLe h.left_le) (K.subgroupOfEquivOfLe h.right_le)
        h.subgroupOfEquivOfLe_normalizer_comm).trans h.semidirectProductMulEquiv =
      SemidirectProduct.mulEquivSubgroup h.isComplement'_subgroupOf := by
  ext x
  exact h.coe_semidirectProductMulEquiv_apply _

end IsLocalComplement

end Subgroup
