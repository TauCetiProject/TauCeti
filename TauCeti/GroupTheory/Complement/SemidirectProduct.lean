/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SemidirectProduct
public import TauCeti.GroupTheory.Complement.Local

/-!
# Local complements and semidirect products

A local complement `K` of `N` inside an intermediate subgroup `H` in which `N` is normal determines
an internal semidirect-product isomorphism `N ⋊ K ≃* H`, extending
`SemidirectProduct.mulEquivSubgroup` from global complements (`Subgroup.IsComplement'`) to local
complements (`Subgroup.IsLocalComplement`).

## Main definitions

* `Subgroup.IsLocalComplement.semidirectProductMulEquiv`: the internal semidirect-product
  isomorphism `N ⋊ K ≃* H` determined by a local complement `K` of `N` in `H` when `N` is normal
  in `H`.

## Main results

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

namespace Subgroup.IsLocalComplement

variable {G : Type*} [Group G] {N K H : Subgroup G}
  [(N.subgroupOf H).Normal] (h : N.IsLocalComplement K H)

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
  simp

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
  simp

/-- Under `N.subgroupOf H ≃* N` and `K.subgroupOf H ≃* K`, the local isomorphism
`Subgroup.IsLocalComplement.semidirectProductMulEquiv` agrees with
`SemidirectProduct.mulEquivSubgroup` applied inside `H`. -/
theorem congr_subgroupOfEquivOfLe_trans_semidirectProductMulEquiv :
    (SemidirectProduct.congr (N.subgroupOfEquivOfLe h.left_le) (K.subgroupOfEquivOfLe h.right_le)
        h.subgroupOfEquivOfLe_normalizer_comm).trans h.semidirectProductMulEquiv =
      SemidirectProduct.mulEquivSubgroup h.isComplement'_subgroupOf := by
  ext x
  simp

end Subgroup.IsLocalComplement
