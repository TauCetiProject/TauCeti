/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SemidirectProduct
public import TauCeti.GroupTheory.Complement.Local

/-!
# Semidirect-product decompositions for local complements

When `N` is normal in `H` and `K` is a local complement of `N` in `H`, `K` normalizes `N` and
multiplication gives a group isomorphism `N ⋊ K ≃* H`
(`Subgroup.IsLocalComplement.semidirectProductMulEquiv`) whose inverse is the product
decomposition `Subgroup.IsLocalComplement.equiv` into `leftProjection` and `rightProjection`.

When `N` is normal in the ambient group `G`, specializing `H = ⊤` identifies this local
isomorphism with Mathlib's `SemidirectProduct.mulEquivSubgroup` through `Subgroup.topEquiv` and
relates the inverse components of `SemidirectProduct.mulEquivSubgroup` to `leftProjection` and
`rightProjection` at `⊤`. No finiteness or commutativity assumptions are made.

## Main definitions and results

* `Subgroup.IsLocalComplement.semidirectProductMulEquiv`: the multiplication isomorphism
  `N ⋊ K ≃* H` for a local complement `K` of `N` in `H`.
* `Subgroup.IsLocalComplement.toEquiv_semidirectProductMulEquiv_symm`,
  `Subgroup.IsLocalComplement.left_semidirectProductMulEquiv_symm`, and
  `Subgroup.IsLocalComplement.right_semidirectProductMulEquiv_symm`: its inverse agrees with the
  local decomposition and its two projections.
* `Subgroup.IsLocalComplement.semidirectProductMulEquiv_top_trans_topEquiv`: for a local
  complement in `⊤`, the local semidirect-product isomorphism followed by `Subgroup.topEquiv` is
  `SemidirectProduct.mulEquivSubgroup`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] {N K H : Subgroup G}

namespace IsLocalComplement

variable [(N.subgroupOf H).Normal] (h : N.IsLocalComplement K H)

/-- Multiplication identifies the external semidirect product of a normal subgroup `N` of `H`
and a local complement `K` in `H` with the ambient subgroup `H`. -/
noncomputable def semidirectProductMulEquiv :
    N ⋊[(N.normalizerMonoidHom).comp (inclusion h.right_le_normalizer)] K ≃* H where
  toFun x :=
    ⟨(x.left : G) * x.right, H.mul_mem (h.left_le x.left.property) (h.right_le x.right.property)⟩
  invFun y := ⟨(h.equiv y).1, (h.equiv y).2⟩
  left_inv x := by
    ext <;> simp
  right_inv y := Subtype.ext (h.equiv_fst_mul_equiv_snd y)
  map_mul' x y :=
    Subtype.ext (by
      simpa only [SemidirectProduct.monoidHomSubgroup_apply, coe_mul] using
        (SemidirectProduct.monoidHomSubgroup h.right_le_normalizer).map_mul x y)

/-- Evaluating `semidirectProductMulEquiv` in the ambient group multiplies the two components. -/
@[simp]
theorem coe_semidirectProductMulEquiv_apply
    (x : N ⋊[(N.normalizerMonoidHom).comp (inclusion h.right_le_normalizer)] K) :
    (h.semidirectProductMulEquiv x : G) = (x.left : G) * x.right := (rfl)

/-- Including `H` into `G` after `semidirectProductMulEquiv` is
`SemidirectProduct.monoidHomSubgroup`. -/
@[simp]
theorem subtype_comp_semidirectProductMulEquiv :
    H.subtype.comp h.semidirectProductMulEquiv =
      SemidirectProduct.monoidHomSubgroup h.right_le_normalizer := by
  ext x
  simp

/-- On the left factor, `semidirectProductMulEquiv` is the subgroup inclusion `N →* H`. -/
@[simp]
theorem semidirectProductMulEquiv_inl (n : N) :
    h.semidirectProductMulEquiv (SemidirectProduct.inl n) = inclusion h.left_le n := by
  apply Subtype.ext
  simp

/-- On the right factor, `semidirectProductMulEquiv` is the subgroup inclusion `K →* H`. -/
@[simp]
theorem semidirectProductMulEquiv_inr (k : K) :
    h.semidirectProductMulEquiv (SemidirectProduct.inr k) = inclusion h.right_le k := by
  apply Subtype.ext
  simp

/-- Restricting `semidirectProductMulEquiv` to `inl` gives `inclusion h.left_le`. -/
@[simp]
theorem semidirectProductMulEquiv_comp_inl :
    (MonoidHom.ofClass h.semidirectProductMulEquiv).comp SemidirectProduct.inl =
      inclusion h.left_le := by
  ext n
  simp

/-- Restricting `semidirectProductMulEquiv` to `inr` gives `inclusion h.right_le`. -/
@[simp]
theorem semidirectProductMulEquiv_comp_inr :
    (MonoidHom.ofClass h.semidirectProductMulEquiv).comp SemidirectProduct.inr =
      inclusion h.right_le := by
  ext k
  simp

/-- As a bijection of types, `semidirectProductMulEquiv` is `SemidirectProduct.equivProd`
followed by the inverse of the local decomposition `h.equiv`. -/
theorem toEquiv_semidirectProductMulEquiv :
    h.semidirectProductMulEquiv.toEquiv = SemidirectProduct.equivProd.trans h.equiv.symm := by
  ext x
  exact (h.coe_semidirectProductMulEquiv_apply x).trans
    (h.coe_equiv_symm_apply (x.left, x.right)).symm

/-- As a bijection of types, `semidirectProductMulEquiv.symm` is the local decomposition `h.equiv`
followed by `SemidirectProduct.equivProd.symm`. -/
theorem toEquiv_semidirectProductMulEquiv_symm :
    h.semidirectProductMulEquiv.symm.toEquiv =
      h.equiv.trans SemidirectProduct.equivProd.symm :=
  congrArg Equiv.symm h.toEquiv_semidirectProductMulEquiv

/-- The left component of `semidirectProductMulEquiv.symm` is `leftProjection`. -/
@[simp]
theorem left_semidirectProductMulEquiv_symm (x : H) :
    (h.semidirectProductMulEquiv.symm x).left = h.leftProjection x :=
  (h.leftProjection_apply x).symm

/-- The right component of `semidirectProductMulEquiv.symm` is `rightProjection`. -/
@[simp]
theorem right_semidirectProductMulEquiv_symm (x : H) :
    (h.semidirectProductMulEquiv.symm x).right = h.rightProjection x :=
  (h.rightProjection_apply x).symm

/-- Evaluating `semidirectProductMulEquiv.symm` decomposes an element of `H` into its left and
right projections inside the semidirect product. -/
theorem semidirectProductMulEquiv_symm_apply (x : H) :
    h.semidirectProductMulEquiv.symm x =
      SemidirectProduct.inl (h.leftProjection x) *
        SemidirectProduct.inr (h.rightProjection x) := by
  rw [← h.left_semidirectProductMulEquiv_symm, ← h.right_semidirectProductMulEquiv_symm,
    SemidirectProduct.inl_left_mul_inr_right]

/-- The inverse of `semidirectProductMulEquiv` sends an included element of `N` to `inl`. -/
@[simp]
theorem semidirectProductMulEquiv_symm_inclusion_left (n : N) :
    h.semidirectProductMulEquiv.symm (inclusion h.left_le n) = SemidirectProduct.inl n := by
  rw [MulEquiv.symm_apply_eq, semidirectProductMulEquiv_inl]

/-- The inverse of `semidirectProductMulEquiv` sends an included element of `K` to `inr`. -/
@[simp]
theorem semidirectProductMulEquiv_symm_inclusion_right (k : K) :
    h.semidirectProductMulEquiv.symm (inclusion h.right_le k) = SemidirectProduct.inr k := by
  rw [MulEquiv.symm_apply_eq, semidirectProductMulEquiv_inr]

/-- Projecting `semidirectProductMulEquiv.symm` to the acting factor `K` gives
`rightProjection`. -/
@[simp]
theorem rightHom_comp_semidirectProductMulEquiv_symm :
    SemidirectProduct.rightHom.comp (MonoidHom.ofClass h.semidirectProductMulEquiv.symm) =
      h.rightProjection := by
  apply MonoidHom.ext
  intro x
  exact h.right_semidirectProductMulEquiv_symm x

end IsLocalComplement

/-- Viewing a local complement in `⊤` globally, its local semidirect-product isomorphism followed
by `Subgroup.topEquiv` is `SemidirectProduct.mulEquivSubgroup`. -/
theorem IsLocalComplement.semidirectProductMulEquiv_top_trans_topEquiv [N.Normal]
    (h : N.IsLocalComplement K ⊤) :
    h.semidirectProductMulEquiv.trans Subgroup.topEquiv =
      SemidirectProduct.mulEquivSubgroup (isLocalComplement_top_iff.mp h) := by
  ext x
  simp

namespace IsComplement'

variable [N.Normal] {D : Subgroup G} (h : N.IsComplement' D)

/-- The left component of `(SemidirectProduct.mulEquivSubgroup h).symm` agrees with the local
`leftProjection` in `⊤`. -/
theorem left_mulEquivSubgroup_symm_eq_leftProjection (g : G) :
    ((SemidirectProduct.mulEquivSubgroup h).symm g).left =
      (isLocalComplement_top_iff.mpr h).leftProjection ⟨g, mem_top g⟩ := by
  rw [SemidirectProduct.left_mulEquivSubgroup_symm]
  simp

/-- The right component of `(SemidirectProduct.mulEquivSubgroup h).symm` agrees with the local
`rightProjection` in `⊤`. -/
theorem right_mulEquivSubgroup_symm_eq_rightProjection (g : G) :
    ((SemidirectProduct.mulEquivSubgroup h).symm g).right =
      (isLocalComplement_top_iff.mpr h).rightProjection ⟨g, mem_top g⟩ := by
  rw [SemidirectProduct.right_mulEquivSubgroup_symm]
  simp

end IsComplement'

end Subgroup
