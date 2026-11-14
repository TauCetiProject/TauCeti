/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SemidirectProduct
public import TauCeti.GroupTheory.GroupExtension.Quotient.Local

/-!
# Semidirect-product decompositions for local and global complements

When `N` is normal in `H` and `K` is a local complement of `N` in `H`, `K` normalizes `N` and
multiplication gives a group isomorphism `N ⋊ K ≃* H`
(`Subgroup.IsLocalComplement.semidirectProductMulEquiv`) whose inverse is the product
decomposition `Subgroup.IsLocalComplement.equiv` into `leftProjection` and `rightProjection`.
Evaluating those components in the ambient group recovers the local quotient splitting of `H` over
`H ⧸ N.subgroupOf H` and its normal remainder.

When `N` is normal in the ambient group `G` and `N.IsComplement' D`, specializing `H = ⊤`
identifies this local isomorphism with Mathlib's `SemidirectProduct.mulEquivSubgroup` through
`Subgroup.topEquiv`, connects the inverse components of `SemidirectProduct.mulEquivSubgroup` to
`Subgroup.IsComplement'.quotientSplitting`, and identifies `SemidirectProduct.mulEquivSubgroup`
with `GroupExtension.Splitting.semidirectProductMulEquiv` along the quotient isomorphism
`G ⧸ N ≃* D`. No finiteness or commutativity assumptions are made.

## Main definitions and results

* `Subgroup.IsLocalComplement.semidirectProductMulEquiv`: the multiplication isomorphism
  `N ⋊ K ≃* H` for a local complement `K` of `N` in `H`.
* `Subgroup.IsLocalComplement.toEquiv_semidirectProductMulEquiv_symm`,
  `Subgroup.IsLocalComplement.left_semidirectProductMulEquiv_symm`, and
  `Subgroup.IsLocalComplement.right_semidirectProductMulEquiv_symm`: its inverse agrees with the
  local decomposition and its two projections.
* `Subgroup.IsComplement'.isLocalComplement_top_semidirectProductMulEquiv_trans_topEquiv`: for a
  global complement, the local semidirect-product isomorphism at `⊤` followed by
  `Subgroup.topEquiv` is `SemidirectProduct.mulEquivSubgroup`.
* `Subgroup.IsComplement'.coe_right_mulEquivSubgroup_symm` and
  `Subgroup.IsComplement'.coe_left_mulEquivSubgroup_symm`: the components of
  `(SemidirectProduct.mulEquivSubgroup h).symm` in `G` are `h.quotientSplitting (g : G ⧸ N)` and
  `g * (h.quotientSplitting (g : G ⧸ N))⁻¹`.
* `Subgroup.IsComplement'.quotientSemidirectProductCongr` and
  `Subgroup.IsComplement'.quotientSemidirectProductCongr_trans_mulEquivSubgroup`: relabelling the
  acting factor along `G ⧸ N ≃* D` identifies `SemidirectProduct.mulEquivSubgroup h` with
  `h.quotientSplitting.semidirectProductMulEquiv`.
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
    Subtype.ext ((SemidirectProduct.monoidHomSubgroup h.right_le_normalizer).map_mul x y)

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
  rfl

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
      h.equiv.trans SemidirectProduct.equivProd.symm := by
  ext y <;> rfl

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

/-- In the ambient group, the right component of `semidirectProductMulEquiv.symm` agrees with the
local quotient splitting evaluated on the coset of `x`. -/
theorem coe_right_semidirectProductMulEquiv_symm (x : H) :
    ((h.semidirectProductMulEquiv.symm x).right : G) =
      ((N.localQuotientSplittingEquiv H h.left_le).symm ⟨K, h⟩
        (QuotientGroup.mk' (N.subgroupOf H) x) : G) := by
  rw [h.right_semidirectProductMulEquiv_symm, h.coe_localQuotientSplittingEquiv_symm_mk]

/-- In the ambient group, the left component of `semidirectProductMulEquiv.symm` is the remainder
after dividing out the local quotient splitting value. -/
theorem coe_left_semidirectProductMulEquiv_symm (x : H) :
    ((h.semidirectProductMulEquiv.symm x).left : G) = (x : G) *
      ((N.localQuotientSplittingEquiv H h.left_le).symm ⟨K, h⟩
        (QuotientGroup.mk' (N.subgroupOf H) x) : G)⁻¹ := by
  rw [h.left_semidirectProductMulEquiv_symm,
    h.coe_leftProjection_eq_mul_inv_localQuotientSplitting]

end IsLocalComplement

namespace IsComplement'

variable [N.Normal] {D : Subgroup G} (h : N.IsComplement' D)

/-- Viewing a global complement as a local complement in `⊤`, its local semidirect-product
isomorphism followed by `Subgroup.topEquiv` is `SemidirectProduct.mulEquivSubgroup`. -/
theorem isLocalComplement_top_semidirectProductMulEquiv_trans_topEquiv :
    ((isLocalComplement_top_iff.mpr h).semidirectProductMulEquiv).trans Subgroup.topEquiv =
      SemidirectProduct.mulEquivSubgroup h := by
  ext x
  rfl

/-- The left component of `(SemidirectProduct.mulEquivSubgroup h).symm` agrees with the local
`leftProjection` in `⊤`. -/
theorem left_mulEquivSubgroup_symm_eq_leftProjection (g : G) :
    ((SemidirectProduct.mulEquivSubgroup h).symm g).left =
      (isLocalComplement_top_iff.mpr h).leftProjection ⟨g, mem_top g⟩ := by
  rw [SemidirectProduct.left_mulEquivSubgroup_symm, h.isLocalComplement_top_leftProjection]

/-- The right component of `(SemidirectProduct.mulEquivSubgroup h).symm` agrees with the local
`rightProjection` in `⊤`. -/
theorem right_mulEquivSubgroup_symm_eq_rightProjection (g : G) :
    ((SemidirectProduct.mulEquivSubgroup h).symm g).right =
      (isLocalComplement_top_iff.mpr h).rightProjection ⟨g, mem_top g⟩ := by
  rw [SemidirectProduct.right_mulEquivSubgroup_symm, h.isLocalComplement_top_rightProjection]

/-- In `G`, the right component of `(SemidirectProduct.mulEquivSubgroup h).symm` is the quotient
splitting evaluated on the coset. -/
theorem coe_right_mulEquivSubgroup_symm (g : G) :
    (((SemidirectProduct.mulEquivSubgroup h).symm g).right : G) =
      h.quotientSplitting (g : G ⧸ N) := by
  rw [SemidirectProduct.right_mulEquivSubgroup_symm_eq_quotientMulEquiv,
    h.quotientSplitting_apply]

/-- In `G`, the left component of `(SemidirectProduct.mulEquivSubgroup h).symm` is the remainder
after dividing out the quotient splitting value. -/
theorem coe_left_mulEquivSubgroup_symm (g : G) :
    (((SemidirectProduct.mulEquivSubgroup h).symm g).left : G) =
      g * (h.quotientSplitting (g : G ⧸ N))⁻¹ := by
  rw [← h.coe_right_mulEquivSubgroup_symm, SemidirectProduct.left_mulEquivSubgroup_symm,
    SemidirectProduct.right_mulEquivSubgroup_symm, IsComplement.equiv_fst_eq_mul_inv]

/-- Composing `SemidirectProduct.mulEquivSubgroup` with `inr` and `G ⧸ N ≃* D` recovers the
quotient splitting homomorphism. -/
theorem mulEquivSubgroup_comp_inr_comp_quotientMulEquiv :
    (MonoidHom.ofClass (SemidirectProduct.mulEquivSubgroup h)).comp
      (SemidirectProduct.inr.comp (MonoidHom.ofClass h.symm.QuotientMulEquiv)) =
      h.quotientSplitting.toMonoidHom := by
  rw [← MonoidHom.comp_assoc, SemidirectProduct.mulEquivSubgroup_comp_inr]
  ext q
  exact (h.quotientSplitting_apply q).symm

/-- Conjugation on `N` induced by `h.quotientSplitting` agrees with ambient conjugation through
the quotient isomorphism `G ⧸ N ≃* D`. -/
theorem quotientSplitting_conjAct_eq (q : G ⧸ N) :
    h.quotientSplitting.conjAct q =
      ((N.normalizerMonoidHom).comp (inclusion (N.normalizer_eq_top ▸ le_top)))
        (h.symm.QuotientMulEquiv q) := by
  ext n : 1
  apply Subtype.ext
  have hcomm := N.quotientExtension.inl_conjAct_comm (e := h.quotientSplitting q) (n := n)
  simpa only [GroupExtension.Splitting.conjAct, MonoidHom.comp_apply,
    MonoidHom.coe_ofClass, quotientExtension_inl, subtype_apply, h.quotientSplitting_apply,
    normalizerMonoidHom_apply_apply_coe, coe_inclusion] using hcomm

/-- Relabelling the acting quotient `G ⧸ N` along `h.symm.QuotientMulEquiv` identifies the
extension semidirect product of `h.quotientSplitting` with the subgroup semidirect product
`N ⋊ D`. -/
noncomputable def quotientSemidirectProductCongr :
    N ⋊[h.quotientSplitting.conjAct] (G ⧸ N) ≃*
      N ⋊[(N.normalizerMonoidHom).comp (inclusion (N.normalizer_eq_top ▸ le_top))] D :=
  SemidirectProduct.congr (MulEquiv.refl N) h.symm.QuotientMulEquiv fun q => by
    ext n
    simp [h.quotientSplitting_conjAct_eq q]

/-- `quotientSemidirectProductCongr` acts as the identity on the left factor. -/
@[simp]
theorem left_quotientSemidirectProductCongr
    (x : N ⋊[h.quotientSplitting.conjAct] (G ⧸ N)) :
    (h.quotientSemidirectProductCongr x).left = x.left := (rfl)

/-- `quotientSemidirectProductCongr` applies `h.symm.QuotientMulEquiv` on the right factor. -/
@[simp]
theorem right_quotientSemidirectProductCongr
    (x : N ⋊[h.quotientSplitting.conjAct] (G ⧸ N)) :
    (h.quotientSemidirectProductCongr x).right = h.symm.QuotientMulEquiv x.right := (rfl)

/-- `quotientSemidirectProductCongr` fixes the included normal subgroup. -/
@[simp]
theorem quotientSemidirectProductCongr_inl (n : N) :
    h.quotientSemidirectProductCongr (SemidirectProduct.inl n) = SemidirectProduct.inl n := by
  apply SemidirectProduct.ext
  · rfl
  · simp only [right_quotientSemidirectProductCongr, SemidirectProduct.right_inl, map_one]

/-- `quotientSemidirectProductCongr` transports the included quotient along
`h.symm.QuotientMulEquiv`. -/
@[simp]
theorem quotientSemidirectProductCongr_inr (q : G ⧸ N) :
    h.quotientSemidirectProductCongr (SemidirectProduct.inr q) =
      SemidirectProduct.inr (h.symm.QuotientMulEquiv q) := by
  ext <;> simp

/-- `quotientSemidirectProductCongr.symm` acts as the identity on the left factor. -/
@[simp]
theorem left_quotientSemidirectProductCongr_symm
    (x : N ⋊[(N.normalizerMonoidHom).comp (inclusion (N.normalizer_eq_top ▸ le_top))] D) :
    (h.quotientSemidirectProductCongr.symm x).left = x.left := (rfl)

/-- `quotientSemidirectProductCongr.symm` projects the right factor to its coset in `G ⧸ N`. -/
@[simp]
theorem right_quotientSemidirectProductCongr_symm
    (x : N ⋊[(N.normalizerMonoidHom).comp (inclusion (N.normalizer_eq_top ▸ le_top))] D) :
    (h.quotientSemidirectProductCongr.symm x).right = (x.right : G ⧸ N) := by
  exact h.symm.QuotientMulEquiv_symm_apply x.right

/-- `quotientSemidirectProductCongr.symm` fixes the included normal subgroup. -/
@[simp]
theorem quotientSemidirectProductCongr_symm_inl (n : N) :
    h.quotientSemidirectProductCongr.symm (SemidirectProduct.inl n) =
      SemidirectProduct.inl n := by
  ext <;> simp

/-- `quotientSemidirectProductCongr.symm` projects the included complement to its cosets in
`G ⧸ N`. -/
@[simp]
theorem quotientSemidirectProductCongr_symm_inr (d : D) :
    h.quotientSemidirectProductCongr.symm (SemidirectProduct.inr d) =
      SemidirectProduct.inr (d : G ⧸ N) := by
  ext <;> simp

/-- Following `quotientSemidirectProductCongr` with `SemidirectProduct.mulEquivSubgroup` recovers
the semidirect-product isomorphism induced by `h.quotientSplitting`. -/
theorem quotientSemidirectProductCongr_trans_mulEquivSubgroup :
    h.quotientSemidirectProductCongr.trans (SemidirectProduct.mulEquivSubgroup h) =
      h.quotientSplitting.semidirectProductMulEquiv := by
  ext x
  simp [h.quotientSplitting_apply]

/-- Following `(SemidirectProduct.mulEquivSubgroup h).symm` with
`quotientSemidirectProductCongr.symm` recovers the inverse semidirect-product isomorphism of
`h.quotientSplitting`. -/
theorem mulEquivSubgroup_symm_trans_quotientSemidirectProductCongr_symm :
    (SemidirectProduct.mulEquivSubgroup h).symm.trans h.quotientSemidirectProductCongr.symm =
      h.quotientSplitting.semidirectProductMulEquiv.symm := by
  rw [← h.quotientSemidirectProductCongr_trans_mulEquivSubgroup]
  apply MulEquiv.ext
  intro g
  rfl

end IsComplement'

end Subgroup
