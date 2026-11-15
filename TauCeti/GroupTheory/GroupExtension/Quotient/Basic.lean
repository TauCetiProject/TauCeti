/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Splitting
public import TauCeti.GroupTheory.GroupExtension.Of.Surjective
public import TauCeti.GroupTheory.SemidirectProduct

/-!
# The quotient extension and subgroup complements

For a normal subgroup `N` of `G`, the quotient homomorphism gives an extension of `G ⧸ N`
by `N`. Its splittings correspond bijectively to subgroup complements of `N`, without
finiteness or commutativity assumptions. The inverse construction uses Mathlib's
`Subgroup.IsComplement'.QuotientMulEquiv`: a complement is isomorphic to the quotient,
and its inverse inclusion is the required section homomorphism.

For a complement `D` of `N`, the ambient components of `(SemidirectProduct.mulEquivSubgroup h).symm`
are `g * (h.quotientSplitting (g : G ⧸ N))⁻¹` and `h.quotientSplitting (g : G ⧸ N)`, and
relabelling the acting quotient `G ⧸ N` along `h.symm.QuotientMulEquiv`
(`Subgroup.IsComplement'.quotientSemidirectProductCongr`) identifies
`SemidirectProduct.mulEquivSubgroup h` with `h.quotientSplitting.semidirectProductMulEquiv`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

/-- The extension of `G ⧸ N` by `N` given by inclusion and the quotient homomorphism. -/
def quotientExtension : GroupExtension N G (G ⧸ N) :=
  GroupExtension.ofMulEquivKer (QuotientGroup.mk'_surjective N)
    (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' N).symm)

@[simp]
theorem quotientExtension_inl : N.quotientExtension.inl = N.subtype := by
  rw [quotientExtension, GroupExtension.ofMulEquivKer_inl]
  ext
  rfl

@[simp]
theorem quotientExtension_rightHom :
    N.quotientExtension.rightHom = QuotientGroup.mk' N := by
  rw [quotientExtension, GroupExtension.ofMulEquivKer_rightHom]

variable {N} {D : Subgroup G}

/-- A complement gives a splitting of the quotient extension by inverting its isomorphism
with the quotient. -/
noncomputable def IsComplement'.quotientSplitting (h : N.IsComplement' D) :
    N.quotientExtension.Splitting where
  toMonoidHom := D.subtype.comp h.symm.QuotientMulEquiv.toMonoidHom
  rightInverse_rightHom q := by
    simpa only [quotientExtension_rightHom, MonoidHom.toFun_eq_coe, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, subtype_apply, QuotientGroup.mk'_apply,
      IsComplement'.QuotientMulEquiv_apply] using
      h.symm.quotientGroupMk_leftQuotientEquiv q

theorem IsComplement'.quotientSplitting_apply (h : N.IsComplement' D) (q : G ⧸ N) :
    h.quotientSplitting q = (h.symm.QuotientMulEquiv q : G) := (rfl)

/-- The splitting sends the coset of an element of the complement back to that element. -/
@[simp]
theorem IsComplement'.quotientSplitting_mk (h : N.IsComplement' D) (d : D) :
    h.quotientSplitting ((d : G) : G ⧸ N) = d := by
  rw [quotientSplitting_apply]
  have hd : h.symm.QuotientMulEquiv.symm d = ((d : G) : G ⧸ N) :=
    h.symm.QuotientMulEquiv_symm_apply d
  rw [← hd, MulEquiv.apply_symm_apply]

/-- The splitting constructed from a complement has exactly that complement as its range. -/
@[simp]
theorem IsComplement'.range_quotientSplitting (h : N.IsComplement' D) :
    h.quotientSplitting.toMonoidHom.range = D := by
  rw [quotientSplitting, MonoidHom.range_comp]
  simp [← MonoidHom.range_eq_map]

end Subgroup

namespace GroupExtension.Splitting

variable {G : Type*} [Group G] {N : Subgroup G} [N.Normal]

/-- A splitting of the quotient extension has complementary range. -/
theorem isComplement'_range_quotientExtension (s : N.quotientExtension.Splitting) :
    N.IsComplement' s.toMonoidHom.range := by
  simpa only [Subgroup.quotientExtension_inl, Subgroup.range_subtype] using s.isComplement'_range

/-- Recovering a splitting from its complementary range returns the original splitting. -/
@[simp]
theorem quotientSplitting_range (s : N.quotientExtension.Splitting) :
    s.isComplement'_range_quotientExtension.quotientSplitting = s := by
  apply eq_of_range_eq
  simp

end GroupExtension.Splitting

namespace Subgroup

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

/-- Splittings of the quotient extension correspond bijectively to subgroup complements. -/
noncomputable def quotientSplittingEquiv :
    N.quotientExtension.Splitting ≃ {D : Subgroup G // N.IsComplement' D} where
  toFun s := ⟨s.toMonoidHom.range, s.isComplement'_range_quotientExtension⟩
  invFun D := D.property.quotientSplitting
  left_inv s := s.quotientSplitting_range
  right_inv D := by
    apply Subtype.ext
    exact D.property.range_quotientSplitting

@[simp]
theorem quotientSplittingEquiv_apply_coe (s : N.quotientExtension.Splitting) :
    (N.quotientSplittingEquiv s).val = s.toMonoidHom.range := (rfl)

@[simp]
theorem quotientSplittingEquiv_symm_apply (D : {D : Subgroup G // N.IsComplement' D})
    (q : G ⧸ N) :
    N.quotientSplittingEquiv.symm D q = D.property.quotientSplitting q := (rfl)

/-- A normal subgroup has a complement if and only if its quotient extension splits. -/
theorem exists_isComplement'_iff_nonempty_splitting_quotientExtension :
    (∃ D : Subgroup G, N.IsComplement' D) ↔ Nonempty N.quotientExtension.Splitting := by
  rw [← nonempty_subtype]
  exact N.quotientSplittingEquiv.nonempty_congr.symm

namespace IsComplement'

variable {N} {D : Subgroup G} (h : N.IsComplement' D)

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
