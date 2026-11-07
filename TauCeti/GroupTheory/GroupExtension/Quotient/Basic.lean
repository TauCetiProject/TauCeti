/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Splitting
public import TauCeti.GroupTheory.GroupExtension.Of.Surjective

/-!
# The quotient extension and subgroup complements

For a normal subgroup `N` of `G`, the quotient homomorphism gives an extension of `G ⧸ N`
by `N`. Its splittings correspond bijectively to subgroup complements of `N`, without
finiteness or commutativity assumptions. The inverse construction uses Mathlib's
`Subgroup.IsComplement'.QuotientMulEquiv`: a complement is isomorphic to the quotient,
and its inverse inclusion is the required section homomorphism.
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

end Subgroup
