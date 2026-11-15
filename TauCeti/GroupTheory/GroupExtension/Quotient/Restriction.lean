/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.Local
public import TauCeti.GroupTheory.QuotientGroup.KerEquiv
public import TauCeti.GroupTheory.GroupExtension.Quotient.Cohomology
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Corestriction
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Restricting the class of a quotient extension

Let `N` be an abelian normal subgroup of `G` and `N ≤ H`. The quotient `H ⧸ N` is the image of
`H` in `G ⧸ N`, and `N.subgroupOf H` is `N`. This file proves that the class of the quotient
extension of `G` by `N` in `H²(G ⧸ N, N)` restricts, on that image, to the class of the
quotient extension of `H` by `N`.

As a consequence, if `N` has a local complement in a subgroup `H`, then `[G : H]` kills the
class of the quotient extension of `G`: the restricted class vanishes by
`Subgroup.exists_complement_iff_cohomologyClass_eq_zero` applied to `H`, and restriction
followed by corestriction is multiplication by the index (when `H` has infinite index,
`H.index = 0` and there is nothing to prove). This is the step of the cohomological
proof of Gaschütz's splitting theorem that uses the local complement; no finiteness of `G` or
of `N` is needed for it.

## Main definitions

* `Subgroup.subgroupOfRepHom`: `N.subgroupOf H ≃ N` as a morphism of representations of the
  image of `H` in `G ⧸ N`.

## Main results

* `Subgroup.map_subtype_cohomologyClass_factorSet_quotientExtension`: the restriction formula.
* `Subgroup.IsLocalComplement.index_nsmul_cohomologyClass_eq_zero`: a local complement in `H`
  forces `[G : H]` to kill the class of the quotient extension.

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math. 190
  (1952), 93–107.
* K. S. Brown, *Cohomology of Groups*, Chapter IV, §3 and Chapter III, §9.
-/

public section

namespace Subgroup

open groupCohomology CategoryTheory
open scoped IsMulCommutative

section

variable {G : Type*} [Group G] {N : Subgroup G} [N.Normal] [IsMulCommutative N] {H : Subgroup G}

attribute [local instance] quotientConjugationAction

/-- Identifying `N.subgroupOf H` with `N` intertwines the quotient conjugation actions of
`H ⧸ N.subgroupOf H` and of its image in `G ⧸ N`. -/
theorem subgroupOfEquivOfLe_smul (hNH : N ≤ H) (y : H ⧸ N.subgroupOf H) (n : N.subgroupOf H) :
    N.subgroupOfEquivOfLe hNH (y • n) =
      (quotientSubgroupOfMulEquivMap N H y : G ⧸ N) • N.subgroupOfEquivOfLe hNH n := by
  induction y using QuotientGroup.induction_on with | H h => ?_
  apply Subtype.ext
  simp [MulAut.conjNormal_apply]

end

variable {G : Type} [Group G] {N : Subgroup G} [N.Normal] [IsMulCommutative N] {H : Subgroup G}

attribute [local instance] quotientConjugationAction

/-- Identifying `N.subgroupOf H` with `N` is a morphism of representations of the image of `H`
in `G ⧸ N`. That image acts on `N.subgroupOf H` through
`Subgroup.quotientSubgroupOfMulEquivMap` and the quotient conjugation action of `H`,
and on `N` by restricting the quotient conjugation action of `G`. -/
noncomputable def subgroupOfRepHom (hNH : N ≤ H) :
    Rep.res (quotientSubgroupOfMulEquivMap N H).symm.toMonoidHom
        (Rep.ofMulDistribMulAction (H ⧸ N.subgroupOf H) (N.subgroupOf H)) ⟶
      Rep.res (H.map (QuotientGroup.mk' N)).subtype (Rep.ofMulDistribMulAction (G ⧸ N) N) :=
  Rep.ofHom ⟨(N.subgroupOfEquivOfLe hNH).toMonoidHom.toAdditive.toIntLinearMap, fun q => by
    ext x
    have h := subgroupOfEquivOfLe_smul hNH ((quotientSubgroupOfMulEquivMap N H).symm q) x.toMul
    rw [MulEquiv.apply_symm_apply] at h
    -- Both representations act on `Additive.ofMul` of their arguments, so the intertwining
    -- identity is `Additive.ofMul` of `subgroupOfEquivOfLe_smul`.
    exact congrArg Additive.ofMul h⟩

@[simp]
theorem subgroupOfRepHom_hom_apply (hNH : N ≤ H) (x : Additive (N.subgroupOf H)) :
    (subgroupOfRepHom hNH).hom x = Additive.ofMul (N.subgroupOfEquivOfLe hNH x.toMul) :=
  (rfl)

/-- A section of the quotient extension of `G`, read on the image of `H`, is a section of the
quotient extension of `H`. -/
private noncomputable def restrictSection (hNH : N ≤ H) (σ : N.quotientExtension.Section) :
    (N.subgroupOf H).quotientExtension.Section where
  toFun y := ⟨σ (quotientSubgroupOfMulEquivMap N H y), by
    have h := σ.rightHom_section (quotientSubgroupOfMulEquivMap N H y : G ⧸ N)
    rw [quotientExtension_rightHom] at h
    have hmem : σ (quotientSubgroupOfMulEquivMap N H y) ∈
        (H.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := by
      rw [mem_comap, h]
      exact (quotientSubgroupOfMulEquivMap N H y).property
    rwa [QuotientGroup.comap_map_mk', sup_eq_right.mpr hNH] at hmem⟩
  rightInverse_rightHom y := by
    simp only [quotientExtension_rightHom]
    apply (quotientSubgroupOfMulEquivMap N H).injective
    apply Subtype.ext
    rw [QuotientGroup.mk'_apply, coe_quotientSubgroupOfMulEquivMap_mk]
    simpa using σ.rightHom_section (quotientSubgroupOfMulEquivMap N H y : G ⧸ N)

omit [IsMulCommutative N] in
private theorem coe_restrictSection (hNH : N ≤ H) (σ : N.quotientExtension.Section)
    (y : H ⧸ N.subgroupOf H) :
    (restrictSection hNH σ y : G) = σ (quotientSubgroupOfMulEquivMap N H y) :=
  (rfl)

/-- The factor set of the restricted section is the factor set of the original section, read on
the image of `H`. -/
private theorem coe_factorSet_restrictSection (hNH : N ≤ H) (σ : N.quotientExtension.Section)
    (hσ : σ 1 = 1) (hσ' : restrictSection hNH σ 1 = 1) (y₁ y₂ : H ⧸ N.subgroupOf H) :
    ((TauCeti.GroupExtension.factorSet (restrictSection hNH σ) hσ'
        (N.subgroupOf H).quotientExtension_inducesAction (y₁, y₂) : H) : G) =
      TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction
        (quotientSubgroupOfMulEquivMap N H y₁, quotientSubgroupOfMulEquivMap N H y₂) := by
  have h₁ := congrArg Subtype.val (TauCeti.GroupExtension.inl_factorSet (restrictSection hNH σ)
    hσ' (N.subgroupOf H).quotientExtension_inducesAction y₁ y₂)
  have h₂ := TauCeti.GroupExtension.inl_factorSet σ hσ N.quotientExtension_inducesAction
    (quotientSubgroupOfMulEquivMap N H y₁ : G ⧸ N) (quotientSubgroupOfMulEquivMap N H y₂)
  simp only [quotientExtension_inl, subtype_apply] at h₁ h₂
  rw [h₁, h₂]
  simp [coe_restrictSection]

/-- **The restriction formula for the class of the quotient extension.** Restricted to the
image of `H ≥ N` in `G ⧸ N`, the class of the quotient extension of `G` by `N` is the class of
the quotient extension of `H` by `N.subgroupOf H`, transported along
`Subgroup.quotientSubgroupOfMulEquivMap` and `Subgroup.subgroupOfRepHom`. Both
classes are presented by the factor sets of arbitrary normalized sections. -/
theorem map_subtype_cohomologyClass_factorSet_quotientExtension (hNH : N ≤ H)
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1)
    (τ : (N.subgroupOf H).quotientExtension.Section) (hτ : τ 1 = 1) :
    groupCohomology.map (H.map (QuotientGroup.mk' N)).subtype (𝟙 _) 2
        (TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction).cohomologyClass =
      groupCohomology.map (quotientSubgroupOfMulEquivMap N H).symm.toMonoidHom
          (subgroupOfRepHom hNH) 2
        (TauCeti.GroupExtension.factorSet τ hτ
          (N.subgroupOf H).quotientExtension_inducesAction).cohomologyClass := by
  have hτ' : restrictSection hNH σ 1 = 1 := by
    apply Subtype.ext
    rw [coe_restrictSection, map_one, OneMemClass.coe_one, hσ, OneMemClass.coe_one]
  rw [TauCeti.GroupExtension.cohomologyClass_factorSet_eq τ (restrictSection hNH σ) hτ hτ',
    TauCeti.FactorSet.cohomologyClass_def, TauCeti.FactorSet.cohomologyClass_def,
    H2π_comp_map_apply, H2π_comp_map_apply]
  congr 1
  ext q₁ q₂
  have key : TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction (q₁, q₂) =
      N.subgroupOfEquivOfLe hNH (TauCeti.GroupExtension.factorSet (restrictSection hNH σ) hτ'
        (N.subgroupOf H).quotientExtension_inducesAction
          ((quotientSubgroupOfMulEquivMap N H).symm q₁,
            (quotientSubgroupOfMulEquivMap N H).symm q₂)) := by
    apply Subtype.ext
    rw [subgroupOfEquivOfLe_apply_coe, coe_factorSet_restrictSection, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
  rw [TauCeti.groupCohomology.mapCocycles₂_apply, TauCeti.groupCohomology.mapCocycles₂_apply]
  simp only [TauCeti.FactorSet.coe_toCocycles₂]
  rw [subgroupOfRepHom_hom_apply, Rep.hom_id]
  -- The identity morphism acts as the identity and `Additive.toMul ∘ Additive.ofMul = id`.
  exact congrArg Additive.ofMul key

/-- **A local complement in `H` forces the index of `H` to kill the class of the quotient
extension.** If `N` has a local complement in `H`, then `[G : H]` kills the class in
`H²(G ⧸ N, N)` of the quotient extension of `G` by `N`: the restriction of the class to the image
of `H` is the class of the split quotient extension of `H`, and restriction followed by
corestriction is multiplication by the index. When `H` has infinite index, `H.index = 0` and the
statement is trivial. Neither `G` nor `N` need be finite. -/
theorem IsLocalComplement.index_nsmul_cohomologyClass_eq_zero {K : Subgroup G}
    (hK : N.IsLocalComplement K H) (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    H.index •
      (TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction).cohomologyClass =
        0 := by
  by_cases hH : H.FiniteIndex
  swap
  · rw [not_finiteIndex_iff.1 hH, zero_smul]
  let τ := TauCeti.GroupExtension.normalizeSection
    (N.subgroupOf H).quotientExtension.surjInvRightHom
  have hτ : τ 1 = 1 := TauCeti.GroupExtension.normalizeSection_one _
  have hτ0 : (TauCeti.GroupExtension.factorSet τ hτ
      (N.subgroupOf H).quotientExtension_inducesAction).cohomologyClass = 0 :=
    ((N.subgroupOf H).exists_complement_iff_cohomologyClass_eq_zero τ hτ).1
      ⟨_, hK.isComplement'_subgroupOf⟩
  have hindex : (H.map (QuotientGroup.mk' N)).index = H.index :=
    H.index_map_eq (QuotientGroup.mk'_surjective N) ((QuotientGroup.ker_mk' N).trans_le hK.left_le)
  have : (H.map (QuotientGroup.mk' N)).FiniteIndex :=
    FiniteIndex.map_of_surjective H (QuotientGroup.mk'_surjective N)
  rw [← hindex]
  refine TauCeti.groupCohomology.index_nsmul_eq_zero_of_map_eq_zero _ ?_
  rw [map_subtype_cohomologyClass_factorSet_quotientExtension hK.left_le σ hσ τ hτ, hτ0, map_zero]

end Subgroup
