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

Let `N` be an abelian normal subgroup of `G` and `N ≤ H`. The quotient `H ⧸ N.subgroupOf H` is
isomorphic to the image of `H` in `G ⧸ N`, and `N.subgroupOf H` is isomorphic to `N`. This file
proves that the induced comparison in cohomology is an isomorphism in every degree
(`Subgroup.subgroupOfCohomologyIso`) and carries the class of the quotient extension of `H` by
`N.subgroupOf H` to the restriction of the class of the quotient extension of `G` by `N`
(`Subgroup.map_subtype_cohomologyClass_factorSet_quotientExtension`). Consequently `N` has a local
complement in `H` if and only if the restricted class vanishes
(`Subgroup.exists_isLocalComplement_iff_map_subtype_cohomologyClass_eq_zero`), and a local
complement in `H` forces `[G : H]` to kill the global extension class
(`Subgroup.IsLocalComplement.index_nsmul_cohomologyClass_eq_zero`).

When `[G : H]` is prime to `|N|`, `H` automatically contains `N`
(`Subgroup.le_of_coprime_index_card`), restriction to the image of `H` in `G ⧸ N` is injective on
`Hⁿ(G ⧸ N, N)` in every degree
(`Subgroup.map_subtype_quotientConjugationAction_injective_of_coprime_index`), and the global
extension class of `G` by `N` vanishes if and only if the local extension class of `H` by
`N.subgroupOf H` vanishes
(`Subgroup.cohomologyClass_factorSet_quotientExtension_eq_zero_iff_of_coprime_index`). Combining
`[G : H] • x = 0` with `|N| • x = 0` (`TauCeti.FactorSet.natCard_nsmul_cohomologyClass_eq_zero`)
gives the cohomological proof of Gaschütz's splitting criterion
(`Subgroup.IsLocalComplement.cohomologyClass_factorSet_eq_zero_of_coprime_index`); neither `G`,
`H`, nor `N` need be finite.

## Main definitions

* `Subgroup.subgroupOfRepHom`: `N.subgroupOf H ≃ N` as a morphism of representations of the
  image of `H` in `G ⧸ N`.
* `Subgroup.subgroupOfCohomologyIso`: the isomorphism
  `Hⁿ(H ⧸ N.subgroupOf H, N.subgroupOf H) ≅ Hⁿ(H.map (mk' N), N)` induced by
  `Subgroup.quotientSubgroupOfMulEquivMap` and `Subgroup.subgroupOfEquivOfLe`.

## Main results

* `Subgroup.map_subtype_cohomologyClass_factorSet_quotientExtension`: the restriction formula.
* `Subgroup.exists_isLocalComplement_iff_map_subtype_cohomologyClass_eq_zero`: `N` has a local
  complement in `H ≥ N` if and only if the restriction of the quotient extension class to the
  image of `H` vanishes.
* `Subgroup.IsLocalComplement.index_nsmul_cohomologyClass_eq_zero`: a local complement in `H`
  forces `[G : H]` to kill the class of the quotient extension.
* `Subgroup.map_subtype_quotientConjugationAction_injective_of_coprime_index`: when `[G : H]` is
  prime to `|N|`, restriction to the image of `H` is injective on `Hⁿ(G ⧸ N, N)` in every degree.
* `Subgroup.cohomologyClass_factorSet_quotientExtension_eq_zero_iff_of_coprime_index`: when
  `[G : H]` is prime to `|N|`, the quotient extension class of `G` by `N` vanishes if and only if
  that of `H` by `N.subgroupOf H` vanishes.
* `Subgroup.IsLocalComplement.cohomologyClass_factorSet_eq_zero_of_coprime_index`: a local
  complement of `N` in a subgroup of index prime to `|N|` kills the global quotient extension
  class.

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

/-- `Subgroup.subgroupOfRepHom` is an isomorphism of representations of the image of `H` in
`G ⧸ N`. -/
instance isIso_subgroupOfRepHom (hNH : N ≤ H) : IsIso (subgroupOfRepHom hNH) := by
  refine (ConcreteCategory.isIso_iff_bijective (subgroupOfRepHom hNH)).mpr ?_
  have hfun : ⇑(subgroupOfRepHom hNH).hom =
      Additive.ofMul ∘ N.subgroupOfEquivOfLe hNH ∘ Additive.toMul := rfl
  rw [hfun]
  exact Additive.ofMul.bijective.comp ((N.subgroupOfEquivOfLe hNH).bijective.comp
    Additive.toMul.bijective)

/-- The cohomology isomorphism `Hⁿ(H ⧸ N.subgroupOf H, N.subgroupOf H) ≅ Hⁿ(H.map (mk' N), N)`
induced by `Subgroup.quotientSubgroupOfMulEquivMap` on the quotient groups and
`Subgroup.subgroupOfEquivOfLe` on the abelian normal subgroup. -/
noncomputable def subgroupOfCohomologyIso (hNH : N ≤ H) (n : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction (H ⧸ N.subgroupOf H) (N.subgroupOf H)) n ≅
      groupCohomology (Rep.res (H.map (QuotientGroup.mk' N)).subtype
        (Rep.ofMulDistribMulAction (G ⧸ N) N)) n :=
  groupCohomology.mapIso
    (B := Rep.ofMulDistribMulAction (H ⧸ N.subgroupOf H) (N.subgroupOf H))
    (A := Rep.res (H.map (QuotientGroup.mk' N)).subtype (Rep.ofMulDistribMulAction (G ⧸ N) N))
    (quotientSubgroupOfMulEquivMap N H)
    (N.subgroupOfEquivOfLe hNH).toAdditive.toIntLinearEquiv
    (fun y => LinearMap.ext fun x =>
      congrArg Additive.ofMul (subgroupOfEquivOfLe_smul hNH y x.toMul)) n

/-- The forward direction of `Subgroup.subgroupOfCohomologyIso` is the map induced on cohomology by
`(quotientSubgroupOfMulEquivMap N H).symm.toMonoidHom` and `Subgroup.subgroupOfRepHom`. Not
`@[simp]` because `simp` rewrites `MulEquiv.toMonoidHom` to a coercion, which no longer matches the
domain of `Subgroup.subgroupOfRepHom`. -/
theorem subgroupOfCohomologyIso_hom (hNH : N ≤ H) (n : ℕ) :
    (subgroupOfCohomologyIso hNH n).hom =
      groupCohomology.map (quotientSubgroupOfMulEquivMap N H).symm.toMonoidHom
        (subgroupOfRepHom hNH) n :=
  (groupCohomology.mapIso_hom ..).trans
    (groupCohomology.map_congr rfl (LinearMap.ext fun _ => rfl) n)

/-- Postcomposing the transport map along `Subgroup.subgroupOfRepHom` with the inverse of
`Subgroup.subgroupOfCohomologyIso` is the identity. -/
@[reassoc]
theorem map_subgroupOfRepHom_comp_subgroupOfCohomologyIso_inv (hNH : N ≤ H) (n : ℕ) :
    groupCohomology.map (quotientSubgroupOfMulEquivMap N H).symm.toMonoidHom
        (subgroupOfRepHom hNH) n ≫ (subgroupOfCohomologyIso hNH n).inv = 𝟙 _ := by
  rw [← subgroupOfCohomologyIso_hom, Iso.hom_inv_id]

/-- Applying the inverse of `Subgroup.subgroupOfCohomologyIso` cancels transport along
`Subgroup.subgroupOfRepHom`. -/
theorem subgroupOfCohomologyIso_inv_map_subgroupOfRepHom_apply (hNH : N ≤ H) (n : ℕ)
    (x : groupCohomology (Rep.ofMulDistribMulAction (H ⧸ N.subgroupOf H) (N.subgroupOf H)) n) :
    (subgroupOfCohomologyIso hNH n).inv
        (groupCohomology.map (quotientSubgroupOfMulEquivMap N H).symm.toMonoidHom
          (subgroupOfRepHom hNH) n x) = x := by
  rw [← subgroupOfCohomologyIso_hom]
  exact (subgroupOfCohomologyIso hNH n).hom_inv_id_apply x

/-- Precomposing the transport map along `Subgroup.subgroupOfRepHom` with the inverse of
`Subgroup.subgroupOfCohomologyIso` is the identity. -/
@[reassoc]
theorem subgroupOfCohomologyIso_inv_comp_map_subgroupOfRepHom (hNH : N ≤ H) (n : ℕ) :
    (subgroupOfCohomologyIso hNH n).inv ≫
      groupCohomology.map (quotientSubgroupOfMulEquivMap N H).symm.toMonoidHom
        (subgroupOfRepHom hNH) n = 𝟙 _ := by
  rw [← subgroupOfCohomologyIso_hom, Iso.inv_hom_id]

/-- Transport along `Subgroup.subgroupOfRepHom` cancels the inverse of
`Subgroup.subgroupOfCohomologyIso`. -/
theorem map_subgroupOfRepHom_subgroupOfCohomologyIso_inv_apply (hNH : N ≤ H) (n : ℕ)
    (x : groupCohomology (Rep.res (H.map (QuotientGroup.mk' N)).subtype
      (Rep.ofMulDistribMulAction (G ⧸ N) N)) n) :
    groupCohomology.map (quotientSubgroupOfMulEquivMap N H).symm.toMonoidHom
        (subgroupOfRepHom hNH) n ((subgroupOfCohomologyIso hNH n).inv x) = x := by
  rw [← subgroupOfCohomologyIso_hom]
  exact (subgroupOfCohomologyIso hNH n).inv_hom_id_apply x

/-- The transport map on cohomology along `Subgroup.quotientSubgroupOfMulEquivMap` and
`Subgroup.subgroupOfRepHom` is an isomorphism in every degree. -/
instance isIso_map_subgroupOfRepHom (hNH : N ≤ H) (n : ℕ) :
    IsIso (groupCohomology.map (quotientSubgroupOfMulEquivMap N H).symm.toMonoidHom
      (subgroupOfRepHom hNH) n) :=
  subgroupOfCohomologyIso_hom hNH n ▸ inferInstanceAs (IsIso (subgroupOfCohomologyIso hNH n).hom)

/-- The transport map on cohomology along `Subgroup.quotientSubgroupOfMulEquivMap` and
`Subgroup.subgroupOfRepHom` is bijective in every degree. -/
theorem map_subgroupOfRepHom_bijective (hNH : N ≤ H) (n : ℕ) :
    Function.Bijective (groupCohomology.map (quotientSubgroupOfMulEquivMap N H).symm.toMonoidHom
      (subgroupOfRepHom hNH) n) :=
  have := isIso_map_subgroupOfRepHom hNH n
  ConcreteCategory.bijective_of_isIso
    (groupCohomology.map (quotientSubgroupOfMulEquivMap N H).symm.toMonoidHom
      (subgroupOfRepHom hNH) n)

/-- A cohomology class of `H ⧸ N.subgroupOf H` vanishes under transport along
`Subgroup.subgroupOfRepHom` if and only if it is zero. -/
theorem map_subgroupOfRepHom_eq_zero_iff (hNH : N ≤ H) (n : ℕ)
    (x : groupCohomology (Rep.ofMulDistribMulAction (H ⧸ N.subgroupOf H) (N.subgroupOf H)) n) :
    groupCohomology.map (quotientSubgroupOfMulEquivMap N H).symm.toMonoidHom
        (subgroupOfRepHom hNH) n x = 0 ↔ x = 0 :=
  map_eq_zero_iff _ (map_subgroupOfRepHom_bijective hNH n).injective

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

/-- Applying the inverse of `Subgroup.subgroupOfCohomologyIso` to the restricted quotient extension
class of `G` by `N` recovers the quotient extension class of `H` by `N.subgroupOf H`. -/
theorem subgroupOfCohomologyIso_inv_map_subtype_cohomologyClass_factorSet_quotientExtension
    (hNH : N ≤ H) (σ : N.quotientExtension.Section) (hσ : σ 1 = 1)
    (τ : (N.subgroupOf H).quotientExtension.Section) (hτ : τ 1 = 1) :
    (subgroupOfCohomologyIso hNH 2).inv
        (groupCohomology.map (H.map (QuotientGroup.mk' N)).subtype (𝟙 _) 2
          (TauCeti.GroupExtension.factorSet σ hσ
            N.quotientExtension_inducesAction).cohomologyClass) =
      (TauCeti.GroupExtension.factorSet τ hτ
        (N.subgroupOf H).quotientExtension_inducesAction).cohomologyClass := by
  rw [map_subtype_cohomologyClass_factorSet_quotientExtension hNH σ hσ τ hτ,
    subgroupOfCohomologyIso_inv_map_subgroupOfRepHom_apply]

/-- For `N ≤ H`, the restriction of the quotient extension class of `G` by `N` to the image of `H`
in `G ⧸ N` vanishes if and only if the quotient extension class of `H` by `N.subgroupOf H`
vanishes. -/
theorem map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff (hNH : N ≤ H)
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1)
    (τ : (N.subgroupOf H).quotientExtension.Section) (hτ : τ 1 = 1) :
    groupCohomology.map (H.map (QuotientGroup.mk' N)).subtype (𝟙 _) 2
        (TauCeti.GroupExtension.factorSet σ hσ
          N.quotientExtension_inducesAction).cohomologyClass = 0 ↔
      (TauCeti.GroupExtension.factorSet τ hτ
        (N.subgroupOf H).quotientExtension_inducesAction).cohomologyClass = 0 := by
  rw [map_subtype_cohomologyClass_factorSet_quotientExtension hNH σ hσ τ hτ,
    map_subgroupOfRepHom_eq_zero_iff]

/-- **Local complements and the restricted extension class.** For `N ≤ H`, the abelian normal
subgroup `N` has a local complement in `H` if and only if the restriction of the quotient extension
class of `G` by `N` to the image of `H` in `G ⧸ N` vanishes. Neither `G`, `H`, nor `N` need be
finite. -/
theorem exists_isLocalComplement_iff_map_subtype_cohomologyClass_eq_zero (hNH : N ≤ H)
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    (∃ K : Subgroup G, N.IsLocalComplement K H) ↔
      groupCohomology.map (H.map (QuotientGroup.mk' N)).subtype (𝟙 _) 2
        (TauCeti.GroupExtension.factorSet σ hσ
          N.quotientExtension_inducesAction).cohomologyClass = 0 := by
  let τ := TauCeti.GroupExtension.normalizeSection
    (N.subgroupOf H).quotientExtension.surjInvRightHom
  have hτ : τ 1 = 1 := TauCeti.GroupExtension.normalizeSection_one _
  exact (exists_isLocalComplement_iff_exists_isComplement'_subgroupOf hNH).trans
    (((N.subgroupOf H).exists_complement_iff_cohomologyClass_eq_zero τ hτ).trans
      (map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff hNH σ hσ τ hτ).symm)

/-- If `N` has a local complement in `H`, the restriction of the quotient extension class of `G`
by `N` to the image of `H` in `G ⧸ N` vanishes. -/
theorem IsLocalComplement.map_subtype_cohomologyClass_eq_zero {K : Subgroup G}
    (hK : N.IsLocalComplement K H) (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    groupCohomology.map (H.map (QuotientGroup.mk' N)).subtype (𝟙 _) 2
      (TauCeti.GroupExtension.factorSet σ hσ
        N.quotientExtension_inducesAction).cohomologyClass = 0 :=
  (exists_isLocalComplement_iff_map_subtype_cohomologyClass_eq_zero hK.left_le σ hσ).mp ⟨K, hK⟩

/-- **A local complement in `H` forces the index of `H` to kill the class of the quotient
extension.** If `N` has a local complement in `H`, then `[G : H]` kills the class in
`H²(G ⧸ N, N)` of the quotient extension of `G` by `N`. When `H` has infinite index, `H.index = 0`
and the statement holds trivially. Neither `G` nor `N` need be finite. -/
theorem IsLocalComplement.index_nsmul_cohomologyClass_eq_zero {K : Subgroup G}
    (hK : N.IsLocalComplement K H) (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    H.index •
      (TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction).cohomologyClass =
        0 := by
  by_cases hH : H.FiniteIndex
  swap
  · rw [not_finiteIndex_iff.1 hH, zero_smul]
  have hindex : (H.map (QuotientGroup.mk' N)).index = H.index :=
    H.index_map_eq (QuotientGroup.mk'_surjective N) ((QuotientGroup.ker_mk' N).trans_le hK.left_le)
  rw [← hindex]
  exact TauCeti.groupCohomology.index_nsmul_eq_zero_of_map_eq_zero _
    (hK.map_subtype_cohomologyClass_eq_zero σ hσ)

/-- **When `[G : H]` is prime to `|N|`, restriction to the image of `H` is injective on
`Hⁿ(G ⧸ N, N)`**, in every degree `n`. Neither `G`, `H`, nor `N` need be finite. -/
theorem map_subtype_quotientConjugationAction_injective_of_coprime_index
    (hcop : Nat.Coprime H.index (Nat.card N)) (n : ℕ) :
    Function.Injective (groupCohomology.map (H.map (QuotientGroup.mk' N)).subtype
      (𝟙 (Rep.res (H.map (QuotientGroup.mk' N)).subtype
        (Rep.ofMulDistribMulAction (G ⧸ N) N))) n) := by
  refine TauCeti.groupCohomology.map_subtype_injective_of_coprime_index_card _ _ ?_ n
  have hdvd : (H.map (QuotientGroup.mk' N)).index ∣ H.index :=
    H.index_map_dvd (QuotientGroup.mk'_surjective N)
  have hcard : Nat.card (Rep.ofMulDistribMulAction (G ⧸ N) N) = Nat.card N :=
    Nat.card_congr Additive.toMul
  rw [hcard]
  exact hcop.coprime_dvd_left hdvd

/-- When `[G : H]` is prime to `|N|`, the quotient extension class of `G` by `N` vanishes on the
image of `H` in `G ⧸ N` if and only if it vanishes on `G ⧸ N`. Neither `G`, `H`, nor `N` need be
finite. -/
theorem map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff_of_coprime_index
    (hcop : Nat.Coprime H.index (Nat.card N))
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    groupCohomology.map (H.map (QuotientGroup.mk' N)).subtype (𝟙 _) 2
        (TauCeti.GroupExtension.factorSet σ hσ
          N.quotientExtension_inducesAction).cohomologyClass = 0 ↔
      (TauCeti.GroupExtension.factorSet σ hσ
        N.quotientExtension_inducesAction).cohomologyClass = 0 :=
  map_eq_zero_iff _ (map_subtype_quotientConjugationAction_injective_of_coprime_index hcop 2)

/-- **Coprime-index detection of the quotient extension class** (Gaschütz). When `[G : H]` is prime
to `|N|`, the subgroup `H` contains `N` and the class of the quotient extension of `G` by `N`
vanishes if and only if the class of the quotient extension of `H` by `N.subgroupOf H` vanishes.
Neither `G`, `H`, nor `N` need be finite. -/
theorem cohomologyClass_factorSet_quotientExtension_eq_zero_iff_of_coprime_index
    (hcop : Nat.Coprime H.index (Nat.card N))
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1)
    (τ : (N.subgroupOf H).quotientExtension.Section) (hτ : τ 1 = 1) :
    (TauCeti.GroupExtension.factorSet σ hσ
        N.quotientExtension_inducesAction).cohomologyClass = 0 ↔
      (TauCeti.GroupExtension.factorSet τ hτ
        (N.subgroupOf H).quotientExtension_inducesAction).cohomologyClass = 0 :=
  (map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff_of_coprime_index
    hcop σ hσ).symm.trans
    (map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff
      (le_of_coprime_index_card hcop) σ hσ τ hτ)

/-- **Cohomological form of Gaschütz's splitting theorem.** If `N` has a local complement in a
subgroup `H` whose index `[G : H]` is prime to `|N|`, then the class of the quotient extension of
`G` by `N` vanishes (so `N` has a global complement in `G` by
`Subgroup.exists_complement_iff_cohomologyClass_eq_zero`). Neither `G`, `H`, nor `N` need be
finite. -/
theorem IsLocalComplement.cohomologyClass_factorSet_eq_zero_of_coprime_index {K : Subgroup G}
    (hK : N.IsLocalComplement K H) (hcop : Nat.Coprime H.index (Nat.card N))
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    (TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction).cohomologyClass =
      0 :=
  (nsmul_eq_zero_iff_of_coprime hcop).1
    ⟨hK.index_nsmul_cohomologyClass_eq_zero σ hσ,
      TauCeti.FactorSet.natCard_nsmul_cohomologyClass_eq_zero _⟩

end Subgroup
