/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Complement.Local
public import TauCeti.GroupTheory.GroupExtension.Quotient.Cohomology
public import TauCeti.GroupTheory.QuotientGroup.KerEquiv
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Sylow

/-!
# Restricting the class of a quotient extension and the cohomological Gaschütz proof

Let `N` be an abelian normal subgroup of `G` and `N ≤ H`. The quotient `H ⧸ N` is the image of
`H` in `G ⧸ N`, and `N.subgroupOf H` is `N`. This file proves that this identification of
representations and cohomology groups is an isomorphism in every degree, and that the class of the
quotient extension of `G` by `N` in `H²(G ⧸ N, N)` restricts, on the image of `H`, to the class of
the quotient extension of `H` by `N`. Consequently `N` has a local complement in `H` if and only if
that restricted class vanishes.

Combined with corestriction and coefficient-cardinality annihilation
(`TauCeti.FactorSet.natCard_nsmul_cohomologyClass_eq_zero`), this gives the cohomological proof of
Gaschütz's splitting theorem and of Sylow detection:

* If `N` has a local complement in `H`, then `[G : H]` kills the class of the quotient extension of
  `G` (`Subgroup.IsLocalComplement.index_nsmul_cohomologyClass_eq_zero`); when `[G : H]` is coprime
  to `|N|`, Bézout with `|N| • x = 0` forces `x = 0`
  (`Subgroup.IsLocalComplement.cohomologyClass_eq_zero_of_coprime_index`). More generally,
  restriction `H²(G ⧸ N, N) ⟶ H²(H ⧸ N, N)` is injective when `[G : H]` is coprime to `|N|`, so
  the global extension class vanishes if and only if `H`'s quotient extension class vanishes, and
  if and only if `N` has a local complement in `H`.
* If `N` is an abelian normal `p`-subgroup (`IsPGroup p N`, not necessarily finite) and `P` is a
  finite-index Sylow `p`-subgroup of `G`, the image of `P` in `G ⧸ N` is a finite-index Sylow
  `p`-subgroup of `G ⧸ N`, so restriction to `P.map (QuotientGroup.mk' N)` is injective on
  `H²(G ⧸ N, N)` (for finite `N` of order `p ^ j`, directly via
  `TauCeti.groupCohomology.eq_zero_of_pow_nsmul_eq_zero_of_map_sylow_eq_zero`, and in general via
  `TauCeti.groupCohomology.map_sylow_injective_of_isAddPGroup`). Hence the global extension class
  vanishes if and only if `P`'s quotient extension class vanishes, and if and only if `N` has a
  local complement in `P`.

Combined with `Subgroup.exists_complement_iff_cohomologyClass_eq_zero`, these criteria recover
Gaschütz's splitting theorem and Sylow detection of complements on `G : Type` without crossed
transfer.

## Main definitions

* `Subgroup.subgroupOfRepHom` and `Subgroup.subgroupOfRepIso`: `N.subgroupOf H ≃ N` as a morphism
  and isomorphism of representations of the image of `H` in `G ⧸ N`.
* `Subgroup.subgroupOfCohomologyIso`: the induced isomorphism
  `Hⁿ(H ⧸ N.subgroupOf H, N.subgroupOf H) ≅ Hⁿ(H.map (QuotientGroup.mk' N), N)`.

## Main results

* `Subgroup.map_subtype_cohomologyClass_factorSet_quotientExtension`: the restriction formula.
* `Subgroup.exists_isLocalComplement_iff_map_subtype_cohomologyClass_eq_zero`: `N` has a local
  complement in `H` if and only if the restricted extension class on `H.map (QuotientGroup.mk' N)`
  vanishes.
* `Subgroup.IsLocalComplement.index_nsmul_cohomologyClass_eq_zero` and
  `Subgroup.IsLocalComplement.cohomologyClass_eq_zero_of_coprime_index`: a local complement in `H`
  forces `[G : H]` to kill the quotient extension class, and forces the class itself to vanish when
  `[G : H]` is coprime to `|N|`.
* `Subgroup.cohomologyClass_factorSet_quotientExtension_eq_zero_iff_of_coprime_index` and
  `Subgroup.exists_isLocalComplement_iff_cohomologyClass_eq_zero_of_coprime_index`: the
  coprime-index cohomological Gaschütz criteria.
* `IsPGroup.cohomologyClass_factorSet_quotientExtension_eq_zero_iff_sylow` and
  `IsPGroup.exists_isLocalComplement_sylow_iff_cohomologyClass_eq_zero`: the cohomological Sylow
  detection criteria (requiring neither `[Finite G]` nor `[Finite N]`).

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math. 190
  (1952), 93–107.
* K. S. Brown, *Cohomology of Groups*, Chapter IV, §3 and Chapter III, §9.
* J. S. Milne, *Class Field Theory*, Chapter II, Corollary 1.33.
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

/-- Identifying `N.subgroupOf H` with `N` is an isomorphism of representations of the image of `H`
in `G ⧸ N`. -/
noncomputable def subgroupOfRepIso (hNH : N ≤ H) :
    Rep.res (quotientSubgroupOfMulEquivMap N H).symm.toMonoidHom
        (Rep.ofMulDistribMulAction (H ⧸ N.subgroupOf H) (N.subgroupOf H)) ≅
      Rep.res (H.map (QuotientGroup.mk' N)).subtype (Rep.ofMulDistribMulAction (G ⧸ N) N) :=
  Rep.mkIso (Representation.Equiv.mk (N.subgroupOfEquivOfLe hNH).toAdditive.toIntLinearEquiv
    fun q ↦ by
      ext x
      have h := subgroupOfEquivOfLe_smul hNH ((quotientSubgroupOfMulEquivMap N H).symm q) x.toMul
      rw [MulEquiv.apply_symm_apply] at h
      exact congrArg Additive.ofMul h)

@[simp]
theorem subgroupOfRepIso_hom (hNH : N ≤ H) :
    (subgroupOfRepIso hNH).hom = subgroupOfRepHom hNH := by
  ext x
  rfl

instance (hNH : N ≤ H) : IsIso (subgroupOfRepHom hNH) :=
  subgroupOfRepIso_hom hNH ▸ inferInstance

/-- Inverse representation morphism along `Subgroup.quotientSubgroupOfMulEquivMap`, used to build
`Subgroup.subgroupOfCohomologyIso`. -/
private noncomputable def subgroupOfRepInvHom (hNH : N ≤ H) :
    Rep.res (quotientSubgroupOfMulEquivMap N H).toMonoidHom
        (Rep.res (H.map (QuotientGroup.mk' N)).subtype (Rep.ofMulDistribMulAction (G ⧸ N) N)) ⟶
      Rep.ofMulDistribMulAction (H ⧸ N.subgroupOf H) (N.subgroupOf H) :=
  Rep.ofHom ⟨(N.subgroupOfEquivOfLe hNH).symm.toMonoidHom.toAdditive.toIntLinearMap, fun y ↦ by
    ext1 x
    let m : N := Additive.toMul (x : Additive N)
    have h : (N.subgroupOfEquivOfLe hNH).symm
        ((quotientSubgroupOfMulEquivMap N H y : G ⧸ N) • m) =
        y • (N.subgroupOfEquivOfLe hNH).symm m :=
      (N.subgroupOfEquivOfLe hNH).injective (by
        rw [MulEquiv.apply_symm_apply, subgroupOfEquivOfLe_smul, MulEquiv.apply_symm_apply])
    exact congrArg Additive.ofMul h⟩

private theorem subgroupOfRepHom_comp_inv_toLinearMap (hNH : N ≤ H) :
    (subgroupOfRepInvHom hNH).hom.toLinearMap.comp (subgroupOfRepHom hNH).hom.toLinearMap =
      LinearMap.id :=
  LinearMap.ext fun (x : Additive (N.subgroupOf H)) ↦
    congrArg Additive.ofMul ((N.subgroupOfEquivOfLe hNH).symm_apply_apply x.toMul)

private theorem subgroupOfRepInvHom_comp_hom_toLinearMap (hNH : N ≤ H) :
    (subgroupOfRepHom hNH).hom.toLinearMap.comp (subgroupOfRepInvHom hNH).hom.toLinearMap =
      LinearMap.id :=
  LinearMap.ext fun (x : Additive N) ↦
    congrArg Additive.ofMul ((N.subgroupOfEquivOfLe hNH).apply_symm_apply x.toMul)

/-- The isomorphism `Hⁿ(H ⧸ N.subgroupOf H, N.subgroupOf H) ≅ Hⁿ(H.map (QuotientGroup.mk' N), N)`
induced in every degree `n` by `Subgroup.quotientSubgroupOfMulEquivMap` and
`Subgroup.subgroupOfEquivOfLe`. -/
noncomputable def subgroupOfCohomologyIso (hNH : N ≤ H) (n : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction (H ⧸ N.subgroupOf H) (N.subgroupOf H)) n ≅
      groupCohomology
        (Rep.res (H.map (QuotientGroup.mk' N)).subtype (Rep.ofMulDistribMulAction (G ⧸ N) N)) n :=
  groupCohomology.mapIso (quotientSubgroupOfMulEquivMap N H)
    (LinearEquiv.ofLinearMap (subgroupOfRepHom hNH).hom.toLinearMap
      (subgroupOfRepInvHom hNH).hom.toLinearMap
      (subgroupOfRepInvHom_comp_hom_toLinearMap hNH)
      (subgroupOfRepHom_comp_inv_toLinearMap hNH))
    (fun y ↦ LinearMap.ext fun (x : Additive (N.subgroupOf H)) ↦
      congrArg Additive.ofMul (subgroupOfEquivOfLe_smul hNH y x.toMul))
    n

@[simp]
theorem subgroupOfCohomologyIso_hom (hNH : N ≤ H) (n : ℕ) :
    (subgroupOfCohomologyIso hNH n).hom =
      groupCohomology.map (quotientSubgroupOfMulEquivMap N H).symm.toMonoidHom
        (subgroupOfRepHom hNH) n :=
  (rfl)

instance (hNH : N ≤ H) (n : ℕ) :
    IsIso (groupCohomology.map (quotientSubgroupOfMulEquivMap N H).symm.toMonoidHom
      (subgroupOfRepHom hNH) n) :=
  subgroupOfCohomologyIso_hom hNH n ▸ inferInstance

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

/-- The restriction to `H.map (QuotientGroup.mk' N)` of the quotient extension class of `G` by `N`
vanishes if and only if the quotient extension class of `H` by `N.subgroupOf H` vanishes. -/
theorem map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff (hNH : N ≤ H)
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1)
    (τ : (N.subgroupOf H).quotientExtension.Section) (hτ : τ 1 = 1) :
    groupCohomology.map (H.map (QuotientGroup.mk' N)).subtype (𝟙 _) 2
        (TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction).cohomologyClass =
      0 ↔
      (TauCeti.GroupExtension.factorSet τ hτ
        (N.subgroupOf H).quotientExtension_inducesAction).cohomologyClass = 0 := by
  rw [map_subtype_cohomologyClass_factorSet_quotientExtension hNH σ hσ τ hτ,
    ← subgroupOfCohomologyIso_hom hNH 2]
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (subgroupOfCohomologyIso hNH 2).hom).1)

/-- For `N ≤ H`, `N` has a local complement in `H` if and only if the restriction of the quotient
extension class of `G` by `N` to `H.map (QuotientGroup.mk' N)` vanishes. -/
theorem exists_isLocalComplement_iff_map_subtype_cohomologyClass_eq_zero (hNH : N ≤ H)
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    (∃ K : Subgroup G, N.IsLocalComplement K H) ↔
      groupCohomology.map (H.map (QuotientGroup.mk' N)).subtype (𝟙 _) 2
        (TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction).cohomologyClass =
          0 := by
  let τ := TauCeti.GroupExtension.normalizeSection
    (N.subgroupOf H).quotientExtension.surjInvRightHom
  have hτ : τ 1 = 1 := TauCeti.GroupExtension.normalizeSection_one _
  exact (exists_isLocalComplement_iff_exists_isComplement'_subgroupOf hNH).trans <|
    ((N.subgroupOf H).exists_complement_iff_cohomologyClass_eq_zero τ hτ).trans
      (map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff hNH σ hσ τ hτ).symm

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
  have hindex : (H.map (QuotientGroup.mk' N)).index = H.index :=
    H.index_map_eq (QuotientGroup.mk'_surjective N) ((QuotientGroup.ker_mk' N).trans_le hK.left_le)
  have : (H.map (QuotientGroup.mk' N)).FiniteIndex :=
    FiniteIndex.map_of_surjective H (QuotientGroup.mk'_surjective N)
  rw [← hindex]
  exact TauCeti.groupCohomology.index_nsmul_eq_zero_of_map_eq_zero _
    ((exists_isLocalComplement_iff_map_subtype_cohomologyClass_eq_zero hK.left_le σ hσ).1 ⟨K, hK⟩)

/-- **Cohomological Gaschütz vanishing.** If `N` has a local complement in `H` and `[G : H]` is
coprime to `Nat.card N`, then the class in `H²(G ⧸ N, N)` of the quotient extension of `G` by `N`
vanishes: both `[G : H]` and `Nat.card N` annihilate the class. Neither `G` nor `N` need be
finite. -/
theorem IsLocalComplement.cohomologyClass_eq_zero_of_coprime_index {K : Subgroup G}
    (hK : N.IsLocalComplement K H) (hcop : Nat.Coprime H.index (Nat.card N))
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    (TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction).cohomologyClass =
      0 :=
  (nsmul_eq_zero_iff_of_coprime hcop).1
    ⟨hK.index_nsmul_cohomologyClass_eq_zero σ hσ,
      TauCeti.FactorSet.natCard_nsmul_cohomologyClass_eq_zero _⟩

omit [IsMulCommutative N] in
private theorem le_of_coprime_index (hcop : Nat.Coprime H.index (Nat.card N)) : N ≤ H :=
  le_sup_right.trans <| relIndex_eq_one.mp <| Nat.eq_one_of_dvd_coprimes hcop
    (relIndex_dvd_index_of_le le_sup_left)
    ((relIndex_sup_of_le_normalizer (le_normalizer_of_normal (H := N))).symm ▸
      relIndex_dvd_card H N)

/-- **Cohomological Gaschütz criterion on extension classes.** When `[G : H]` is coprime to
`Nat.card N` (which forces `N ≤ H` since `N` is normal), the class of the quotient extension of `G`
by `N` vanishes if and only if the class of the quotient extension of `H` by `N.subgroupOf H`
vanishes. -/
theorem cohomologyClass_factorSet_quotientExtension_eq_zero_iff_of_coprime_index
    (hcop : Nat.Coprime H.index (Nat.card N))
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1)
    (τ : (N.subgroupOf H).quotientExtension.Section) (hτ : τ 1 = 1) :
    (TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction).cohomologyClass = 0 ↔
      (TauCeti.GroupExtension.factorSet τ hτ
        (N.subgroupOf H).quotientExtension_inducesAction).cohomologyClass = 0 := by
  have hNH : N ≤ H := le_of_coprime_index hcop
  have hindex : (H.map (QuotientGroup.mk' N)).index = H.index :=
    H.index_map_eq (QuotientGroup.mk'_surjective N) ((QuotientGroup.ker_mk' N).trans_le hNH)
  have hcard : Nat.card (Rep.ofMulDistribMulAction (G ⧸ N) N) = Nat.card N :=
    Nat.card_congr Additive.toMul
  have hinj := TauCeti.groupCohomology.map_subtype_injective_of_coprime_index
    (H.map (QuotientGroup.mk' N)) (A := Rep.ofMulDistribMulAction (G ⧸ N) N)
    (by rwa [hindex, hcard]) 2
  rw [← map_eq_zero_iff _ hinj,
    map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff hNH σ hσ τ hτ]

/-- **Cohomological Gaschütz criterion for local complements.** When `[G : H]` is coprime to
`Nat.card N` (which forces `N ≤ H` since `N` is normal), `N` has a local complement in `H` if and
only if the quotient extension class of `G` by `N` vanishes. Combined with
`Subgroup.exists_complement_iff_cohomologyClass_eq_zero`, this recovers Gaschütz's splitting
theorem on `G : Type` without crossed transfer. -/
theorem exists_isLocalComplement_iff_cohomologyClass_eq_zero_of_coprime_index
    (hcop : Nat.Coprime H.index (Nat.card N))
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    (∃ K : Subgroup G, N.IsLocalComplement K H) ↔
      (TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction).cohomologyClass =
        0 := by
  have hNH : N ≤ H := le_of_coprime_index hcop
  let τ := TauCeti.GroupExtension.normalizeSection
    (N.subgroupOf H).quotientExtension.surjInvRightHom
  have hτ : τ 1 = 1 := TauCeti.GroupExtension.normalizeSection_one _
  exact (exists_isLocalComplement_iff_map_subtype_cohomologyClass_eq_zero hNH σ hσ).trans <|
    (map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff hNH σ hσ τ hτ).trans
      (cohomologyClass_factorSet_quotientExtension_eq_zero_iff_of_coprime_index hcop σ hσ τ
        hτ).symm

end Subgroup

namespace IsPGroup

open CategoryTheory
open scoped IsMulCommutative

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal]
  [IsMulCommutative N]

attribute [local instance] Subgroup.quotientConjugationAction

/-- **Cohomological Sylow detection on extension classes.** Let `N` be an abelian normal
`p`-subgroup of `G` (not necessarily finite) and `P` a finite-index Sylow `p`-subgroup of `G`
(which contains `N` by `IsPGroup.le_sylow_of_normal`). Then the quotient extension class of `G` by
`N` in `H²(G ⧸ N, N)` vanishes if and only if the quotient extension class of `P` by
`N.subgroupOf P` vanishes: the image `(P : Subgroup G).map (QuotientGroup.mk' N)` is a finite-index
Sylow `p`-subgroup of `G ⧸ N`, on which restriction is injective because `Additive N` is an
additive `p`-group. -/
theorem cohomologyClass_factorSet_quotientExtension_eq_zero_iff_sylow
    (hN : IsPGroup p N) (P : Sylow p G) [P.FiniteIndex]
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1)
    (τ : (N.subgroupOf P).quotientExtension.Section) (hτ : τ 1 = 1) :
    (TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction).cohomologyClass = 0 ↔
      (TauCeti.GroupExtension.factorSet τ hτ
        (N.subgroupOf (P : Subgroup G)).quotientExtension_inducesAction).cohomologyClass = 0 := by
  let Q : Sylow p (G ⧸ N) :=
    (P.isPGroup.map (QuotientGroup.mk' N)).toSylow
      (P.not_dvd_index <| ·.trans <| P.index_map_dvd (QuotientGroup.mk'_surjective N))
  have hQ : (Q : Subgroup (G ⧸ N)) = (P : Subgroup G).map (QuotientGroup.mk' N) :=
    IsPGroup.toSylow_coe _ _
  have : (Q : Subgroup (G ⧸ N)).FiniteIndex := by
    rw [hQ]
    exact Subgroup.FiniteIndex.map_of_surjective (P : Subgroup G) (QuotientGroup.mk'_surjective N)
  have hAdd : IsAddPGroup p (Additive N) := fun a ↦
    let ⟨k, hk⟩ := hN a.toMul
    ⟨k, Additive.toMul.injective (by rw [toMul_nsmul, hk, toMul_zero])⟩
  have hinj : Function.Injective
      (groupCohomology.map ((P : Subgroup G).map (QuotientGroup.mk' N)).subtype
        (𝟙 (Rep.res ((P : Subgroup G).map (QuotientGroup.mk' N)).subtype
          (Rep.ofMulDistribMulAction (G ⧸ N) N))) 2) := by
    rw [← hQ]
    exact TauCeti.groupCohomology.map_sylow_injective_of_isAddPGroup
      (Rep.ofMulDistribMulAction (G ⧸ N) N) 2 p Q hAdd
  rw [← map_eq_zero_iff _ hinj,
    Subgroup.map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff
      (hN.le_sylow_of_normal P) σ hσ τ hτ]

/-- **Cohomological Sylow detection for local complements.** For an abelian normal `p`-subgroup
`N` of `G` (not necessarily finite) and a finite-index Sylow `p`-subgroup `P` of `G`, `N` has a
local complement in `P` if and only if the quotient extension class of `G` by `N` vanishes.
Combined with `Subgroup.exists_complement_iff_cohomologyClass_eq_zero`, this recovers Sylow
detection of complements on `G : Type` without assuming `[Finite G]` or `[Finite N]`. -/
theorem exists_isLocalComplement_sylow_iff_cohomologyClass_eq_zero
    (hN : IsPGroup p N) (P : Sylow p G) [P.FiniteIndex]
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    (∃ K : Subgroup G, N.IsLocalComplement K P) ↔
      (TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction).cohomologyClass =
        0 := by
  let τ := TauCeti.GroupExtension.normalizeSection
    (N.subgroupOf (P : Subgroup G)).quotientExtension.surjInvRightHom
  have hτ : τ 1 = 1 := TauCeti.GroupExtension.normalizeSection_one _
  exact (Subgroup.exists_isLocalComplement_iff_map_subtype_cohomologyClass_eq_zero
      (hN.le_sylow_of_normal P) σ hσ).trans <|
    (Subgroup.map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff
      (hN.le_sylow_of_normal P) σ hσ τ hτ).trans
      (hN.cohomologyClass_factorSet_quotientExtension_eq_zero_iff_sylow P σ hσ τ hτ).symm

end IsPGroup
