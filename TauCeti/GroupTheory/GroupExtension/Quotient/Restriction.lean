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
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Restricting the class of a quotient extension and the cohomological Gaschütz proof

Let `N` be an abelian normal subgroup of `G` and `N ≤ H`. The quotient `H ⧸ N.subgroupOf H` is
isomorphic to the image of `H` in `G ⧸ N`, and `N.subgroupOf H` is isomorphic to `N`, intertwining
the quotient conjugation actions (`Subgroup.subgroupOfCohomologyIso`). This file proves that the
class of the quotient extension of `G` by `N` in `H²(G ⧸ N, N)` restricts, on that image, to the
transported class of the quotient extension of `H` by `N.subgroupOf H`. Because the transport is
an isomorphism, the restricted class vanishes if and only if `N` has a local complement in `H`
(`Subgroup.map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff`).

Combining this with corestriction yields the cohomological proofs of Gaschütz's splitting theorem
and of Sylow complement detection, without using crossed transfer:

* If `N` has a local complement in `H`, then `[G : H]` kills the extension class
  (`Subgroup.IsLocalComplement.index_nsmul_cohomologyClass_eq_zero`), while `Monoid.exponent N`
  (and hence `Nat.card N`) kills every factor-set class
  (`TauCeti.FactorSet.exponent_nsmul_cohomologyClass_eq_zero`,
  `TauCeti.FactorSet.natCard_nsmul_cohomologyClass_eq_zero`). When `[G : H]` is coprime to
  `Monoid.exponent N` (or to `Nat.card N`), Bézout forces the class to vanish, and
  `Subgroup.exists_complement_iff_cohomologyClass_eq_zero` produces a global complement of `N` in
  `G`. Stated in terms of `Monoid.exponent N`, this covers infinite abelian normal subgroups of
  finite exponent (such as infinite elementary abelian `p`-groups) where `Nat.card N = 0`.
* When `N` is an abelian normal `p`-subgroup of finite index in `G` and `P` is a Sylow `p`-subgroup
  of `G`, the image of `P` in the finite group `G ⧸ N` is a Sylow `p`-subgroup and `N` is an
  additive `p`-group, so restriction `Hⁿ(G ⧸ N, N) ⟶ Hⁿ(P.map (mk' N), N)` is injective in every
  degree (`IsPGroup.map_subtype_quotientConjugation_sylow_injective`). In degree `2` this detects
  global complements of `N` from `P` (`IsPGroup.exists_isComplement'_iff_sylow_of_finiteIndex`),
  without assuming `N` is finite.

## Main definitions

* `Subgroup.subgroupOfRepHom`: `N.subgroupOf H ≃ N` as a morphism of representations of the
  image of `H` in `G ⧸ N`.
* `Subgroup.subgroupOfCohomologyIso`: the induced isomorphism
  `Hⁿ(H ⧸ N.subgroupOf H, N.subgroupOf H) ≅ Hⁿ(H.map (mk' N), N)`.

## Main results

* `Subgroup.map_subtype_cohomologyClass_factorSet_quotientExtension`: the restriction formula.
* `Subgroup.map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff`: the restricted
  class vanishes if and only if `N` has a local complement in `H`.
* `Subgroup.IsLocalComplement.index_nsmul_cohomologyClass_eq_zero`: a local complement in `H`
  forces `[G : H]` to kill the class of the quotient extension.
* `Subgroup.map_subtype_quotientConjugation_injective_of_coprime_index_exponent`,
  `Subgroup.map_subtype_quotientConjugation_injective_of_coprime_index`: restriction on
  `Hⁿ(G ⧸ N, N)` is injective when `[G : H]` is coprime to `Monoid.exponent N` or `Nat.card N`.
* `Subgroup.cohomologyClass_factorSet_quotientExtension_eq_zero_iff_of_coprime_index_exponent`,
  `Subgroup.cohomologyClass_factorSet_quotientExtension_eq_zero_iff_of_coprime_index`,
  `Subgroup.exists_isComplement'_iff_exists_isLocalComplement_of_coprime_index_exponent`: the
  cohomological Gaschütz vanishing and splitting criteria.
* `IsPGroup.map_subtype_quotientConjugation_sylow_injective`,
  `IsPGroup.cohomologyClass_factorSet_quotientExtension_eq_zero_iff_sylow`,
  `IsPGroup.exists_isComplement'_iff_sylow_of_finiteIndex`,
  `IsPGroup.exists_isComplement'_iff_sylow_subgroupOf_of_finiteIndex`: Sylow restriction
  injectivity and cohomological Sylow detection of complements.

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math. 190
  (1952), 93–107.
* K. S. Brown, *Cohomology of Groups*, Chapter IV, §3 and Chapter III, §9–10.
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

/-- Identifying `H ⧸ N.subgroupOf H` with `H.map (QuotientGroup.mk' N)` and `N.subgroupOf H`
with `N` induces an isomorphism between `Hⁿ(H ⧸ N.subgroupOf H, N.subgroupOf H)` and
`Hⁿ(H.map (QuotientGroup.mk' N), Res N)` in every degree `n`. -/
noncomputable def subgroupOfCohomologyIso (hNH : N ≤ H) (n : ℕ) :
    groupCohomology
        (Rep.ofMulDistribMulAction (H ⧸ N.subgroupOf H) (N.subgroupOf H)) n ≅
      groupCohomology
        (Rep.res (H.map (QuotientGroup.mk' N)).subtype
          (Rep.ofMulDistribMulAction (G ⧸ N) N)) n :=
  groupCohomology.mapIso
    (B := Rep.ofMulDistribMulAction (H ⧸ N.subgroupOf H) (N.subgroupOf H))
    (A := Rep.res (H.map (QuotientGroup.mk' N)).subtype (Rep.ofMulDistribMulAction (G ⧸ N) N))
    (quotientSubgroupOfMulEquivMap N H)
    (N.subgroupOfEquivOfLe hNH).toAdditive.toIntLinearEquiv
    (fun y ↦ LinearMap.ext fun x ↦
      congrArg Additive.ofMul (subgroupOfEquivOfLe_smul hNH y (Additive.toMul x))) n

/-- The forward map of `Subgroup.subgroupOfCohomologyIso` is the change-of-group map along
`(quotientSubgroupOfMulEquivMap N H).symm` and `Subgroup.subgroupOfRepHom`. -/
theorem subgroupOfCohomologyIso_hom (hNH : N ≤ H) (n : ℕ) :
    (subgroupOfCohomologyIso hNH n).hom =
      groupCohomology.map (quotientSubgroupOfMulEquivMap N H).symm.toMonoidHom
        (subgroupOfRepHom hNH) n :=
  groupCohomology.map_congr rfl (LinearMap.ext fun _ ↦ rfl) n

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

/-- Transporting the restricted class of the quotient extension of `G` back along
`Subgroup.subgroupOfCohomologyIso` recovers the class of the quotient extension of `H`. -/
theorem subgroupOfCohomologyIso_inv_map_subtype_cohomologyClass (hNH : N ≤ H)
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1)
    (τ : (N.subgroupOf H).quotientExtension.Section) (hτ : τ 1 = 1) :
    (subgroupOfCohomologyIso hNH 2).inv
        (groupCohomology.map (H.map (QuotientGroup.mk' N)).subtype (𝟙 _) 2
          (TauCeti.GroupExtension.factorSet σ hσ
            N.quotientExtension_inducesAction).cohomologyClass) =
      (TauCeti.GroupExtension.factorSet τ hτ
        (N.subgroupOf H).quotientExtension_inducesAction).cohomologyClass := by
  rw [map_subtype_cohomologyClass_factorSet_quotientExtension hNH σ hσ τ hτ,
    ← subgroupOfCohomologyIso_hom]
  exact (subgroupOfCohomologyIso hNH 2).hom_inv_id_apply _

/-- **Local complements and the restricted extension class.** For `N ≤ H ≤ G`, the restriction of
the class of `N → G → G ⧸ N` to the image of `H` in `G ⧸ N` vanishes if and only if `N` has a
local complement in `H`. Neither finiteness nor coprimality is assumed. -/
theorem map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff (hNH : N ≤ H)
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    groupCohomology.map (H.map (QuotientGroup.mk' N)).subtype (𝟙 _) 2
        (TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction).cohomologyClass =
          0 ↔
      ∃ K : Subgroup G, N.IsLocalComplement K H := by
  let τ := TauCeti.GroupExtension.normalizeSection
    (N.subgroupOf H).quotientExtension.surjInvRightHom
  have hτ : τ 1 = 1 := TauCeti.GroupExtension.normalizeSection_one _
  rw [map_subtype_cohomologyClass_factorSet_quotientExtension hNH σ hσ τ hτ,
    ← subgroupOfCohomologyIso_hom,
    map_eq_zero_iff _ ((ModuleCat.mono_iff_injective (subgroupOfCohomologyIso hNH 2).hom).1
      inferInstance),
    ← (N.subgroupOf H).exists_complement_iff_cohomologyClass_eq_zero τ hτ,
    exists_isLocalComplement_iff_exists_isComplement'_subgroupOf hNH]

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
  rw [← H.index_map_eq (QuotientGroup.mk'_surjective N)
    ((QuotientGroup.ker_mk' N).trans_le hK.left_le)]
  exact TauCeti.groupCohomology.index_nsmul_eq_zero_of_map_eq_zero _
    ((map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff
      hK.left_le σ hσ).2 ⟨K, hK⟩)

/-- Restriction `Hⁿ(G ⧸ N, N) ⟶ Hⁿ(H.map (mk' N), N)` is injective in every degree `n` when
`N ≤ H` and `[G : H]` is coprime to the exponent of `N`. Neither `G`, `[G : H]`, nor `N` need be
finite. -/
theorem map_subtype_quotientConjugation_injective_of_coprime_index_exponent (hNH : N ≤ H)
    (hcop : Nat.Coprime H.index (Monoid.exponent N)) (n : ℕ) :
    Function.Injective
      (groupCohomology.map (H.map (QuotientGroup.mk' N)).subtype
        (𝟙 (Rep.res (H.map (QuotientGroup.mk' N)).subtype
          (Rep.ofMulDistribMulAction (G ⧸ N) N))) n) := by
  refine TauCeti.groupCohomology.map_subtype_injective_of_coprime_index_exponent _ ?_ n
  rw [H.index_map_eq (QuotientGroup.mk'_surjective N) ((QuotientGroup.ker_mk' N).trans_le hNH)]
  -- The carrier of `Rep.ofMulDistribMulAction (G ⧸ N) N` is `Additive N`, whose additive exponent
  -- is `Monoid.exponent N` by `AddMonoid.exponent_additive`.
  exact hcop

/-- Restriction `Hⁿ(G ⧸ N, N) ⟶ Hⁿ(H.map (mk' N), N)` is injective in every degree `n` when
`N ≤ H` and `[G : H]` is coprime to `Nat.card N`. -/
theorem map_subtype_quotientConjugation_injective_of_coprime_index (hNH : N ≤ H)
    (hcop : Nat.Coprime H.index (Nat.card N)) (n : ℕ) :
    Function.Injective
      (groupCohomology.map (H.map (QuotientGroup.mk' N)).subtype
        (𝟙 (Rep.res (H.map (QuotientGroup.mk' N)).subtype
          (Rep.ofMulDistribMulAction (G ⧸ N) N))) n) :=
  map_subtype_quotientConjugation_injective_of_coprime_index_exponent hNH
    (hcop.coprime_dvd_right Group.exponent_dvd_nat_card) n

/-- **Cohomological Gaschütz vanishing (exponent form).** If `N` has a local complement in `H` and
`[G : H]` is coprime to `Monoid.exponent N`, then the class of the quotient extension of `G` by `N`
vanishes: `[G : H]` kills the class by `IsLocalComplement.index_nsmul_cohomologyClass_eq_zero`,
`Monoid.exponent N` kills it by `TauCeti.FactorSet.exponent_nsmul_cohomologyClass_eq_zero`, and
Bézout forces it to be zero. -/
theorem
    IsLocalComplement.cohomologyClass_factorSet_quotientExtension_eq_zero_of_coprime_index_exponent
    {K : Subgroup G} (hK : N.IsLocalComplement K H)
    (hcop : Nat.Coprime H.index (Monoid.exponent N))
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    (TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction).cohomologyClass =
      0 :=
  (nsmul_eq_zero_iff_of_coprime hcop).1
    ⟨hK.index_nsmul_cohomologyClass_eq_zero σ hσ,
      (TauCeti.GroupExtension.factorSet σ hσ
        N.quotientExtension_inducesAction).exponent_nsmul_cohomologyClass_eq_zero⟩

/-- **Cohomological Gaschütz vanishing (order form).** If `N` has a local complement in `H` and
`[G : H]` is coprime to `Nat.card N`, then the class of the quotient extension of `G` by `N`
vanishes. -/
theorem IsLocalComplement.cohomologyClass_factorSet_quotientExtension_eq_zero_of_coprime_index
    {K : Subgroup G} (hK : N.IsLocalComplement K H)
    (hcop : Nat.Coprime H.index (Nat.card N))
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    (TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction).cohomologyClass =
      0 :=
  hK.cohomologyClass_factorSet_quotientExtension_eq_zero_of_coprime_index_exponent
    (hcop.coprime_dvd_right Group.exponent_dvd_nat_card) σ hσ

/-- **Cohomological Gaschütz criterion (exponent form).** When `N ≤ H` and `[G : H]` is coprime to
`Monoid.exponent N`, the class of the quotient extension of `G` by `N` vanishes if and only if `N`
has a local complement in `H`. -/
theorem cohomologyClass_factorSet_quotientExtension_eq_zero_iff_of_coprime_index_exponent
    (hNH : N ≤ H) (hcop : Nat.Coprime H.index (Monoid.exponent N))
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    (TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction).cohomologyClass =
        0 ↔
      ∃ K : Subgroup G, N.IsLocalComplement K H :=
  ⟨fun h0 ↦ (map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff hNH σ hσ).1
      (by rw [h0, map_zero]),
    fun ⟨_, hK⟩ ↦
      hK.cohomologyClass_factorSet_quotientExtension_eq_zero_of_coprime_index_exponent hcop σ hσ⟩

/-- **Cohomological Gaschütz criterion (order form).** When `N ≤ H` and `[G : H]` is coprime to
`Nat.card N`, the class of the quotient extension of `G` by `N` vanishes if and only if `N` has a
local complement in `H`. Combined with `Subgroup.exists_complement_iff_cohomologyClass_eq_zero`,
this gives a cohomological proof of Gaschütz's splitting theorem independent of crossed transfer. -/
theorem cohomologyClass_factorSet_quotientExtension_eq_zero_iff_of_coprime_index
    (hNH : N ≤ H) (hcop : Nat.Coprime H.index (Nat.card N))
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    (TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction).cohomologyClass =
        0 ↔
      ∃ K : Subgroup G, N.IsLocalComplement K H :=
  cohomologyClass_factorSet_quotientExtension_eq_zero_iff_of_coprime_index_exponent hNH
    (hcop.coprime_dvd_right Group.exponent_dvd_nat_card) σ hσ

/-- **Gaschütz's splitting theorem for bounded-exponent kernels.** If `N` is an abelian normal
subgroup of `G` with a local complement in `H` and `[G : H]` is coprime to `Monoid.exponent N`,
then `N` has a complement in `G`. Unlike
`Subgroup.IsLocalComplement.exists_isComplement'_of_coprime_index`, `N` may be infinite of finite
exponent (such as an infinite elementary abelian `p`-group), where `Nat.card N = 0`. -/
theorem IsLocalComplement.exists_isComplement'_of_coprime_index_exponent {K : Subgroup G}
    (hK : N.IsLocalComplement K H) (hcop : Nat.Coprime H.index (Monoid.exponent N)) :
    ∃ D : Subgroup G, N.IsComplement' D := by
  let σ := TauCeti.GroupExtension.normalizeSection N.quotientExtension.surjInvRightHom
  have hσ : σ 1 = 1 := TauCeti.GroupExtension.normalizeSection_one _
  exact (N.exists_complement_iff_cohomologyClass_eq_zero σ hσ).2
    (hK.cohomologyClass_factorSet_quotientExtension_eq_zero_of_coprime_index_exponent hcop σ hσ)

/-- **Gaschütz's splitting criterion for bounded-exponent kernels.** When `N ≤ H` and `[G : H]` is
coprime to `Monoid.exponent N`, the abelian normal subgroup `N` has a complement in `G` if and only
if it has a local complement in `H`. -/
theorem exists_isComplement'_iff_exists_isLocalComplement_of_coprime_index_exponent (hNH : N ≤ H)
    (hcop : Nat.Coprime H.index (Monoid.exponent N)) :
    (∃ D : Subgroup G, N.IsComplement' D) ↔ ∃ K : Subgroup G, N.IsLocalComplement K H :=
  ⟨fun ⟨D, hD⟩ ↦ ⟨D ⊓ H, hD.isLocalComplement_inf hNH⟩,
    fun ⟨_, hK⟩ ↦ hK.exists_isComplement'_of_coprime_index_exponent hcop⟩

end Subgroup

namespace IsPGroup

open groupCohomology CategoryTheory Subgroup
open scoped IsMulCommutative

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal]
  [IsMulCommutative N] [N.FiniteIndex]

attribute [local instance] quotientConjugationAction

/-- **Sylow restriction injectivity for an abelian normal `p`-subgroup.** Let `N` be an abelian
normal `p`-subgroup of finite index in `G` (for instance, in any finite group `G`, or an infinite
`p`-subgroup such as a Prüfer `p`-group with finite quotient `G ⧸ N`), and let `P` be a Sylow
`p`-subgroup of `G`. Then restriction from `G ⧸ N` to the image of `P` is injective on
`Hⁿ(G ⧸ N, N)` in every degree `n`. -/
theorem map_subtype_quotientConjugation_sylow_injective (hN : IsPGroup p N) (P : Sylow p G)
    (n : ℕ) :
    Function.Injective
      (groupCohomology.map ((P : Subgroup G).map (QuotientGroup.mk' N)).subtype
        (𝟙 (Rep.res ((P : Subgroup G).map (QuotientGroup.mk' N)).subtype
          (Rep.ofMulDistribMulAction (G ⧸ N) N))) n) := by
  have : (P : Subgroup G).FiniteIndex :=
    Subgroup.finiteIndex_of_le (hN.le_sylow_of_normal P)
  let Q : Sylow p (G ⧸ N) :=
    (P.isPGroup.map (QuotientGroup.mk' N)).toSylow
      (P.not_dvd_index <| ·.trans <|
        (P : Subgroup G).index_map_dvd (QuotientGroup.mk'_surjective N))
  -- `Additive N` has the same `ℕ`-action as `N` has powers, so `IsPGroup p N` is definitionally
  -- `IsAddPGroup p` on the underlying module of `Rep.ofMulDistribMulAction (G ⧸ N) N`.
  have hA : IsAddPGroup p (Rep.ofMulDistribMulAction (G ⧸ N) N) := hN
  exact hA.map_sylow_injective Q n

/-- **Cohomological Sylow detection of complements.** For an abelian normal `p`-subgroup `N` of
finite index in `G` and a Sylow `p`-subgroup `P` of `G`, the class of the quotient extension of `G`
by `N` vanishes if and only if `N` has a local complement in `P`. Neither `G` nor `N` need be
finite. -/
theorem cohomologyClass_factorSet_quotientExtension_eq_zero_iff_sylow (hN : IsPGroup p N)
    (P : Sylow p G) (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    (TauCeti.GroupExtension.factorSet σ hσ N.quotientExtension_inducesAction).cohomologyClass =
        0 ↔
      ∃ K : Subgroup G, N.IsLocalComplement K P := by
  rw [← map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff
    (hN.le_sylow_of_normal P) σ hσ]
  exact (map_eq_zero_iff _ (hN.map_subtype_quotientConjugation_sylow_injective P 2)).symm

/-- **Sylow detection of complements for finite-index `p`-subgroups.** An abelian normal
`p`-subgroup `N` of finite index in `G` has a complement in `G` if and only if it has a local
complement in a Sylow `p`-subgroup `P`. Unlike `IsPGroup.exists_isComplement'_iff_sylow`,
finiteness of `N` is not assumed (covering, for instance, extensions of finite groups by Prüfer
`p`-groups); when `G` is finite, `[N.FiniteIndex]` is automatic and this gives a cohomological
proof of Sylow complement detection independent of crossed transfer. -/
theorem exists_isComplement'_iff_sylow_of_finiteIndex (hN : IsPGroup p N) (P : Sylow p G) :
    (∃ D : Subgroup G, N.IsComplement' D) ↔ ∃ K : Subgroup G, N.IsLocalComplement K P := by
  let σ := TauCeti.GroupExtension.normalizeSection N.quotientExtension.surjInvRightHom
  have hσ : σ 1 = 1 := TauCeti.GroupExtension.normalizeSection_one _
  exact (N.exists_complement_iff_cohomologyClass_eq_zero σ hσ).trans
    (hN.cohomologyClass_factorSet_quotientExtension_eq_zero_iff_sylow P σ hσ)

/-- **Sylow detection of complements for finite-index `p`-subgroups**, stated inside `P`: an
abelian normal `p`-subgroup `N` of finite index in `G` has a complement in `G` if and only if
`N.subgroupOf P` has a complement in the group `P`. -/
theorem exists_isComplement'_iff_sylow_subgroupOf_of_finiteIndex (hN : IsPGroup p N)
    (P : Sylow p G) :
    (∃ D : Subgroup G, N.IsComplement' D) ↔
      ∃ K : Subgroup P, (N.subgroupOf P).IsComplement' K :=
  (hN.exists_isComplement'_iff_sylow_of_finiteIndex P).trans
    (Subgroup.exists_isLocalComplement_iff_exists_isComplement'_subgroupOf
      (hN.le_sylow_of_normal P))

end IsPGroup
