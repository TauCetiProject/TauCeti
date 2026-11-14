/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Sylow
public import TauCeti.GroupTheory.Complement.Local
public import TauCeti.GroupTheory.QuotientGroup.KerEquiv
public import TauCeti.GroupTheory.GroupExtension.Quotient.Cohomology
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Corestriction
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Sylow

/-!
# Restricting the class of a quotient extension

Let `N` be an abelian normal subgroup of `G` and `N ≤ H`. The quotient `H ⧸ N` is the image of
`H` in `G ⧸ N`, and `N.subgroupOf H` is `N`. This file proves that these identifications induce an
isomorphism `Subgroup.subgroupOfGroupCohomologyIso` in every degree `n`, and that the class of the
quotient extension of `G` by `N` in `H²(G ⧸ N, N)` restricts, on the image of `H`, to the class of
the quotient extension of `H` by `N`. Consequently `N` has a local complement in `H` if and only if
that restricted class vanishes
(`Subgroup.exists_isLocalComplement_iff_map_subtype_cohomologyClass_eq_zero`).

Comparing this restriction with corestriction yields the cohomological proofs of Gaschütz's
splitting theorem and of Sylow complement detection:

* If `N` has a local complement in `H`, then `[G : H]` kills the class of the quotient extension
  of `G` (`Subgroup.IsLocalComplement.index_nsmul_cohomologyClass_eq_zero`). Since `|N|` also kills
  that class (`TauCeti.FactorSet.card_nsmul_cohomologyClass_eq_zero`), coprimality of `[G : H]` and
  `|N|` forces the class to vanish
  (`Subgroup.IsLocalComplement.cohomologyClass_factorSet_quotientExtension_eq_zero`). More
  generally, restriction to the image of `H` is injective in every degree when `[G : H]` is prime
  to `|N|` (`Subgroup.map_quotientGroupMk_injective_of_coprime_index`).
* If `N` is a `p`-subgroup (`IsPGroup p N`, not necessarily finite) and `P` is a Sylow
  `p`-subgroup of `G` of finite index, then the image of `P` in `G ⧸ N` is a Sylow `p`-subgroup of
  `G ⧸ N`, so restriction to it is injective in every degree
  (`IsPGroup.map_quotientGroupMk_sylow_injective`) and the quotient-extension class of `G`
  vanishes if and only if that of `P` does
  (`IsPGroup.cohomologyClass_factorSet_quotientExtension_eq_zero_iff_sylow`).

Combined with `Subgroup.exists_complement_iff_cohomologyClass_eq_zero`, these give self-contained
cohomological proofs of Gaschütz's splitting theorem and of Sylow complement detection for
`G : Type`, checked in the `example` declarations at the end of the file without importing
`TauCeti.GroupTheory.Complement.Gaschutz` or `TauCeti.GroupTheory.Complement.Sylow`.

## Main definitions

* `Subgroup.subgroupOfRepHom`: `N.subgroupOf H ≃ N` as a morphism of representations of the
  image of `H` in `G ⧸ N`.
* `Subgroup.subgroupOfGroupCohomologyIso`: the resulting isomorphism between
  `Hⁿ(H ⧸ N.subgroupOf H, N.subgroupOf H)` and `Hⁿ(H.map (QuotientGroup.mk' N), N)`.

## Main results

* `Subgroup.map_subtype_cohomologyClass_factorSet_quotientExtension`: the restriction formula,
  with `Subgroup.map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff` and
  `Subgroup.exists_isLocalComplement_iff_map_subtype_cohomologyClass_eq_zero` its vanishing
  criteria.
* `Subgroup.IsLocalComplement.index_nsmul_cohomologyClass_eq_zero`: a local complement in `H`
  forces `[G : H]` to kill the class of the quotient extension.
* `Subgroup.map_quotientGroupMk_injective_of_coprime_index`,
  `Subgroup.IsLocalComplement.cohomologyClass_factorSet_quotientExtension_eq_zero`, and
  `Subgroup.cohomologyClass_factorSet_quotientExtension_eq_zero_iff_of_coprime_index`: injectivity
  of restriction and vanishing of the extension class across an index prime to `|N|`.
* `IsPGroup.map_quotientGroupMk_sylow_injective` and
  `IsPGroup.cohomologyClass_factorSet_quotientExtension_eq_zero_iff_sylow`: injectivity of
  restriction and detection of the extension class on a finite-index Sylow `p`-subgroup.

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

/-- For `N ≤ H`, the group isomorphism `quotientSubgroupOfMulEquivMap N H` and the coefficient
isomorphism `N.subgroupOfEquivOfLe hNH` identify the cohomology of `H ⧸ N.subgroupOf H` on
`N.subgroupOf H` with the cohomology of the image of `H` in `G ⧸ N` on `N`, in every degree `n`. -/
noncomputable def subgroupOfGroupCohomologyIso (hNH : N ≤ H) (n : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction (H ⧸ N.subgroupOf H) (N.subgroupOf H)) n ≅
      groupCohomology (Rep.res (H.map (QuotientGroup.mk' N)).subtype
        (Rep.ofMulDistribMulAction (G ⧸ N) N)) n :=
  groupCohomology.mapIso (quotientSubgroupOfMulEquivMap N H)
    (N.subgroupOfEquivOfLe hNH).toAdditive.toIntLinearEquiv
    (fun y => LinearMap.ext fun (x : Additive (N.subgroupOf H)) =>
      congrArg Additive.ofMul (subgroupOfEquivOfLe_smul hNH y x.toMul))
    n

/-- The forward direction of `Subgroup.subgroupOfGroupCohomologyIso` is the map on cohomology
induced by `(quotientSubgroupOfMulEquivMap N H).symm` and `Subgroup.subgroupOfRepHom`. -/
@[simp]
theorem subgroupOfGroupCohomologyIso_hom (hNH : N ≤ H) (n : ℕ) :
    (subgroupOfGroupCohomologyIso hNH n).hom =
      groupCohomology.map (quotientSubgroupOfMulEquivMap N H).symm.toMonoidHom
        (subgroupOfRepHom hNH) n :=
  groupCohomology.map_congr rfl (LinearMap.ext fun _ => rfl) n

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

/-- Restricted to the image of `H ≥ N` in `G ⧸ N`, the class of the quotient extension of `G` by
`N` vanishes if and only if the class of the quotient extension of `H` by `N.subgroupOf H`
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
    ← subgroupOfGroupCohomologyIso_hom hNH 2]
  exact map_eq_zero_iff _ (subgroupOfGroupCohomologyIso hNH 2).toLinearEquiv.injective

/-- For `N ≤ H`, the abelian normal subgroup `N` has a local complement in `H` if and only if the
restriction of the quotient-extension class of `G` to the image of `H` in `G ⧸ N` vanishes. -/
theorem exists_isLocalComplement_iff_map_subtype_cohomologyClass_eq_zero (hNH : N ≤ H)
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    (∃ K : Subgroup G, N.IsLocalComplement K H) ↔
      groupCohomology.map (H.map (QuotientGroup.mk' N)).subtype (𝟙 _) 2
        (TauCeti.GroupExtension.factorSet σ hσ
          N.quotientExtension_inducesAction).cohomologyClass = 0 := by
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
  have hindex : (H.map (QuotientGroup.mk' N)).index = H.index :=
    H.index_map_eq (QuotientGroup.mk'_surjective N) ((QuotientGroup.ker_mk' N).trans_le hK.left_le)
  rw [← hindex]
  exact TauCeti.groupCohomology.index_nsmul_eq_zero_of_map_eq_zero _ <|
    (exists_isLocalComplement_iff_map_subtype_cohomologyClass_eq_zero hK.left_le σ hσ).1 ⟨K, hK⟩

/-- When `[G : H]` is prime to `|N|`, restriction
`Hⁿ(G ⧸ N, N) ⟶ Hⁿ(H.map (QuotientGroup.mk' N), N)` is injective in every degree `n`. -/
theorem map_quotientGroupMk_injective_of_coprime_index
    (hcop : Nat.Coprime H.index (Nat.card N)) (n : ℕ) :
    Function.Injective (groupCohomology.map (H.map (QuotientGroup.mk' N)).subtype
      (𝟙 (Rep.res (H.map (QuotientGroup.mk' N)).subtype
        (Rep.ofMulDistribMulAction (G ⧸ N) N))) n) := by
  have hcard : Nat.card (Rep.ofMulDistribMulAction (G ⧸ N) N) = Nat.card N :=
    Nat.card_congr Additive.toMul
  exact TauCeti.groupCohomology.map_subtype_injective_of_coprime_natCard _
    (hcard.symm ▸ hcop.of_dvd_left (H.index_map_dvd (QuotientGroup.mk'_surjective N))) n

/-- **Cohomological Gaschütz vanishing.** If an abelian normal subgroup `N` has a local complement
in a subgroup `H` whose index `[G : H]` is prime to `|N|`, then the class in `H²(G ⧸ N, N)` of the
quotient extension of `G` by `N` vanishes. -/
theorem IsLocalComplement.cohomologyClass_factorSet_quotientExtension_eq_zero {K : Subgroup G}
    (hK : N.IsLocalComplement K H) (hcop : Nat.Coprime H.index (Nat.card N))
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    (TauCeti.GroupExtension.factorSet σ hσ
      N.quotientExtension_inducesAction).cohomologyClass = 0 :=
  (nsmul_eq_zero_iff_of_coprime hcop).1
    ⟨hK.index_nsmul_cohomologyClass_eq_zero σ hσ,
      TauCeti.FactorSet.card_nsmul_cohomologyClass_eq_zero _⟩

/-- When `[G : H]` is prime to `|N|`, the class of the quotient extension of `G` by `N` vanishes
if and only if the class of the quotient extension of `H` by `N.subgroupOf H` vanishes. That
`N ≤ H` follows automatically from normality of `N` and coprimality of `[G : H]` with `|N|`. -/
theorem cohomologyClass_factorSet_quotientExtension_eq_zero_iff_of_coprime_index
    (hcop : Nat.Coprime H.index (Nat.card N))
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1)
    (τ : (N.subgroupOf H).quotientExtension.Section) (hτ : τ 1 = 1) :
    (TauCeti.GroupExtension.factorSet σ hσ
        N.quotientExtension_inducesAction).cohomologyClass = 0 ↔
      (TauCeti.GroupExtension.factorSet τ hτ
        (N.subgroupOf H).quotientExtension_inducesAction).cohomologyClass = 0 := by
  have hNH : N ≤ H := relIndex_eq_one.1 <| Nat.eq_one_of_dvd_coprimes hcop
    (relIndex_sup_of_le_normalizer (le_normalizer_of_normal (H := N)) ▸
      relIndex_dvd_index_of_le le_sup_left)
    (H.relIndex_dvd_card N)
  exact (map_eq_zero_iff _ (map_quotientGroupMk_injective_of_coprime_index hcop 2)).symm.trans
    (map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff hNH σ hσ τ hτ)

end Subgroup

namespace IsPGroup

open groupCohomology CategoryTheory
open scoped IsMulCommutative

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal]
  [IsMulCommutative N]

attribute [local instance] Subgroup.quotientConjugationAction

/-- For an abelian normal `p`-subgroup `N` of `G` (not necessarily finite) and a Sylow `p`-subgroup
`P` of finite index, restriction `Hⁿ(G ⧸ N, N) ⟶ Hⁿ(P.map (QuotientGroup.mk' N), N)` is injective
in every degree `n`. -/
theorem map_quotientGroupMk_sylow_injective (hN : IsPGroup p N) (P : Sylow p G) [P.FiniteIndex]
    (n : ℕ) :
    Function.Injective (groupCohomology.map ((P : Subgroup G).map (QuotientGroup.mk' N)).subtype
      (𝟙 (Rep.res ((P : Subgroup G).map (QuotientGroup.mk' N)).subtype
        (Rep.ofMulDistribMulAction (G ⧸ N) N))) n) := by
  let Pbar : Sylow p (G ⧸ N) := (P.isPGroup.map (QuotientGroup.mk' N)).toSylow
    (P.not_dvd_index <| ·.trans <| P.index_map_dvd (QuotientGroup.mk'_surjective N))
  have : Pbar.FiniteIndex :=
    Subgroup.FiniteIndex.map_of_surjective (P : Subgroup G) (QuotientGroup.mk'_surjective N)
  exact TauCeti.groupCohomology.map_sylow_injective_of_isAddPGroup
    (Rep.ofMulDistribMulAction (G ⧸ N) N) n p Pbar
    fun a ↦ let ⟨j, hj⟩ := hN a.toMul; ⟨j, congrArg Additive.ofMul hj⟩

/-- **Cohomological Sylow detection of the extension class.** For an abelian normal `p`-subgroup
`N` of `G` (not necessarily finite) and a Sylow `p`-subgroup `P` of finite index, the class of the
quotient extension of `G` by `N` vanishes if and only if the class of the quotient extension of `P`
by `N.subgroupOf P` vanishes. -/
theorem cohomologyClass_factorSet_quotientExtension_eq_zero_iff_sylow
    (hN : IsPGroup p N) (P : Sylow p G) [P.FiniteIndex]
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1)
    (τ : (N.subgroupOf P).quotientExtension.Section) (hτ : τ 1 = 1) :
    (TauCeti.GroupExtension.factorSet σ hσ
        N.quotientExtension_inducesAction).cohomologyClass = 0 ↔
      (TauCeti.GroupExtension.factorSet τ hτ
        (N.subgroupOf P).quotientExtension_inducesAction).cohomologyClass = 0 :=
  (map_eq_zero_iff _ (hN.map_quotientGroupMk_sylow_injective P 2)).symm.trans
    (Subgroup.map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff
      (hN.le_sylow_of_normal P) σ hσ τ hτ)

end IsPGroup

section CohomologicalSplittingExamples

open scoped IsMulCommutative

/-- Self-contained cohomological proof of Gaschütz's splitting theorem for `G : Type`, combining
`Subgroup.IsLocalComplement.cohomologyClass_factorSet_quotientExtension_eq_zero` with
`Subgroup.exists_complement_iff_cohomologyClass_eq_zero` without crossed transfers. -/
example {G : Type} [Group G] {N K H : Subgroup G} [N.Normal] [IsMulCommutative N]
    (hK : N.IsLocalComplement K H) (hcop : Nat.Coprime H.index (Nat.card N)) :
    ∃ D : Subgroup G, N.IsComplement' D := by
  let σ := TauCeti.GroupExtension.normalizeSection N.quotientExtension.surjInvRightHom
  have hσ : σ 1 = 1 := TauCeti.GroupExtension.normalizeSection_one _
  exact (N.exists_complement_iff_cohomologyClass_eq_zero σ hσ).2
    (hK.cohomologyClass_factorSet_quotientExtension_eq_zero hcop σ hσ)

/-- Self-contained cohomological proof of Sylow complement detection for `G : Type` (valid even for
infinite abelian normal `p`-subgroups `N`), combining
`IsPGroup.map_quotientGroupMk_sylow_injective`,
`Subgroup.exists_isLocalComplement_iff_map_subtype_cohomologyClass_eq_zero`, and
`Subgroup.exists_complement_iff_cohomologyClass_eq_zero`. -/
example {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal]
    [IsMulCommutative N] (hN : IsPGroup p N) (P : Sylow p G) [P.FiniteIndex] :
    (∃ D : Subgroup G, N.IsComplement' D) ↔ ∃ K : Subgroup G, N.IsLocalComplement K P := by
  let _ := N.quotientConjugationAction
  let σ := TauCeti.GroupExtension.normalizeSection N.quotientExtension.surjInvRightHom
  have hσ : σ 1 = 1 := TauCeti.GroupExtension.normalizeSection_one _
  exact (N.exists_complement_iff_cohomologyClass_eq_zero σ hσ).trans <|
    (map_eq_zero_iff _ (hN.map_quotientGroupMk_sylow_injective P 2)).symm.trans
      (Subgroup.exists_isLocalComplement_iff_map_subtype_cohomologyClass_eq_zero
        (hN.le_sylow_of_normal P) σ hσ).symm

end CohomologicalSplittingExamples
