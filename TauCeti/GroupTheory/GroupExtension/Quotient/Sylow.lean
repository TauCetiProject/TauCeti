/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Quotient.Restriction
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Sylow

/-!
# Sylow restriction for the class of a quotient extension

Let `N` be an abelian normal `p`-subgroup of a group `G`, and let `P` be a Sylow `p`-subgroup of
`G` of finite index. The image of `P` in `G ⧸ N` is a Sylow `p`-subgroup of `G ⧸ N` of finite
index, and the underlying additive group of `N` is a `p`-group. Consequently restriction from
`G ⧸ N` to the image of `P` is injective on `Hⁿ(G ⧸ N, N)` in every degree
(`IsPGroup.map_subtype_quotientConjugationAction_injective`).

Combined with the restriction formula for the quotient extension (`Subgroup.subgroupOfCohomologyIso`
and `Subgroup.map_subtype_cohomologyClass_factorSet_quotientExtension`) and the containment `N ≤ P`
(`IsPGroup.le_sylow_of_normal`), the class of the quotient extension of `G` by `N` vanishes if and
only if the class of the quotient extension of `P` by `N.subgroupOf P` vanishes
(`IsPGroup.cohomologyClass_factorSet_quotientExtension_eq_zero_iff_sylow`), equivalently if and only
if `N` has a local complement in `P`
(`IsPGroup.cohomologyClass_factorSet_quotientExtension_eq_zero_iff_exists_isLocalComplement_sylow`).
Together with `Subgroup.exists_complement_iff_cohomologyClass_eq_zero`, this gives the cohomological
proof of Gaschütz's Sylow detection of complements (`IsPGroup.exists_isComplement'_iff_sylow`), and
applies without assuming `G` or `N` finite (only `[P.FiniteIndex]`).

## Main results

* `IsPGroup.map_subtype_quotientConjugationAction_injective`: restriction to the image of a
  finite-index Sylow `p`-subgroup `P` in `G ⧸ N` is injective on `Hⁿ(G ⧸ N, N)` in every degree.
* `IsPGroup.map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff`: the quotient
  extension class of `G` by `N` vanishes on the image of `P` if and only if it vanishes globally.
* `IsPGroup.cohomologyClass_factorSet_quotientExtension_eq_zero_iff_sylow`: the quotient extension
  class of `G` by `N` vanishes if and only if that of `P` by `N.subgroupOf P` vanishes.
* `IsPGroup.cohomologyClass_factorSet_quotientExtension_eq_zero_iff_exists_isLocalComplement_sylow`:
  the quotient extension class of `G` by `N` vanishes if and only if `N` has a local complement in
  `P`.

## References

* W. Gaschütz, *Zur Erweiterungstheorie der endlichen Gruppen*, J. reine angew. Math. 190
  (1952), 93–107, 2. Reduktionssatz.
* K. S. Brown, *Cohomology of Groups*, Chapter IV, §3 and Chapter III, §10.
-/

public section

open CategoryTheory
open scoped IsMulCommutative

namespace IsPGroup

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal]
  [IsMulCommutative N]

attribute [local instance] Subgroup.quotientConjugationAction

/-- **Restriction to the image of a finite-index Sylow `p`-subgroup is injective on
`Hⁿ(G ⧸ N, N)`**, in every degree `n`, for any abelian normal `p`-subgroup `N` of `G`. Neither `G`
nor `N` need be finite. -/
theorem map_subtype_quotientConjugationAction_injective (hN : IsPGroup p N)
    (P : Sylow p G) [(P : Subgroup G).FiniteIndex] (n : ℕ) :
    Function.Injective (groupCohomology.map ((P : Subgroup G).map (QuotientGroup.mk' N)).subtype
      (𝟙 (Rep.res ((P : Subgroup G).map (QuotientGroup.mk' N)).subtype
        (Rep.ofMulDistribMulAction (G ⧸ N) N))) n) := by
  let Q : Sylow p (G ⧸ N) :=
    (P.isPGroup.map (QuotientGroup.mk' N)).toSylow
      (P.not_dvd_index <| ·.trans <| P.index_map_dvd (QuotientGroup.mk'_surjective N))
  have hQ : (Q : Subgroup (G ⧸ N)) = (P : Subgroup G).map (QuotientGroup.mk' N) := rfl
  have : (Q : Subgroup (G ⧸ N)).FiniteIndex :=
    hQ ▸ Subgroup.FiniteIndex.map_of_surjective (P : Subgroup G) (QuotientGroup.mk'_surjective N)
  have hAdd : IsAddPGroup p (Rep.ofMulDistribMulAction (G ⧸ N) N) := fun x ↦ hN x.toMul
  exact TauCeti.groupCohomology.map_sylow_injective_of_isAddPGroup _ n hAdd Q

/-- For an abelian normal `p`-subgroup `N` of `G` and a finite-index Sylow `p`-subgroup `P`, the
quotient extension class of `G` by `N` vanishes on the image of `P` in `G ⧸ N` if and only if it
vanishes on `G ⧸ N`. Neither `G` nor `N` need be finite. -/
theorem map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff (hN : IsPGroup p N)
    (P : Sylow p G) [(P : Subgroup G).FiniteIndex]
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    groupCohomology.map ((P : Subgroup G).map (QuotientGroup.mk' N)).subtype (𝟙 _) 2
        (TauCeti.GroupExtension.factorSet σ hσ
          N.quotientExtension_inducesAction).cohomologyClass = 0 ↔
      (TauCeti.GroupExtension.factorSet σ hσ
        N.quotientExtension_inducesAction).cohomologyClass = 0 :=
  map_eq_zero_iff _ (hN.map_subtype_quotientConjugationAction_injective P 2)

/-- **Sylow detection of the quotient extension class** (Gaschütz). For an abelian normal
`p`-subgroup `N` of `G` and a finite-index Sylow `p`-subgroup `P`, the class of the quotient
extension of `G` by `N` vanishes if and only if the class of the quotient extension of `P` by
`N.subgroupOf P` vanishes. Neither `G` nor `N` need be finite. -/
theorem cohomologyClass_factorSet_quotientExtension_eq_zero_iff_sylow (hN : IsPGroup p N)
    (P : Sylow p G) [(P : Subgroup G).FiniteIndex]
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1)
    (τ : (N.subgroupOf P).quotientExtension.Section) (hτ : τ 1 = 1) :
    (TauCeti.GroupExtension.factorSet σ hσ
        N.quotientExtension_inducesAction).cohomologyClass = 0 ↔
      (TauCeti.GroupExtension.factorSet τ hτ
        (N.subgroupOf P).quotientExtension_inducesAction).cohomologyClass = 0 :=
  (hN.map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff P σ hσ).symm.trans
    (Subgroup.map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff
      (hN.le_sylow_of_normal P) σ hσ τ hτ)

/-- **Sylow local-complement criterion for the quotient extension class** (Gaschütz). For an
abelian normal `p`-subgroup `N` of `G` and a finite-index Sylow `p`-subgroup `P`, the class of the
quotient extension of `G` by `N` vanishes if and only if `N` has a local complement in `P`. Neither
`G` nor `N` need be finite. -/
theorem cohomologyClass_factorSet_quotientExtension_eq_zero_iff_exists_isLocalComplement_sylow
    (hN : IsPGroup p N) (P : Sylow p G) [(P : Subgroup G).FiniteIndex]
    (σ : N.quotientExtension.Section) (hσ : σ 1 = 1) :
    (TauCeti.GroupExtension.factorSet σ hσ
        N.quotientExtension_inducesAction).cohomologyClass = 0 ↔
      ∃ K : Subgroup G, N.IsLocalComplement K P :=
  (hN.map_subtype_cohomologyClass_factorSet_quotientExtension_eq_zero_iff P σ hσ).symm.trans
    (Subgroup.exists_isLocalComplement_iff_map_subtype_cohomologyClass_eq_zero
      (hN.le_sylow_of_normal P) σ hσ).symm

end IsPGroup
