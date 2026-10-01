/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.GaloisMaps
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.Restriction
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Abelianization

/-!
# Low-degree functoriality for finite normal layers

The Artin map is obtained by reading Tate's isomorphism between degrees `-2` and `0` through two
canonical identifications. This file records how the degree `-2` identification behaves under a
restriction of finite normal layers. Restriction in degree `-2` is group-theoretic transfer, while
corestriction is induced by inclusion of Galois groups.

These formulas identify the change-of-group legs in the Artin--Tate squares comparing the Artin
maps of two layers: inclusion of ground levels against transfer, and the norm against inclusion
of Galois groups.

## Main results

* `LayerRestriction.tateHMinusTwoEquivAbelianization_trivialTateRes`: degree `-2` restriction is
  the transfer on abelianized Galois groups.
* `LayerRestriction.tateHMinusTwoEquivAbelianization_trivialTateCor`: degree `-2`
  corestriction is the inclusion on abelianized Galois groups.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, Section 4.
* J.-P. Serre, *Local Fields*, Chapter XI, Section 3.
-/

public noncomputable section

open CategoryTheory Rep

namespace TauCeti.ClassFieldTheory.LayerRestriction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {small big : NormalLayer G}

attribute [local instance] Subgroup.fintypeOfFinite Subgroup.fintypeQuotientOfFiniteIndex

/-- Restriction in Tate degree `-2`, read through the low-degree identifications of two layers,
is group-theoretic transfer on their abelianized Galois groups. -/
theorem tateHMinusTwoEquivAbelianization_trivialTateRes
    (T : LayerRestriction small big) (x : big.TrivialTateH (-2)) :
    small.tateHMinusTwoEquivAbelianization (T.trivialTateRes (-2) x) =
      T.transferHom (big.tateHMinusTwoEquivAbelianization x) := by
  rw [T.trivialTateRes_neg_two, ModuleCat.comp_apply]
  rw [T.transferHom_eq_map_comp_lift_transfer, AddMonoidHom.comp_apply]
  apply (MonoidHom.ofInjective T.galHom_injective).abelianizationCongr.toAdditive.injective
  have hc := T.trivialTateRangeIso_hom_neg_two_tateHMinusTwoEquivAbelianization
    ((T.trivialTateRangeIso (-2)).inv
    (TauCeti.TateCohomology.HNegTwoRes (Rep.trivial ℤ big.Gal ℤ) T.galHom.range x))
  rw [Iso.inv_hom_id_apply] at hc
  have hr := TauCeti.TateCohomology.HNegTwoAddEquivAbelianization_HNegTwoRes
    T.galHom.range x
  rw [← NormalLayer.tateHMinusTwoEquivAbelianization_apply] at hr
  calc
    _ = (TensorProduct.rid ℤ (Additive (Abelianization T.galHom.range))).toAddEquiv
        (TauCeti.TateCohomology.HNegTwoAddEquivTensorOfIsTrivial
          (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))
          (TauCeti.TateCohomology.HNegTwoRes (Rep.trivial ℤ big.Gal ℤ)
            T.galHom.range x)) := hc.symm
    _ = (Abelianization.lift
        (Abelianization.of : T.galHom.range →* Abelianization T.galHom.range).transfer).toAdditive
          (big.tateHMinusTwoEquivAbelianization x) := hr
    _ = _ := by
      let E := (MonoidHom.ofInjective T.galHom_injective).abelianizationCongr.toAdditive
      exact (E.apply_symm_apply _).symm

/-- Corestriction in Tate degree `-2`, read through the low-degree identifications of two layers,
is the map on abelianizations induced by inclusion of their Galois groups. -/
theorem tateHMinusTwoEquivAbelianization_trivialTateCor
    (T : LayerRestriction small big) (x : small.TrivialTateH (-2)) :
    big.tateHMinusTwoEquivAbelianization (T.trivialTateCor (-2) x) =
      T.inclusionHom (small.tateHMinusTwoEquivAbelianization x) := by
  rw [T.trivialTateCor_neg_two, ModuleCat.comp_apply,
    NormalLayer.tateHMinusTwoEquivAbelianization_apply,
    TauCeti.TateCohomology.HNegTwoAddEquivAbelianization_HNegTwoCor,
    T.trivialTateRangeIso_hom_neg_two_tateHMinusTwoEquivAbelianization]
  rw [T.inclusionHom_apply, MonoidHom.toAdditive_apply_apply,
    MonoidHom.toAdditive_apply_apply, MonoidHom.toAdditive_apply_apply,
    toMul_ofMul, Abelianization.map_map_apply]
  have h : T.galHom.range.subtype.comp
      (MonoidHom.ofInjective T.galHom_injective : small.Gal →* T.galHom.range) = T.galHom :=
    MonoidHom.ext fun _ ↦ MonoidHom.ofInjective_apply T.galHom_injective
  rw [h]

end TauCeti.ClassFieldTheory.LayerRestriction
