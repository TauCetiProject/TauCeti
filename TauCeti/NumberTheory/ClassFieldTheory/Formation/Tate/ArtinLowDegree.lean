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

Together with the existing degree-zero formulas for restriction and corestriction, these are the
four edges of the two Artin--Tate tower squares. The remaining input for those squares is the
compatibility of cup product with the corresponding change-of-group maps.

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

private theorem rangeRestriction (T : LayerRestriction small big)
    (x : big.TrivialTateH (-2)) :
    (TensorProduct.rid ℤ (Additive (Abelianization T.galHom.range))).toAddEquiv
        (TauCeti.TateCohomology.HNegTwoAddEquivTensorOfIsTrivial
          (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))
          (TauCeti.TateCohomology.HNegTwoRes (Rep.trivial ℤ big.Gal ℤ)
            T.galHom.range x)) =
      (Abelianization.lift
        (Abelianization.of : T.galHom.range →* Abelianization T.galHom.range).transfer).toAdditive
        (big.tateHMinusTwoEquivAbelianization x) := by
  have h := TauCeti.TateCohomology.HNegTwoAddEquivTensorOfIsTrivial_HNegTwoRes
    T.galHom.range (Rep.trivial ℤ big.Gal ℤ) x
  rw [h, NormalLayer.tateHMinusTwoEquivAbelianization_apply,
    TauCeti.TateCohomology.HNegTwoAddEquivAbelianization_apply]
  generalize TauCeti.TateCohomology.HNegTwoAddEquivTensorOfIsTrivial
    (Rep.trivial ℤ big.Gal ℤ) x = t
  induction t using TensorProduct.inductionOn with
  | tmul y n => simp
  | add y z hy hz => simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hy hz

private theorem rangeComparison (T : LayerRestriction small big)
    (x : small.TrivialTateH (-2)) :
    (TensorProduct.rid ℤ (Additive (Abelianization T.galHom.range))).toAddEquiv
        (TauCeti.TateCohomology.HNegTwoAddEquivTensorOfIsTrivial
          (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ))
          ((T.trivialTateRangeIso (-2)).hom x)) =
      (Abelianization.map (MonoidHom.ofInjective T.galHom_injective)).toAdditive
        (small.tateHMinusTwoEquivAbelianization x) := by
  rw [TauCeti.TateCohomology.HNegTwoAddEquivTensorOfIsTrivial_apply]
  rw [T.isoGroupHomology_hom_trivialTateRangeIso_hom_neg_two_apply]
  let y : groupHomology.H1 (Rep.trivial ℤ small.Gal ℤ) :=
    (TateCohomology.isoGroupHomology (-2) 1 rfl).hom.app
      (Rep.trivial ℤ small.Gal ℤ) x
  change (TensorProduct.rid ℤ (Additive (Abelianization T.galHom.range))).toAddEquiv
    (groupHomology.H1AddEquivOfIsTrivial _
      (groupHomology.map _ T.trivialRangeRepHom 1 y)) = _
  rw [TauCeti.groupHomology.H1AddEquivOfIsTrivial_map]
  rw [NormalLayer.tateHMinusTwoEquivAbelianization_apply,
    TauCeti.TateCohomology.HNegTwoAddEquivAbelianization_apply,
    TauCeti.TateCohomology.HNegTwoAddEquivTensorOfIsTrivial_apply]
  generalize groupHomology.H1AddEquivOfIsTrivial (Rep.trivial ℤ small.Gal ℤ) y = t
  induction t using TensorProduct.inductionOn with
  | tmul y n =>
      rw [TensorProduct.map_tmul]
      change (TensorProduct.rid ℤ (Additive (Abelianization T.galHom.range)))
        (_ ⊗ₜ T.trivialRangeRepHom n) = _
      rw [T.trivialRangeRepHom_apply, TensorProduct.rid_tmul, TensorProduct.rid_tmul,
        map_zsmul]
      rfl
  | add y z hy hz => simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hy hz

private theorem ambientCorestriction (T : LayerRestriction small big)
    (x : tateCohomology
      (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ)) (-2)) :
    big.tateHMinusTwoEquivAbelianization
        (TauCeti.TateCohomology.HNegTwoCor
          (Rep.trivial ℤ big.Gal ℤ) T.galHom.range.subtype x) =
      (Abelianization.map T.galHom.range.subtype).toAdditive
        ((TensorProduct.rid ℤ (Additive (Abelianization T.galHom.range))).toAddEquiv
          (TauCeti.TateCohomology.HNegTwoAddEquivTensorOfIsTrivial
            (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ)) x)) := by
  rw [NormalLayer.tateHMinusTwoEquivAbelianization_apply,
    TauCeti.TateCohomology.HNegTwoAddEquivAbelianization_apply,
    TauCeti.TateCohomology.HNegTwoAddEquivTensorOfIsTrivial_HNegTwoCor]
  generalize TauCeti.TateCohomology.HNegTwoAddEquivTensorOfIsTrivial
    (Rep.res T.galHom.range.subtype (Rep.trivial ℤ big.Gal ℤ)) x = t
  induction t using TensorProduct.inductionOn with
  | tmul y n => simp
  | add y z hy hz => simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hy hz

/-- Restriction in Tate degree `-2`, read through the low-degree identifications of two layers,
is group-theoretic transfer on their abelianized Galois groups. -/
theorem tateHMinusTwoEquivAbelianization_trivialTateRes
    (T : LayerRestriction small big) (x : big.TrivialTateH (-2)) :
    small.tateHMinusTwoEquivAbelianization (T.trivialTateRes (-2) x) =
      T.transferHom (big.tateHMinusTwoEquivAbelianization x) := by
  rw [T.trivialTateRes_neg_two, ModuleCat.comp_apply]
  rw [T.transferHom_eq_rangeTransfer, AddMonoidHom.comp_apply]
  apply (MonoidHom.ofInjective T.galHom_injective).abelianizationCongr.toAdditive.injective
  have hc := rangeComparison T ((T.trivialTateRangeIso (-2)).inv
    (TauCeti.TateCohomology.HNegTwoRes (Rep.trivial ℤ big.Gal ℤ) T.galHom.range x))
  rw [Iso.inv_hom_id_apply] at hc
  have hr := rangeRestriction T x
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
  rw [T.trivialTateCor_neg_two, ModuleCat.comp_apply, ambientCorestriction,
    rangeComparison]
  rw [T.inclusionHom_apply, MonoidHom.toAdditive_apply_apply,
    MonoidHom.toAdditive_apply_apply, MonoidHom.toAdditive_apply_apply,
    toMul_ofMul, Abelianization.map_map_apply]
  congr 1

end TauCeti.ClassFieldTheory.LayerRestriction
