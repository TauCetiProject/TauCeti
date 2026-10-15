/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Pinning.Isomorphism
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Pinning.Basic
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Symplectic.RootSubgroup

/-!
# The pinning of the integral type-C carrier

The full-weight type-`C_(n+1)` Kostant carrier over `ℤ` has the same defining ideal in
`O(GL_(2n+2))` as the standard symplectic group `Sp_(2n+2)`. This file transports the standard
pinning of `Sp_(2n+2)` along the resulting isomorphism of coordinate Hopf algebras, which gives the
carrier a pinning over `ℤ`: a reductive group scheme structure, the paired diagonal torus, the
isotropic flag Borel subgroup, and a trivialization of each simple root space.

The simple roots keep their Bourbaki numbering, and the root vector at the simple root numbered
`i` is the differential of the carrier's own `i`th raising Kostant root subgroup at the unit
tangent vector of `𝔾ₐ` (`TauCeti.SpStd.pinning_rootVector`). So the trivializations of the simple
root spaces are those given by the explicit numbered root subgroups of the carrier. The torus of
the pinning is the paired diagonal torus of `Sp_(2n+2)`; on group schemes,
`TauCeti.SpStd.weightTorus_comp_symplecticIso_hom` identifies it with the weight torus of the
carrier after the integral change from fundamental-weight to classical torus coordinates.

## Main declarations

* `TauCeti.SpStd.coordinateSymplecticIso`: the coordinate Hopf algebra of the carrier is that of
  `Sp_(2n+2)` over `ℤ`.
* `TauCeti.SpStd.coordinateSymplecticIso_hom_comp_rootSubgroupCoordinateMap`: in coordinates,
  the numbered root subgroups of the carrier are the corresponding symplectic root subgroups.
* `TauCeti.SpStd.pinning`: the pinning of the carrier over `ℤ`.
* `TauCeti.SpStd.pinningSimpleRootEquiv`: Bourbaki numbering of its simple roots.
* `TauCeti.SpStd.pinning_rootVector`: its root vectors are the differentials of the numbered
  raising root subgroups.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §§3–4.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate III.
-/

public section

open CategoryTheory
open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.SpStd

variable (n : ℕ)

/-- The coordinate Hopf algebra of the integral full-weight type-`C_(n+1)` carrier is the
coordinate Hopf algebra of `Sp_(2n+2)` over `ℤ`: both are quotients of `O(GL_(2n+2))` by the same
Hopf ideal. -/
noncomputable def coordinateSymplecticIso :
    coordinateHopfAlgebra n ≅ Symplectic.coordinateHopfAlgebra ℤ (n + 1) :=
  eqToIso (congrArg (CommHopfAlgCat.quotient
    (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))))
      ((definingIdeal_def n).symm.trans (definingIdeal_eq_symplecticDefiningHopfIdeal n)))

/-- The carrier--symplectic coordinate isomorphism is compatible with the quotient maps from
`O(GL_(2n+2))`. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_coordinateSymplecticIso_hom :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1)))
          (kostantToralDefiningIdeal (rootGenerator n) (cartanGenerator n) (rep n)
            (lattice n).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
            (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n)) ≫
        (coordinateSymplecticIso n).hom =
      Symplectic.coordinateMap ℤ (n + 1) := by
  rw [Symplectic.coordinateMap_def]
  exact CommHopfAlgCat.mkQuotient_comp_eqToHom
    ((definingIdeal_def n).symm.trans (definingIdeal_eq_symplecticDefiningHopfIdeal n)).symm

/-- In coordinates, the carrier--symplectic isomorphism carries each standard symplectic root
subgroup to the numbered Kostant root subgroup of the carrier, parameter included. -/
@[reassoc (attr := simp)]
theorem coordinateSymplecticIso_hom_comp_rootSubgroupCoordinateMap
    (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    (coordinateSymplecticIso n).hom ≫
        Symplectic.rootSubgroupCoordinateMap (R := ℤ) (symplecticRootIndex n k) =
      kostantRootSubgroupToralCoordinateMap (rootGenerator n) (cartanGenerator n) (rep n)
        (lattice n).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
        (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) k := by
  apply CommHopfAlgCat.mkQuotient_hom_ext
  rw [mkQuotient_comp_coordinateSymplecticIso_hom_assoc,
    mkQuotient_comp_kostantRootSubgroupToralCoordinateMap,
    kostantRootSubgroupCoordinateMap_eq_comp_rootSubgroupCoordinateMap]

/-- The coordinate algebra of the carrier is smooth over `ℤ`. -/
instance instSmoothCoordinateHopfAlgebra : Algebra.Smooth ℤ (coordinateHopfAlgebra n) :=
  Algebra.Smooth.of_equiv
    (CommHopfAlgCat.ofIso (coordinateSymplecticIso n).symm).toAlgEquiv

/-- **The pinning of the integral full-weight type-`C_(n+1)` carrier**, transported from the
standard pinning of `Sp_(2n+2)` over `ℤ`. -/
noncomputable def pinning : Pinning ℤ (coordinateHopfAlgebra n) (n + 1) :=
  (Symplectic.standardPinning ℤ (n + 1)).comapOfIso (coordinateSymplecticIso n)

/-- The torus of the carrier pinning is the paired diagonal torus of `Sp_(2n+2)`, pulled back to
the carrier. -/
@[simp]
theorem pinning_torus :
    (pinning n).torus =
      (Symplectic.splitMaximalTorus ℤ (n + 1)).comapOfIso (coordinateSymplecticIso n) := by
  rw [pinning, Pinning.comapOfIso_torus, Symplectic.standardPinning_torus]

/-- The Borel subgroup of the carrier pinning is the isotropic flag stabilizer of `Sp_(2n+2)`,
pulled back to the carrier. -/
@[simp]
theorem pinning_borel :
    (pinning n).borel =
      (Symplectic.IsotropicFlag.definingHopfIdeal ℤ (n + 1)).comapOfSurjective
        (coordinateSymplecticIso n).hom.hom
        (ConcreteCategory.bijective_of_isIso (coordinateSymplecticIso n).hom).2 := by
  rw [pinning, Pinning.comapOfIso_borel, Symplectic.standardPinning_borel]

/-- The simple roots of the carrier pinning are those of the standard pinning of `Sp_(2n+2)`. -/
theorem isSimpleRoot_pinning_iff (α : ULift.{0} (Fin (n + 1)) →₀ ℤ) :
    (pinning n).torus.IsSimpleRoot (pinning n).borel α ↔
      (Symplectic.standardPinning ℤ (n + 1)).torus.IsSimpleRoot
        (Symplectic.standardPinning ℤ (n + 1)).borel α :=
  Pinning.isSimpleRoot_comapOfIso_iff _ _ α

/-- Bourbaki numbering of the simple roots of the carrier pinning. -/
noncomputable def pinningSimpleRootEquiv :
    Fin (n + 1) ≃ {α // (pinning n).torus.IsSimpleRoot (pinning n).borel α} :=
  (Symplectic.standardPinningSimpleRootEquiv (R := ℤ)).trans
    (Equiv.subtypeEquivRight fun α ↦ (isSimpleRoot_pinning_iff n α).symm)

/-- The simple root numbered `i` is the `i`th type-C simple root of the diagonal root datum. -/
@[simp]
theorem coe_pinningSimpleRootEquiv_apply (i : Fin (n + 1)) :
    (pinningSimpleRootEquiv n i : ULift.{0} (Fin (n + 1)) →₀ ℤ) =
      (Symplectic.diagonalRootDatum.{0} (n + 1)).root
        (Symplectic.diagonalSimpleRootIndex (n + 1) i) := by
  rw [pinningSimpleRootEquiv, Equiv.trans_apply, Equiv.subtypeEquivRight_apply_coe,
    Symplectic.standardPinningSimpleRootEquiv_apply]

/-- **The root vectors of the carrier pinning are the differentials of the numbered raising Kostant
root subgroups**, evaluated at the unit tangent vector of `𝔾ₐ`. -/
theorem pinning_rootVector (i : Fin (n + 1)) :
    (pinning n).rootVector (pinningSimpleRootEquiv n i) =
      (Derivation.cotangentLinearEquiv (B := ℤ)).symm
        (derivationComp (B := ℤ)
          (kostantRootSubgroupToralCoordinateMap (rootGenerator n) (cartanGenerator n) (rep n)
            (lattice n).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
            (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) (.inl i)).hom
          ((AdditiveGroup.gaTangentLinearEquiv (R := ℤ) (B := ℤ)).symm 1)) := by
  have hα : (⟨(pinningSimpleRootEquiv n i).val,
      (isSimpleRoot_pinning_iff n _).mp (pinningSimpleRootEquiv n i).property⟩ :
        {α // (Symplectic.standardPinning ℤ (n + 1)).torus.IsSimpleRoot
          (Symplectic.standardPinning ℤ (n + 1)).borel α}) =
      Symplectic.standardPinningSimpleRootEquiv i :=
    Subtype.ext (by
      rw [coe_pinningSimpleRootEquiv_apply, Symplectic.standardPinningSimpleRootEquiv_apply])
  -- The carrier pinning is the transported standard pinning of `Sp_(2n+2)`.
  refine (Pinning.comapOfIso_rootVector (Symplectic.standardPinning ℤ (n + 1))
    (coordinateSymplecticIso n) (pinningSimpleRootEquiv n i)).trans ?_
  refine (congrArg (fun α ↦ Derivation.dualCotangentMap (coordinateSymplecticIso n).hom.hom
    ((Symplectic.standardPinning ℤ (n + 1)).rootVector α)) hα).trans ?_
  refine (congrArg (Derivation.dualCotangentMap (coordinateSymplecticIso n).hom.hom)
    (Symplectic.standardPinning_rootVector i)).trans ?_
  refine (Derivation.dualCotangentMap_cotangentLinearEquiv_symm _ _).trans
    (congrArg (Derivation.cotangentLinearEquiv (B := ℤ)).symm ?_)
  -- The symplectic root vector is the differential of its root subgroup at the unit tangent.
  have hroot := Symplectic.derivationComp_rootSubgroup_eq_smul_rootVector (R := ℤ) (B := ℤ)
    (Symplectic.diagonalSimpleRootIndex (n + 1) i)
    ((AdditiveGroup.gaTangentLinearEquiv (R := ℤ) (B := ℤ)).symm 1)
  rw [LinearEquiv.apply_symm_apply] at hroot
  rw [← (hroot.trans (one_smul ℤ _))]
  -- In coordinates, the carrier's raising root subgroup is the symplectic simple root subgroup.
  have hmap := congrArg CommHopfAlgCat.Hom.hom
    (coordinateSymplecticIso_hom_comp_rootSubgroupCoordinateMap n (.inl i))
  rw [CommHopfAlgCat.hom_comp, symplecticRootIndex_inl] at hmap
  refine Eq.trans ?_ (congrArg (fun f ↦ derivationComp (B := ℤ) f
    ((AdditiveGroup.gaTangentLinearEquiv (R := ℤ) (B := ℤ)).symm 1)) hmap)
  rw [derivationComp_comp, LinearMap.comp_apply]

end TauCeti.SpStd
