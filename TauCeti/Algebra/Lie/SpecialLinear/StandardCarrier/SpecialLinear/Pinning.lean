/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Pinning.Isomorphism
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Pinning.Basic
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.SpecialLinear.Integral
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.UpperTriangular

/-!
# An integral pinning on the explicit type A carrier

Transport the standard special-linear pinning to the actual full-weight Kostant carrier over
`ℤ`. Its stored Borel pulls back to the existing integral upper-triangular carrier ideal, and
its stored root vectors are the differentials of the existing numbered Kostant root maps,
at additive parameter zero applied to tangent vector one.

The stored torus uses the classical determinant-one diagonal coordinates. No identification
with the fundamental-weight parametrization of the original carrier torus is asserted here.
-/

public section

open CategoryTheory

namespace TauCeti.SlStd

noncomputable section

attribute [local instance high] Algebra.toModule

variable (r : ℕ)

/-- The integral pinning on the full-weight type `A_r` Kostant carrier. -/
def pinning : Pinning ℤ (coordinateHopfAlgebra r) r :=
  (SpecialLinear.standardPinning ℤ r).comapOfIso (coordinateSpecialLinearIso r)

/-- The stored torus is the pullback of the determinant-one diagonal torus. -/
@[simp]
theorem pinning_torus :
    (pinning r).torus =
      (SpecialLinear.splitMaximalTorus ℤ r).comapOfIso (coordinateSpecialLinearIso r) := by
  rw [pinning, Pinning.comapOfIso_torus, SpecialLinear.standardPinning_torus]

/-- The coordinate map of the actual stored torus is restriction through the integral comparison. -/
theorem pinning_torus_coordinateMap :
    (pinning r).torus.coordinateMap = (coordinateSpecialLinearIso r).hom ≫
      (SpecialLinear.splitMaximalTorus ℤ r).coordinateMap := by
  rw [pinning_torus, SplitMaximalTorus.comapOfIso_coordinateMap]

/-- The stored Borel is the inverse image of the standard special-linear upper-triangular ideal. -/
@[simp]
theorem pinning_borel :
    (pinning r).borel =
      (SpecialLinear.UpperTriangular.definingHopfIdeal ℤ (r + 1)).comapOfSurjective
        (coordinateSpecialLinearIso r).hom.hom
        (ConcreteCategory.bijective_of_isIso (coordinateSpecialLinearIso r).hom).2 := by
  rw [pinning, Pinning.comapOfIso_borel, SpecialLinear.standardPinning_borel]

/-- In the ambient general-linear algebra, the stored Borel has exactly the pre-existing
integral upper-triangular carrier equations. -/
theorem comap_pinning_borel :
    (pinning r).borel.comapOfSurjective
        (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
          (definingIdeal r)).hom (CommHopfAlgCat.mkQuotient_surjective _ _) =
      upperTriangularDefiningIdeal r := by
  have hpre : (pinning r).borel.comapOfSurjective
        (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
          (definingIdeal r)).hom (CommHopfAlgCat.mkQuotient_surjective _ _) =
      (SpecialLinear.UpperTriangular.definingHopfIdeal ℤ (r + 1)).comapOfSurjective
        (SpecialLinear.coordinateMap ℤ (r + 1)).hom
        (CommHopfAlgCat.mkQuotient_surjective _ _) := by
    have hcomp : (coordinateSpecialLinearIso r).hom.hom.comp
        (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
          (definingIdeal r)).hom = (SpecialLinear.coordinateMap ℤ (r + 1)).hom := by
      simpa only [CommHopfAlgCat.hom_comp] using
        congrArg CommHopfAlgCat.Hom.hom (mkQuotient_comp_coordinateSpecialLinearIso_hom r)
    simp only [pinning_borel, HopfIdeal.comapOfSurjective_comapOfSurjective, hcomp]
  have hker : HopfIdeal.kerOfSurjective (SpecialLinear.coordinateMap ℤ (r + 1)).hom
      (CommHopfAlgCat.mkQuotient_surjective _ _) =
        SpecialLinear.definingHopfIdeal ℤ (r + 1) :=
    HopfIdeal.kerOfSurjective_mkBialgHom _
  rw [hpre, SpecialLinear.UpperTriangular.definingHopfIdeal_def,
    HopfIdeal.comapOfSurjective_map, hker, upperTriangularDefiningIdeal_def,
    definingIdeal_eq_specialLinearDefiningHopfIdeal, sup_comm]

/-- Bourbaki numbering of the intrinsic simple roots of the actual carrier pinning. -/
def pinningSimpleRootEquiv :
    Fin r ≃ {α // (pinning r).torus.IsSimpleRoot (pinning r).borel α} :=
  (SpecialLinear.standardPinningSimpleRootEquiv (R := ℤ)).trans
    (Equiv.subtypeEquivRight fun α ↦
      ((SpecialLinear.standardPinning ℤ r).isSimpleRoot_comapOfIso_iff
        (coordinateSpecialLinearIso r) α).symm)

/-- The numbered simple root retains its consecutive-difference character. -/
@[simp]
theorem pinningSimpleRootEquiv_apply (i : Fin r) :
    (pinningSimpleRootEquiv r i).val =
      (SpecialLinear.diagonalRootDatum r).root (SpecialLinear.diagonalSimpleRootIndex r i) :=
  SpecialLinear.standardPinningSimpleRootEquiv_apply i

private theorem pinning_rootVector_transport (i : Fin r) :
    (pinning r).rootVector (pinningSimpleRootEquiv r i) =
      Derivation.dualCotangentMap (coordinateSpecialLinearIso r).hom.hom
        (SpecialLinear.rootVector (R := ℤ) (SpecialLinear.diagonalSimpleRootIndex r i)) := by
  calc
    _ = Derivation.dualCotangentMap (coordinateSpecialLinearIso r).hom.hom
        ((SpecialLinear.standardPinning ℤ r).rootVector
          (SpecialLinear.standardPinningSimpleRootEquiv (R := ℤ) i)) :=
      Pinning.comapOfIso_rootVector _ _ _
    _ = _ := by rw [SpecialLinear.standardPinning_rootVector]

private theorem pinning_rootVector_pair (i : Fin r) :
    (pinning r).rootVector (pinningSimpleRootEquiv r i) =
      (Derivation.cotangentLinearEquiv (R := ℤ) (A := coordinateHopfAlgebra r) (B := ℤ)).symm
        (derivationComp (B := ℤ)
          (rootSubgroupCoordinateMapOfPair r (rootTarget_ne_rootSource r (Sum.inl i))).hom
          ((AdditiveGroup.gaTangentLinearEquiv (R := ℤ) (B := ℤ)).symm 1)) := by
  let δ := (AdditiveGroup.gaTangentLinearEquiv (R := ℤ) (B := ℤ)).symm 1
  let p := SpecialLinear.diagonalSimpleRootIndex r i
  have hs : (Derivation.cotangentLinearEquiv (R := ℤ)
        (A := SpecialLinear.coordinateHopfAlgebra ℤ (r + 1)) (B := ℤ)).symm
        (derivationComp (B := ℤ) (SpecialLinear.rootSubgroupCoordinateMap p.2).hom δ) =
      SpecialLinear.rootVector (R := ℤ) p := by
    simpa only [δ, LinearEquiv.apply_symm_apply, one_smul] using
      SpecialLinear.cotangentLinearEquiv_symm_derivationComp_rootSubgroup p δ
  rw [pinning_rootVector_transport, ← hs, Derivation.dualCotangentMap_cotangentLinearEquiv_symm,
    ← LinearMap.comp_apply, ← derivationComp_comp, ← CommHopfAlgCat.hom_comp,
    coordinateSpecialLinearIso_hom_comp_rootSubgroupCoordinateMap]
  simp only [p, δ, SpecialLinear.diagonalSimpleRootIndex_fst,
    SpecialLinear.diagonalSimpleRootIndex_snd, rootTarget_inl, rootSource_inl]

/-- The stored root vector is the differential at additive parameter zero of the existing
positive Kostant root map, applied to tangent vector one. -/
theorem pinning_rootVector (i : Fin r) :
    (pinning r).rootVector (pinningSimpleRootEquiv r i) =
      (Derivation.cotangentLinearEquiv (R := ℤ) (A := coordinateHopfAlgebra r) (B := ℤ)).symm
        (derivationComp (B := ℤ)
          (UniversalEnvelopingAlgebra.kostantRootSubgroupToralCoordinateMap
            (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
            (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
            (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) (Sum.inl i) :
            coordinateHopfAlgebra r ⟶ AdditiveGroup.coordinateHopfAlgebra ℤ).hom
          ((AdditiveGroup.gaTangentLinearEquiv (R := ℤ) (B := ℤ)).symm 1)) := by
  rw [pinning_rootVector_pair]
  exact congrArg (fun f : coordinateHopfAlgebra r ⟶ AdditiveGroup.coordinateHopfAlgebra ℤ ↦
    (Derivation.cotangentLinearEquiv (R := ℤ) (A := coordinateHopfAlgebra r) (B := ℤ)).symm
      (derivationComp (B := ℤ) f.hom
        ((AdditiveGroup.gaTangentLinearEquiv (R := ℤ) (B := ℤ)).symm 1)))
    (rootSubgroupCoordinateMapOfPair_eq_rootSubgroupCoordinateMap r (Sum.inl i))

end

end TauCeti.SlStd
