/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.BaseChange
public import TauCeti.Algebra.Lie.D4.Tripled.MaximalTorus
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Maximal
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

/-!
# The intrinsic weight torus of the integral tripled D₄ carrier

Restriction to the four-dimensional weight torus is surjective on carrier coordinates.
Its kernel defines a closed split torus inside every specialization of the integral
tripled carrier. On points over every commutative value algebra, this closed subgroup is
exactly the diagonal intersection of the carrier with `GL₂₄`. The ideal is the scalar
extension of its integral counterpart, without a flatness or reducedness assumption.

These are intrinsic closed-subgroup data for a pinning of the integral toral closure.
They concern its specialization, not the subgroup generated anew over the coefficient ring.
No equality between those carriers, scheme-theoretic maximality, or identification with
an independently pinned simply connected group is asserted.

## Main declarations

* `TauCeti.D4Tripled.weightTorusDefiningIdeal`: the intrinsic torus ideal.
* `TauCeti.D4Tripled.weightTorusCoordinateIso`: the rank-four split quotient.
* `TauCeti.D4Tripled.mem_quotientPointsSubgroup_weightTorusDefiningIdeal_iff_isDiag`:
  the closed torus is precisely the diagonal intersection on all algebra-valued points.
* `TauCeti.D4Tripled.weightTorusDefiningIdeal_eq_map_diagonalTorusDefiningIdeal`:
  scheme-theoretic equality with the diagonal intersection.
* `TauCeti.D4Tripled.map_baseChangeHopfIdeal_weightTorusIntegralDefiningIdeal`:
  compatibility with specialization from the integral carrier.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 3 and 17.
* The kernel, quotient and specialization construction follows
  `TauCeti.Algebra.Lie.E7.Minuscule.WeightTorus`.
* The diagonal characterization uses the triality-product calculation in
  `TauCeti.Algebra.Lie.D4.Tripled.MaximalTorus`.
-/

public section

open CategoryTheory
open TauCeti.DynkinType

namespace TauCeti.D4Tripled

universe u v

noncomputable section

/-- Restriction to the integral weight torus is surjective on coordinates. -/
theorem weightTorusIntegralCoordinateMap_surjective :
    Function.Surjective weightTorusIntegralCoordinateMap.hom := by
  apply Function.Surjective.of_comp
    (g := (CommHopfAlgCat.mkQuotient
      (GeneralLinear.coordinateHopfAlgebra ℤ 24) definingIdeal).hom)
  have h := GeneralLinear.weightTorusCoordinateMap_surjective (R := ℤ) d4TripledWeight
    span_range_d4TripledWeight_eq_top
  rw [← mkQuotient_comp_weightTorusIntegralCoordinateMap] at h
  simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp] using h

/-- The defining Hopf ideal of the weight torus in the integral tripled carrier. -/
def weightTorusIntegralDefiningIdeal :
    HopfIdeal ℤ
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ 24) definingIdeal) :=
  HopfIdeal.kerOfSurjective weightTorusIntegralCoordinateMap.hom
    weightTorusIntegralCoordinateMap_surjective

/-- Integral coordinates vanish on the torus exactly when they belong to its ideal. -/
@[simp↓]
theorem mem_weightTorusIntegralDefiningIdeal
    (x : CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ 24) definingIdeal) :
    x ∈ weightTorusIntegralDefiningIdeal ↔ weightTorusIntegralCoordinateMap.hom x = 0 := by
  rw [weightTorusIntegralDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

variable (R : Type u) [CommRing R]

/-- Restriction to the weight torus remains surjective after arbitrary specialization. -/
theorem weightTorusToBaseChangeCoordinateMap_surjective :
    Function.Surjective (weightTorusToBaseChangeCoordinateMap R).hom := by
  rw [← baseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap R]
  exact _root_.CommHopfAlgCat.baseChangeMap_surjective_of_iso
    weightTorusIntegralCoordinateMap weightTorusIntegralCoordinateMap_surjective
    (baseChangeCoordinateIso R)
    (_root_.CommHopfAlgCat.isoMk
      (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv ℤ R
        (G := SplitTorus.characterGroup (Fin 4))))

/-- The defining ideal of the weight torus inside the specialized integral tripled carrier. -/
def weightTorusDefiningIdeal : HopfIdeal R (coordinateHopfAlgebra R) :=
  HopfIdeal.kerOfSurjective (weightTorusToBaseChangeCoordinateMap R).hom
    (weightTorusToBaseChangeCoordinateMap_surjective R)

/-- A specialized carrier coordinate belongs to the torus ideal exactly when it vanishes
under restriction to the torus. -/
@[simp↓]
theorem mem_weightTorusDefiningIdeal (x : coordinateHopfAlgebra R) :
    x ∈ weightTorusDefiningIdeal R ↔ (weightTorusToBaseChangeCoordinateMap R).hom x = 0 := by
  rw [weightTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

/-- The quotient by the torus ideal is canonically the rank-four split-torus coordinate algebra. -/
def weightTorusCoordinateIso :
    FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R) ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 4)) :=
  ObjectProperty.isoMk _ <|
    CommHopfAlgCat.Hom.quotientKerOfSurjectiveIso (weightTorusToBaseChangeCoordinateMap R)
      (weightTorusToBaseChangeCoordinateMap_surjective R)

/-- The quotient identification recovers the original restriction to the weight torus. -/
@[simp]
theorem mkQuotient_comp_weightTorusCoordinateIso_hom :
    FiniteTypeCommHopfAlgCat.mkQuotient (finiteTypeCoordinateHopfAlgebra R)
          (weightTorusDefiningIdeal R) ≫ (weightTorusCoordinateIso R).hom =
      ObjectProperty.homMk (weightTorusToBaseChangeCoordinateMap R) :=
  ObjectProperty.hom_ext _ (CommHopfAlgCat.Hom.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _)

/-- The intrinsic closed weight torus is split over every commutative base ring. -/
theorem splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R)) := by
  -- The split-torus predicate uses a character lattice in the coefficient-ring universe.
  let e := AddEquiv.toMultiplicative
    (Finsupp.domCongr (M := ℤ) (Equiv.ulift.symm : Fin 4 ≃ ULift.{u} (Fin 4)))
  let i : DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 4)) ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (ULift.{u} (Fin 4))) :=
    ObjectProperty.isoMk _ <| _root_.CommHopfAlgCat.isoMk
      (MonoidAlgebra.domCongrBialgEquiv R R e)
  exact (splitTorusCommHopfAlgProperty R).prop_of_iso
    (i.symm ≪≫ (weightTorusCoordinateIso R).symm)
    (SplitTorus.splitTorus_coordinateRing R (ULift.{u} (Fin 4)))

/-- On every commutative value algebra, the intrinsic torus points are the original tripled
weight-torus matrix points. -/
theorem map_quotientPointsSubgroup_weightTorusDefiningIdeal (A : CommAlgCat.{v} R) :
    (CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R) A).map
        (baseChangePointsMulEquiv R A).toMonoidHom =
      (weightTorusPoints A).range := by
  rw [weightTorusDefiningIdeal,
    HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor]
  ext g
  simp only [MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨SplitTorus.pointsMulEquiv q,
      (baseChangePointsMulEquiv_mapPointsFunctor_weightTorusToBaseChangeCoordinateMap R A q).symm⟩
  · rintro ⟨s, rfl⟩
    refine ⟨_, ⟨(SplitTorus.pointsMulEquiv (R := R) (A := A)).symm s, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom,
      baseChangePointsMulEquiv_mapPointsFunctor_weightTorusToBaseChangeCoordinateMap,
      MulEquiv.apply_symm_apply]

/-- A point of the specialized integral carrier lies in the intrinsic torus exactly when its
matrix is diagonal. This holds over nonreduced value algebras as well as fields. -/
@[simp↓]
theorem mem_quotientPointsSubgroup_weightTorusDefiningIdeal_iff_isDiag
    (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R) A) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R) A ↔
      (((baseChangePointsMulEquiv R A g : points A) :
        Matrix.GeneralLinearGroup (Fin 24) A) : Matrix (Fin 24) (Fin 24) A).IsDiag := by
  rw [← mem_range_weightTorusPoints_iff_isDiag,
    ← map_quotientPointsSubgroup_weightTorusDefiningIdeal R A, Subgroup.mem_map_equiv,
    MulEquiv.symm_apply_apply]

/-- The weight torus is the scheme-theoretic intersection of the integral carrier with the
full diagonal torus of `GL₂₄`, including over nonreduced coefficient rings. -/
theorem weightTorusDefiningIdeal_eq_map_diagonalTorusDefiningIdeal :
    weightTorusDefiningIdeal R =
      (GeneralLinear.diagonalTorusDefiningIdeal R 24).map (coordinateMap R).hom := by
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq
  intro A
  ext g
  rw [mem_quotientPointsSubgroup_weightTorusDefiningIdeal_iff_isDiag,
    CommHopfAlgCat.mem_quotientPointsSubgroup_map_iff,
    GeneralLinear.mem_quotientPointsSubgroup_diagonalTorusDefiningIdeal_iff,
    coe_baseChangePointsMulEquiv_apply, mapPointsFunctor_coordinateMap_app]

/-- The intrinsic torus ideal is the scalar extension of the integral torus ideal.
No flatness assumption on the coefficient ring is required. -/
@[simp↓]
theorem map_baseChangeHopfIdeal_weightTorusIntegralDefiningIdeal :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := R) weightTorusIntegralDefiningIdeal).map
        (baseChangeCoordinateIso R).inv.hom =
      weightTorusDefiningIdeal R := by
  rw [weightTorusIntegralDefiningIdeal, weightTorusDefiningIdeal]
  refine CommHopfAlgCat.map_baseChangeHopfIdeal_kerOfSurjective
    (baseChangeCoordinateIso R).symm
    (_root_.CommHopfAlgCat.isoMk
      (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv ℤ R
        (G := SplitTorus.characterGroup (Fin 4))))
    weightTorusIntegralCoordinateMap_surjective
    (weightTorusToBaseChangeCoordinateMap_surjective R) ?_
  simpa only [Iso.symm_inv, _root_.CommHopfAlgCat.isoMk_hom] using
    baseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap R

end

end TauCeti.D4Tripled
