/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints

/-!
# The intrinsic weight-torus ideal of the type-D spin carrier

For `4 ≤ n`, the weights of the full spin module span the type-`Dₙ` character lattice, so
restriction of carrier coordinates to the rank-`n` weight torus is surjective, over `ℤ` and after
base change to any commutative ring. Its kernel therefore defines a closed split torus inside the
carrier, with quotient coordinate algebra canonically identified with the split-torus coordinate
algebra. This file identifies the points of that closed subgroup with the named spin
weight-torus points over every commutative value algebra and proves that its defining ideal is
the scalar extension of the integral torus ideal.

These are the closed-subgroup data of the torus in a pinning of the carrier. Neither maximality
of the torus nor an identification with the pinned simply connected type-`Dₙ` group is
asserted.

## Main declarations

* `TauCeti.TypeDSpinCarrier.weightTorusToBaseChangeCoordinateMap_surjective`: the transported
  weight-torus coordinate map is surjective over every commutative ring.
* `TauCeti.TypeDSpinCarrier.weightTorusDefiningIdeal`: the intrinsic ideal in the specialized
  carrier.
* `TauCeti.TypeDSpinCarrier.weightTorusCoordinateIso`: its quotient is the rank-`n` split
  torus.
* `TauCeti.TypeDSpinCarrier.map_quotientPointsSubgroup_weightTorusDefiningIdeal`: the torus
  points are exactly the named spin weight-torus points.
* `TauCeti.TypeDSpinCarrier.map_baseChangeHopfIdeal_weightTorusIntegralDefiningIdeal`:
  compatibility with scalar extension from the integral carrier, without a flatness assumption.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 3 and 17.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* The construction follows the type-`E₆` one in
  `TauCeti.Algebra.Lie.E6.Minuscule.WeightTorus`.
-/

public section

open CategoryTheory

namespace TauCeti.TypeDSpinCarrier

universe v w

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n)

/-! ## Surjectivity of the weight-torus coordinate maps -/

/-- The integral weight-torus coordinate map is surjective, because the spin weights span the
character lattice. -/
theorem weightTorusIntegralCoordinateMap_surjective :
    Function.Surjective (weightTorusIntegralCoordinateMap n hn).hom := by
  apply Function.Surjective.of_comp
    (g := (CommHopfAlgCat.mkQuotient
      (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) (definingIdeal n hn)).hom)
  have h := GeneralLinear.weightTorusCoordinateMap_surjective (R := ℤ) (basisWeight n)
    (span_range_basisWeight_eq_top n)
  rw [← mkQuotient_comp_weightTorusIntegralCoordinateMap] at h
  simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp] using h

/-- **The transported rank-`n` weight-torus coordinate map is surjective.** Thus the weight
torus remains a closed split torus in every specialized carrier. -/
theorem weightTorusToBaseChangeCoordinateMap_surjective (A : Type v) [CommRing A] :
    Function.Surjective (weightTorusToBaseChangeCoordinateMap n hn A).hom := by
  rw [← baseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap n hn A]
  exact (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv ℤ A
      (G := SplitTorus.characterGroup (Fin n))).surjective.comp
    ((CommHopfAlgCat.baseChangeMap_surjective (K := A) (weightTorusIntegralCoordinateMap n hn)
      (weightTorusIntegralCoordinateMap_surjective n hn)).comp
      (ConcreteCategory.bijective_of_isIso (baseChangeCoordinateIso n hn A).hom).2)

/-! ## The torus ideals -/

/-- The defining ideal of the weight torus in the integral spin carrier. -/
def weightTorusIntegralDefiningIdeal :
    HopfIdeal ℤ
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n))
        (definingIdeal n hn)) :=
  HopfIdeal.kerOfSurjective (weightTorusIntegralCoordinateMap n hn).hom
    (weightTorusIntegralCoordinateMap_surjective n hn)

/-- An integral carrier coordinate belongs to the torus ideal exactly when its restriction
vanishes. -/
@[simp↓]
theorem mem_weightTorusIntegralDefiningIdeal
    (x : CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n))
      (definingIdeal n hn)) :
    x ∈ weightTorusIntegralDefiningIdeal n hn ↔
      (weightTorusIntegralCoordinateMap n hn).hom x = 0 := by
  rw [weightTorusIntegralDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

variable (R : Type v) [CommRing R]

/-- The defining ideal of the weight torus inside the spin carrier specialized to `R`. -/
def weightTorusDefiningIdeal : HopfIdeal R (coordinateHopfAlgebra n hn R) :=
  HopfIdeal.kerOfSurjective (weightTorusToBaseChangeCoordinateMap n hn R).hom
    (weightTorusToBaseChangeCoordinateMap_surjective n hn R)

/-- A specialized carrier coordinate belongs to the torus ideal exactly when its restriction
vanishes. -/
@[simp↓]
theorem mem_weightTorusDefiningIdeal (x : coordinateHopfAlgebra n hn R) :
    x ∈ weightTorusDefiningIdeal n hn R ↔
      (weightTorusToBaseChangeCoordinateMap n hn R).hom x = 0 := by
  rw [weightTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

/-- The quotient by the weight-torus ideal is canonically its split-torus coordinate algebra. -/
def weightTorusCoordinateIso :
    FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra n hn R)
        (weightTorusDefiningIdeal n hn R) ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin n)) :=
  ObjectProperty.isoMk _ <|
    CommHopfAlgCat.Hom.quotientKerOfSurjectiveIso (weightTorusToBaseChangeCoordinateMap n hn R)
      (weightTorusToBaseChangeCoordinateMap_surjective n hn R)

/-- The quotient identification recovers the original restriction of coordinates to the torus. -/
@[simp]
theorem mkQuotient_comp_weightTorusCoordinateIso_hom :
    FiniteTypeCommHopfAlgCat.mkQuotient (finiteTypeCoordinateHopfAlgebra n hn R)
          (weightTorusDefiningIdeal n hn R) ≫ (weightTorusCoordinateIso n hn R).hom =
      ObjectProperty.homMk (weightTorusToBaseChangeCoordinateMap n hn R) :=
  ObjectProperty.hom_ext _ (CommHopfAlgCat.Hom.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _)

/-- The closed subgroup cut out by the weight-torus ideal is a split torus over any base ring. -/
theorem splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra n hn R)
        (weightTorusDefiningIdeal n hn R)) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  let e : Multiplicative (Fin n →₀ ℤ) ≃* Multiplicative (ULift.{v} (Fin n) →₀ ℤ) :=
    AddEquiv.toMultiplicative (Finsupp.domCongr Equiv.ulift.symm)
  let i : DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin n)) ≅
      DiagonalizableGroup.coordinateRing R
        (SplitTorus.characterGroup (ULift.{v} (Fin n))) :=
    ObjectProperty.isoMk _
      (_root_.CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv R R e))
  exact ⟨n, ⟨(weightTorusCoordinateIso n hn R ≪≫ i).symm⟩⟩

grind_pattern splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal =>
  weightTorusDefiningIdeal n hn R

/-! ## Points of the torus -/

/-- The points defined by the intrinsic torus ideal, read as carrier points, are exactly the
named spin weight-torus points. The value algebra need not be reduced or a field. -/
theorem map_quotientPointsSubgroup_weightTorusDefiningIdeal (B : CommAlgCat.{w} R) :
    (CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra n hn R)
        (weightTorusDefiningIdeal n hn R) B).map
        (baseChangePointsMulEquiv n hn R B).toMonoidHom =
      (weightTorusPoints n hn B).range := by
  rw [weightTorusDefiningIdeal,
    HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor]
  -- The range is a subgroup of the points-functor object, which is the points group only up to
  -- unfolding `HopfAlgebra.pointsFunctor`, so `MonoidHom.range_comp` does not match syntactically.
  -- Membership in the image is therefore unpacked elementwise.
  ext g
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨SplitTorus.pointsMulEquiv q,
      (baseChangePointsMulEquiv_mapPointsFunctor_weightTorusToBaseChangeCoordinateMap
        n hn R B q).symm⟩
  · rintro ⟨s, rfl⟩
    refine ⟨_, ⟨(SplitTorus.pointsMulEquiv (R := R) (A := B)).symm s, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom,
      baseChangePointsMulEquiv_mapPointsFunctor_weightTorusToBaseChangeCoordinateMap,
      MulEquiv.apply_symm_apply]

/-! ## Base change from the integral carrier -/

/-- The carrier's scalar-extension identification sends the scalar-extended integral torus
ideal to the intrinsic torus ideal over `R`. No flatness or reducedness is required. -/
@[simp↓]
theorem map_baseChangeHopfIdeal_weightTorusIntegralDefiningIdeal :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := R) (weightTorusIntegralDefiningIdeal n hn)).map
        (baseChangeCoordinateIso n hn R).inv.hom =
      weightTorusDefiningIdeal n hn R := by
  rw [weightTorusIntegralDefiningIdeal, weightTorusDefiningIdeal]
  refine CommHopfAlgCat.map_baseChangeHopfIdeal_kerOfSurjective
    (baseChangeCoordinateIso n hn R).symm
    (_root_.CommHopfAlgCat.isoMk
      (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv ℤ R
        (G := SplitTorus.characterGroup (Fin n))))
    (weightTorusIntegralCoordinateMap_surjective n hn)
    (weightTorusToBaseChangeCoordinateMap_surjective n hn R) ?_
  simpa only [Iso.symm_inv, _root_.CommHopfAlgCat.isoMk_hom] using
    baseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap n hn R

end

end TauCeti.TypeDSpinCarrier
