/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.ClosedGenerators
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints

/-!
# The intrinsic weight-torus ideal of the E₇ minuscule carrier

Restriction of carrier coordinates to the rank-seven weight torus is surjective. Its kernel
therefore defines a closed split torus inside the carrier, with quotient coordinate algebra
canonically identified with the split-torus coordinate algebra. This file identifies its points
with the named minuscule weight-torus matrices over every commutative value algebra and proves
that its defining ideal is the scalar extension of the integral torus ideal.

These are the closed-subgroup data needed to choose a maximal torus and a pinning. Neither
maximality nor identification with the pinned simply connected type-E₇ group is asserted.

## Main declarations

* `TauCeti.E7Minuscule.weightTorusDefiningIdeal`: the intrinsic ideal in the specialized carrier.
* `TauCeti.E7Minuscule.weightTorusCoordinateIso`: its quotient is the rank-seven split torus.
* `TauCeti.E7Minuscule.map_quotientPointsSubgroup_weightTorusDefiningIdeal`: the torus points in
  the ambient general linear group are exactly the named weight-torus matrix points.
* `TauCeti.E7Minuscule.map_baseChangeHopfIdeal_weightTorusIntegralDefiningIdeal`: compatibility
  with scalar extension from the integral carrier, without a flatness assumption.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 3 and 17.
* The quotient and base-change constructions follow
  `TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.ClosedImmersion`; the point-subgroup
  identification follows `TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.MaximalTorus`.
-/

public section

open CategoryTheory
open TauCeti.DynkinType

namespace TauCeti.E7Minuscule

universe u v

noncomputable section

/-- The defining ideal of the weight torus in the integral minuscule carrier. -/
def weightTorusIntegralDefiningIdeal :
    HopfIdeal ℤ
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ 56) definingIdeal) :=
  HopfIdeal.kerOfSurjective weightTorusIntegralCoordinateMap.hom
    weightTorusIntegralCoordinateMap_surjective

/-- An integral carrier coordinate belongs to the torus ideal exactly when its restriction
vanishes. -/
@[simp↓]
theorem mem_weightTorusIntegralDefiningIdeal
    (x : CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ 56) definingIdeal) :
    x ∈ weightTorusIntegralDefiningIdeal ↔ weightTorusIntegralCoordinateMap.hom x = 0 := by
  rw [weightTorusIntegralDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

variable (R : Type u) [CommRing R]

/-- The defining ideal of the weight torus inside the minuscule carrier specialized to `R`. -/
def weightTorusDefiningIdeal : HopfIdeal R (coordinateHopfAlgebra R) :=
  HopfIdeal.kerOfSurjective (weightTorusToBaseChangeCoordinateMap R).hom
    (weightTorusToBaseChangeCoordinateMap_surjective R)

/-- A specialized carrier coordinate belongs to the torus ideal exactly when its restriction
vanishes. -/
@[simp↓]
theorem mem_weightTorusDefiningIdeal (x : coordinateHopfAlgebra R) :
    x ∈ weightTorusDefiningIdeal R ↔ (weightTorusToBaseChangeCoordinateMap R).hom x = 0 := by
  rw [weightTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

/-- The quotient by the weight-torus ideal is canonically its split-torus coordinate algebra. -/
def weightTorusCoordinateIso :
    FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R) ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 7)) :=
  ObjectProperty.isoMk _ <|
    CommHopfAlgCat.Hom.quotientKerOfSurjectiveIso (weightTorusToBaseChangeCoordinateMap R)
      (weightTorusToBaseChangeCoordinateMap_surjective R)

/-- The quotient identification recovers the original restriction of coordinates to the torus. -/
@[simp]
theorem mkQuotient_comp_weightTorusCoordinateIso_hom :
    FiniteTypeCommHopfAlgCat.mkQuotient (finiteTypeCoordinateHopfAlgebra R)
          (weightTorusDefiningIdeal R) ≫ (weightTorusCoordinateIso R).hom =
      ObjectProperty.homMk (weightTorusToBaseChangeCoordinateMap R) :=
  ObjectProperty.hom_ext _ (CommHopfAlgCat.Hom.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _)

/-- The closed subgroup cut out by the weight-torus ideal is a split torus over any base ring. -/
theorem splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R)) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  let e : Multiplicative (Fin 7 →₀ ℤ) ≃* Multiplicative (ULift.{u} (Fin 7) →₀ ℤ) :=
    AddEquiv.toMultiplicative (Finsupp.domCongr Equiv.ulift.symm)
  let i : DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 7)) ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (ULift.{u} (Fin 7))) :=
    ObjectProperty.isoMk _
      (_root_.CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv R R e))
  exact ⟨7, ⟨(weightTorusCoordinateIso R ≪≫ i).symm⟩⟩

grind_pattern splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal =>
  weightTorusDefiningIdeal R

/-- On all algebra-valued points, restriction to the torus followed by the carrier inclusion
is the named minuscule weight-torus matrix. -/
@[simp↓]
theorem pointsMulEquiv_mapPointsFunctor_weightTorusToBaseChangeCoordinateMap
    (A : CommAlgCat.{v} R)
    (q : HopfAlgebra.points (R := R)
      (H := (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 7))).obj) A) :
    GeneralLinear.pointsMulEquiv 56
        ((CommHopfAlgCat.Hom.mapPointsFunctor (coordinateMap R)).app A
          ((CommHopfAlgCat.Hom.mapPointsFunctor (weightTorusToBaseChangeCoordinateMap R)).app A
            q)) =
      (weightTorusPoints A (SplitTorus.pointsMulEquiv q) :
        Matrix.GeneralLinearGroup (Fin 56) A) := by
  -- The categorical weight-torus point formula requires the base ring and torus index in one
  -- universe. The direct bialgebra map allows arbitrary `R : Type u` with weights in `Fin 7`.
  have hcomp : (weightTorusToBaseChangeCoordinateMap R).hom.comp (coordinateMap R).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) e7MinusculeWeight := by
    rw [← _root_.CommHopfAlgCat.hom_comp,
      coordinateMap_comp_weightTorusToBaseChangeCoordinateMap,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  have hp := CommHopfAlgCat.Hom.mapPointsFunctor_app_apply
    (coordinateMap R ≫ weightTorusToBaseChangeCoordinateMap R) A q
  simp only [_root_.CommHopfAlgCat.hom_comp, hcomp] at hp
  have he := (CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply
    (coordinateMap R) (weightTorusToBaseChangeCoordinateMap R) A q).symm.trans hp
  apply Units.ext
  rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
  refine (congrArg (fun g ↦
    (GeneralLinear.pointsMulEquiv 56 g : Matrix (Fin 56) (Fin 56) A)) he).trans ?_
  rw [GeneralLinear.pointsMulEquiv_apply, GeneralLinear.weightTorusCoordinateBialgHom_def,
    DiagonalizableGroup.pointToGeneralLinear_comp_diagonalCoordinateMap]
  congr 1
  funext i
  exact congrArg (fun s : Aˣ ↦ (s : A))
    (SplitTorus.charOfPoint_weightCharacter q (e7MinusculeWeight i))

/-- The points defined by the intrinsic torus ideal, mapped into `GL₅₆`, are exactly the named
weight-torus matrix points. The value algebra need not be reduced or a field. -/
theorem map_quotientPointsSubgroup_weightTorusDefiningIdeal (A : CommAlgCat.{v} R) :
    (CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R) A).map
        ((GeneralLinear.pointsMulEquiv (R := R) 56).toMonoidHom.comp
          ((CommHopfAlgCat.Hom.mapPointsFunctor (coordinateMap R)).app A).hom) =
      ((weightTorusPoints A).range).map (points A).subtype := by
  rw [weightTorusDefiningIdeal,
    HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor]
  ext g
  simp only [Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨_, ⟨SplitTorus.pointsMulEquiv q, rfl⟩,
      (pointsMulEquiv_mapPointsFunctor_weightTorusToBaseChangeCoordinateMap R A q).symm⟩
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    refine ⟨_, ⟨(SplitTorus.pointsMulEquiv (R := R) (A := A)).symm s, rfl⟩, ?_⟩
    -- The image subgroup uses bundled monoid homomorphisms, whereas the point formula uses
    -- the categorical point maps. `convert` compares these presentations of the same maps.
    convert pointsMulEquiv_mapPointsFunctor_weightTorusToBaseChangeCoordinateMap R A
      ((SplitTorus.pointsMulEquiv (R := R) (A := A)).symm s) using 1
    · rfl
    · rw [MulEquiv.apply_symm_apply]
      rfl

/-- The carrier's scalar-extension identification sends the scalar-extended integral torus
ideal to the intrinsic torus ideal over `R`. No flatness or reducedness is required. -/
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
        (G := SplitTorus.characterGroup (Fin 7))))
    weightTorusIntegralCoordinateMap_surjective
    (weightTorusToBaseChangeCoordinateMap_surjective R) ?_
  simpa only [Iso.symm_inv, _root_.CommHopfAlgCat.isoMk_hom] using
    baseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap R

end

end TauCeti.E7Minuscule
