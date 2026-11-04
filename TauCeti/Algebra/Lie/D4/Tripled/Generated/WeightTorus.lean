/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.Generated.StandardComodule
public import TauCeti.Algebra.Lie.D4.Tripled.Generated.Positive.Basic
public import TauCeti.Algebra.Lie.D4.Tripled.Generated.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints

/-!
# The closed weight torus of the generated tripled D₄ carrier

The twenty-four weights of the tripled representation generate the full rank-four character
lattice. Restriction of coordinates to its weight torus is therefore surjective, and its kernel
defines a closed split torus in the subgroup generated over the ground ring. This torus lies in
the generated positive subgroup. Its points, viewed in `GL₂₄`, are exactly the named tripled
weight-torus matrices, including over nonreduced value algebras.

The torus ideal commutes with free scalar extension under the generated-carrier comparison.
These are closed-subgroup data for a pinning; maximality is not asserted. The generated subgroup
is not identified here with the specialization of the integral toral closure or with an
independently constructed pinned simply connected group.

## Main declarations

* `TauCeti.D4Tripled.Generated.weightTorusDefiningIdeal`: the intrinsic closed-torus ideal.
* `TauCeti.D4Tripled.Generated.weightTorusCoordinateIso`: its quotient is the rank-four split
  torus.
* `TauCeti.D4Tripled.Generated.map_quotientPointsSubgroup_weightTorusDefiningIdeal`: the
  matrix-valued points are precisely the named weight-torus matrices.
* `TauCeti.D4Tripled.Generated.map_baseChangeHopfIdeal_weightTorusDefiningIdeal`: compatibility
  with free scalar extension.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 3 and 17.
* The closed-torus and point-subgroup constructions follow
  `TauCeti.Algebra.Lie.E7.Minuscule.WeightTorus`, using the generated carrier's existing torus
  lift instead of the integral carrier's restriction map.
-/

public section

open CategoryTheory
open TauCeti.DynkinType

namespace TauCeti.D4Tripled

universe u v w

noncomputable section

variable (R : Type u) [CommRing R]

/-- Restriction to the weight torus is surjective on the generated carrier's coordinates. -/
theorem generatedWeightTorusCoordinateMap_surjective :
    Function.Surjective (generatedWeightTorusCoordinateMap R).hom := by
  apply Function.Surjective.of_comp (g := (generatedCoordinateMap R).hom)
  have hcomp := congrArg _root_.CommHopfAlgCat.Hom.hom
    (generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap R)
  rw [_root_.CommHopfAlgCat.hom_comp,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap] at hcomp
  rw [← BialgHom.coe_comp, hcomp, GeneralLinear.weightTorusCoordinateBialgHom_def]
  exact DiagonalizableGroup.surjective_diagonalCoordinateMap _ _
    (SplitTorus.closure_range_weightCharacter_eq_top _ span_range_d4TripledWeight_eq_top)

namespace Generated

/-- The defining Hopf ideal of the weight torus inside the generated tripled carrier. -/
def weightTorusDefiningIdeal : HopfIdeal R (generatedCoordinateHopfAlgebra R) :=
  HopfIdeal.kerOfSurjective (generatedWeightTorusCoordinateMap R).hom
    (generatedWeightTorusCoordinateMap_surjective R)

/-- A coordinate belongs to the torus ideal exactly when its restriction vanishes. -/
@[simp↓]
theorem mem_weightTorusDefiningIdeal {R : Type u} [CommRing R]
    {x : generatedCoordinateHopfAlgebra R} :
    x ∈ weightTorusDefiningIdeal R ↔ (generatedWeightTorusCoordinateMap R).hom x = 0 := by
  rw [weightTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

/-- The weight torus is contained in the generated positive subgroup, contravariantly on ideals. -/
theorem positive_definingIdeal_le_weightTorusDefiningIdeal :
    Positive.definingIdeal R ≤ weightTorusDefiningIdeal R := by
  intro x hx
  rw [mem_weightTorusDefiningIdeal]
  rw [generatedWeightTorusCoordinateMap_def]
  exact ((Positive.le_definingIdeal_iff R _).mp le_rfl).2 hx

/-- The quotient by the torus ideal is canonically the rank-four split-torus coordinate algebra. -/
def weightTorusCoordinateIso :
    FiniteTypeCommHopfAlgCat.quotient (generatedFiniteTypeCoordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R) ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 4)) :=
  ObjectProperty.isoMk _ <|
    CommHopfAlgCat.Hom.quotientKerOfSurjectiveIso (generatedWeightTorusCoordinateMap R)
      (generatedWeightTorusCoordinateMap_surjective R)

/-- The quotient identification recovers the original restriction to the weight torus. -/
@[simp]
theorem mkQuotient_comp_weightTorusCoordinateIso_hom :
    FiniteTypeCommHopfAlgCat.mkQuotient (generatedFiniteTypeCoordinateHopfAlgebra R)
          (weightTorusDefiningIdeal R) ≫ (weightTorusCoordinateIso R).hom =
      ObjectProperty.homMk (generatedWeightTorusCoordinateMap R) :=
  ObjectProperty.hom_ext _ (CommHopfAlgCat.Hom.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _)

/-- The closed subgroup defined by the weight-torus ideal is split over every base ring. -/
theorem splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient (generatedFiniteTypeCoordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R)) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  let e : Multiplicative (Fin 4 →₀ ℤ) ≃* Multiplicative (ULift.{u} (Fin 4) →₀ ℤ) :=
    AddEquiv.toMultiplicative (Finsupp.domCongr Equiv.ulift.symm)
  let i : DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 4)) ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (ULift.{u} (Fin 4))) :=
    ObjectProperty.isoMk _
      (_root_.CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv R R e))
  exact ⟨4, ⟨(weightTorusCoordinateIso R ≪≫ i).symm⟩⟩

/-- Torus points in the generated carrier map to the named tripled weight-torus matrices. -/
@[simp↓]
theorem pointsMulEquiv_mapPointsFunctor_generatedWeightTorusCoordinateMap
    (A : CommAlgCat.{v} R)
    (q : HopfAlgebra.points (R := R)
      (H := (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 4))).obj) A) :
    GeneralLinear.pointsMulEquiv 24
        ((CommHopfAlgCat.Hom.mapPointsFunctor (generatedCoordinateMap R)).app A
          ((CommHopfAlgCat.Hom.mapPointsFunctor (generatedWeightTorusCoordinateMap R)).app A q)) =
      (weightTorusPoints A (SplitTorus.pointsMulEquiv q) :
        Matrix.GeneralLinearGroup (Fin 24) A) := by
  have hcomp : (generatedWeightTorusCoordinateMap R).hom.comp (generatedCoordinateMap R).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) d4TripledWeight := by
    rw [← _root_.CommHopfAlgCat.hom_comp,
      generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  have hp := CommHopfAlgCat.Hom.mapPointsFunctor_app_apply
    (generatedCoordinateMap R ≫ generatedWeightTorusCoordinateMap R) A q
  simp only [_root_.CommHopfAlgCat.hom_comp, hcomp] at hp
  have he := (CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply
    (generatedCoordinateMap R) (generatedWeightTorusCoordinateMap R) A q).symm.trans hp
  apply Units.ext
  rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
  refine (congrArg (fun g ↦
    (GeneralLinear.pointsMulEquiv 24 g : Matrix (Fin 24) (Fin 24) A)) he).trans ?_
  rw [GeneralLinear.pointsMulEquiv_apply, GeneralLinear.weightTorusCoordinateBialgHom_def,
    DiagonalizableGroup.pointToGeneralLinear_comp_diagonalCoordinateMap]
  congr 1
  funext i
  exact congrArg (fun s : Aˣ ↦ (s : A))
    (SplitTorus.charOfPoint_weightCharacter q (d4TripledWeight i))

/-- The closed torus's points in `GL₂₄` are precisely the named weight-torus matrices, over
arbitrary commutative value algebras. -/
theorem map_quotientPointsSubgroup_weightTorusDefiningIdeal (A : CommAlgCat.{v} R) :
    (CommHopfAlgCat.quotientPointsSubgroup (generatedCoordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R) A).map
        ((GeneralLinear.pointsMulEquiv (R := R) 24).toMonoidHom.comp
          ((CommHopfAlgCat.Hom.mapPointsFunctor (generatedCoordinateMap R)).app A).hom) =
      ((weightTorusPoints A).range).map (points A).subtype := by
  rw [weightTorusDefiningIdeal,
    HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor]
  ext g
  simp only [Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨_, ⟨SplitTorus.pointsMulEquiv q, rfl⟩,
      (pointsMulEquiv_mapPointsFunctor_generatedWeightTorusCoordinateMap R A q).symm⟩
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    refine ⟨_, ⟨(SplitTorus.pointsMulEquiv (R := R) (A := A)).symm s, rfl⟩, ?_⟩
    -- The subgroup uses bundled monoid maps; the point equation uses categorical components.
    convert pointsMulEquiv_mapPointsFunctor_generatedWeightTorusCoordinateMap R A
      ((SplitTorus.pointsMulEquiv (R := R) (A := A)).symm s) using 1
    · rfl
    · rw [MulEquiv.apply_symm_apply]
      rfl

variable (K : Type max u w) [CommRing K] [Algebra R K] [Module.Free R K]

/-- Free scalar extension carries the intrinsic torus ideal to the intrinsic torus ideal of
the generated carrier over the extended base. -/
@[simp↓]
theorem map_baseChangeHopfIdeal_weightTorusDefiningIdeal :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (weightTorusDefiningIdeal R)).map
        (generatedCoordinateHopfAlgebraBaseChangeIso R K).hom.hom =
      weightTorusDefiningIdeal K := by
  rw [weightTorusDefiningIdeal, weightTorusDefiningIdeal]
  refine CommHopfAlgCat.map_baseChangeHopfIdeal_kerOfSurjective
    (generatedCoordinateHopfAlgebraBaseChangeIso R K)
    (generatorCoordinateAlgebraBaseChangeIso R K (.inr ()))
    (generatedWeightTorusCoordinateMap_surjective R)
    (generatedWeightTorusCoordinateMap_surjective K) ?_
  rw [Iso.inv_comp_eq]
  simpa only [generatedWeightTorusCoordinateMap_def] using
    baseChangeMap_generatedCoordinateLift_comp_generatorCoordinateAlgebraBaseChangeIso_hom
      R K (.inr ())

end Generated

end

end TauCeti.D4Tripled
