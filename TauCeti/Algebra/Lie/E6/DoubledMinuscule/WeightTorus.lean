/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import TauCeti.Algebra.Lie.E6.DoubledMinuscule.MaximalTorus
import TauCeti.Algebra.Lie.E6.DoubledMinuscule.PointsFunctor
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints

/-!
# The intrinsic diagonal torus of the doubled E₆ carrier

The weights of `V(ϖ₁) ⊕ V(ϖ₆)` span the full type-`E₆` character lattice. Restriction of
coordinates to its rank-six weight torus is therefore surjective, integrally and after
specialization to any commutative ring. Its kernel defines a closed split torus inside the
specialized integral carrier, with quotient identified by `weightTorusCoordinateIso`.

`map_quotientPointsSubgroup_weightTorusDefiningIdeal` identifies this closed subgroup's
algebra-valued points with the named weight-torus matrices.
`mem_quotientPointsSubgroup_weightTorusDefiningIdeal_iff_isDiag` identifies them exactly with
the diagonal carrier matrices, using the carrier's invariant cross product. These statements
allow nonreduced value algebras and small characteristics.
`map_baseChangeHopfIdeal_weightTorusIntegralDefiningIdeal` shows that this intrinsic ideal is
the specialization of the integral torus ideal, without flatness assumptions.

This concerns the specialization of the integral toral closure, not the potentially smaller
subgroup generated after specialization. Neither schematic torus maximality nor reductivity
is asserted here.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 3 and 17.
* The coordinate construction follows
  `TauCeti.Algebra.Lie.E6.Minuscule.WeightTorus`.
* The diagonal-point characterization uses
  `TauCeti.E6DoubledMinuscule.mem_range_weightTorusPoints_iff_isDiag`.
-/

public section

open CategoryTheory

namespace TauCeti.E6DoubledMinuscule

universe u v

noncomputable section

/-- The integral weight-torus restriction is surjective because the doubled minuscule weights
span the full character lattice. -/
theorem weightTorusIntegralCoordinateMap_surjective :
    Function.Surjective weightTorusIntegralCoordinateMap.hom := by
  apply Function.Surjective.of_comp
    (g := (CommHopfAlgCat.mkQuotient
      (GeneralLinear.coordinateHopfAlgebra ℤ 54) definingIdeal).hom)
  have h := GeneralLinear.weightTorusCoordinateMap_surjective (R := ℤ) matrixWeight
    span_range_matrixWeight_eq_top
  rw [← mkQuotient_comp_weightTorusIntegralCoordinateMap] at h
  simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp] using h

/-- The weight-torus restriction remains surjective after specialization to any commutative
ring, so the torus remains a closed subgroup. -/
theorem weightTorusToBaseChangeCoordinateMap_surjective (A : Type u) [CommRing A] :
    Function.Surjective (weightTorusToBaseChangeCoordinateMap A).hom := by
  rw [← baseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap A]
  exact (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv ℤ A
      (G := SplitTorus.characterGroup (Fin 6))).surjective.comp
    ((CommHopfAlgCat.baseChangeMap_surjective (K := A) weightTorusIntegralCoordinateMap
      weightTorusIntegralCoordinateMap_surjective).comp
      (ConcreteCategory.bijective_of_isIso (baseChangeCoordinateIso A).hom).2)

/-- The intrinsic defining ideal of the rank-six weight torus in the integral doubled E₆
carrier. -/
def weightTorusIntegralDefiningIdeal :
    HopfIdeal ℤ
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ 54) definingIdeal) :=
  HopfIdeal.kerOfSurjective weightTorusIntegralCoordinateMap.hom
    weightTorusIntegralCoordinateMap_surjective

/-- An integral coordinate belongs to the torus ideal exactly when its restriction vanishes. -/
@[simp↓]
theorem mem_weightTorusIntegralDefiningIdeal
    (x : CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ 54) definingIdeal) :
    x ∈ weightTorusIntegralDefiningIdeal ↔ weightTorusIntegralCoordinateMap.hom x = 0 := by
  rw [weightTorusIntegralDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

variable (R : Type u) [CommRing R]

/-- The intrinsic defining ideal of the weight torus in the specialized integral doubled E₆
carrier. -/
def weightTorusDefiningIdeal : HopfIdeal R (coordinateHopfAlgebra R) :=
  HopfIdeal.kerOfSurjective (weightTorusToBaseChangeCoordinateMap R).hom
    (weightTorusToBaseChangeCoordinateMap_surjective R)

/-- A specialized coordinate belongs to the torus ideal exactly when its restriction vanishes. -/
@[simp↓]
theorem mem_weightTorusDefiningIdeal (x : coordinateHopfAlgebra R) :
    x ∈ weightTorusDefiningIdeal R ↔ (weightTorusToBaseChangeCoordinateMap R).hom x = 0 := by
  rw [weightTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

/-- The quotient by the intrinsic torus ideal is the rank-six split-torus coordinate algebra. -/
def weightTorusCoordinateIso :
    FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R) ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 6)) :=
  ObjectProperty.isoMk _ <|
    CommHopfAlgCat.Hom.quotientKerOfSurjectiveIso (weightTorusToBaseChangeCoordinateMap R)
      (weightTorusToBaseChangeCoordinateMap_surjective R)

/-- The quotient identification recovers restriction of coordinates to the weight torus. -/
@[simp]
theorem mkQuotient_comp_weightTorusCoordinateIso_hom :
    FiniteTypeCommHopfAlgCat.mkQuotient (finiteTypeCoordinateHopfAlgebra R)
          (weightTorusDefiningIdeal R) ≫ (weightTorusCoordinateIso R).hom =
      ObjectProperty.homMk (weightTorusToBaseChangeCoordinateMap R) :=
  ObjectProperty.hom_ext _ (CommHopfAlgCat.Hom.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _)

/-- The intrinsic weight-torus ideal cuts out a split torus over every commutative base ring. -/
theorem splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R)) := by
  rw [splitTorusCommHopfAlgProperty_iff]
  let e : Multiplicative (Fin 6 →₀ ℤ) ≃* Multiplicative (ULift.{u} (Fin 6) →₀ ℤ) :=
    AddEquiv.toMultiplicative (Finsupp.domCongr Equiv.ulift.symm)
  let i : DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 6)) ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (ULift.{u} (Fin 6))) :=
    ObjectProperty.isoMk _
      (_root_.CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv R R e))
  exact ⟨6, ⟨(weightTorusCoordinateIso R ≪≫ i).symm⟩⟩

grind_pattern splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal =>
  weightTorusDefiningIdeal R

/-- The torus inclusion, followed by the carrier inclusion into `GL₅₄`, evaluates to the named
weight-torus matrix over every commutative value algebra. -/
@[simp↓]
theorem pointsMulEquiv_mapPointsFunctor_weightTorusToBaseChangeCoordinateMap
    (A : CommAlgCat.{v} R)
    (q : HopfAlgebra.points (R := R)
      (H := (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin 6))).obj) A) :
    GeneralLinear.pointsMulEquiv 54
        ((CommHopfAlgCat.Hom.mapPointsFunctor (coordinateMap R)).app A
          ((CommHopfAlgCat.Hom.mapPointsFunctor (weightTorusToBaseChangeCoordinateMap R)).app A
            q)) =
      (weightTorusPoints A (SplitTorus.pointsMulEquiv q) :
        Matrix.GeneralLinearGroup (Fin 54) A) := by
  -- The bialgebra-level formula avoids imposing the base ring's universe on `Fin 6`.
  have hcomp : (weightTorusToBaseChangeCoordinateMap R).hom.comp (coordinateMap R).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) matrixWeight := by
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
    (GeneralLinear.pointsMulEquiv 54 g : Matrix (Fin 54) (Fin 54) A)) he).trans ?_
  rw [GeneralLinear.pointsMulEquiv_apply, GeneralLinear.weightTorusCoordinateBialgHom_def,
    DiagonalizableGroup.pointToGeneralLinear_comp_diagonalCoordinateMap]
  congr 1
  funext i
  exact congrArg (fun s : Aˣ ↦ (s : A))
    (SplitTorus.charOfPoint_weightCharacter q (matrixWeight i))

/-- The points cut out by the intrinsic torus ideal, mapped into `GL₅₄`, are exactly the named
weight-torus matrix points. No reducedness or field hypothesis on the value algebra is needed. -/
theorem map_quotientPointsSubgroup_weightTorusDefiningIdeal (A : CommAlgCat.{v} R) :
    (CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R) A).map
        ((GeneralLinear.pointsMulEquiv (R := R) 54).toMonoidHom.comp
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
    -- The subgroup uses bundled monoid homomorphisms, whereas the point formula uses
    -- categorical point maps. `convert` compares these presentations of the same maps.
    convert pointsMulEquiv_mapPointsFunctor_weightTorusToBaseChangeCoordinateMap R A
      ((SplitTorus.pointsMulEquiv (R := R) (A := A)).symm s) using 1
    · rfl
    · rw [MulEquiv.apply_symm_apply]
      rfl

/-- A carrier point belongs to the intrinsic weight torus exactly when its ambient matrix is
diagonal. This tests the closed subgroup on every value algebra, including nonreduced ones. -/
@[simp↓]
theorem mem_quotientPointsSubgroup_weightTorusDefiningIdeal_iff_isDiag
    (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R) A) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R) A ↔
      (GeneralLinear.pointsMulEquiv 54
        ((CommHopfAlgCat.Hom.mapPointsFunctor (coordinateMap R)).app A g) :
          Matrix (Fin 54) (Fin 54) A).IsDiag := by
  let f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R) A →*
      Matrix.GeneralLinearGroup (Fin 54) A :=
    (GeneralLinear.pointsMulEquiv (R := R) 54).toMonoidHom.comp
      ((CommHopfAlgCat.Hom.mapPointsFunctor (coordinateMap R)).app A).hom
  have hf : Function.Injective f := (GeneralLinear.pointsMulEquiv 54).injective.comp
    (CommHopfAlgCat.Hom.mapPointsFunctor_app_injective_of_surjective
      (coordinateMap R) (coordinateMap_surjective R) A)
  have hfg : f g = GeneralLinear.pointsMulEquiv 54
      (CommHopfAlgCat.quotientPointsHom (GeneralLinear.coordinateHopfAlgebra R 54)
        (baseChangeDefiningIdeal R) A g) :=
    congrArg (GeneralLinear.pointsMulEquiv 54) (mapPointsFunctor_coordinateMap_app R g)
  have hmap : (CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R)
      (weightTorusDefiningIdeal R) A).map f =
      ((weightTorusPoints A).range).map (points A).subtype :=
    map_quotientPointsSubgroup_weightTorusDefiningIdeal R A
  have hmem : g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R)
      (weightTorusDefiningIdeal R) A ↔
      f g ∈ ((weightTorusPoints A).range).map (points A).subtype := by
    rw [← hmap, Subgroup.mem_map_iff_mem hf]
  have hf_apply : f g = GeneralLinear.pointsMulEquiv 54
      ((CommHopfAlgCat.Hom.mapPointsFunctor (coordinateMap R)).app A g) := rfl
  rw [hmem, ← hf_apply]
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, he⟩
    rw [← he]
    rw [Subgroup.subtype_apply, coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
    exact Matrix.isDiag_diagonal _
  · intro hg
    -- The scalar-extension point comparison recovers an integral-carrier point with the
    -- same matrix. Its cross-product diagonal criterion works over every value algebra.
    let p := (pointsPresentation
      (CommAlgCat.restrictScalarsObj (algebraMap ℤ R) A)).mulEquiv
        (CommHopfAlgCat.baseChangeIsoPointsMulEquiv (baseChangeCoordinateIso R) A g)
    have hp : (p : Matrix.GeneralLinearGroup (Fin 54) A) = f g := by
      rw [GeneralLinear.IntegralPointsPresentation.coe_mulEquiv_apply]
      exact (GeneralLinear.pointsMulEquiv_quotientPointsHom_baseChangeIsoPointsMulEquiv
        54 definingIdeal (baseChangeDefiningIdeal R) (baseChangeCoordinateIso R)
        (mkQuotient_comp_baseChangeCoordinateIso_hom R) A g).trans hfg.symm
    exact ⟨p, (mem_range_weightTorusPoints_iff_isDiag p).mpr (by rw [hp]; exact hg), hp⟩

/-- The specialization isomorphism sends the scalar-extended integral torus ideal to the
intrinsic torus ideal over `R`, without flatness or reducedness assumptions. -/
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
        (G := SplitTorus.characterGroup (Fin 6))))
    weightTorusIntegralCoordinateMap_surjective
    (weightTorusToBaseChangeCoordinateMap_surjective R) ?_
  simpa only [Iso.symm_inv, _root_.CommHopfAlgCat.isoMk_hom] using
    baseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap R

end

end TauCeti.E6DoubledMinuscule
