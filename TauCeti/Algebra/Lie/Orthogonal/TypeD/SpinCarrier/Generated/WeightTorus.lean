/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.Positive.Basic
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.WeightTorus
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints

/-!
# The closed weight torus of the generated type-D spin subgroup

For `4 ≤ n`, restriction from the ground-ring-generated full spin subgroup to its weight
torus is surjective. Its kernel defines a closed rank-`n` split torus contained in the
generated positive subgroup. Its algebra-valued points are the named spin weight-torus
matrices, and its defining ideal commutes with free scalar extension.

This is a torus in the subgroup generated over the ground ring, not the specialization of the
integral carrier. Neither equality of those carriers nor maximality of the torus is asserted.
These closed-subgroup data supply the torus inclusion needed for a pinning.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 3 and 17.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* The construction follows `TauCeti.Algebra.Lie.E7.Minuscule.Generated.WeightTorus` and the
  specialized spin-torus comparison in
  `TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.WeightTorus`.
-/

public section

open CategoryTheory

namespace TauCeti.TypeDSpinCarrier.Generated

universe u v w

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n) (R : Type u) [CommRing R]

/-- Restriction of the generated spin group's coordinates to the weight torus is surjective. -/
theorem generatedWeightTorusCoordinateMap_surjective :
    Function.Surjective (generatedWeightTorusCoordinateMap n hn R).hom := by
  have h : Function.Surjective (generatorCoordinateMap n hn R (.inr ())).hom := by
    rw [generatorCoordinateMap_inr, ← coordinateMap_comp_weightTorusToBaseChangeCoordinateMap]
    exact (weightTorusToBaseChangeCoordinateMap_surjective n hn R).comp
      (coordinateMap_surjective n hn R)
  rw [← generatedCoordinateMap_comp_generatedCoordinateLift] at h
  rw [generatedWeightTorusCoordinateMap_def]
  exact Function.Surjective.of_comp h

/-- The defining ideal of the weight torus inside the ground-ring-generated spin group. -/
def weightTorusDefiningIdeal : HopfIdeal R (generatedCoordinateHopfAlgebra n hn R) :=
  HopfIdeal.kerOfSurjective (generatedWeightTorusCoordinateMap n hn R).hom
    (generatedWeightTorusCoordinateMap_surjective n hn R)

/-- A generated-carrier coordinate lies in the torus ideal exactly when its restriction vanishes.
-/
@[simp]
theorem mem_weightTorusDefiningIdeal (x : generatedCoordinateHopfAlgebra n hn R) :
    x ∈ weightTorusDefiningIdeal n hn R ↔
      (generatedWeightTorusCoordinateMap n hn R).hom x = 0 := by
  rw [weightTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

/-- The torus quotient is canonically the rank-`n` split-torus coordinate algebra. -/
def weightTorusCoordinateIso :
    FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.of R (generatedCoordinateHopfAlgebra n hn R))
        (weightTorusDefiningIdeal n hn R) ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin n)) :=
  ObjectProperty.isoMk _ <|
    _root_.CommHopfAlgCat.Hom.quotientKerOfSurjectiveIso
      (generatedWeightTorusCoordinateMap n hn R)
      (generatedWeightTorusCoordinateMap_surjective n hn R)

/-- The quotient identification recovers restriction to the weight torus. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_weightTorusCoordinateIso_hom :
    FiniteTypeCommHopfAlgCat.mkQuotient
        (FiniteTypeCommHopfAlgCat.of R (generatedCoordinateHopfAlgebra n hn R))
        (weightTorusDefiningIdeal n hn R) ≫ (weightTorusCoordinateIso n hn R).hom =
      ObjectProperty.homMk (generatedWeightTorusCoordinateMap n hn R) :=
  ObjectProperty.hom_ext _ <|
    _root_.CommHopfAlgCat.Hom.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _

/-- The closed torus is split over every commutative base ring. -/
theorem splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.of R (generatedCoordinateHopfAlgebra n hn R))
        (weightTorusDefiningIdeal n hn R)) := by
  exact (splitTorusCommHopfAlgProperty R).prop_of_iso
    (TypeDSpinCarrier.weightTorusCoordinateIso n hn R ≪≫
      (weightTorusCoordinateIso n hn R).symm)
    (TypeDSpinCarrier.splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal n hn R)

grind_pattern splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal =>
  weightTorusDefiningIdeal n hn R

/-- Contravariantly, the weight torus is contained in the generated positive subgroup. -/
theorem carrierDefiningIdeal_le_weightTorusDefiningIdeal :
    Positive.carrierDefiningIdeal n hn R ≤ weightTorusDefiningIdeal n hn R := by
  intro x hx
  rw [mem_weightTorusDefiningIdeal, generatedWeightTorusCoordinateMap_def]
  exact Positive.carrierDefiningIdeal_toIdeal_le_ker_generatedCoordinateLift n hn R (.inr ()) hx

/-- On algebra-valued points, the generated torus morphism gives the named spin torus matrix. -/
@[simp↓]
theorem pointsMulEquiv_mapPointsFunctor_generatedWeightTorusCoordinateMap
    (A : CommAlgCat.{v} R)
    (q : HopfAlgebra.points (R := R)
      (H := (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin n))).obj) A) :
    GeneralLinear.pointsMulEquiv (dimension n)
        ((CommHopfAlgCat.Hom.mapPointsFunctor (generatedCoordinateMap n hn R)).app A
          ((CommHopfAlgCat.Hom.mapPointsFunctor
            (generatedWeightTorusCoordinateMap n hn R)).app A q)) =
      (weightTorusPoints n hn A (SplitTorus.pointsMulEquiv q) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) A) := by
  have hg := CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply
    (generatedCoordinateMap n hn R) (generatedWeightTorusCoordinateMap n hn R) A q
  have hs := CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply
    (coordinateMap n hn R) (weightTorusToBaseChangeCoordinateMap n hn R) A q
  rw [generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap] at hg
  rw [coordinateMap_comp_weightTorusToBaseChangeCoordinateMap] at hs
  have he := congrArg (GeneralLinear.pointsMulEquiv (dimension n)) (hg.symm.trans hs)
  have hp := congrArg (fun g : points n hn A ↦
    (g : Matrix.GeneralLinearGroup (Fin (dimension n)) A))
    (baseChangePointsMulEquiv_mapPointsFunctor_weightTorusToBaseChangeCoordinateMap n hn R A q)
  have hcoe := coe_baseChangePointsMulEquiv_apply n hn R A
    ((CommHopfAlgCat.Hom.mapPointsFunctor
      (weightTorusToBaseChangeCoordinateMap n hn R)).app A q)
  rw [hcoe] at hp
  rw [mapPointsFunctor_coordinateMap_app n hn R
    ((CommHopfAlgCat.Hom.mapPointsFunctor
      (weightTorusToBaseChangeCoordinateMap n hn R)).app A q)] at he
  exact he.trans hp

/-- The closed generated torus maps to exactly the named spin weight-torus matrices.
The value algebra need not be reduced or a field. -/
theorem map_quotientPointsSubgroup_weightTorusDefiningIdeal (A : CommAlgCat.{v} R) :
    (CommHopfAlgCat.quotientPointsSubgroup (generatedCoordinateHopfAlgebra n hn R)
        (weightTorusDefiningIdeal n hn R) A).map
        ((GeneralLinear.pointsMulEquiv (R := R) (dimension n)).toMonoidHom.comp
          ((CommHopfAlgCat.Hom.mapPointsFunctor (generatedCoordinateMap n hn R)).app A).hom) =
      ((weightTorusPoints n hn A).range).map (points n hn A).subtype := by
  rw [weightTorusDefiningIdeal,
    HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor]
  ext g
  simp only [Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  -- The subgroup image uses bundled homomorphisms; the point formula uses their element maps.
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    refine ⟨_, ⟨SplitTorus.pointsMulEquiv q, rfl⟩, ?_⟩
    simp only [Subgroup.coe_subtype]
    exact (pointsMulEquiv_mapPointsFunctor_generatedWeightTorusCoordinateMap n hn R A q).symm
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    refine ⟨_, ⟨(SplitTorus.pointsMulEquiv (R := R) (A := A)).symm s, rfl⟩, ?_⟩
    simp only [Subgroup.coe_subtype]
    have h := pointsMulEquiv_mapPointsFunctor_generatedWeightTorusCoordinateMap n hn R A
      ((SplitTorus.pointsMulEquiv (R := R) (A := A)).symm s)
    rw [MulEquiv.apply_symm_apply] at h
    exact h

variable (S : Type max u w) [CommRing S] [Algebra R S] [Module.Free R S]

/-- Free scalar extension transports the generated spin torus ideal to the intrinsic torus ideal
of the generated subgroup over the extension ring. -/
@[simp↓]
theorem map_baseChange_weightTorusDefiningIdeal :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := S) (weightTorusDefiningIdeal n hn R)).map
        (generatedCoordinateHopfAlgebraBaseChangeIso n hn R S).hom.hom =
      weightTorusDefiningIdeal n hn S := by
  unfold weightTorusDefiningIdeal
  apply CommHopfAlgCat.map_baseChangeHopfIdeal_kerOfSurjective
    (generatedCoordinateHopfAlgebraBaseChangeIso n hn R S)
    (generatorCoordinateAlgebraBaseChangeIso n R S (.inr ()))
    (generatedWeightTorusCoordinateMap_surjective n hn R)
    (generatedWeightTorusCoordinateMap_surjective n hn S)
  rw [generatedWeightTorusCoordinateMap_def, generatedWeightTorusCoordinateMap_def,
    baseChangeMap_generatedCoordinateLift_comp_generatorCoordinateAlgebraBaseChangeIso_hom,
    Iso.inv_hom_id_assoc]

end

end TauCeti.TypeDSpinCarrier.Generated
