/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.StandardComodule
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.Positive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.WeightTorus
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints

/-!
# The closed weight torus of the generated type-B spin subgroup

Restriction from the ground-ring-generated type-`Bₙ₊₁` spin subgroup to its rank-`(n + 1)`
weight torus is surjective. Its kernel defines a closed split torus contained in the generated
positive subgroup. The points of this torus are exactly the named spin weight-torus matrices,
over every commutative value algebra, and its ideal commutes with free scalar extension.

These are torus data for a pinning, not a maximality assertion. The ground-ring-generated
subgroup is not identified with the specialization of the integral spin carrier or with the
pinned simply connected group scheme; constructions on it transfer to the latter only along
such an identification.

## Main declarations

* `TauCeti.TypeBSpinCarrier.Generated.weightTorusDefiningIdeal`: the torus ideal in the
  generated carrier.
* `TauCeti.TypeBSpinCarrier.Generated.weightTorusCoordinateIso`: its quotient is the
  rank-`(n + 1)` split-torus coordinate algebra.
* `TauCeti.TypeBSpinCarrier.Generated.carrierDefiningIdeal_le_weightTorusDefiningIdeal`:
  the torus is contained in the generated positive subgroup.
* `TauCeti.TypeBSpinCarrier.Generated.map_quotientPointsSubgroup_weightTorusDefiningIdeal`:
  the point subgroup maps to precisely the spin weight-torus matrices.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 3 and 17.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* The construction adapts `TauCeti.Algebra.Lie.E7.Minuscule.Generated.WeightTorus` and
  the type-B specialized-carrier torus in
  `TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.WeightTorus`.
-/

public section

open CategoryTheory

namespace TauCeti.TypeBSpinCarrier.Generated

universe u v w

noncomputable section

variable (n : ℕ) (R : Type u) [CommRing R]

/-- Restriction of the generated spin subgroup's coordinates to the weight torus is surjective. -/
theorem generatedWeightTorusCoordinateMap_surjective :
    Function.Surjective (generatedWeightTorusCoordinateMap n R).hom := by
  have h : Function.Surjective (generatorCoordinateMap n R (.inr ())).hom := by
    rw [generatorCoordinateMap_inr, ← coordinateMap_comp_weightTorusToBaseChangeCoordinateMap]
    exact (weightTorusToBaseChangeCoordinateMap_surjective n R).comp (coordinateMap_surjective n R)
  rw [← generatedCoordinateMap_comp_generatedCoordinateLift] at h
  rw [generatedWeightTorusCoordinateMap_def]
  exact Function.Surjective.of_comp h

/-- The defining ideal of the weight torus inside the ground-ring-generated spin subgroup. -/
def weightTorusDefiningIdeal : HopfIdeal R (generatedCoordinateHopfAlgebra n R) :=
  HopfIdeal.kerOfSurjective (generatedWeightTorusCoordinateMap n R).hom
    (generatedWeightTorusCoordinateMap_surjective n R)

/-- A generated-carrier coordinate lies in the torus ideal exactly when its restriction is zero. -/
@[simp]
theorem mem_weightTorusDefiningIdeal (x : generatedCoordinateHopfAlgebra n R) :
    x ∈ weightTorusDefiningIdeal n R ↔ (generatedWeightTorusCoordinateMap n R).hom x = 0 := by
  rw [weightTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]

/-- The intrinsic torus quotient is the rank-`(n + 1)` split-torus coordinate algebra. -/
def weightTorusCoordinateIso :
    FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.of R (generatedCoordinateHopfAlgebra n R))
        (weightTorusDefiningIdeal n R) ≅
      DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup (Fin (n + 1))) :=
  ObjectProperty.isoMk _ <|
    _root_.CommHopfAlgCat.Hom.quotientKerOfSurjectiveIso
      (generatedWeightTorusCoordinateMap n R) (generatedWeightTorusCoordinateMap_surjective n R)

/-- The quotient identification recovers restriction to the weight torus. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_weightTorusCoordinateIso_hom :
    FiniteTypeCommHopfAlgCat.mkQuotient
        (FiniteTypeCommHopfAlgCat.of R (generatedCoordinateHopfAlgebra n R))
        (weightTorusDefiningIdeal n R) ≫ (weightTorusCoordinateIso n R).hom =
      ObjectProperty.homMk (generatedWeightTorusCoordinateMap n R) := by
  apply ObjectProperty.hom_ext
  exact _root_.CommHopfAlgCat.Hom.mkQuotient_comp_quotientKerOfSurjectiveIso_hom _ _

/-- The closed subgroup cut out by the intrinsic torus ideal is split over any commutative ring. -/
theorem splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal :
    splitTorusCommHopfAlgProperty R
      (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.of R (generatedCoordinateHopfAlgebra n R))
        (weightTorusDefiningIdeal n R)) := by
  exact (splitTorusCommHopfAlgProperty R).prop_of_iso
    (TypeBSpinCarrier.weightTorusCoordinateIso n R ≪≫ (weightTorusCoordinateIso n R).symm)
    (TypeBSpinCarrier.splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal n R)

grind_pattern splitTorusCommHopfAlgProperty_quotient_weightTorusDefiningIdeal =>
  weightTorusDefiningIdeal n R

/-- Contravariantly, the closed weight torus lies in the generated positive subgroup. -/
theorem carrierDefiningIdeal_le_weightTorusDefiningIdeal :
    Positive.carrierDefiningIdeal n R ≤ weightTorusDefiningIdeal n R := by
  intro x hx
  rw [mem_weightTorusDefiningIdeal, generatedWeightTorusCoordinateMap_def]
  exact Positive.carrierDefiningIdeal_toIdeal_le_ker_generatedCoordinateLift n R (.inr ()) hx

/-- On algebra-valued points, the generated torus restriction gives the named spin weight matrix. -/
@[simp↓]
theorem pointsMulEquiv_mapPointsFunctor_generatedWeightTorusCoordinateMap
    (A : CommAlgCat.{v} R)
    (q : HopfAlgebra.points (R := R)
      (H := (DiagonalizableGroup.coordinateRing R
        (SplitTorus.characterGroup (Fin (n + 1)))).obj) A) :
    GeneralLinear.pointsMulEquiv (dimension n)
        ((CommHopfAlgCat.Hom.mapPointsFunctor (generatedCoordinateMap n R)).app A
          ((CommHopfAlgCat.Hom.mapPointsFunctor (generatedWeightTorusCoordinateMap n R)).app A q)) =
      (weightTorusPoints n A (SplitTorus.pointsMulEquiv q) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) A) := by
  have hg := CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply
    (generatedCoordinateMap n R) (generatedWeightTorusCoordinateMap n R) A q
  have hs := CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply
    (coordinateMap n R) (weightTorusToBaseChangeCoordinateMap n R) A q
  rw [generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap] at hg
  rw [coordinateMap_comp_weightTorusToBaseChangeCoordinateMap] at hs
  have hp := congrArg Subtype.val
    (baseChangePointsMulEquiv_mapPointsFunctor_weightTorusToBaseChangeCoordinateMap n R A q)
  have hc := coe_baseChangePointsMulEquiv_apply n R A
    ((CommHopfAlgCat.Hom.mapPointsFunctor
      (weightTorusToBaseChangeCoordinateMap n R)).app A q)
  have he := mapPointsFunctor_coordinateMap_app n R (B := A)
    ((CommHopfAlgCat.Hom.mapPointsFunctor
      (weightTorusToBaseChangeCoordinateMap n R)).app A q)
  -- Compare the generated route with coordinateMap ≫ weightTorusToBaseChangeCoordinateMap,
  -- then use the specialized carrier's baseChangePointsMulEquiv to identify the weight matrix.
  exact (congrArg (GeneralLinear.pointsMulEquiv (dimension n))
    ((hg.symm.trans hs).trans he)).trans (hc.symm.trans hp)

/-- The closed generated torus maps to exactly the spin weight-torus matrices.
The value algebra need not be reduced or a field. -/
theorem map_quotientPointsSubgroup_weightTorusDefiningIdeal (A : CommAlgCat.{v} R) :
    (CommHopfAlgCat.quotientPointsSubgroup (generatedCoordinateHopfAlgebra n R)
        (weightTorusDefiningIdeal n R) A).map
        ((GeneralLinear.pointsMulEquiv (R := R) (dimension n)).toMonoidHom.comp
          ((CommHopfAlgCat.Hom.mapPointsFunctor (generatedCoordinateMap n R)).app A).hom) =
      ((weightTorusPoints n A).range).map (points n A).subtype := by
  rw [weightTorusDefiningIdeal,
    HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor]
  ext g
  simp only [Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    refine ⟨_, ⟨SplitTorus.pointsMulEquiv q, rfl⟩, ?_⟩
    simp only [Subgroup.coe_subtype]
    exact (pointsMulEquiv_mapPointsFunctor_generatedWeightTorusCoordinateMap n R A q).symm
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    refine ⟨_, ⟨(SplitTorus.pointsMulEquiv (R := R) (A := A)).symm s, rfl⟩, ?_⟩
    simp only [Subgroup.coe_subtype]
    have h := pointsMulEquiv_mapPointsFunctor_generatedWeightTorusCoordinateMap n R A
      ((SplitTorus.pointsMulEquiv (R := R) (A := A)).symm s)
    rw [MulEquiv.apply_symm_apply] at h
    exact h

variable (S : Type max u w) [CommRing S] [Algebra R S] [Module.Free R S]

/-- The generated-carrier comparison transports the torus ideal under free scalar extension. -/
@[simp↓]
theorem map_baseChange_weightTorusDefiningIdeal :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := S) (weightTorusDefiningIdeal n R)).map
        (generatedCoordinateHopfAlgebraBaseChangeIso n R S).hom.hom =
      weightTorusDefiningIdeal n S := by
  unfold weightTorusDefiningIdeal
  apply CommHopfAlgCat.map_baseChangeHopfIdeal_kerOfSurjective
    (generatedCoordinateHopfAlgebraBaseChangeIso n R S)
    (generatorCoordinateAlgebraBaseChangeIso n R S (.inr ()))
    (generatedWeightTorusCoordinateMap_surjective n R)
    (generatedWeightTorusCoordinateMap_surjective n S)
  rw [generatedWeightTorusCoordinateMap_def, generatedWeightTorusCoordinateMap_def,
    baseChangeMap_generatedCoordinateLift_comp_generatorCoordinateAlgebraBaseChangeIso_hom,
    Iso.inv_hom_id_assoc]

end

end TauCeti.TypeBSpinCarrier.Generated
