/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.WeightTorus
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Functorial
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Centralizer
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

/-!
# Schematic self-centralization of the doubled E₆ weight torus

The rank-six weight torus of the integral doubled minuscule carrier is its own schematic
centralizer, after specialization to any commutative base ring. The point statement tests every
commutative value algebra, not just rational points over infinite fields. Equality of the defining
ideals therefore includes infinitesimal structure, even in characteristics two and three.

Distinct weight characters force a centralizing matrix to be diagonal. The all-ring criterion
`TauCeti.E6DoubledMinuscule.mem_quotientPointsSubgroup_weightTorusDefiningIdeal_iff_isDiag`,
obtained from the invariant cross product, then identifies the intrinsic torus. This supplies
schematic torus
recognition for the explicit carrier, not an identification with the pinned simply connected
group scheme of type E₆. Constructions transfer to that pinned group only along such an
identification once proved. No equality with the separately ground-ring-generated carrier is
asserted.

## Main results

* `centralizerPointsSubgroup_eq_range_weightTorus`: the centralizer is the torus on all value
  algebras, including finite and nonreduced ones.
* `centralizerHopfIdeal_eq_weightTorusDefiningIdeal`: the centralizer's defining Hopf ideal is
  the intrinsic weight-torus ideal.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§16 and 26.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 3 and 17.
* The schematic diagonalization uses the method of
  `TauCeti.Algebra.Lie.E7.Minuscule.Generated.TorusCentralizer`; the diagonal-intersection
  calculation is the doubled carrier's existing invariant-cross-product construction.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.E6DoubledMinuscule

universe u v

variable (R : Type u) [CommRing R]

private theorem centralizer_iff_isDiag (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R) A) :
    g ∈ BialgHom.centralizerPointsSubgroup (weightTorusToBaseChangeCoordinateMap R).hom A ↔
      (GeneralLinear.pointsMulEquiv 54 (BialgHom.mapDomain (coordinateMap R).hom g) :
        Matrix (Fin 54) (Fin 54) A).IsDiag := by
  have hwt : Function.Injective matrixWeight := by
    intro a b h
    apply minusculeCharacter_injective
    exact congrArg SplitTorus.weightCharacter h
  have h := BialgHom.centralizerHopfIdeal_comp_le_ker_iff
    (coordinateMap R).hom (coordinateMap_surjective R)
    (weightTorusToBaseChangeCoordinateMap R).hom g
  have hcomp : (weightTorusToBaseChangeCoordinateMap R).hom.comp (coordinateMap R).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) matrixWeight := by
    rw [← CommHopfAlgCat.hom_comp, coordinateMap_comp_weightTorusToBaseChangeCoordinateMap,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  rw [hcomp, GeneralLinear.centralizerHopfIdeal_weightTorus_le_ker_iff_isDiag _ hwt] at h
  rw [BialgHom.centralizerPointsSubgroup, CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  simpa only [IsConcreteLE.le_iff, RingHom.mem_ker, HopfIdeal.mem_toIdeal] using h.symm

/-- Over every value algebra, the schematic centralizer of the doubled E₆ weight torus is
exactly the image of that torus. This tests extensions of the value algebra, rather than only
commutation with its rational torus points. -/
theorem centralizerPointsSubgroup_eq_range_weightTorus (A : CommAlgCat.{v} R) :
    BialgHom.centralizerPointsSubgroup (weightTorusToBaseChangeCoordinateMap R).hom A =
      (BialgHom.mapDomain (weightTorusToBaseChangeCoordinateMap R).hom).range := by
  -- Use the membership API: the intrinsic ideal's definition is not exposed.
  have hker : weightTorusDefiningIdeal R =
      HopfIdeal.kerOfSurjective (weightTorusToBaseChangeCoordinateMap R).hom
        (weightTorusToBaseChangeCoordinateMap_surjective R) := by
    ext x
    rw [mem_weightTorusDefiningIdeal, HopfIdeal.mem_kerOfSurjective]
  rw [← HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range _
    (weightTorusToBaseChangeCoordinateMap_surjective R) A, ← hker]
  ext g
  rw [centralizer_iff_isDiag,
    mem_quotientPointsSubgroup_weightTorusDefiningIdeal_iff_isDiag,
    CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, BialgHom.mapDomain_apply]

/-- The schematic centralizer of the doubled E₆ weight torus is cut out by the intrinsic
weight-torus Hopf ideal. This is equality of ideals, not merely equality of geometric points;
no reducedness, flatness or field hypothesis is required. -/
theorem centralizerHopfIdeal_eq_weightTorusDefiningIdeal :
    BialgHom.centralizerHopfIdeal (weightTorusToBaseChangeCoordinateMap R).hom =
      weightTorusDefiningIdeal R := by
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq
  intro A
  ext g
  rw [← BialgHom.centralizerPointsSubgroup, centralizer_iff_isDiag,
    mem_quotientPointsSubgroup_weightTorusDefiningIdeal_iff_isDiag,
    CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, BialgHom.mapDomain_apply]

end TauCeti.E6DoubledMinuscule
