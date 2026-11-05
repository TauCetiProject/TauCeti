/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Functorial
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Centralizer

/-!
# The schematic torus centralizer of the specialized E₇ minuscule carrier

The centralizer of the weight torus in the base change of the integral E₇ minuscule carrier
consists exactly of diagonal carrier matrices, over every commutative base ring and value
algebra. Schematic centralization tests commutation after extensions of the value algebra;
unlike testing rational torus points alone, it separates the weights over finite fields and
nonreduced rings as well.

This identifies the centralizer with the carrier's intersection with the ambient diagonal
torus. Identifying that intersection with the rank-seven weight torus is a separate question;
no torus maximality or identification with an independently pinned group is asserted here.
Nor is the specialized integral carrier identified with the subgroup generated after base
change by its root subgroups and torus.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§16 and 26.
* The closed-immersion argument follows
  `TauCeti.Algebra.Lie.E7.Minuscule.Generated.TorusCentralizer`, using instead the specialized
  integral carrier and its transported torus from `TauCeti.Algebra.Lie.E7.Minuscule.BaseChange`.
-/

public section

open CategoryTheory

namespace TauCeti.E7Minuscule

universe u v

variable (R : Type u) [CommRing R]

/-- A point of the specialized integral E₇ carrier centralizes its weight torus
scheme-theoretically exactly when its matrix is diagonal, over any value algebra. -/
@[simp↓]
theorem mem_centralizerPointsSubgroup_iff_isDiag (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R) A) :
    g ∈ BialgHom.centralizerPointsSubgroup (weightTorusToBaseChangeCoordinateMap R).hom A ↔
      (GeneralLinear.pointsMulEquiv 56
        (BialgHom.mapDomain (coordinateMap R).hom g) :
          Matrix (Fin 56) (Fin 56) A).IsDiag := by
  have hcomp : (weightTorusToBaseChangeCoordinateMap R).hom.comp (coordinateMap R).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) DynkinType.e7MinusculeWeight := by
    rw [← CommHopfAlgCat.hom_comp,
      coordinateMap_comp_weightTorusToBaseChangeCoordinateMap,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  have h := BialgHom.centralizerHopfIdeal_comp_le_ker_iff
    (coordinateMap R).hom (coordinateMap_surjective R)
    (weightTorusToBaseChangeCoordinateMap R).hom g
  rw [hcomp, GeneralLinear.centralizerHopfIdeal_weightTorus_le_ker_iff_isDiag _
    DynkinType.e7MinusculeWeight_injective] at h
  rw [BialgHom.centralizerPointsSubgroup, CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  simpa only [IsConcreteLE.le_iff, RingHom.mem_ker, HopfIdeal.mem_toIdeal] using h.symm

/-- The schematic torus centralizer in the specialized integral E₇ carrier is the inverse
image of the ambient diagonal torus under its closed matrix embedding, on every value algebra. -/
theorem centralizerPointsSubgroup_eq_comap_diagonalTorus (A : CommAlgCat.{v} R) :
    BialgHom.centralizerPointsSubgroup (weightTorusToBaseChangeCoordinateMap R).hom A =
      (diagonalTorus A 56).comap
        ((GeneralLinear.pointsMulEquiv (R := R) 56).toMonoidHom.comp
          (BialgHom.mapDomain (coordinateMap R).hom)) := by
  ext g
  simp only [Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    mem_diagonalTorus_iff]
  exact mem_centralizerPointsSubgroup_iff_isDiag R A g

end TauCeti.E7Minuscule
