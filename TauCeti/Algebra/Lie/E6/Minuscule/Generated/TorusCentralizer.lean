/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.Generated.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Functorial
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Centralizer

/-!
# The schematic weight-torus centralizer in the generated E₆ carrier

The centralizer of the generated E₆ weight torus consists exactly of the diagonal carrier
matrices, over every commutative base ring and value algebra. Schematic centralization tests
commutation after every extension of the value algebra, so the distinct minuscule characters
separate the weight lines even over finite fields and nonreduced rings.

This reduces self-centralization of the weight torus to identifying the diagonal intersection
of the generated carrier. That intersection is not identified here with the weight torus, and
neither torus maximality nor agreement with an independently pinned group is asserted. The
generated subgroup is also not identified with the specialization of the integral carrier.

## Main results

* `TauCeti.E6Minuscule.Generated.mem_centralizerPointsSubgroup_iff_isDiag`: membership in the
  schematic centralizer is equivalent to diagonality of the carrier matrix.
* `TauCeti.E6Minuscule.Generated.centralizerPointsSubgroup_eq_comap_diagonalTorus`: the
  centralizer is the inverse image of the full diagonal torus under the closed matrix embedding.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§16 and 26.
* The proof specializes the closed-immersion and multiplicity-free weight criteria, following
  `TauCeti.Algebra.Lie.E7.Minuscule.Generated.TorusCentralizer`.
-/

public section

open CategoryTheory

namespace TauCeti.E6Minuscule.Generated

universe u v

variable (R : Type u) [CommRing R]

/-- A point of the generated E₆ carrier centralizes the weight torus scheme-theoretically
exactly when its matrix is diagonal. The value algebra can be nonreduced or finite. -/
@[simp↓]
theorem mem_centralizerPointsSubgroup_iff_isDiag (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (R := R) (H := generatedCoordinateHopfAlgebra R) A) :
    g ∈ BialgHom.centralizerPointsSubgroup (generatedWeightTorusCoordinateMap R).hom A ↔
      (GeneralLinear.pointsMulEquiv 27
        (BialgHom.mapDomain (generatedCoordinateMap R).hom g) :
          Matrix (Fin 27) (Fin 27) A).IsDiag := by
  have hcomp : (generatedWeightTorusCoordinateMap R).hom.comp
        (generatedCoordinateMap R).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) DynkinType.e6MinusculeWeight := by
    rw [← CommHopfAlgCat.hom_comp,
      generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap, weightTable_weight]
  have h := BialgHom.centralizerHopfIdeal_comp_le_ker_iff
    (generatedCoordinateMap R).hom (generatedCoordinateMap_surjective R)
    (generatedWeightTorusCoordinateMap R).hom g
  rw [hcomp, GeneralLinear.centralizerHopfIdeal_weightTorus_le_ker_iff_isDiag _
    DynkinType.e6MinusculeWeight_injective] at h
  rw [BialgHom.centralizerPointsSubgroup, CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  simpa only [IsConcreteLE.le_iff, RingHom.mem_ker, HopfIdeal.mem_toIdeal] using h.symm

/-- On every value algebra, the schematic torus centralizer is the inverse image of the full
diagonal torus under the generated carrier's closed matrix embedding. -/
theorem centralizerPointsSubgroup_eq_comap_diagonalTorus (A : CommAlgCat.{v} R) :
    BialgHom.centralizerPointsSubgroup (generatedWeightTorusCoordinateMap R).hom A =
      (diagonalTorus A 27).comap
        ((GeneralLinear.pointsMulEquiv (R := R) 27).toMonoidHom.comp
          (BialgHom.mapDomain (generatedCoordinateMap R).hom)) := by
  ext g
  simp only [Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    mem_diagonalTorus_iff]
  exact mem_centralizerPointsSubgroup_iff_isDiag R A g

end TauCeti.E6Minuscule.Generated
