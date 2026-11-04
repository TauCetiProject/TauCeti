/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Generated.WeightTorus
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Functorial
import TauCeti.Algebra.Lie.E6.DoubledMinuscule.MaximalTorus
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Centralizer
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

/-!
# The schematic torus centralizer of the generated doubled E₆ group

The closed weight torus of the ground-ring-generated doubled minuscule group is its own
scheme-theoretic centralizer. The equality holds on every commutative value algebra, including
nonreduced algebras and finite fields, and on defining Hopf ideals, not just their radicals.
It supplies the toral-centralizer identification used in recognizing a numbered pinning.

Distinct integral weight characters force a centralizing matrix to be diagonal. The inclusion
in the specialization of the integral carrier then lets its invariant cross product recover the
torus parameters. This uses only that inclusion, not equality of the two carriers. No comparison
with an independently pinned simply connected group is asserted.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1.
* SGA 3, Exposé XI, centralizers of groups of multiplicative type.
* The schematic diagonalization follows
  `TauCeti.Algebra.Lie.E7.Minuscule.Generated.TorusCentralizer`.
* Torus-parameter recovery is the invariant-cross-product calculation in
  `TauCeti.E6DoubledMinuscule.mem_range_weightTorusPoints_iff_isDiag`.
-/

public section

open CategoryTheory

namespace TauCeti.E6DoubledMinuscule.Generated

universe u v

variable (R : Type u) [CommRing R]

/-- A generated point centralizes the weight torus scheme-theoretically exactly when its
matrix is diagonal, over any commutative value algebra. -/
theorem mem_centralizerPointsSubgroup_iff_isDiag (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (R := R) (H := generatedCoordinateHopfAlgebra R) A) :
    g ∈ BialgHom.centralizerPointsSubgroup (generatedWeightTorusCoordinateMap R).hom A ↔
      (GeneralLinear.pointsMulEquiv 54
        (BialgHom.mapDomain (generatedCoordinateMap R).hom g) :
          Matrix (Fin 54) (Fin 54) A).IsDiag := by
  have hcomp : (generatedWeightTorusCoordinateMap R).hom.comp
        (generatedCoordinateMap R).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) matrixWeight := by
    rw [← CommHopfAlgCat.hom_comp,
      generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  have hc := BialgHom.centralizerHopfIdeal_comp_le_ker_iff
    (generatedCoordinateMap R).hom (generatedCoordinateMap_surjective R)
    (generatedWeightTorusCoordinateMap R).hom g
  rw [hcomp, GeneralLinear.centralizerHopfIdeal_weightTorus_le_ker_iff_isDiag _
    (fun a b hab ↦ minusculeCharacter_injective
      (congrArg SplitTorus.weightCharacter hab))] at hc
  rw [BialgHom.centralizerPointsSubgroup, CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  simpa only [IsConcreteLE.le_iff, RingHom.mem_ker, HopfIdeal.mem_toIdeal] using hc.symm

/-- The diagonal points of the generated carrier are exactly the points of its closed weight
torus. No reducedness or characteristic hypothesis is needed. -/
@[simp↓]
theorem mem_quotientPointsSubgroup_weightTorusDefiningIdeal_iff_isDiag
    (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (R := R) (H := generatedCoordinateHopfAlgebra R) A) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (generatedCoordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R) A ↔
      (GeneralLinear.pointsMulEquiv 54
        (BialgHom.mapDomain (generatedCoordinateMap R).hom g) :
          Matrix (Fin 54) (Fin 54) A).IsDiag := by
  -- Use the point-functor API explicitly before comparing the two carriers' matrices.
  rw [BialgHom.mapDomain_apply, ← CommHopfAlgCat.Hom.mapPointsFunctor_app_apply]
  obtain ⟨h, hh⟩ := exists_carrierPoint R A g
  rw [← hh, ← mem_range_weightTorusPoints_iff_isDiag h]
  let f := (GeneralLinear.pointsMulEquiv (R := R) 54).toMonoidHom.comp
    ((CommHopfAlgCat.Hom.mapPointsFunctor (generatedCoordinateMap R)).app A).hom
  have hf : Function.Injective f :=
    (GeneralLinear.pointsMulEquiv 54).injective.comp
      (CommHopfAlgCat.Hom.mapPointsFunctor_app_injective_of_surjective
        (generatedCoordinateMap R) (generatedCoordinateMap_surjective R) A)
  have hfg : f g = (h : Matrix.GeneralLinearGroup (Fin 54) A) := hh.symm
  have hmem := Subgroup.mem_map_iff_mem (K := CommHopfAlgCat.quotientPointsSubgroup
    (generatedCoordinateHopfAlgebra R) (weightTorusDefiningIdeal R) A) (x := g) hf
  rw [map_quotientPointsSubgroup_weightTorusDefiningIdeal R A, hfg] at hmem
  exact hmem.symm.trans (Subgroup.mem_map_iff_mem (points A).subtype_injective)

/-- On every value algebra, a point centralizes the weight torus scheme-theoretically exactly
when it belongs to that closed torus. No reducedness or characteristic hypothesis is needed. -/
@[simp↓]
theorem mem_centralizerPointsSubgroup_iff_mem_quotientPointsSubgroup
    (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (R := R) (H := generatedCoordinateHopfAlgebra R) A) :
    g ∈ BialgHom.centralizerPointsSubgroup (generatedWeightTorusCoordinateMap R).hom A ↔
      g ∈ CommHopfAlgCat.quotientPointsSubgroup (generatedCoordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R) A :=
  (mem_centralizerPointsSubgroup_iff_isDiag R A g).trans
    (mem_quotientPointsSubgroup_weightTorusDefiningIdeal_iff_isDiag R A g).symm

/-- The scheme-theoretic centralizer of the generated doubled E₆ weight torus is cut out by
exactly the torus ideal, including its infinitesimal structure over arbitrary ground rings. -/
@[simp]
theorem centralizerHopfIdeal_eq_weightTorusDefiningIdeal :
    BialgHom.centralizerHopfIdeal (generatedWeightTorusCoordinateMap R).hom =
      weightTorusDefiningIdeal R := by
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq
  intro A
  ext g
  exact mem_centralizerPointsSubgroup_iff_mem_quotientPointsSubgroup R A g

end TauCeti.E6DoubledMinuscule.Generated
