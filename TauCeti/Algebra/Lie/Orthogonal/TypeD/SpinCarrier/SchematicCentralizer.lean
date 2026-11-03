/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.TorusCentralizer
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Functorial
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Centralizer

/-!
# The schematic weight-torus centralizer of the type-D spin carrier

The centralizer of the full spin weight torus consists exactly of the diagonal carrier
matrices over every commutative base ring and value algebra. Schematic centralization tests
commutation after extension of the value algebra, not just with its rational torus points.
Consequently this calculation also applies over finite fields and nonreduced rings, where
rational characters need not separate the spin weights.

The result transports through the points equivalence for the specialized integral carrier.
It does not identify that carrier with the group generated after specialization. Nor does it
identify the diagonal intersection with the weight torus: that further calculation is needed
for self-centralization and maximality of the torus.

The proof follows the schematic centralizer calculation in
`TauCeti.Algebra.Lie.E7.Minuscule.Generated.TorusCentralizer`, using the closed matrix
embedding and the distinct integral spin weights.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§16 and 26.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
-/

public section

open CategoryTheory

namespace TauCeti.TypeDSpinCarrier

universe u v

variable (n : ℕ) (hn : 4 ≤ n) (R : Type u) [CommRing R]

/-- A point of the specialized integral spin carrier centralizes the weight torus
scheme-theoretically exactly when its spin matrix is diagonal. No reducedness or
infinitude assumption is imposed on the value algebra. -/
@[simp↓]
theorem mem_centralizerPointsSubgroup_iff_isDiag (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra n hn R) A) :
    g ∈ BialgHom.centralizerPointsSubgroup (weightTorusToBaseChangeCoordinateMap n hn R).hom A ↔
      ((baseChangePointsMulEquiv n hn R A g :
        Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
          Matrix (Fin (dimension n)) (Fin (dimension n)) A).IsDiag := by
  have hcomp : (weightTorusToBaseChangeCoordinateMap n hn R).hom.comp
        (coordinateMap n hn R).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) (basisWeight n) := by
    rw [← CommHopfAlgCat.hom_comp, coordinateMap_comp_weightTorusToBaseChangeCoordinateMap,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]
  have h := BialgHom.centralizerHopfIdeal_comp_le_ker_iff
    (coordinateMap n hn R).hom (coordinateMap_surjective n hn R)
    (weightTorusToBaseChangeCoordinateMap n hn R).hom g
  have hw : Function.Injective (basisWeight n) := fun a b hab ↦
    basisCharacter_injective n (congrArg SplitTorus.weightCharacter hab)
  rw [hcomp, GeneralLinear.centralizerHopfIdeal_weightTorus_le_ker_iff_isDiag _ hw] at h
  have hp : BialgHom.mapDomain (coordinateMap n hn R).hom g =
      CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra R (dimension n))
        (baseChangeDefiningIdeal n hn R) A g :=
    mapPointsFunctor_coordinateMap_app n hn R g
  rw [hp] at h
  rw [BialgHom.centralizerPointsSubgroup, CommHopfAlgCat.mem_quotientPointsSubgroup_iff,
    coe_baseChangePointsMulEquiv_apply]
  simpa only [IsConcreteLE.le_iff, RingHom.mem_ker, HopfIdeal.mem_toIdeal] using h.symm

/-- The points comparison carries the schematic torus centralizer onto precisely the
existing subgroup of diagonal spin-carrier points, over every value algebra. -/
theorem map_centralizerPointsSubgroup (A : CommAlgCat.{v} R) :
    (BialgHom.centralizerPointsSubgroup
        (weightTorusToBaseChangeCoordinateMap n hn R).hom A).map
        (baseChangePointsMulEquiv n hn R A).toMonoidHom = diagonalPoints n hn A := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_centralizerPointsSubgroup_iff_isDiag,
    MulEquiv.apply_symm_apply, mem_diagonalPoints_iff]

end TauCeti.TypeDSpinCarrier
