/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generated.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Centralizer

/-!
# The schematic weight-torus centralizer in the generated type-B spin carrier

The centralizer of the weight torus in the generated type-`Bₙ₊₁` spin subgroup consists
exactly of the diagonal spin matrices, over every commutative base ring and value algebra.
Schematic centralization tests all extensions of the value algebra, rather than just its
rational torus points. Distinct integral spin weights therefore suffice even over finite
fields and nonreduced rings.

The membership criterion `mem_centralizerPointsSubgroup_iff_isDiag` and subgroup equality
`centralizerPointsSubgroup_eq_comap_diagonalTorus` reduce recognition of the torus centralizer
to identifying the diagonal intersection of the generated carrier. That intersection is not
identified here with the weight torus; neither torus maximality nor agreement with the
specialized integral carrier or an independently pinned simply connected group is asserted.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§16 and 26.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* The argument follows the generated E₇ centralizer computation in
  `TauCeti.Algebra.Lie.E7.Minuscule.Generated.TorusCentralizer`, using the general
  `BialgHom.centralizerHopfIdeal_comp_le_ker_iff` and
  `GeneralLinear.centralizerHopfIdeal_weightTorus_le_ker_iff_isDiag`.
-/

public section

open CategoryTheory

namespace TauCeti.TypeBSpinCarrier

universe u v

variable (n : ℕ) (R : Type u) [CommRing R]

/-- A point of the generated type-`Bₙ₊₁` spin carrier centralizes the weight torus
scheme-theoretically exactly when its spin matrix is diagonal. No infinitude or reducedness
hypothesis is imposed on the value algebra. -/
@[simp↓]
theorem mem_centralizerPointsSubgroup_iff_isDiag (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (R := R) (H := generatedCoordinateHopfAlgebra n R) A) :
    g ∈ BialgHom.centralizerPointsSubgroup (generatedWeightTorusCoordinateMap n R).hom A ↔
      (GeneralLinear.pointsMulEquiv (dimension n)
        (BialgHom.mapDomain (generatedCoordinateMap n R).hom g) :
          Matrix (Fin (dimension n)) (Fin (dimension n)) A).IsDiag := by
  exact BialgHom.mem_centralizerPointsSubgroup_iff_isDiag_of_comp
    (generatedCoordinateMap n R).hom (generatedCoordinateMap_surjective n R)
    (generatedWeightTorusCoordinateMap n R).hom (basisWeight n)
    (fun _ _ h ↦ basisCharacter_injective n (congrArg SplitTorus.weightCharacter h))
    (by rw [← CommHopfAlgCat.hom_comp,
      generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]) A g

/-- Over every value algebra, the schematic weight-torus centralizer is the inverse image
of the full diagonal torus under the generated spin carrier's closed matrix embedding. -/
theorem centralizerPointsSubgroup_eq_comap_diagonalTorus (A : CommAlgCat.{v} R) :
    BialgHom.centralizerPointsSubgroup (generatedWeightTorusCoordinateMap n R).hom A =
      (diagonalTorus A (dimension n)).comap
        ((GeneralLinear.pointsMulEquiv (R := R) (dimension n)).toMonoidHom.comp
          (BialgHom.mapDomain (generatedCoordinateMap n R).hom)) := by
  exact BialgHom.centralizerPointsSubgroup_eq_comap_diagonalTorus_of_comp
    (generatedCoordinateMap n R).hom (generatedCoordinateMap_surjective n R)
    (generatedWeightTorusCoordinateMap n R).hom (basisWeight n)
    (fun _ _ h ↦ basisCharacter_injective n (congrArg SplitTorus.weightCharacter h))
    (by rw [← CommHopfAlgCat.hom_comp,
      generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap,
      GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]) A

end TauCeti.TypeBSpinCarrier
