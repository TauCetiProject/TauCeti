/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Map
import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.WeightTorus

/-!
# The weight torus of the generated type-D spin group

The weight-torus coordinate map of the ground-ring-generated full-spin group is surjective,
so it defines a closed subgroup. Its differential is injective over every commutative
coefficient algebra. Neither maximality of this torus nor an identification of the generated
group with the specialization of the integral carrier is asserted.

The surjectivity proof uses the integral carrier's weight-torus calculation in
`TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.WeightTorus` and the generated subgroup's
factorization of the ambient weight-torus map.
-/

public section

open CategoryTheory

namespace TauCeti.TypeDSpinCarrier

universe u v

variable (n : ℕ) (hn : 4 ≤ n) (R : Type u) [CommRing R]

/-- The weight torus is a closed subgroup of the generated group: its coordinate map is
surjective because the full-spin weights span the character lattice. -/
theorem generatedWeightTorusCoordinateMap_surjective :
    Function.Surjective (generatedWeightTorusCoordinateMap n hn R).hom := by
  have h := (weightTorusToBaseChangeCoordinateMap_surjective n hn R).comp
    (coordinateMap_surjective n hn R)
  rw [← BialgHom.coe_comp, ← _root_.CommHopfAlgCat.hom_comp,
    coordinateMap_comp_weightTorusToBaseChangeCoordinateMap,
    ← generatedCoordinateMap_comp_generatedWeightTorusCoordinateMap] at h
  exact Function.Surjective.of_comp
    (by simpa only [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp] using h)

/-- The weight-torus differential is injective over every commutative coefficient algebra. -/
theorem derivationCompLieHom_generatedWeightTorusCoordinateMap_injective
    (B : Type v) [CommRing B] [Algebra R B] :
    Function.Injective
      (derivationCompLieHom (B := B) (generatedWeightTorusCoordinateMap n hn R).hom) :=
  derivationCompLieHom_injective_of_surjective _
    (generatedWeightTorusCoordinateMap_surjective n hn R)

end TauCeti.TypeDSpinCarrier
