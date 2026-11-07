/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Frobenius
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.GraphAutomorphism
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.CharacterMap

/-!
# Character pullback on the doubled E₆ carrier

The graph automorphism exchanges the two minuscule summands by a signed monomial matrix.
Its action on torus parameters is precomposition with the inverse node permutation, so its
pullback on characters is precomposition with the forward permutation. The two permutations
coincide here because the diagram symmetry is an involution. Frobenius pulls characters back
by multiplication by its power. These character calculations apply over arbitrary commutative
value rings and use the torus equations of the independently constructed endomorphisms.

The character calculations follow the organization of
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.CharacterMap`, but use
the full-weight doubled carrier, not the adjoint Geck carrier.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 29.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
-/

public section

namespace TauCeti.E6DoubledMinuscule

universe v

/-- The graph automorphism pulls characters back by the inverse datum action:
precomposition with the node permutation. -/
theorem isCharacterMap_graphAutomorphismPoints (A : Type v) [CommRing A] :
    IsCharacterMap (weightTorusPoints A) (graphAutomorphismPoints A).toMonoidHom
      (LinearEquiv.funCongrLeft ℤ ℤ graphPermE6).toLinearMap := by
  refine isCharacterMap_iff.mpr fun s => ?_
  rw [MulEquiv.coe_toMonoidHom, graphAutomorphismPoints_weightTorusPoints]
  congr 1
  funext i
  have hsingle : (LinearMap.funLeft ℤ ℤ graphPermE6) (Pi.single i 1) =
      Pi.single (graphPermE6.symm i) 1 :=
    Pi.single_comp_equiv graphPermE6 i 1
  rw [torusPointMap_apply, LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply,
    hsingle, torusCharacter_single, zpow_one, graphPermE6_symm]

/-- The `p ^ k`-power Frobenius pulls characters back by multiplication by `p ^ k`. -/
theorem isCharacterMap_frobenius (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p] :
    IsCharacterMap (weightTorusPoints A) (frobenius p k A) ((p ^ k : ℕ) • 1) :=
  isCharacterMap_iff.mpr fun s => by
    rw [frobenius_weightTorusPoints, torusPointMap_nsmul, torusPointMap_one,
      MonoidHom.pow_apply, MonoidHom.id_apply]

end TauCeti.E6DoubledMinuscule
