/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Tangent

/-!
# Tangent equations of symplectic weight-parabolic intersections

Intersecting the symplectic group with a general-linear weight parabolic cuts out the
filtration-preserving symplectic tangent matrices. The equations are stated in paired
coordinates, so the same criterion can be used for self-dual flag orders rather than
mistakenly imposing upper triangularity in the original paired basis order.

On coordinate rings the intersection is the image of the general-linear parabolic's
Hopf ideal under the symplectic quotient map. The calculation uses
`HopfIdeal.lieSubalgebra_map` and the general-linear weight-parabolic tangent criterion.
It requires neither smoothness of the intersection nor a reduced coefficient ring.
These tangent equations determine containment of adjoint root spaces in flag stabilizers.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 24.6.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
-/

public section

namespace TauCeti.Symplectic

universe u v

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
  {m : ℕ}

/-- A symplectic tangent vector belongs to the inverse image of a general-linear weight
parabolic precisely when its paired matrix preserves the induced weight filtration.
The weights can encode any order, including the complete self-dual flag order. -/
theorem mem_lieSubalgebra_map_weightParabolicDefiningHopfIdeal_iff
    (w : Fin (m + m) → ℤ)
    (d : Derivation R (coordinateHopfAlgebra R m)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R m) B)) :
    d ∈ HopfIdeal.lieSubalgebra (B := B)
        ((GeneralLinear.weightParabolicDefiningHopfIdeal R w).map (coordinateMap R m).hom) ↔
      (tangentMatrix m d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) B).BlockTriangular
        (OrderDual.toDual ∘ w ∘ finSumFinEquiv) := by
  rw [GeneralLinear.mem_lieSubalgebra_map_weightParabolicDefiningHopfIdeal_iff,
    coordinateMap_def, CommHopfAlgCat.hom_mkQuotient,
    derivationCompLieHom_apply, ← HopfIdeal.quotientLieHom_apply, tangentMatrix_apply_coe]
  simpa only [Matrix.reindex_apply, Equiv.symm_symm, Function.comp_assoc,
    Equiv.self_comp_symm, Function.comp_id] using
    (Matrix.blockTriangular_reindex_iff
      (M := GeneralLinear.tangentMatrix (m + m)
        (HopfIdeal.quotientLieHom (definingHopfIdeal R m) d))
      (e := finSumFinEquiv.symm)
      (b := OrderDual.toDual ∘ w ∘ finSumFinEquiv)).symm

end TauCeti.Symplectic
