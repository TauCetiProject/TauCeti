/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Adjoint.Comodule

/-!
# Entrywise classification of special-linear adjoint weights

A nonzero matrix entry of an adjoint weight vector of `SL_{r+1}` determines its
character as the difference of the corresponding diagonal torus weights. This
entrywise criterion holds over every commutative base ring and supplies the
classification of the full root set in
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Root.Adjoint`.

Weight membership is tested by the torus coaction, so it retains information that
rational points alone may lose over rings with nilpotents or in positive characteristic.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1 and Example 21.2.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* The entrywise argument follows
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Classification`.
-/

public section

namespace TauCeti.SpecialLinear

universe u

noncomputable section

variable {R : Type u} [CommRing R] {r : ℕ}

/-- A nonzero entry of an adjoint weight vector determines its character, over any
commutative base ring. -/
theorem weightCharacter_eq_of_mem_adjointWeightSpace_of_apply_ne_zero
    {α : Multiplicative (ULift.{u} (Fin r) →₀ ℤ)}
    {x : Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra R (r + 1)))}
    (hx : x ∈ Derivation.adjointWeightSpace (diagonalTorusCoordinateMap r R).hom α)
    {i j : Fin (r + 1)}
    (hentry : (tangentMatrix (r + 1) (Derivation.cotangentLinearEquiv (B := R) x) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) R) i j ≠ 0) :
    SplitTorus.weightCharacter (diagonalTorusWeight r i - diagonalTorusWeight r j) = α := by
  by_contra hweight
  exact hentry ((mem_adjointWeightSpace_iff α x).mp hx i j hweight)

end

end TauCeti.SpecialLinear
