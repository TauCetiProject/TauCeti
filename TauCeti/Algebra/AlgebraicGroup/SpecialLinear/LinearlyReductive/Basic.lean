/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.CompleteReducibility
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Connected
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent.Basic
public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.Killing
import TauCeti.Algebra.Lie.GeneralLinear.Radical

/-!
# Complete reducibility for special linear groups in characteristic zero

In characteristic zero, the Lie algebra of `SLₙ` is semisimple: its tangent Lie algebra is
`slₙ`, and Mathlib's Cartan criterion turns the vanishing of its solvable radical into a
nondegenerate Killing form. Weyl's complete reducibility theorem for comodules then proves that
every finite-dimensional representation of `SLₙ` is completely reducible.

This is a concrete case of, but does not prove, the general equivalence between reductivity and
linear reductivity in characteristic zero.

## Main declaration

* `TauCeti.SpecialLinear.linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra`:
  the coordinate Hopf algebra of `SLₙ` is linearly reductive in characteristic zero.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §13.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §6, for Cartan's criterion.
-/

public section

namespace TauCeti

namespace SpecialLinear

universe u

variable (k : Type u) [Field k] [CharZero k]

/-- The tangent Lie algebra of `SLₙ` has nondegenerate Killing form in characteristic zero. -/
instance (n : ℕ) : LieAlgebra.IsKilling k
    (Derivation k (coordinateHopfAlgebra k n)
      (Bialgebra.CounitAlgebra k (coordinateHopfAlgebra k n) k)) :=
  LieEquiv.isKilling (tangentLieEquivSl (R := k) (B := k) n).symm

/-- **`SLₙ` is linearly reductive in characteristic zero.** Every finite-dimensional comodule
over its coordinate Hopf algebra is completely reducible. -/
theorem linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra (n : ℕ) :
    linearlyReductiveCommHopfAlgProperty k (coordinateHopfAlgebra k n) :=
  linearlyReductiveCommHopfAlgProperty.of_finiteType_of_connected_of_isKilling
    (by rw [← finiteTypeCoordinateHopfAlgebra_obj]
        exact (finiteTypeCoordinateHopfAlgebra k n).property)
    (SpecialLinear.geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k n)

end SpecialLinear

end TauCeti
