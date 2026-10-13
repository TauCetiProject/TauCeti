/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.CompleteReducibility
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Basic
public import Mathlib.Algebra.Lie.Killing
import TauCeti.Algebra.AlgebraicGroup.Symplectic.Connected
import TauCeti.Algebra.AlgebraicGroup.Symplectic.Tangent.Basic
import TauCeti.Algebra.Lie.Symplectic.Killing

/-!
# Complete reducibility for symplectic groups in characteristic zero

In characteristic zero, the Lie algebra of `Sp₂ₘ` has nondegenerate Killing form. Over an
algebraic closure `K` of the base field, the tangent Lie algebra of the base-changed group is
Mathlib's `LieAlgebra.Symplectic.sp (Fin m) K`, whose standard module is faithful, irreducible
and trace-free, so its Killing form is nondegenerate; this descends to the base field. Since
`Sp₂ₘ` is geometrically connected, Weyl's complete reducibility theorem for comodules then proves
that every finite-dimensional representation of `Sp₂ₘ` is completely reducible.

This is a concrete case of, but does not prove, the general equivalence between reductivity and
linear reductivity in characteristic zero.

The argument follows the special-linear case in
`TauCeti/Algebra/AlgebraicGroup/SpecialLinear/LinearlyReductive.lean`
(`TauCeti.SpecialLinear.linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra`), with the
symplectic Lie algebra in place of `slₙ`.

## Main declaration

* `TauCeti.Symplectic.linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra`:
  the coordinate Hopf algebra of `Sp₂ₘ` is linearly reductive in characteristic zero.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §13.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §6, for Cartan's criterion.
-/

public section

namespace TauCeti

namespace Symplectic

universe u

variable (k : Type u) [Field k] [CharZero k]

/-- The tangent Lie algebra of `Sp₂ₘ` has nondegenerate Killing form in characteristic zero. -/
instance (m : ℕ) : LieAlgebra.IsKilling k
    (Derivation k (coordinateHopfAlgebra k m)
      (Bialgebra.CounitAlgebra k (coordinateHopfAlgebra k m) k)) := by
  let K := AlgebraicClosure k
  refine (isKilling_lie_baseChange_iff (K := K)).1 ?_
  exact LieAlgebra.isKilling_of_equiv
    ((tangentBaseChangeLieEquiv (R := k) (K := K)).symm.trans
      (tangentLieEquivSp (R := k) (B := K) m)).symm

/-- **`Sp₂ₘ` is linearly reductive in characteristic zero.** Every finite-dimensional comodule
over its coordinate Hopf algebra is completely reducible. -/
theorem linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra (m : ℕ) :
    linearlyReductiveCommHopfAlgProperty k (coordinateHopfAlgebra k m) :=
  linearlyReductiveCommHopfAlgProperty.of_finiteType_of_connected_of_isKilling
    (by rw [← finiteTypeCoordinateHopfAlgebra_obj]
        exact (finiteTypeCoordinateHopfAlgebra k m).property)
    (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k m)

end Symplectic

end TauCeti
