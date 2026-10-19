/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.CompleteReducibility
public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Basic
public import Mathlib.Algebra.Lie.Killing
import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.LinearlyReductive
import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.LinearlyReductive.Basic
import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Connected
import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.LowRank
import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Tangent
import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Torus
import TauCeti.Algebra.Lie.Orthogonal.Killing

/-!
# Complete reducibility for special orthogonal groups in characteristic zero

In characteristic zero every finite-dimensional representation of the standard special orthogonal
group `SOₙ` is completely reducible, in every dimension.

From dimension three on, the argument is Lie-algebraic. The tangent Lie algebra of `SOₙ` is
Mathlib's `LieAlgebra.Orthogonal.so (Fin n) k`, which has trivial radical
(`TauCeti.hasTrivialRadical_so`) and hence nondegenerate Killing form. Since `SOₙ` is
geometrically connected, Weyl's complete reducibility theorem for comodules applies.

The irreducibility of the standard module behind this needs `n ≥ 3`, and dimension two is
genuinely different: `so₂` is a nonzero abelian Lie algebra in characteristic zero, so its Killing
form vanishes. The low dimensions are covered by existing results instead: `SO₀` and `SO₁` are the
special linear groups `SL₀` and `SL₁`, and `SO₂` is a torus.

This is a concrete case of, but does not prove, the general equivalence between reductivity and
linear reductivity in characteristic zero.

The argument follows the symplectic case in
`TauCeti/Algebra/AlgebraicGroup/Symplectic/LinearlyReductive.lean`
(`TauCeti.Symplectic.linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra`), with the
orthogonal Lie algebra in place of `sp₂ₘ`.

## Main declarations

* `TauCeti.SpecialOrthogonal.isKilling_tangent_of_three_le`: the tangent Lie algebra of `SOₙ` has
  nondegenerate Killing form in characteristic zero, for `n ≥ 3`.
* `TauCeti.SpecialOrthogonal.linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra`:
  the coordinate Hopf algebra of `SOₙ` is linearly reductive in characteristic zero.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §13.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §6, for Cartan's criterion.
-/

public section

namespace TauCeti

namespace SpecialOrthogonal

universe u

variable (k : Type u) [Field k] [CharZero k]

/-- The tangent Lie algebra of `SOₙ` has nondegenerate Killing form in characteristic zero, in
dimension at least three. -/
theorem isKilling_tangent_of_three_le (n : ℕ) (hn : 3 ≤ n) :
    LieAlgebra.IsKilling k
      (Derivation k (coordinateHopfAlgebra k n)
        (Bialgebra.CounitAlgebra k (coordinateHopfAlgebra k n) k)) := by
  let : Invertible (2 : k) := invertibleOfNonzero two_ne_zero
  have : LieAlgebra.HasTrivialRadical k (LieAlgebra.Orthogonal.so (Fin n) k) :=
    hasTrivialRadical_so k (by rwa [Fintype.card_fin])
  exact LieEquiv.isKilling (tangentLieEquivSo (R := k) (B := k) n).symm

/-- **`SOₙ` is linearly reductive in characteristic zero**, in every dimension. Every
finite-dimensional comodule over its coordinate Hopf algebra is completely reducible.

`SO₀` and `SO₁` are special linear and `SO₂` is a torus; from dimension three on the Killing form
of the tangent Lie algebra is nondegenerate. -/
theorem linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra (n : ℕ) :
    linearlyReductiveCommHopfAlgProperty k (coordinateHopfAlgebra k n) := by
  rw [← finiteTypeCoordinateHopfAlgebra_obj]
  match n with
  | 0 =>
    rw [finiteTypeCoordinateHopfAlgebra_zero, SpecialLinear.finiteTypeCoordinateHopfAlgebra_obj]
    exact SpecialLinear.linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra k 0
  | 1 =>
    rw [finiteTypeCoordinateHopfAlgebra_one, SpecialLinear.finiteTypeCoordinateHopfAlgebra_obj]
    exact SpecialLinear.linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra k 1
  | 2 => exact (torusCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra_two k).linearlyReductive
  | m + 3 =>
    have := isKilling_tangent_of_three_le k (m + 3) (by omega)
    rw [finiteTypeCoordinateHopfAlgebra_obj]
    exact linearlyReductiveCommHopfAlgProperty.of_finiteType_of_connected_of_isKilling
      (by rw [← finiteTypeCoordinateHopfAlgebra_obj]
          exact (finiteTypeCoordinateHopfAlgebra k (m + 3)).property)
      (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k (m + 3))

end SpecialOrthogonal

end TauCeti
