/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.CompleteReducibility
public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Basic
public import Mathlib.Algebra.Lie.Killing
import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Connected
import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Tangent
import TauCeti.Algebra.Lie.Orthogonal.Killing

/-!
# Complete reducibility for special orthogonal groups in characteristic zero

In characteristic zero and dimension `n ≥ 3`, the Lie algebra of `SOₙ` has nondegenerate Killing
form. Over an algebraic closure `K` of the base field, the tangent Lie algebra of the base-changed
group is Mathlib's `LieAlgebra.Orthogonal.so (Fin n) K`, whose standard module is faithful,
irreducible and trace-free, so its Killing form is nondegenerate; this descends to the base field.
Since `SOₙ` is geometrically connected, Weyl's complete reducibility theorem for comodules then
proves that every finite-dimensional representation of `SOₙ` is completely reducible.

The bound `n ≥ 3` is needed for the Lie-algebraic argument: `so₂` is abelian, so its Killing
form vanishes.

This is a concrete case of, but does not prove, the general equivalence between reductivity and
linear reductivity in characteristic zero.

The argument follows the symplectic case in
`TauCeti/Algebra/AlgebraicGroup/Symplectic/LinearlyReductive.lean`
(`TauCeti.Symplectic.linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra`), with the
orthogonal Lie algebra in place of `sp₂ₘ`.

## Main declarations

* `TauCeti.SpecialOrthogonal.isKilling_tangent`: the tangent Lie algebra of `SOₙ` has
  nondegenerate Killing form in characteristic zero, for `n ≥ 3`.
* `TauCeti.SpecialOrthogonal.linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra`:
  the coordinate Hopf algebra of `SOₙ` is linearly reductive in characteristic zero, for
  `n ≥ 3`.

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
theorem isKilling_tangent (n : ℕ) (hn : 3 ≤ n) :
    LieAlgebra.IsKilling k
      (Derivation k (coordinateHopfAlgebra k n)
        (Bialgebra.CounitAlgebra k (coordinateHopfAlgebra k n) k)) := by
  let K := AlgebraicClosure k
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  have : LieAlgebra.HasTrivialRadical K (LieAlgebra.Orthogonal.so (Fin n) K) :=
    hasTrivialRadical_so K (by rw [Fintype.card_fin]; omega)
  refine (isKilling_lie_baseChange_iff (K := K)).1 ?_
  exact LieAlgebra.isKilling_of_equiv
    ((tangentBaseChangeLieEquiv (R := k) (K := K)).symm.trans
      (tangentLieEquivSo (R := k) (B := K) n)).symm

/-- **`SOₙ` is linearly reductive in characteristic zero**, in dimension at least three. Every
finite-dimensional comodule over its coordinate Hopf algebra is completely reducible. -/
theorem linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra (n : ℕ) (hn : 3 ≤ n) :
    linearlyReductiveCommHopfAlgProperty k (coordinateHopfAlgebra k n) := by
  -- The packaged quotient carries structure instances that cannot be transported across
  -- `finiteTypeCoordinateHopfAlgebra_obj`; this wrapper keeps its object definitionally equal
  -- to the coordinate Hopf algebra while reusing the existing finite-type property.
  let H : FiniteTypeCommHopfAlgCat k :=
    ⟨coordinateHopfAlgebra k n, by
      rw [← finiteTypeCoordinateHopfAlgebra_obj]
      exact (finiteTypeCoordinateHopfAlgebra k n).property⟩
  have hconnected : geometricallyConnectedCommHopfAlgProperty k H.obj :=
    geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k n
  exact @linearlyReductiveCommHopfAlgProperty.of_geometricallyConnected_of_isKilling k _ _ H
    (isKilling_tangent k n hn) hconnected

end SpecialOrthogonal

end TauCeti
