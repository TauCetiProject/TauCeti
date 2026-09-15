/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.DerivationEntry
public import TauCeti.Algebra.Lie.F4.ShortRoot.QuotientCoordinates

/-!
# Coordinates along the short-root ideal of type F4

Modulo two the twenty-six matrices of `TauCeti.F4ShortRoot.quotientMatrix` and the twenty-six
multiplication operators of `TauCeti.F4ShortRoot.multiplicationOperator` are linearly independent,
and fifty of the fifty-two have a matrix position at which they alone are nonzero. In particular
each multiplication operator has such a position, so a single matrix entry reads off the
coefficient of that operator in any combination of the fifty-two. This file tabulates those
positions and records the two duality statements that make them coordinates: a multiplication
operator is odd at its own position and even at the position of another, and every representing
matrix is even at every one of them.

The remaining two of the fifty-two, the representing matrices of the two zero weights, have no
private position; their coordinates are the two-term functionals
`TauCeti.F4ShortRoot.quotientCoordinate`, which are recorded here entry by entry.

No independence or spanning statement is proved here, and the two families are not related to any
Lie algebra.

## Main definitions

* `TauCeti.F4ShortRoot.idealRow` and `TauCeti.F4ShortRoot.idealCol`: the position private to each
  multiplication operator.

## Main results

* `TauCeti.F4ShortRoot.multiplicationOperator_ideal`: the multiplication operators are dual
  modulo two to the private positions.
* `TauCeti.F4ShortRoot.quotientMatrix_ideal`: the representing matrices are even at every private
  position.
* `TauCeti.F4ShortRoot.quotientCoordinate_entries`: the vanishing of the short-root quotient
  coordinates, entry by entry.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [CommRing R]

/-- The row of the matrix position at which, among the twenty-six representing matrices and the
twenty-six multiplication operators, only the `a`th multiplication operator is odd. -/
@[expose] def idealRow : Fin 26 → Fin 26 :=
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 10, 0, 2, 1, 3, 2, 4, 3, 4, 5, 6, 8, 10, 12]

/-- The column of that matrix position. -/
@[expose] def idealCol : Fin 26 → Fin 26 :=
  ![13, 10, 8, 6, 5, 4, 3, 4, 2, 3, 1, 2, 10, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0]

/-- **The multiplication operators are dual modulo two to their private positions.** -/
theorem multiplicationOperator_ideal (a b : Fin 26) :
    multiplicationOperator b (idealRow a) (idealCol a) ≡ (if a = b then 1 else 0) [ZMOD 2] := by
  rw [multiplicationOperator_apply]
  revert a b
  decide +kernel

/-- **The representing matrices are even at every private position of a multiplication
operator.** -/
theorem quotientMatrix_ideal (q a : Fin 26) :
    quotientMatrix q (idealRow a) (idealCol a) ≡ 0 [ZMOD 2] := by
  rw [quotientMatrix_apply]
  revert q a
  decide +kernel

/-- **The vanishing of the short-root quotient coordinates, entry by entry.** -/
theorem quotientCoordinate_entries {X : Matrix (Fin 26) (Fin 26) R}
    (h : ∀ p, quotientCoordinate p X = 0) (p : Fin 26) :
    ((coordinateCoeff 0 p : ℤ) : R) * X (coordinateRow 0 p) (coordinateCol 0 p) +
      ((coordinateCoeff 1 p : ℤ) : R) * X (coordinateRow 1 p) (coordinateCol 1 p) = 0 := by
  rw [← quotientCoordinate_def]
  exact h p

end TauCeti.F4ShortRoot
