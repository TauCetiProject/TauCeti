/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.Partition.Conjugate
public import TauCeti.RepresentationTheory.Symmetric.Specht.ConjugateTable
public import TauCeti.RepresentationTheory.Symmetric.Specht.SingletonSecondRow

/-!
# The sign-transpose identity on the character tables of `S₃` and `S₄`

Checks of `TauCeti.spechtChar_conjugate` and its consequences in
`TauCeti.RepresentationTheory.Symmetric.Specht.ConjugateTable` on small symmetric groups.

* On three letters the shape `(2, 1)` is its own conjugate, so its character vanishes on the
  transposition, and the row involution of the complex character table fixes its row. Its value
  at the identity is the degree `2`.
* On four letters the conjugate of `(3, 1)` is `(2, 1, 1)`. On the representatives
  `1, (0 1), (0 1)(2 3), (0 1 2), (0 1 2 3)` of the classes `1⁴, 2·1², 2², 3·1, 4`, the row of
  `(2, 1, 1)` is the row of `(3, 1)` times the signs `1, -1, 1, 1, -1`.

Both conjugates are read off the conjugate `(2, 1ⁿ)` of the shape `(n + 1, 1)`
(`TauCeti.Nat.Partition.conjugate_parts_singletonSecondRow`).
-/

public section

namespace TauCeti.Examples

open TauCeti.Nat.Partition (conjugate_parts_singletonSecondRow conjugate_singletonSecondRow_one
  singletonSecondRow)

/-! ### Three letters -/

/-- The character of `S^((2,1))` vanishes on the transposition `(0 1)`. -/
example : spechtChar (singletonSecondRow 1) (Equiv.swap 0 1) = 0 :=
  spechtChar_eq_zero_of_conjugate_eq conjugate_singletonSecondRow_one
    (Equiv.Perm.sign_swap (by decide))

/-- The degree of `S^((2,1))` is `2`. -/
example : spechtChar (singletonSecondRow 1) 1 = 2 := by
  rw [spechtChar_one, finrank_spechtModule_singletonSecondRow]
  norm_num

/-- The row involution of the complex character table of `S₃` fixes the row of `χ^((2,1))`. -/
example :
    conjugateIrreducibleIndex 3 (partitionEquivIrreducibleIndex 3 (singletonSecondRow 1)) =
      partitionEquivIrreducibleIndex 3 (singletonSecondRow 1) := by
  rw [conjugateIrreducibleIndex_partitionEquivIrreducibleIndex, conjugate_singletonSecondRow_one]

/-! ### Four letters -/

/-- The conjugate of the shape `(3, 1)` of `4` is `(2, 1, 1)`. -/
theorem conjugate_singletonSecondRow_two_parts :
    (singletonSecondRow 2).conjugate.parts = {2, 1, 1} := by
  rw [conjugate_parts_singletonSecondRow]
  rfl

/-- The degree of `S^((2,1,1))` is `3`, that of `S^((3,1))`. -/
example : spechtChar (singletonSecondRow 2).conjugate 1 = 3 := by
  rw [spechtChar_conjugate, spechtChar_one, finrank_spechtModule_singletonSecondRow]
  norm_num

/-- On the class `2·1²`, the row of `(2, 1, 1)` is minus the row of `(3, 1)`. -/
example : spechtChar (singletonSecondRow 2).conjugate (Equiv.swap 0 1) =
    -spechtChar (singletonSecondRow 2) (Equiv.swap 0 1) := by
  rw [spechtChar_conjugate, Equiv.Perm.sign_swap (by decide)]
  simp

/-- On the class `2²`, the rows of `(2, 1, 1)` and `(3, 1)` agree. -/
example :
    spechtChar (singletonSecondRow 2).conjugate (Equiv.swap 0 1 * Equiv.swap 2 3) =
      spechtChar (singletonSecondRow 2) (Equiv.swap 0 1 * Equiv.swap 2 3) := by
  have hsign : Equiv.Perm.sign (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) = 1 := by
    decide
  rw [spechtChar_conjugate, hsign]
  simp

/-- On the class `3·1`, the rows of `(2, 1, 1)` and `(3, 1)` agree. -/
example :
    spechtChar (singletonSecondRow 2).conjugate (Equiv.swap 0 1 * Equiv.swap 1 2) =
      spechtChar (singletonSecondRow 2) (Equiv.swap 0 1 * Equiv.swap 1 2) := by
  have hsign : Equiv.Perm.sign (Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) = 1 := by
    decide
  rw [spechtChar_conjugate, hsign]
  simp

/-- On the class `4`, the row of `(2, 1, 1)` is minus the row of `(3, 1)`. -/
example : spechtChar (singletonSecondRow 2).conjugate (finRotate 4) =
    -spechtChar (singletonSecondRow 2) (finRotate 4) := by
  have hsign : Equiv.Perm.sign (finRotate 4) = -1 := by decide
  rw [spechtChar_conjugate, hsign]
  simp

end TauCeti.Examples
