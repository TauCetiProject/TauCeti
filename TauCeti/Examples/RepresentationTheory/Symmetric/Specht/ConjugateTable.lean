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

Both conjugates are read off the conjugate `(2, 1ⁿ)` of the shape `(n + 1, 1)`, whose columns are
counted by `Nat.Partition.sum_map_conjugate_parts`.
-/

public section

namespace TauCeti.Examples

open TauCeti.Nat.Partition (singletonSecondRow singletonSecondRow_parts)

/-- **The conjugate of the shape `(n + 1, 1)` is `(2, 1ⁿ)`**: the first column of `(n + 1, 1)` has
two cells and each of the next `n` columns has one. -/
theorem conjugate_parts_singletonSecondRow (n : ℕ) :
    (singletonSecondRow n).conjugate.parts = 2 ::ₘ Multiset.replicate n 1 := by
  ext j
  rcases eq_or_ne j 0 with rfl | hj
  · rw [Multiset.count_eq_zero.mpr fun h ↦ (Nat.Partition.parts_pos _ h).ne' rfl,
      Multiset.count_eq_zero.mpr (by simp [Multiset.mem_replicate])]
  -- Count the multiplicity of `j` as the sum of its indicator, the form of a column count.
  have hcount (s : Multiset ℕ) : s.count j = (s.map fun x ↦ if x = j then 1 else 0).sum := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      rcases eq_or_ne a j with rfl | h
      · simp [ih, add_comm]
      · simp [h, h.symm, ih]
  rw [hcount, hcount, Nat.Partition.sum_map_conjugate_parts _ _ (by simp [hj.symm]) (m := n + 1)
    (by simp [singletonSecondRow_parts]), Finset.sum_range_succ']
  have hk (k : ℕ) (hk : k ∈ Finset.range n) :
      ((singletonSecondRow n).parts.filter (k + 1 < ·)).card = 1 := by
    simp [singletonSecondRow_parts, Finset.mem_range.mp hk]
  rw [Finset.sum_congr rfl fun k hk' ↦ by rw [hk k hk']]
  simp [singletonSecondRow_parts, Multiset.filter_singleton, add_comm]

/-! ### Three letters -/

/-- The shape `(2, 1)` of `3` is its own conjugate. -/
theorem conjugate_singletonSecondRow_one :
    (singletonSecondRow 1).conjugate = singletonSecondRow 1 := by
  ext1
  rw [conjugate_parts_singletonSecondRow, singletonSecondRow_parts]
  rfl

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
