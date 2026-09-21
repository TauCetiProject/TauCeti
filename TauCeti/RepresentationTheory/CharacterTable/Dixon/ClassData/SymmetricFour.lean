/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Basic

/-!
# Class data for the symmetric group on four letters

The conjugacy classes of `S₄ = Equiv.Perm (Fin 4)` are indexed by the five partitions of four.
This file gives one explicit permutation of each cycle type, then lets the executable
`TauCeti.ClassData` API calculate the classes and their multiplication constants.

The chosen order is the identity, a transposition, a product of two disjoint transpositions, a
three-cycle, and a four-cycle.  Thus the class sizes are `1, 6, 3, 8, 6`.  This ordering is used by
the exact character-table certificate in
`TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.SymmetricFour`.

## Main declarations

* `TauCeti.symmetricGroupFourClassData`: computable class data for `S₄`.
* `TauCeti.reps_symmetricGroupFourClassData`, `TauCeti.rep_symmetricGroupFourClassData`: the
  chosen representatives in cycle-type order.
* `TauCeti.card_classFinset_symmetricGroupFourClassData`: the five class sizes.
* `TauCeti.structureConstantTable_symmetricGroupFourClassData`: the complete class-algebra
  multiplication table.

## References

* G. James and M. Liebeck, *Representations and Characters of Groups*, Section 11.3.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

/-- **The five numbered conjugacy classes of `S₄`.**  Representatives have cycle types
`1⁴`, `2·1²`, `2²`, `3·1`, and `4`, in that order. -/
@[expose] def symmetricGroupFourClassData : ClassData (Equiv.Perm (Fin 4)) where
  reps := [1, swap 0 1, swap 0 1 * swap 2 3,
    [0, 1, 2].formPerm, [0, 1, 2, 3].formPerm]
  pairwise_not_isConj := by decide
  exists_isConj := by decide

/-- The chosen representatives of the classes of `S₄`, in the cycle-type ordering
`1⁴`, `2·1²`, `2²`, `3·1`, `4`. -/
@[simp]
theorem reps_symmetricGroupFourClassData :
    symmetricGroupFourClassData.reps =
      [1, swap 0 1, swap 0 1 * swap 2 3, [0, 1, 2].formPerm, [0, 1, 2, 3].formPerm] :=
  rfl

/-- The symmetric group on four letters has five conjugacy classes. -/
@[simp]
theorem numClasses_symmetricGroupFourClassData : symmetricGroupFourClassData.numClasses = 5 := by
  decide

/-- The representative numbered `i` is the `i`-th entry of the cycle-type ordering
`1⁴`, `2·1²`, `2²`, `3·1`, `4`. -/
@[simp]
theorem rep_symmetricGroupFourClassData (i : Fin symmetricGroupFourClassData.numClasses) :
    symmetricGroupFourClassData.rep i =
      ![1, swap 0 1, swap 0 1 * swap 2 3, [0, 1, 2].formPerm, [0, 1, 2, 3].formPerm]
        (i.cast numClasses_symmetricGroupFourClassData) := by
  fin_cases i <;> rfl

/-- **The conjugacy classes of `S₄` have sizes `1, 6, 3, 8, 6`** in the cycle-type ordering
`1⁴`, `2·1²`, `2²`, `3·1`, `4`. -/
theorem card_classFinset_symmetricGroupFourClassData :
    symmetricGroupFourClassData.classes.map Finset.card = [1, 6, 3, 8, 6] := by
  decide

/-- **The structure constants of the class algebra of `S₄`.**  The outer two indices select
the factors and the innermost list gives the coefficients of the five class sums in their
product, in the ordering `1⁴`, `2·1²`, `2²`, `3·1`, `4`. -/
theorem structureConstantTable_symmetricGroupFourClassData :
    symmetricGroupFourClassData.structureConstantTable =
      [[[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0],
          [0, 0, 0, 0, 1]],
       [[0, 1, 0, 0, 0], [6, 0, 2, 3, 0], [0, 1, 0, 0, 2], [0, 4, 0, 0, 4],
          [0, 0, 4, 3, 0]],
       [[0, 0, 1, 0, 0], [0, 1, 0, 0, 2], [3, 0, 2, 0, 0], [0, 0, 0, 3, 0],
          [0, 2, 0, 0, 1]],
       [[0, 0, 0, 1, 0], [0, 4, 0, 0, 4], [0, 0, 0, 3, 0], [8, 0, 8, 4, 0],
          [0, 4, 0, 0, 4]],
       [[0, 0, 0, 0, 1], [0, 0, 4, 3, 0], [0, 2, 0, 0, 1], [0, 4, 0, 0, 4],
          [6, 0, 2, 3, 0]]] := by
  decide

end TauCeti
