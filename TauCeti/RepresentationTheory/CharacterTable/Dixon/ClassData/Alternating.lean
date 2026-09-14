/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Basic

/-!
# Executable conjugacy-class data for the alternating group of degree four

The alternating group `A₄` has four conjugacy classes: the identity, the three double
transpositions, and two classes of four three-cycles.  This file gives those classes the executable
numbering needed by the Dixon--Schneider character-table algorithm.  The representatives are

* the identity;
* `(0 1)(2 3)`;
* the cycle `(0 1 2)`;
* its inverse `(0 2 1)`.

The two classes of three-cycles are distinct in `A₄`, although they fuse in the symmetric group.
Their separation is the source of the conjugate pair of nontrivial linear characters in the
cyclotomic character table.

## Main definitions

* `TauCeti.alternatingGroupFourDoubleTransposition` and
  `TauCeti.alternatingGroupFourThreeCycle`: the chosen nonidentity representatives.
* `TauCeti.alternatingGroupFourClassData`: the executable four-class numbering.

## Main results

* `TauCeti.numClasses_alternatingGroupFourClassData`: `A₄` has four conjugacy classes.
* `TauCeti.card_classFinset_alternatingGroupFourClassData`: their sizes, in the chosen order, are
  `1`, `3`, `4`, and `4`.

## References

See J.-P. Serre, *Linear Representations of Finite Groups*, §5.2.
-/

public section

namespace TauCeti

open Equiv

/-- The double transposition `(0 1)(2 3)` in `A₄`. -/
@[expose] def alternatingGroupFourDoubleTransposition : alternatingGroup (Fin 4) :=
  ⟨Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3, by simp⟩

/-- The three-cycle `(0 1 2)` in `A₄`. -/
@[expose] def alternatingGroupFourThreeCycle : alternatingGroup (Fin 4) :=
  ⟨Fin.cycleRange 2, by simp⟩

/-- Executable conjugacy-class data for `A₄`, ordered as the identity, the double
transpositions, one class of three-cycles, and the inverse class of three-cycles. -/
@[expose] def alternatingGroupFourClassData : ClassData (alternatingGroup (Fin 4)) where
  reps := [1, alternatingGroupFourDoubleTransposition, alternatingGroupFourThreeCycle,
    alternatingGroupFourThreeCycle⁻¹]
  pairwise_not_isConj := by decide
  exists_isConj := by decide

/-- The representatives in the executable `A₄` class data, in their defining order. -/
@[simp]
theorem reps_alternatingGroupFourClassData :
    alternatingGroupFourClassData.reps =
      [1, alternatingGroupFourDoubleTransposition, alternatingGroupFourThreeCycle,
        alternatingGroupFourThreeCycle⁻¹] := by
  rfl

/-- The alternating group of degree four has four conjugacy classes. -/
@[simp]
theorem numClasses_alternatingGroupFourClassData :
    alternatingGroupFourClassData.numClasses = 4 := by
  rfl

/-- The four numbered conjugacy classes of `A₄` have sizes `1`, `3`, `4`, and `4`. -/
@[simp]
theorem card_classFinset_alternatingGroupFourClassData
    (i : Fin alternatingGroupFourClassData.numClasses) :
    (alternatingGroupFourClassData.classFinset i).card = ![1, 3, 4, 4] i := by
  fin_cases i <;> decide

/-- The ordered list of conjugacy-class sizes of `A₄` is `[1, 3, 4, 4]`. -/
@[simp]
theorem card_classes_alternatingGroupFourClassData :
    alternatingGroupFourClassData.classes.map Finset.card = [1, 3, 4, 4] := by
  decide

end TauCeti
