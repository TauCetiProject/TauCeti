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
* `TauCeti.natCard_alternatingGroup_four`: `A₄` has order twelve.
* `TauCeti.exponent_alternatingGroup_four`: the exponent of `A₄` is six.

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

private theorem orderOf_alternatingGroupFourDoubleTransposition :
    orderOf alternatingGroupFourDoubleTransposition = 2 := by
  apply orderOf_eq_prime <;> decide

private theorem orderOf_alternatingGroupFourThreeCycle :
    orderOf alternatingGroupFourThreeCycle = 3 := by
  apply orderOf_eq_prime <;> decide

private theorem alternatingGroupFourDoubleTransposition_pow_six :
    alternatingGroupFourDoubleTransposition ^ 6 = 1 := by
  decide

private theorem alternatingGroupFourThreeCycle_pow_six :
    alternatingGroupFourThreeCycle ^ 6 = 1 := by
  decide

private theorem alternatingGroupFourThreeCycle_inv_pow_six :
    alternatingGroupFourThreeCycle⁻¹ ^ 6 = 1 := by
  decide

/-- The alternating group of degree four has order twelve: half of `4! = 24`. -/
theorem natCard_alternatingGroup_four : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

/-- The exponent of the alternating group of degree four is six. -/
theorem exponent_alternatingGroup_four :
    Monoid.exponent (alternatingGroup (Fin 4)) = 6 := by
  apply Nat.dvd_antisymm
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro g
    obtain ⟨r, hr, hrg⟩ := alternatingGroupFourClassData.exists_isConj g
    simp only [reps_alternatingGroupFourClassData, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp [isConj_one_right.mp hrg]
    · exact isConj_one_right.mp (alternatingGroupFourDoubleTransposition_pow_six ▸ hrg.pow 6)
    · exact isConj_one_right.mp (alternatingGroupFourThreeCycle_pow_six ▸ hrg.pow 6)
    · exact isConj_one_right.mp (alternatingGroupFourThreeCycle_inv_pow_six ▸ hrg.pow 6)
  · exact Nat.lcm_dvd (orderOf_alternatingGroupFourDoubleTransposition ▸
      Monoid.order_dvd_exponent alternatingGroupFourDoubleTransposition)
      (orderOf_alternatingGroupFourThreeCycle ▸
        Monoid.order_dvd_exponent alternatingGroupFourThreeCycle)

end TauCeti
