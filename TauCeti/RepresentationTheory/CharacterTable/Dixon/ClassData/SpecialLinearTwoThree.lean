/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Basic

/-!
# Executable conjugacy-class data for `SL(2, 3)`

The special linear group `SL(2, 3) = SpecialLinearGroup (Fin 2) (ZMod 3)` has order `24` and
seven conjugacy classes.  This file gives those classes the executable numbering needed by the
Dixon--Schneider character-table algorithm.  With `z = -1`, `s = !![0, 1; -1, 0]` and
`t = !![1, 1; 0, 1]`, the representatives are

* the identity and the central element `z`;
* `s`, of order four, whose class consists of the six elements of order four;
* `t` and `t⁻¹`, of order three, which are not conjugate;
* `z t` and `z t⁻¹`, of order six, which are not conjugate.

The kernel evaluates the matrix arithmetic over `ZMod 3` directly, so the class data and the
structure constants are certified by `decide` on the matrix group itself.

## Main definitions

* `TauCeti.specialLinearTwoThreeZ`, `TauCeti.specialLinearTwoThreeS` and
  `TauCeti.specialLinearTwoThreeT`: the chosen generators of the representatives.
* `TauCeti.specialLinearTwoThreeClassData`: the executable seven-class numbering.

## Main results

* `TauCeti.numClasses_specialLinearTwoThreeClassData`: `SL(2, 3)` has seven conjugacy classes.
* `TauCeti.card_classFinset_specialLinearTwoThreeClassData`: their sizes, in the chosen order, are
  `1`, `1`, `6`, `4`, `4`, `4` and `4`.
* `TauCeti.natCard_specialLinearGroup_two_three`: `SL(2, 3)` has order `24`.
* `TauCeti.exponent_specialLinearGroup_two_three`: the exponent of `SL(2, 3)` is `12`.
-/

public section

namespace TauCeti

open Matrix

/-- The central element `-1` of `SL(2, 3)`. -/
@[expose] def specialLinearTwoThreeZ : SpecialLinearGroup (Fin 2) (ZMod 3) :=
  ⟨!![2, 0; 0, 2], by decide⟩

/-- The element `!![0, 1; -1, 0]` of order four in `SL(2, 3)`. -/
@[expose] def specialLinearTwoThreeS : SpecialLinearGroup (Fin 2) (ZMod 3) :=
  ⟨!![0, 1; 2, 0], by decide⟩

/-- The unipotent element `!![1, 1; 0, 1]` of order three in `SL(2, 3)`. -/
@[expose] def specialLinearTwoThreeT : SpecialLinearGroup (Fin 2) (ZMod 3) :=
  ⟨!![1, 1; 0, 1], by decide⟩

/-- Executable conjugacy-class data for `SL(2, 3)`, ordered as `1`, `z`, `s`, `t`, `t⁻¹`, `z t`
and `z t⁻¹`. -/
@[expose] def specialLinearTwoThreeClassData :
    ClassData (SpecialLinearGroup (Fin 2) (ZMod 3)) where
  reps := [1, specialLinearTwoThreeZ, specialLinearTwoThreeS, specialLinearTwoThreeT,
    specialLinearTwoThreeT⁻¹, specialLinearTwoThreeZ * specialLinearTwoThreeT,
    specialLinearTwoThreeZ * specialLinearTwoThreeT⁻¹]
  pairwise_not_isConj := by decide
  exists_isConj := by decide

/-- The representatives in the executable `SL(2, 3)` class data, in their defining order. -/
@[simp]
theorem reps_specialLinearTwoThreeClassData :
    specialLinearTwoThreeClassData.reps =
      [1, specialLinearTwoThreeZ, specialLinearTwoThreeS, specialLinearTwoThreeT,
        specialLinearTwoThreeT⁻¹, specialLinearTwoThreeZ * specialLinearTwoThreeT,
        specialLinearTwoThreeZ * specialLinearTwoThreeT⁻¹] := by
  rfl

/-- **`SL(2, 3)` has seven conjugacy classes.** -/
@[simp]
theorem numClasses_specialLinearTwoThreeClassData :
    specialLinearTwoThreeClassData.numClasses = 7 := by
  rfl

/-- **The seven numbered conjugacy classes of `SL(2, 3)` have sizes `1`, `1`, `6`, `4`, `4`, `4`
and `4`.** -/
@[simp]
theorem card_classFinset_specialLinearTwoThreeClassData
    (i : Fin specialLinearTwoThreeClassData.numClasses) :
    (specialLinearTwoThreeClassData.classFinset i).card = ![1, 1, 6, 4, 4, 4, 4] i := by
  fin_cases i <;> decide

/-- The ordered list of conjugacy-class sizes of `SL(2, 3)` is `[1, 1, 6, 4, 4, 4, 4]`. -/
@[simp]
theorem card_classes_specialLinearTwoThreeClassData :
    specialLinearTwoThreeClassData.classes.map Finset.card = [1, 1, 6, 4, 4, 4, 4] := by
  decide

/-- **The structure constants of `SL(2, 3)`.**  This is the entire group-specific input to the
Dixon--Schneider computation. -/
theorem structureConstantTable_specialLinearTwoThreeClassData :
    specialLinearTwoThreeClassData.structureConstantTable =
      [[[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
          [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0],
          [0, 0, 0, 0, 0, 0, 1]],
        [[0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0],
          [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 0],
          [0, 0, 0, 0, 1, 0, 0]],
        [[0, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [6, 6, 4, 0, 0, 0, 0],
          [0, 0, 0, 3, 0, 3, 0], [0, 0, 0, 0, 3, 0, 3], [0, 0, 0, 3, 0, 3, 0],
          [0, 0, 0, 0, 3, 0, 3]],
        [[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 3, 0, 3, 0],
          [0, 0, 0, 0, 1, 0, 3], [4, 0, 2, 0, 0, 0, 0], [0, 0, 0, 0, 3, 0, 1],
          [0, 4, 2, 0, 0, 0, 0]],
        [[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 3, 0, 3],
          [4, 0, 2, 0, 0, 0, 0], [0, 0, 0, 1, 0, 3, 0], [0, 4, 2, 0, 0, 0, 0],
          [0, 0, 0, 3, 0, 1, 0]],
        [[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 3, 0, 3, 0],
          [0, 0, 0, 0, 3, 0, 1], [0, 4, 2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 3],
          [4, 0, 2, 0, 0, 0, 0]],
        [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 3, 0, 3],
          [0, 4, 2, 0, 0, 0, 0], [0, 0, 0, 3, 0, 1, 0], [4, 0, 2, 0, 0, 0, 0],
          [0, 0, 0, 1, 0, 3, 0]]] := by
  decide +kernel

private theorem orderOf_specialLinearTwoThreeS : orderOf specialLinearTwoThreeS = 4 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 1) <;> decide

private theorem orderOf_specialLinearTwoThreeT : orderOf specialLinearTwoThreeT = 3 := by
  apply orderOf_eq_prime <;> decide

private theorem rep_pow_twelve :
    ∀ r ∈ specialLinearTwoThreeClassData.reps, r ^ 12 = 1 := by
  decide

/-- `SL(2, 3)` has order `24`. -/
theorem natCard_specialLinearGroup_two_three :
    Nat.card (SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- **The exponent of `SL(2, 3)` is `12`**: every element is conjugate to a representative whose
twelfth power is trivial, and the elements `s` and `t` have orders four and three. -/
theorem exponent_specialLinearGroup_two_three :
    Monoid.exponent (SpecialLinearGroup (Fin 2) (ZMod 3)) = 12 := by
  apply Nat.dvd_antisymm
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro g
    obtain ⟨r, hr, hrg⟩ := specialLinearTwoThreeClassData.exists_isConj g
    exact isConj_one_right.mp (rep_pow_twelve r hr ▸ hrg.pow 12)
  · exact Nat.lcm_dvd (orderOf_specialLinearTwoThreeS ▸
      Monoid.order_dvd_exponent specialLinearTwoThreeS)
      (orderOf_specialLinearTwoThreeT ▸ Monoid.order_dvd_exponent specialLinearTwoThreeT)

end TauCeti
