/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ZModThree.Basic
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Basic

/-!
# Executable conjugacy-class data for `SL(2, 3)`

The special linear group `SL(2, 3) = SpecialLinearGroup (Fin 2) (ZMod 3)` has order `24` and
seven conjugacy classes.  This file gives those classes the executable numbering needed by the
Dixon--Schneider character-table algorithm.  With `z = -1`, `s = TauCeti.sl2ZModThreeI =
!![0, -1; 1, 0]` and `t = TauCeti.sl2ZModThreeT = !![1, 1; 0, 1]`, the representatives are

* the identity and the central element `z`;
* `s`, of order four, whose class consists of the six elements of order four;
* `t` and `t⁻¹`, of order three, which are not conjugate;
* `z t` and `z t⁻¹`, of order six, which are not conjugate.

The kernel evaluates the matrix arithmetic over `ZMod 3` directly, so the class data and the
structure constants are certified by `decide` on the matrix group itself.

## Main definitions

* `TauCeti.specialLinearTwoThreeClassData`: the executable seven-class numbering.

## Main results

* `TauCeti.numClasses_specialLinearTwoThreeClassData`: `SL(2, 3)` has seven conjugacy classes.
* `TauCeti.card_classFinset_specialLinearTwoThreeClassData`: their sizes, in the chosen order, are
  `1`, `1`, `6`, `4`, `4`, `4` and `4`.
* `TauCeti.exponent_specialLinearGroup_two_three`: the exponent of `SL(2, 3)` is `12`.

## References

The conjugacy classes are the case `q = 3` of those of `SL₂(𝔽_q)` in W. Fulton and J. Harris,
*Representation Theory: A First Course*, §5.2. The layout follows
`TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Alternating.Four`.
-/

public section

namespace TauCeti

open Matrix

/-- Executable conjugacy-class data for `SL(2, 3)`, ordered as `1`, `z`, `s`, `t`, `t⁻¹`, `z t`
and `z t⁻¹`. -/
@[expose] def specialLinearTwoThreeClassData :
    ClassData (SpecialLinearGroup (Fin 2) (ZMod 3)) where
  reps := [1, -1, sl2ZModThreeI, sl2ZModThreeT, sl2ZModThreeT⁻¹, -sl2ZModThreeT,
    -sl2ZModThreeT⁻¹]
  pairwise_not_isConj := by decide
  exists_isConj := by decide

/-- The representatives in the executable `SL(2, 3)` class data, in their defining order. -/
@[simp]
theorem reps_specialLinearTwoThreeClassData :
    specialLinearTwoThreeClassData.reps =
      [1, -1, sl2ZModThreeI, sl2ZModThreeT, sl2ZModThreeT⁻¹, -sl2ZModThreeT,
        -sl2ZModThreeT⁻¹] := by
  rfl

/-- **`SL(2, 3)` has seven conjugacy classes.** -/
@[simp]
theorem numClasses_specialLinearTwoThreeClassData :
    specialLinearTwoThreeClassData.numClasses = 7 := by
  rfl

/-- The representative of each numbered conjugacy class of `SL(2, 3)`. -/
@[simp]
theorem rep_specialLinearTwoThreeClassData (i : Fin specialLinearTwoThreeClassData.numClasses) :
    specialLinearTwoThreeClassData.rep i =
      ![1, -1, sl2ZModThreeI, sl2ZModThreeT, sl2ZModThreeT⁻¹, -sl2ZModThreeT,
        -sl2ZModThreeT⁻¹]
        (i.cast numClasses_specialLinearTwoThreeClassData) := by
  fin_cases i <;> rfl

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

private theorem rep_pow_twelve :
    ∀ r ∈ specialLinearTwoThreeClassData.reps, r ^ 12 = 1 := by
  decide

/-- **The exponent of `SL(2, 3)` is `12`.** -/
theorem exponent_specialLinearGroup_two_three :
    Monoid.exponent (SpecialLinearGroup (Fin 2) (ZMod 3)) = 12 := by
  apply Nat.dvd_antisymm
  -- Every element is conjugate to a representative whose twelfth power is trivial.
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro g
    obtain ⟨r, hr, hrg⟩ := specialLinearTwoThreeClassData.exists_isConj g
    exact isConj_one_right.mp (rep_pow_twelve r hr ▸ hrg.pow 12)
  -- The elements `s` and `t` have orders four and three, and `lcm 4 3 = 12`.
  · have h := Nat.lcm_dvd (Monoid.order_dvd_exponent sl2ZModThreeI)
      (Monoid.order_dvd_exponent sl2ZModThreeT)
    rwa [orderOf_sl2ZModThreeI, orderOf_sl2ZModThreeT,
      show Nat.lcm 4 3 = 12 by decide] at h

end TauCeti
