/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
# Basic facts about the discriminant of a number field

The discriminant of a number field is a nonzero integer (Mathlib's `NumberField.discr_ne_zero`), so
its absolute value is strictly positive and a nonzero natural number. Recording the `NeZero`
instances and absolute-value positivity lemmas lets `(discr K).natAbs` serve as the level of a
Dirichlet character whose `L`-function is taken, such as the quadratic character of a quadratic
field, and supplies `0 < |(discr K : ℝ)|` directly to analytic class-number bounds. A nontrivial
number field (`1 < Module.finrank ℚ K`) has `|discr K| > 2` by Hermite–Minkowski
(`NumberField.abs_discr_gt_two`), so its discriminant is not `1`.

## Main results

* `NumberField.instNeZeroDiscr`: `discr K ≠ 0`, as a `NeZero` instance.
* `NumberField.instNeZeroNatAbsDiscr`: `(discr K).natAbs ≠ 0`, as a `NeZero` instance.
* `NumberField.abs_discr_pos` and `NumberField.abs_cast_discr_pos`: `0 < |discr K|` in `ℤ` and in
  any strict ordered ring.
* `NumberField.discr_ne_one`: `discr K ≠ 1` whenever `1 < Module.finrank ℚ K`.
-/

public section

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The discriminant of a number field is nonzero, as a `NeZero` instance. -/
instance instNeZeroDiscr : NeZero (discr K) :=
  ⟨discr_ne_zero K⟩

/-- The absolute value of the discriminant of a number field is a nonzero level, as the
`L`-function of a Dirichlet character of that level requires. -/
instance instNeZeroNatAbsDiscr : NeZero (discr K).natAbs :=
  ⟨Int.natAbs_ne_zero.mpr (discr_ne_zero K)⟩

/-- The absolute value of the discriminant of a number field is strictly positive. -/
theorem abs_discr_pos (K : Type*) [Field K] [NumberField K] : 0 < |discr K| :=
  abs_pos.mpr (discr_ne_zero K)

/-- The absolute value of the cast of a number field discriminant into any strict ordered ring is
strictly positive. -/
theorem abs_cast_discr_pos (K : Type*) [Field K] [NumberField K]
    {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] :
    0 < |(discr K : R)| :=
  abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))

/-- The discriminant of a nontrivial number field (`1 < [K : ℚ]`) is not `1`. -/
theorem discr_ne_one (hK : 1 < Module.finrank ℚ K) : discr K ≠ 1 := by
  have := NumberField.abs_discr_gt_two (K := K) hK
  intro h
  simp [h] at this

end NumberField
