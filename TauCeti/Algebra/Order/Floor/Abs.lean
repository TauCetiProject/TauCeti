/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Floors and absolute values

In an ordered ring with a floor, the integer part `⌊a⌋` has absolute value at most `⌈|a|⌉₊`, and
so does the next integer `⌊a⌋ + 1` when `a` is not an integer. These bound the two integers
between which a non-integer `a` lies by the natural ceiling of `|a|`, for instance when an
estimate known at integer orders is interpolated to the real order `a`.

## Main results

* `Int.natAbs_floor_le_natCeil_abs`: `|⌊a⌋| ≤ ⌈|a|⌉₊`.
* `Int.natAbs_floor_add_one_le_natCeil_abs`: `|⌊a⌋ + 1| ≤ ⌈|a|⌉₊` when `Int.fract a ≠ 0`.
-/

public section

namespace Int

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- In an ordered ring with a floor, the integer part `⌊a⌋` has absolute value at most
`⌈|a|⌉₊`. -/
theorem natAbs_floor_le_natCeil_abs (a : R) : ⌊a⌋.natAbs ≤ ⌈|a|⌉₊ := by
  have h := Nat.le_ceil |a|
  have h₁ : -(⌈|a|⌉₊ : ℤ) ≤ ⌊a⌋ :=
    le_floor.2 (by push_cast; exact (neg_le_neg h).trans (neg_abs_le a))
  have h₂ : ⌊a⌋ ≤ (⌈|a|⌉₊ : ℤ) := by
    exact_mod_cast (floor_le a).trans ((le_abs_self a).trans h)
  omega

/-- In an ordered ring with a floor, if `a` is not an integer then the integer `⌊a⌋ + 1` just
above it has absolute value at most `⌈|a|⌉₊`. -/
theorem natAbs_floor_add_one_le_natCeil_abs {a : R} (ha : fract a ≠ 0) :
    (⌊a⌋ + 1).natAbs ≤ ⌈|a|⌉₊ := by
  have h := Nat.le_ceil |a|
  have h₁ : -(⌈|a|⌉₊ : ℤ) ≤ ⌊a⌋ :=
    le_floor.2 (by push_cast; exact (neg_le_neg h).trans (neg_abs_le a))
  have h₂ : (⌊a⌋ : R) < a := (floor_le a).lt_of_ne fun h ↦ ha (by rw [fract, h, sub_self])
  have h₃ : ⌊a⌋ < (⌈|a|⌉₊ : ℤ) := by exact_mod_cast h₂.trans_le ((le_abs_self a).trans h)
  omega

end Int
