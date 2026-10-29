/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Roots of unity in the circle

Mathlib's `ZMod.toCircle : AddChar (ZMod n) Circle` sends `j` to `e^{2πi j / n}`. This file records
that its values are exactly the `n`-th roots of unity of the circle, in the form used to compare
points of the circle with the same `n`-th power. These are the facts needed to identify the orbits
of the cyclic rotation groups `ℤ/n` acting on the circle, as in the quotient constructions of lens
spaces.

## Main results

* `ZMod.toCircle_pow_eq_one`: the values of `ZMod.toCircle` are `n`-th roots of unity.
* `ZMod.exists_toCircle_eq_of_pow_eq_one`: every `n`-th root of unity in the circle is a value
  of `ZMod.toCircle`.
-/

public section

namespace ZMod

variable {n : ℕ} [NeZero n]

/-- The values of `ZMod.toCircle` are `n`-th roots of unity. -/
theorem toCircle_pow_eq_one (j : ZMod n) : toCircle j ^ n = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, natCast_self, zero_mul, AddChar.map_zero_eq_one]

/-- **The `n`-th roots of unity in the circle are the values of `ZMod.toCircle`.** -/
theorem exists_toCircle_eq_of_pow_eq_one {ζ : Circle} (hζ : ζ ^ n = 1) :
    ∃ j : ZMod n, toCircle j = ζ := by
  obtain ⟨j, hj⟩ := (bijective_rootsOfUnityAddChar (n := n)).2 ⟨toUnits ζ, by
    rw [mem_rootsOfUnity, ← map_pow, hζ, map_one]⟩
  exact ⟨j, by simpa using congrArg (fun u : rootsOfUnity n Circle ↦ ((u : Circleˣ) : Circle)) hj⟩

end ZMod
