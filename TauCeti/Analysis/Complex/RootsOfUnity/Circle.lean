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

It also records that the circle has exactly `n` of them, and that every element of the circle
has an `n`-th root in the circle: writing `u = exp (i t)`, the element `exp (i t / n)` is one.
These compute stabilizers of circle actions with weights, where an element `u` acting by `u ^ n`
fixes a point exactly when it is an `n`-th root of unity.

## Main results

* `ZMod.exists_toCircle_eq_of_pow_eq_one`: every `n`-th root of unity in the circle is a value
  of `ZMod.toCircle`.
* `Circle.nat_card_rootsOfUnity`: the circle has exactly `n` roots of unity of order dividing `n`.
* `Circle.exists_pow_eq`: the circle is divisible.
-/

public section

namespace ZMod

variable {n : ℕ} [NeZero n]

/-- **The `n`-th roots of unity in the circle are the values of `ZMod.toCircle`.** -/
theorem exists_toCircle_eq_of_pow_eq_one {ζ : Circle} (hζ : ζ ^ n = 1) :
    ∃ j : ZMod n, toCircle j = ζ := by
  obtain ⟨j, hj⟩ := (bijective_rootsOfUnityAddChar (n := n)).2 ⟨toUnits ζ, by
    rw [mem_rootsOfUnity, ← map_pow, hζ, map_one]⟩
  exact ⟨j, by simpa using congrArg (fun u : rootsOfUnity n Circle ↦ ((u : Circleˣ) : Circle)) hj⟩

end ZMod

namespace Circle

/-- **The `n`-th roots of unity in the circle.** There are exactly `n` of them. -/
theorem nat_card_rootsOfUnity (n : ℕ) [NeZero n] : Nat.card (rootsOfUnity n Circle) = n := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (bijective_rootsOfUnityAddChar (n := n))),
    Nat.card_zmod]

/-- **The circle is divisible.** Every element of the unit circle has an `n`-th root in the circle
for `n ≠ 0`. -/
theorem exists_pow_eq {n : ℕ} (hn : n ≠ 0) (u : Circle) : ∃ v : Circle, v ^ n = u := by
  obtain ⟨t, rfl⟩ := exp_surjective u
  refine ⟨exp (t / n), ?_⟩
  rw [← exp_natCast_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hn)]

end Circle
