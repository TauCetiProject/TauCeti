/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Commute
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Logic.Pairwise

/-!
# Indicator functions and supports in a monoid with zero

A family `x` commuting pairwise on a set `s` extends by zero outside `s`, via `Set.indicator`, to a
family commuting pairwise everywhere, since `0` commutes with every element. Multiplying a function
`g` by a function equal to `1` on the support of `g` does not change `g`; pointwise, `a * b = b` and
`a • b = b` as soon as `a = 1` whenever `b ≠ 0`.

## Main results

* `TauCeti.mul_eq_right_of_ne_zero_imp_eq_one`, `TauCeti.smul_eq_right_of_ne_zero_imp_eq_one`: if
  `b ≠ 0` implies `a = 1`, then `a * b = b` and `a • b = b`.
* `Set.Pairwise.pairwise_commute_indicator`: the family `s.indicator x` commutes pairwise.
* `Set.EqOn.mul_eq_right`, `Set.EqOn.mul_eq_left`: if `f = 1` on `Function.support g`, then
  `f * g = g` and `g * f = g`.
-/

public section

open scoped Function

namespace TauCeti

/-- If `a = 1` whenever `b ≠ 0`, then `a * b = b`. -/
theorem mul_eq_right_of_ne_zero_imp_eq_one {M : Type*} [MulZeroOneClass M] {a b : M}
    (h : b ≠ 0 → a = 1) : a * b = b := by
  by_cases hb : b = 0
  · rw [hb, mul_zero]
  · rw [h hb, one_mul]

/-- If `a = 1` whenever `b ≠ 0`, then `a • b = b`. -/
theorem smul_eq_right_of_ne_zero_imp_eq_one {R M : Type*} [MonoidWithZero R] [Zero M]
    [MulActionWithZero R M] {a : R} {b : M} (h : b ≠ 0 → a = 1) : a • b = b := by
  by_cases hb : b = 0
  · rw [hb, smul_zero]
  · rw [h hb, one_smul]

end TauCeti

namespace Set

variable {ι M₀ : Type*} [MulZeroClass M₀]

/-- Extending a family commuting pairwise on `s` by zero outside `s` gives a family commuting
pairwise everywhere. -/
theorem Pairwise.pairwise_commute_indicator {s : Set ι} {x : ι → M₀}
    (hc : s.Pairwise (Commute on x)) : Pairwise (Commute on s.indicator x) := fun i j hij ↦ by
  by_cases hi : i ∈ s
  · by_cases hj : j ∈ s
    · simpa [Function.onFun, hi, hj] using hc hi hj hij
    · simp [Function.onFun, hj]
  · simp [Function.onFun, hi]

section Support

variable {α M : Type*} [MulZeroOneClass M] {f g : α → M}

/-- Multiplying `g` on the left by a function equal to `1` on the support of `g` does not
change `g`. -/
theorem EqOn.mul_eq_right (h : EqOn f 1 (Function.support g)) : f * g = g :=
  funext fun _ ↦ TauCeti.mul_eq_right_of_ne_zero_imp_eq_one fun hy ↦ h hy

/-- Multiplying `g` on the right by a function equal to `1` on the support of `g` does not
change `g`. -/
theorem EqOn.mul_eq_left (h : EqOn f 1 (Function.support g)) : g * f = g :=
  funext fun y => by
    by_cases hy : g y = 0
    · simp [hy]
    · simp [h hy]

end Support

end Set
