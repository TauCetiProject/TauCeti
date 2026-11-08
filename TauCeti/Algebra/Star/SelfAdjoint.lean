/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint

/-!
# Nilpotent self-adjoint elements, anticommutation and star transposition

In a star monoid with zero whose star is proper (`IsProperStar`: `star x * x = 0` forces
`x = 0`), such as a matrix ring over a star-ordered ring like `ℝ` or `ℂ`, a self-adjoint element
`x` with `x * x = star x * x = 0` is zero. Since the powers of a self-adjoint element are
self-adjoint, peeling off squares shows that a nilpotent self-adjoint element is zero. This is
what rules out nonzero nilpotent ideals in an algebra of matrices closed under conjugate
transposition.

In a star ring, taking adjoints shows that an element anticommuting with a self-adjoint `γ` has an
adjoint anticommuting with `γ`, as needed for gradings. Similarly, taking stars transposes
one-sided relations with a self-adjoint element: `x * q = x` becomes `q * x = x` for self-adjoint
`x`, and `q * u = 0` becomes `star u * q = 0`.

## Main results

* `IsSelfAdjoint.eq_zero_of_isNilpotent`: a nilpotent self-adjoint element is zero.
* `IsSelfAdjoint.mul_star_eq_neg_star_mul`: if `γ * x = -(x * γ)` for a self-adjoint `γ`, then
  `γ * star x = -(star x * γ)`.
* `IsSelfAdjoint.mul_eq_right_of_mul_eq_left`: for self-adjoint `x` and `q`, `x * q = x` implies
  `q * x = x`.
* `IsSelfAdjoint.star_mul_eq_zero_of_mul_eq_zero`: for self-adjoint `q`, `q * u = 0` implies
  `star u * q = 0`.
-/

public section

section Nilpotent

variable {R : Type*} [MonoidWithZero R] [StarMul R] [IsProperStar R]

/-- **A nilpotent self-adjoint element is zero** when the star is proper. Some such hypothesis is
needed: over `ZMod 2` the symmetric matrix `!![1, 1; 1, 1]` squares to zero. -/
theorem IsSelfAdjoint.eq_zero_of_isNilpotent {x : R} (hx : IsSelfAdjoint x)
    (hnil : IsNilpotent x) : x = 0 := by
  obtain ⟨m, hm⟩ := hnil
  -- `x ^ 2 ^ (j + 1) = star (x ^ 2 ^ j) * x ^ 2 ^ j`, so each vanishing power of the form `2 ^ j`
  -- forces the previous one to vanish
  have key (j : ℕ) (hj : x ^ 2 ^ j = 0) : x = 0 := by
    induction j with
    | zero => simpa using hj
    | succ j ih =>
      refine ih (star_mul_self_eq_zero.mp ?_)
      rwa [(hx.pow (2 ^ j)).star_eq, ← pow_add, ← two_mul, ← pow_succ']
  exact key m (pow_eq_zero_of_le m.lt_two_pow_self.le hm)

end Nilpotent

/-- An element anticommuting with a self-adjoint `γ` has an adjoint anticommuting with `γ`. -/
theorem IsSelfAdjoint.mul_star_eq_neg_star_mul {R : Type*} [NonUnitalNonAssocRing R]
    [StarRing R] {γ x : R} (hγ : IsSelfAdjoint γ) (h : γ * x = -(x * γ)) :
    γ * star x = -(star x * γ) := by
  have h' := congrArg star h
  rw [star_mul, star_neg, star_mul, hγ.star_eq] at h'
  rw [h', neg_neg]

/-- For self-adjoint `x` and `q`, taking stars turns `x * q = x` into `q * x = x`. -/
theorem IsSelfAdjoint.mul_eq_right_of_mul_eq_left {R : Type*} [Mul R] [StarMul R] {x q : R}
    (hx : IsSelfAdjoint x) (hq : IsSelfAdjoint q) (h : x * q = x) : q * x = x := by
  simpa only [star_mul, hq.star_eq, hx.star_eq] using congrArg star h

/-- For self-adjoint `q`, taking stars turns `q * u = 0` into `star u * q = 0`. -/
theorem IsSelfAdjoint.star_mul_eq_zero_of_mul_eq_zero {R : Type*} [NonUnitalNonAssocSemiring R]
    [StarRing R] {q u : R} (hq : IsSelfAdjoint q) (h : q * u = 0) : star u * q = 0 := by
  simpa only [star_mul, hq.star_eq, star_zero] using congrArg star h
