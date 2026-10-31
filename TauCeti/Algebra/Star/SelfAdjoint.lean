/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint

/-!
# Nilpotent self-adjoint elements

In a star monoid with zero whose star is proper (`IsProperStar`: `star x * x = 0` forces
`x = 0`), such as a matrix ring over a star-ordered ring like `ℝ` or `ℂ`, a self-adjoint element
`x` with `x * x = star x * x = 0` is zero. Since the powers of a self-adjoint element are
self-adjoint, peeling off squares shows that a nilpotent self-adjoint element is zero. This is
what rules out nonzero nilpotent ideals in an algebra of matrices closed under conjugate
transposition.

## Main results

* `IsSelfAdjoint.eq_zero_of_isNilpotent`: a nilpotent self-adjoint element is zero.
-/

public section

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
