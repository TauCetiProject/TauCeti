/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Uniformly continuous scalar actions on rings with an absolute value

A scalar action on a ring `A` that commutes with right multiplication,
`m • (x * y) = (m • x) * y` (`IsScalarTower M A A`), such as the algebra action of a commutative
semiring, induces a uniformly continuous action on `WithAbs v` for every fixed scalar. This lets
the scalar action extend to the completion; Mathlib's corresponding instance covers only algebra
actions of a commutative ring on a field.
-/

public section

namespace WithAbs

variable {M A : Type*} [Ring A] [SMul M A] [IsScalarTower M A A]

/-- A scalar action on a ring with an absolute value that commutes with right multiplication, such
as an algebra action, is uniformly continuous in its argument. -/
instance (priority := 100) uniformContinuousConstSMul (v : AbsoluteValue A ℝ) :
    UniformContinuousConstSMul M (WithAbs v) where
  -- An action commuting with right multiplication is left multiplication by `m • 1`.
  uniformContinuous_const_smul m := by
    simpa only [smul_eq_mul, smul_one_mul] using
      uniformContinuous_const_smul (X := WithAbs v) (m • 1 : WithAbs v)

end WithAbs
