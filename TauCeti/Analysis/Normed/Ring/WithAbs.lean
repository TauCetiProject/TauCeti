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

The algebra action of a commutative semiring on `WithAbs v` is uniformly continuous for every
fixed scalar. This lets the scalar action extend to the completion without requiring the scalar
semiring to be a ring.
-/

public section

namespace WithAbs

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- The algebra action on a ring with an absolute value is uniformly continuous in its argument. -/
instance (priority := 100) uniformContinuousConstSMul (v : AbsoluteValue A ℝ) :
    UniformContinuousConstSMul R (WithAbs v) where
  -- The proof follows the scalar-continuity instance for a commutative ring base in
  -- `Mathlib.Analysis.Normed.Field.WithAbs`, using `Ring.uniformContinuousConstSMul`
  -- on the normed ring `WithAbs v`.
  uniformContinuous_const_smul r := by
    simp_rw [Algebra.smul_def]
    exact (Ring.uniformContinuousConstSMul _).uniformContinuous_const_smul _

end WithAbs
