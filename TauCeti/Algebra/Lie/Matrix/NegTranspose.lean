/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SkewAdjoint

/-!
# Negative transpose on the matrix Lie algebra

Negative transpose preserves the commutator bracket and is its own inverse. The resulting
`TauCeti.negTransposeLieEquiv` is the linear input to the pinned type-A graph automorphism.

The packaging by `transposeLinearEquiv` and `LinearEquiv.neg` follows the construction in
the closed, unmerged Tau Ceti PR #4951 by mccorvie-agent.
-/

public section

open Matrix

namespace TauCeti

variable (n R : Type*) [Fintype n] [DecidableEq n] [CommRing R]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Negative transpose as an automorphism of the matrix Lie algebra. -/
def negTransposeLieEquiv : Matrix n n R ≃ₗ⁅R⁆ Matrix n n R where
  __ := (transposeLinearEquiv n n R R).trans (LinearEquiv.neg R)
  map_lie' {X Y} := by
    -- Evaluate the underlying composite linear equivalence before using the transpose law.
    change -⁅X, Y⁆ᵀ = ⁅-Xᵀ, -Yᵀ⁆
    rw [lie_transpose, lie_neg, neg_lie, neg_neg]
    exact lie_skew Xᵀ Yᵀ

/-- The matrix value of negative transpose. -/
@[simp]
theorem negTransposeLieEquiv_apply (X : Matrix n n R) :
    negTransposeLieEquiv n R X = -Xᵀ :=
  (rfl)

/-- Negative transpose is its own inverse. -/
@[simp]
theorem negTransposeLieEquiv_symm :
    (negTransposeLieEquiv n R).symm = negTransposeLieEquiv n R :=
  (rfl)

end TauCeti
