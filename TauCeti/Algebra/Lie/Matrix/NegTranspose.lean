/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SkewAdjoint
public import TauCeti.Algebra.Lie.Subalgebra.Automorphism

/-!
# Negative transpose on the matrix Lie algebra

Negative transpose preserves the commutator bracket and is its own inverse. The resulting
`TauCeti.negTransposeLieEquiv` is the linear input to the pinned type-A graph automorphism.
It restricts to every Lie subalgebra closed under transpose
(`LieSubalgebra.restrictNegTranspose`).

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

namespace LieSubalgebra

open TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
  (L : LieSubalgebra R (Matrix n n R)) (hL : ∀ X ∈ L, Xᵀ ∈ L)

/-- Negative transpose `X ↦ -Xᵀ` restricted to a Lie subalgebra `L` of `𝔤𝔩_n(R)` closed under
transpose. -/
def restrictNegTranspose : L ≃ₗ⁅R⁆ L :=
  (negTransposeLieEquiv n R).ofSubalgebras L L
    (map_eq_self_of_involutive _ (fun X ↦ by simp) fun X hX ↦ by
      simpa using L.neg_mem (hL X hX))

/-- The matrix value of `restrictNegTranspose` is negative transpose. -/
@[simp]
theorem coe_restrictNegTranspose_apply (X : L) :
    (L.restrictNegTranspose hL X : Matrix n n R) = -(X : Matrix n n R)ᵀ := by
  simp [restrictNegTranspose]

/-- `X ↦ -Xᵀ` is an involution. -/
theorem restrictNegTranspose_involutive :
    Function.Involutive (L.restrictNegTranspose hL) :=
  fun X ↦ Subtype.ext (by simp)

/-- Applying `X ↦ -Xᵀ` twice gives back `X`. -/
@[simp]
theorem restrictNegTranspose_restrictNegTranspose (X : L) :
    L.restrictNegTranspose hL (L.restrictNegTranspose hL X) = X :=
  L.restrictNegTranspose_involutive hL X

/-- The inverse of `X ↦ -Xᵀ` is itself. -/
@[simp]
theorem restrictNegTranspose_symm :
    (L.restrictNegTranspose hL).symm = L.restrictNegTranspose hL :=
  LieEquiv.ext fun X ↦ (L.restrictNegTranspose hL).symm_apply_eq.mpr
    (L.restrictNegTranspose_involutive hL X).symm

end LieSubalgebra
