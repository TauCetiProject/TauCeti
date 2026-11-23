/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SkewAdjoint

import TauCeti.Algebra.Lie.Hom
import TauCeti.Algebra.Lie.Subalgebra.Automorphism

/-!
# Negative transpose on the matrix Lie algebra

Negative transpose preserves the commutator bracket and is its own inverse. The resulting
`TauCeti.negTransposeLieEquiv` is the linear input to the pinned type-A graph automorphism, and
`LieSubalgebra.negTransposeEquiv` restricts it to any matrix Lie subalgebra closed under
negative transpose (such as `sl n R` and `sp l R`).

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

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Restrict the negative-transpose Lie automorphism `X ↦ -Xᵀ` to a matrix Lie subalgebra closed
under it. -/
def negTransposeEquiv (S : LieSubalgebra R (Matrix n n R)) (hS : ∀ X ∈ S, -Xᵀ ∈ S) :
    S ≃ₗ⁅R⁆ S :=
  (TauCeti.negTransposeLieEquiv n R).ofSubalgebras S S <|
    S.map_eq_self_of_involutive (TauCeti.negTransposeLieEquiv n R) (fun _ ↦ by simp) hS

/-- The matrix value of `LieSubalgebra.negTransposeEquiv` is negative transpose. -/
@[simp]
theorem coe_negTransposeEquiv (S : LieSubalgebra R (Matrix n n R)) (hS : ∀ X ∈ S, -Xᵀ ∈ S)
    (X : S) : (S.negTransposeEquiv hS X : Matrix n n R) = -(X : Matrix n n R)ᵀ :=
  (TauCeti.negTransposeLieEquiv n R).ofSubalgebras_apply S S _ X

/-- Applying `LieSubalgebra.negTransposeEquiv` twice returns the original matrix. -/
@[simp]
theorem negTransposeEquiv_negTransposeEquiv (S : LieSubalgebra R (Matrix n n R))
    (hS : ∀ X ∈ S, -Xᵀ ∈ S) (X : S) :
    S.negTransposeEquiv hS (S.negTransposeEquiv hS X) = X := by
  apply Subtype.ext
  simp

/-- `LieSubalgebra.negTransposeEquiv` is its own inverse. -/
@[simp]
theorem negTransposeEquiv_symm (S : LieSubalgebra R (Matrix n n R)) (hS : ∀ X ∈ S, -Xᵀ ∈ S) :
    (S.negTransposeEquiv hS).symm = S.negTransposeEquiv hS :=
  LieEquiv.symm_eq_self_of_involutive (S.negTransposeEquiv_negTransposeEquiv hS)

/-- Fixed vectors of `LieSubalgebra.negTransposeEquiv` are the skew-symmetric matrices in `S`. -/
@[simp]
theorem negTransposeEquiv_eq_self_iff (S : LieSubalgebra R (Matrix n n R))
    (hS : ∀ X ∈ S, -Xᵀ ∈ S) (X : S) :
    S.negTransposeEquiv hS X = X ↔ (X : Matrix n n R)ᵀ = -(X : Matrix n n R) := by
  rw [← Subtype.coe_inj, coe_negTransposeEquiv, neg_eq_iff_eq_neg]

/-- Negated vectors of `LieSubalgebra.negTransposeEquiv` are the symmetric matrices in `S`. -/
@[simp]
theorem negTransposeEquiv_eq_neg_iff (S : LieSubalgebra R (Matrix n n R))
    (hS : ∀ X ∈ S, -Xᵀ ∈ S) (X : S) :
    S.negTransposeEquiv hS X = -X ↔ (X : Matrix n n R)ᵀ = (X : Matrix n n R) := by
  rw [← Subtype.coe_inj, coe_negTransposeEquiv, NegMemClass.coe_neg]
  exact neg_inj

end LieSubalgebra
