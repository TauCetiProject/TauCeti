/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import TauCeti.Algebra.Lie.Subalgebra.Automorphism

/-!
# Negative conjugate transpose on the real matrix Lie algebra

For `𝕜 = ℝ` or `ℂ`, negative conjugate transpose `X ↦ -Xᴴ` preserves the commutator bracket and is
its own inverse, so it is an automorphism of `𝔤𝔩_n(𝕜)` viewed as a real Lie algebra. It restricts
to every real Lie subalgebra closed under conjugate transpose. This is the conjugate-linear
counterpart of `TauCeti.negTransposeLieEquiv`, and the candidate Cartan involution of matrix Lie
algebras in `TauCeti.Algebra.Lie.CartanInvolution.Matrix`.

## Main definitions

* `TauCeti.negConjTransposeLieEquiv`: `X ↦ -Xᴴ` as an automorphism of the real Lie algebra
  `𝔤𝔩_n(𝕜)`.
* `LieSubalgebra.restrictNegConjTranspose`: its restriction to a real Lie subalgebra closed under
  conjugate transpose.

## Main results

* `LieSubalgebra.restrictNegConjTranspose_involutive` and
  `LieSubalgebra.restrictNegConjTranspose_symm`: the restriction is an involution, equal to its
  inverse.
-/

public section

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable (𝕜 n : Type*) [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- Negative conjugate transpose `X ↦ -Xᴴ` as an automorphism of `𝔤𝔩_n(𝕜)` viewed as a real Lie
algebra. -/
noncomputable def negConjTransposeLieEquiv : Matrix n n 𝕜 ≃ₗ⁅ℝ⁆ Matrix n n 𝕜 where
  __ := ((conjTransposeLinearEquiv n n ℝ 𝕜).trans (LinearEquiv.neg ℝ) :
    Matrix n n 𝕜 ≃ₗ[ℝ] Matrix n n 𝕜)
  map_lie' {X Y} := by
    -- Evaluate the underlying composite linear equivalence before using the bracket.
    change -⁅X, Y⁆ᴴ = ⁅-Xᴴ, -Yᴴ⁆
    simp only [Ring.lie_def, conjTranspose_sub, conjTranspose_mul, mul_neg, neg_mul, neg_neg,
      neg_sub]

variable {𝕜 n} in
/-- The matrix value of negative conjugate transpose. -/
@[simp]
theorem negConjTransposeLieEquiv_apply (X : Matrix n n 𝕜) :
    negConjTransposeLieEquiv 𝕜 n X = -Xᴴ :=
  (rfl)

/-- Negative conjugate transpose is its own inverse. -/
@[simp]
theorem negConjTransposeLieEquiv_symm :
    (negConjTransposeLieEquiv 𝕜 n).symm = negConjTransposeLieEquiv 𝕜 n :=
  LieEquiv.ext fun X ↦ (negConjTransposeLieEquiv 𝕜 n).symm_apply_eq.mpr (by simp)

end TauCeti

namespace LieSubalgebra

open TauCeti

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
  (L : LieSubalgebra ℝ (Matrix n n 𝕜)) (hL : ∀ X ∈ L, Xᴴ ∈ L)

/-- Negative conjugate transpose `X ↦ -Xᴴ` restricted to a real Lie subalgebra `L` of `𝔤𝔩_n(𝕜)`
closed under conjugate transpose. -/
noncomputable def restrictNegConjTranspose : L ≃ₗ⁅ℝ⁆ L :=
  (negConjTransposeLieEquiv 𝕜 n).ofSubalgebras L L
    (map_eq_self_of_involutive _ (fun X ↦ by simp) fun X hX ↦ by
      simpa using L.neg_mem (hL X hX))

/-- The matrix value of `restrictNegConjTranspose` is negative conjugate transpose. -/
@[simp]
theorem coe_restrictNegConjTranspose_apply (X : L) :
    (L.restrictNegConjTranspose hL X : Matrix n n 𝕜) = -(X : Matrix n n 𝕜)ᴴ := by
  simp [restrictNegConjTranspose]

/-- `X ↦ -Xᴴ` is an involution. -/
theorem restrictNegConjTranspose_involutive :
    Function.Involutive (L.restrictNegConjTranspose hL) :=
  fun X ↦ Subtype.ext (by simp)

/-- Applying `X ↦ -Xᴴ` twice gives back `X`. -/
@[simp]
theorem restrictNegConjTranspose_restrictNegConjTranspose (X : L) :
    L.restrictNegConjTranspose hL (L.restrictNegConjTranspose hL X) = X :=
  L.restrictNegConjTranspose_involutive hL X

/-- The inverse of `X ↦ -Xᴴ` is itself. -/
@[simp]
theorem restrictNegConjTranspose_symm :
    (L.restrictNegConjTranspose hL).symm = L.restrictNegConjTranspose hL :=
  LieEquiv.ext fun X ↦ (L.restrictNegConjTranspose hL).symm_apply_eq.mpr
    (L.restrictNegConjTranspose_involutive hL X).symm

end LieSubalgebra
