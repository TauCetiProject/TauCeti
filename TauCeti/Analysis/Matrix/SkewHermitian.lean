/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Frobenius
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# The invariant trace metric on skew-Hermitian matrices

The real Frobenius inner product restricts to the trace metric `-Re tr(XY)` on
skew-Hermitian matrices. This identifies a positive definite metric on every real
subspace of skew-Hermitian matrices without choosing a basis. Unitary conjugation
preserves the metric, and commutation with a skew-Hermitian matrix is skew-adjoint.
Thus a matrix Lie algebra contained in the skew-Hermitian matrices has a canonical
ad-invariant metric, invariant also under disconnected unitary subgroups.

The norm and inner product in this file use `Matrix.Norms.Frobenius`.
The trace-metric convention is the one used in Oh–Tataru,
*The hyperbolic Yang–Mills equation for connections in an arbitrary topological class*,
Comm. Math. Phys. 365 (2019), §6.1.
-/

public section

noncomputable section

open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace ComplexConjugate

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜]

/-- For a skew-Hermitian first argument, the real Frobenius metric is `-Re tr(XY)`.
The second argument need not be skew-Hermitian. -/
theorem frobenius_real_inner_eq_neg_re_trace_mul {X : Matrix n n 𝕜}
    (hX : Xᴴ = -X) (Y : Matrix n n 𝕜) :
    ⟪X, Y⟫_ℝ = -RCLike.re (X * Y).trace := by
  rw [frobenius_real_inner_eq_re_trace_conjTranspose_mul, hX]
  simp only [neg_mul, trace_neg, map_neg]

/-- On skew-Hermitian matrices the trace metric has the squared Frobenius norm
as its quadratic form, hence is positive definite. -/
theorem neg_re_trace_mul_self_eq_frobenius_norm_sq {X : Matrix n n 𝕜}
    (hX : Xᴴ = -X) : -RCLike.re (X * X).trace = ‖X‖ ^ 2 := by
  rw [← frobenius_real_inner_eq_neg_re_trace_mul hX, real_inner_self_eq_norm_sq]

/-- The trace of a product of two skew-Hermitian matrices is real. -/
theorem star_trace_mul_of_conjTranspose_eq_neg {X Y : Matrix n n 𝕜}
    (hX : Xᴴ = -X) (hY : Yᴴ = -Y) : star (X * Y).trace = (X * Y).trace := by
  rw [← trace_conjTranspose, conjTranspose_mul, hX, hY, neg_mul_neg, trace_mul_comm]

/-- Commutation with a skew-Hermitian matrix is skew-adjoint for the real Frobenius
metric on the whole matrix space. In particular this holds on any matrix Lie
subalgebra of skew-Hermitian matrices. -/
theorem frobenius_real_inner_lie_of_conjTranspose_eq_neg {X : Matrix n n 𝕜}
    (hX : Xᴴ = -X) (Y Z : Matrix n n 𝕜) :
    ⟪⁅X, Y⁆, Z⟫_ℝ = -⟪Y, ⁅X, Z⁆⟫_ℝ := by
  simp only [Ring.lie_def, frobenius_real_inner_eq_re_trace_conjTranspose_mul,
    conjTranspose_sub, conjTranspose_mul, hX, sub_mul, mul_sub, neg_mul, mul_neg,
    trace_sub, trace_neg, map_sub, map_neg, Matrix.mul_assoc]
  rw [trace_mul_comm X (Yᴴ * Z), Matrix.mul_assoc]
  ring

end Matrix
