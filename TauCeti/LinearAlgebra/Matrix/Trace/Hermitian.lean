/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Trace of a Hermitian square

The trace of the square of a Hermitian complex matrix is the sum of its squared entry norms. The
trace of the product of a Hermitian and a skew-Hermitian matrix is purely imaginary
(`Matrix.IsHermitian.re_trace_mul_eq_zero_of_conjTranspose_eq_neg`).
-/

public section

namespace Matrix

/-- The trace of the square of a Hermitian complex matrix is its entrywise squared norm sum. -/
theorem IsHermitian.trace_mul_self_eq_sum_norm_sq {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (A * A).trace = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
  classical
  simp only [trace, diag_apply, Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← hA.apply j i, Complex.star_def, Complex.mul_conj']

/-- The trace `tr(H X)` of the product of a Hermitian matrix `H` and a skew-Hermitian matrix `X`
is purely imaginary. -/
theorem IsHermitian.re_trace_mul_eq_zero_of_conjTranspose_eq_neg {𝕜 ι : Type*} [RCLike 𝕜]
    [Fintype ι] {H X : Matrix ι ι 𝕜} (hH : H.IsHermitian) (hX : Xᴴ = -X) :
    RCLike.re (H * X).trace = 0 := by
  have h : star (H * X).trace = -(H * X).trace := by
    simp [← trace_conjTranspose, hH.eq, hX, trace_mul_comm X]
  have := congrArg RCLike.re h
  simp only [RCLike.star_def, RCLike.conj_re, map_neg] at this
  linarith

end Matrix
