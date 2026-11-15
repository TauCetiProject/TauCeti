/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Traces of Hermitian matrices

The trace of a Hermitian matrix over `ℝ` or `ℂ` is real (`Matrix.IsHermitian.coe_re_trace`), and
the trace of the square of a Hermitian complex matrix is the sum of its squared entry norms
(`Matrix.IsHermitian.trace_mul_self_eq_sum_norm_sq`).
-/

public section

namespace Matrix

/-- The trace of a Hermitian matrix over `ℝ` or `ℂ` equals the coercion of its real part. -/
theorem IsHermitian.coe_re_trace {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]
    {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) :
    (RCLike.re A.trace : 𝕜) = A.trace := by
  rw [← RCLike.conj_eq_iff_re, ← RCLike.star_def, ← trace_conjTranspose, hA.eq]

/-- The trace of the square of a Hermitian complex matrix is its entrywise squared norm sum. -/
theorem IsHermitian.trace_mul_self_eq_sum_norm_sq {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (A * A).trace = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
  classical
  simp only [trace, diag_apply, Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← hA.apply j i, Complex.star_def, Complex.mul_conj']

end Matrix
