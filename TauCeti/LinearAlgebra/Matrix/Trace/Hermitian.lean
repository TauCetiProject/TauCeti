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

The trace of the square of a Hermitian complex matrix is the sum of its squared entry norms.
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

end Matrix
