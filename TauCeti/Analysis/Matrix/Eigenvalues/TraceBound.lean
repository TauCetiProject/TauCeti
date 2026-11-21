/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
public import TauCeti.Analysis.Matrix.Spectrum

/-!
# Bounding the operator norm by even trace powers

For a nonempty Hermitian matrix the even power of the greatest absolute eigenvalue
is at most the sum of all even powers of eigenvalues. This compares the Euclidean
operator norm with an even trace moment suitable for Markov's inequality.
-/

public section

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] [Nonempty n]

/-- The `2*k`-th power of the Euclidean operator norm of a Hermitian matrix is bounded by
the trace of its `2*k`-th power. The trace in this inequality is real. -/
theorem IsHermitian.l2_opNorm_pow_le_re_trace_pow {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (k : ℕ) : ‖A‖ ^ (2 * k) ≤ RCLike.re (A ^ (2 * k)).trace := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i ↦ ‖hA.eigenvalues i‖) Finset.univ_nonempty
  have hnorm : ‖A‖ ≤ ‖hA.eigenvalues i‖ := by
    rw [hA.l2_opNorm_eq_norm_eigenvalues]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j ↦ hmax j (Finset.mem_univ j)
  rw [hA.trace_pow_eq_sum_eigenvalues_pow]
  simp only [map_sum, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  refine (pow_le_pow_left₀ (norm_nonneg _) hnorm _).trans ?_
  rw [Real.norm_eq_abs, pow_abs_two_mul]
  exact Finset.single_le_sum (fun j _ ↦ (even_two_mul k).pow_nonneg (hA.eigenvalues j)) hi

end Matrix
