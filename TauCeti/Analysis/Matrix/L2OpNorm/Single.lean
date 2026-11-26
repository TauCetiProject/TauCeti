/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Euclidean operator norms of matrix units

A single-entry matrix has operator norm equal to the norm of its entry.
-/

public section

open scoped Matrix.Norms.L2Operator

namespace Matrix

/-- The Euclidean operator norm of a matrix with a single possibly nonzero entry is the norm
of that entry. -/
@[simp]
theorem l2_opNorm_single {m n 𝕜 : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [RCLike 𝕜]
    (i : m) (j : n) (a : 𝕜) : ‖single i j a‖ = ‖a‖ := by
  have hs : ‖single i j a‖ * ‖single i j a‖ = ‖a‖ * ‖a‖ := by
    rw [← l2_opNorm_conjTranspose_mul_self, conjTranspose_single, single_mul_single_same,
      ← diagonal_single, l2_opNorm_diagonal]
    rw [Pi.norm_single, norm_mul, norm_star]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by simpa [pow_two] using hs)

end Matrix
