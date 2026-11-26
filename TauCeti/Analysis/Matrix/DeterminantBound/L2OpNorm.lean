/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.L2OpNorm
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard

/-!
# The determinant and the `ℓ²` operator norm

The determinant of a square matrix over `𝕜` has norm at most the `|n|`-th power of its `ℓ²`
operator norm: by Hadamard's inequality it is at most the product of the Euclidean norms of the
rows, and each row has Euclidean norm at most the operator norm.

## Main results

* `Matrix.norm_det_le_l2_opNorm_pow`: `‖det A‖ ≤ ‖A‖ ^ |n|` for the scoped `ℓ²` operator norm.
-/

public section

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator

/-- The determinant of a square matrix has norm at most the `|n|`-th power of its `ℓ²` operator
norm. -/
theorem norm_det_le_l2_opNorm_pow (A : Matrix n n 𝕜) : ‖A.det‖ ≤ ‖A‖ ^ Fintype.card n := by
  refine (norm_det_le_prod_norm_toLp A).trans ?_
  rw [← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ ?_
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (norm_nonneg _)]
  exact sum_norm_sq_le_l2_opNorm_sq A i

end Matrix
