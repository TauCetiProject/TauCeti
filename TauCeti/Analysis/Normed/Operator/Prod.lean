/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Operator norm of maps out of a product

The continuous linear map `(x, y) ↦ f x + g y` out of a product (`ContinuousLinearMap.coprod`) has
operator norm at most `‖f‖ + ‖g‖` (`ContinuousLinearMap.opNorm_coprod_le`). This bounds solution
operators assembled from separate operators for each component of the data, for instance the
forcing and the initial datum of an evolution equation. In particular a continuous linear map out
of `𝕜 × 𝕜` has operator norm at most the sum of the norms of its values on the two coordinate
vectors (`ContinuousLinearMap.opNorm_le_norm_apply_add_norm_apply`).
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]

/-- The operator norm of `(x, y) ↦ f x + g y` is at most `‖f‖ + ‖g‖`. -/
theorem opNorm_coprod_le (f : E →L[𝕜] G) (g : F →L[𝕜] G) : ‖f.coprod g‖ ≤ ‖f‖ + ‖g‖ := by
  rw [← comp_fst_add_comp_snd]
  exact (opNorm_add_le _ _).trans (add_le_add
    ((f.opNorm_comp_le _).trans (mul_le_of_le_one_right (norm_nonneg _) (norm_fst_le _ _ _)))
    ((g.opNorm_comp_le _).trans (mul_le_of_le_one_right (norm_nonneg _) (norm_snd_le _ _ _))))

/-- A continuous linear map out of `𝕜 × 𝕜` has operator norm at most `‖A (1, 0)‖ + ‖A (0, 1)‖`. -/
theorem opNorm_le_norm_apply_add_norm_apply (A : 𝕜 × 𝕜 →L[𝕜] G) :
    ‖A‖ ≤ ‖A (1, 0)‖ + ‖A (0, 1)‖ := by
  refine opNorm_le_bound _ (by positivity) fun w ↦ ?_
  have hw : A w = w.1 • A (1, 0) + w.2 • A (0, 1) := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  rw [hw, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul, mul_comm]
  exacts [by gcongr; exact _root_.norm_fst_le w, by gcongr; exact _root_.norm_snd_le w]

end ContinuousLinearMap
