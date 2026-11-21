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
forcing and the initial datum of an evolution equation. A continuous linear map out of `𝕜 × 𝕜`
is determined by its values on the coordinate vectors
(`ContinuousLinearMap.apply_mk_eq_smul_add_smul`), and has operator norm at most
`‖f (1, 0)‖ + ‖f (0, 1)‖`
(`ContinuousLinearMap.opNorm_le_norm_apply_one_zero_add_norm_apply_zero_one`). The map
`(x, y) ↦ (x, c • y)` on a product with `‖c‖ ≤ 1` is a contraction
(`ContinuousLinearMap.norm_inl_comp_fst_add_smul_inr_comp_snd_le`).
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

/-- A continuous linear map out of `𝕜 × 𝕜` at `(a, b)` is `a` times its value at `(1, 0)` plus `b`
times its value at `(0, 1)`. -/
theorem apply_mk_eq_smul_add_smul (f : 𝕜 × 𝕜 →L[𝕜] G) (a b : 𝕜) :
    f (a, b) = a • f (1, 0) + b • f (0, 1) := by
  rw [← map_smul, ← map_smul, ← map_add]
  simp

/-- A continuous linear map out of `𝕜 × 𝕜` has operator norm at most the sum of the norms of its
values on the coordinate vectors. -/
theorem opNorm_le_norm_apply_one_zero_add_norm_apply_zero_one (f : 𝕜 × 𝕜 →L[𝕜] G) :
    ‖f‖ ≤ ‖f (1, 0)‖ + ‖f (0, 1)‖ := by
  refine f.opNorm_le_bound (by positivity) fun ⟨a, b⟩ ↦ ?_
  rw [f.apply_mk_eq_smul_add_smul a b, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul, mul_comm]
  · exact mul_le_mul_of_nonneg_left (_root_.norm_fst_le (a, b)) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_left (_root_.norm_snd_le (a, b)) (norm_nonneg _)

/-- The map `(x, y) ↦ (x, c • y)` on a product has operator norm at most `1` when `‖c‖ ≤ 1`. -/
theorem norm_inl_comp_fst_add_smul_inr_comp_snd_le {c : 𝕜} (hc : ‖c‖ ≤ 1) :
    ‖(inl 𝕜 E F).comp (fst 𝕜 E F) + c • (inr 𝕜 E F).comp (snd 𝕜 E F)‖ ≤ 1 := by
  have h : (inl 𝕜 E F).comp (fst 𝕜 E F) + c • (inr 𝕜 E F).comp (snd 𝕜 E F) =
      (fst 𝕜 E F).prod (c • snd 𝕜 E F) := by
    ext <;> simp
  rw [h, opNorm_prod, Prod.norm_def]
  refine max_le (norm_fst_le _ _ _) ?_
  rw [norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (norm_snd_le _ _ _)

end ContinuousLinearMap

