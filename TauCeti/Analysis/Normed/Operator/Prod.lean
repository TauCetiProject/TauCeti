/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Operator norms of maps into and out of a product

The continuous linear map `(x, y) ↦ f x + g y` out of a product (`ContinuousLinearMap.coprod`) has
operator norm at most `‖f‖ + ‖g‖` (`ContinuousLinearMap.opNorm_coprod_le`) and at least `‖f‖` and
`‖g‖` (`ContinuousLinearMap.opNorm_le_opNorm_coprod_left`,
`ContinuousLinearMap.opNorm_le_opNorm_coprod_right`). The upper bound bounds solution
operators assembled from separate operators for each component of the data, for instance the
forcing and the initial datum of an evolution equation. A continuous linear map out of `𝕜 × 𝕜`
is determined by its values on the coordinate vectors
(`ContinuousLinearMap.apply_mk_eq_smul_add_smul`), and has operator norm at most
`‖f (1, 0)‖ + ‖f (0, 1)‖`
(`ContinuousLinearMap.opNorm_le_norm_apply_one_zero_add_norm_apply_zero_one`). The map
`(x, y) ↦ (x, c • y)` on a product with `‖c‖ ≤ 1` is a contraction
(`ContinuousLinearMap.norm_inl_comp_fst_add_smul_inr_comp_snd_le`). For an
endomorphism `L` of `E × F`, each component of `L v - v` has norm at most `‖L - 1‖ ‖v‖`
(`ContinuousLinearMap.norm_apply_fst_sub_fst_le`, `ContinuousLinearMap.norm_apply_snd_sub_snd_le`),
so `L` moves each coordinate of `v` little when it is close to the identity.

The map `x ↦ (x, f x)` into a product, the derivative of a graph map, has operator norm at most
`max 1 ‖f‖` (`ContinuousLinearMap.opNorm_id_prod_le`). Padding a map with the zero second
component does not change its norm (`ContinuousLinearMap.opNorm_prod_zero`), and projecting a map
into a product to its first component does not increase it
(`ContinuousLinearMap.opNorm_fst_comp_le`).
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

/-- The operator norm of `f` is at most that of `(x, y) ↦ f x + g y`, its restriction to the
first factor. -/
theorem opNorm_le_opNorm_coprod_left (f : E →L[𝕜] G) (g : F →L[𝕜] G) : ‖f‖ ≤ ‖f.coprod g‖ := by
  simpa using ((f.coprod g).opNorm_comp_le (inl 𝕜 E F)).trans
    (mul_le_of_le_one_right (norm_nonneg _) (norm_inl_le_one 𝕜 E F))

/-- The operator norm of `g` is at most that of `(x, y) ↦ f x + g y`, its restriction to the
second factor. -/
theorem opNorm_le_opNorm_coprod_right (f : E →L[𝕜] G) (g : F →L[𝕜] G) : ‖g‖ ≤ ‖f.coprod g‖ := by
  simpa using ((f.coprod g).opNorm_comp_le (inr 𝕜 E F)).trans
    (mul_le_of_le_one_right (norm_nonneg _) (norm_inr_le_one 𝕜 E F))

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

/-- The operator norm of `x ↦ (x, f x)` is at most `max 1 ‖f‖`. -/
theorem opNorm_id_prod_le (f : E →L[𝕜] F) :
    ‖(ContinuousLinearMap.id 𝕜 E).prod f‖ ≤ max 1 ‖f‖ := by
  rw [opNorm_prod, Prod.norm_def]
  exact max_le_max norm_id_le le_rfl

/-- The operator norm of `x ↦ (f x, 0)` is that of `f`. -/
theorem opNorm_prod_zero (f : E →L[𝕜] F) : ‖f.prod (0 : E →L[𝕜] G)‖ = ‖f‖ := by
  rw [opNorm_prod, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg f)]

/-- The first component of a map into a product has operator norm at most that of the map. -/
theorem opNorm_fst_comp_le (f : E →L[𝕜] F × G) : ‖(fst 𝕜 F G).comp f‖ ≤ ‖f‖ :=
  (opNorm_comp_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (norm_fst_le 𝕜 F G))

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

/-- The first component of `L v - v` has norm at most `‖L - 1‖ ‖v‖`. -/
theorem norm_apply_fst_sub_fst_le (L : E × F →L[𝕜] E × F) (v : E × F) :
    ‖(L v).1 - v.1‖ ≤ ‖L - 1‖ * ‖v‖ :=
  (_root_.norm_fst_le ((L - 1) v)).trans ((L - 1).le_opNorm v)

/-- The second component of `L v - v` has norm at most `‖L - 1‖ ‖v‖`. -/
theorem norm_apply_snd_sub_snd_le (L : E × F →L[𝕜] E × F) (v : E × F) :
    ‖(L v).2 - v.2‖ ≤ ‖L - 1‖ * ‖v‖ :=
  (_root_.norm_snd_le ((L - 1) v)).trans ((L - 1).le_opNorm v)

end ContinuousLinearMap

