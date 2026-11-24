/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Dual norm of a restricted inner product

A uniform bound on the inner product with vectors in a subspace is equivalent to the
same bound on the norm of the orthogonal projection onto that subspace.
-/

public section

open scoped InnerProductSpace

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The norm of the projection of `x` onto `K` is at most `c` exactly when the inner product
with `x` has norm at most `c ‖u‖` for every `u ∈ K`. -/
theorem norm_starProjection_le_iff_forall_norm_inner_le (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (x : E) {c : ℝ} (hc : 0 ≤ c) :
    ‖K.starProjection x‖ ≤ c ↔ ∀ u ∈ K, ‖⟪u, x⟫_𝕜‖ ≤ c * ‖u‖ := by
  have he (u : E) (hu : u ∈ K) : ⟪u, K.starProjection x⟫_𝕜 = ⟪u, x⟫_𝕜 := by
    rw [← K.inner_starProjection_left_eq_right u x, K.starProjection_eq_self_iff.mpr hu]
  constructor
  · intro h u hu
    rw [← he u hu, mul_comm c]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left h (norm_nonneg _))
  · intro h
    by_cases hz : K.starProjection x = 0
    · simpa [hz] using hc
    have hbound := h (K.starProjection x) (K.starProjection_apply_mem x)
    rw [← he _ (K.starProjection_apply_mem x), ← inner_self_re_eq_norm,
      inner_self_eq_norm_mul_norm] at hbound
    exact le_of_mul_le_mul_right hbound (norm_pos_iff.mpr hz)

/-- For a contrast subspace inside the fitted subspace, projecting the fit's error onto the
contrasts gives the same norm bound as projecting the original error. -/
theorem forall_norm_inner_starProjection_sub_le_iff (S : Submodule 𝕜 E) {L : Submodule 𝕜 E}
    [S.HasOrthogonalProjection] [L.HasOrthogonalProjection] (hSL : S ≤ L) (x m : E)
    {c : ℝ} (hc : 0 ≤ c) :
    (∀ u ∈ S, ‖⟪u, L.starProjection x - m⟫_𝕜‖ ≤ c * ‖u‖) ↔
      ‖S.starProjection (x - m)‖ ≤ c := by
  rw [← S.norm_starProjection_le_iff_forall_norm_inner_le _ hc, map_sub, map_sub]
  have h := congrArg (fun f : E →L[𝕜] E ↦ f x)
    (Submodule.starProjection_comp_starProjection_of_le hSL)
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [h]

end Submodule
