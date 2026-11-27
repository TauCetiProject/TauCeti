/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Operator norm bounds from symmetric quadratic forms

The Rayleigh quotient identifies the operator norm of a symmetric continuous linear map with
the supremum of the absolute real part of its quadratic form on unit vectors.
-/

public section

open Metric RCLike

namespace ContinuousLinearMap

/-- For a symmetric continuous linear map, a nonnegative uniform bound on the absolute value of
the real part of its quadratic form over unit vectors bounds its operator norm. -/
theorem norm_le_of_forall_norm_eq_one_abs_re_inner_map_self_le {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (T : E →L[𝕜] E) (hT : T.IsSymmetric)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : E, ‖x‖ = 1 → |RCLike.re (Inner.inner 𝕜 (T x) x)| ≤ C) : ‖T‖ ≤ C := by
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  refine ciSup_le fun x ↦ ?_
  by_cases hx : x = 0
  · subst x
    simpa only [rayleighQuotient_apply_zero, abs_zero] using hC
  · have hxmem : T.rayleighQuotient x ∈
        T.rayleighQuotient '' ({0}ᶜ : Set E) := ⟨x, hx, rfl⟩
    rw [T.image_rayleigh_eq_image_rayleigh_sphere (by norm_num : (0 : ℝ) < 1)] at hxmem
    obtain ⟨y, hy, hxy⟩ := hxmem
    have hy_norm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
    have hquotient : T.rayleighQuotient y =
        RCLike.re (Inner.inner 𝕜 (T y) y) := by
      simp [rayleighQuotient, reApplyInnerSelf_apply, hy_norm]
    rw [← hxy, hquotient]
    exact h y hy_norm

end ContinuousLinearMap
