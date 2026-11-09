/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic

/-!
# Equality in the triangle inequality for a real-valued sum

If a finite sum of real or complex numbers equals the sum of their norms, every summand is
nonnegative real. This detects the common phase of summands after rotating their sum to the
positive real axis.
-/

public section

namespace RCLike

/-- If a finite sum equals the sum of the norms of its summands, each summand is its norm. -/
theorem eq_norm_of_sum_eq_sum_norm {𝕜 : Type*} [RCLike 𝕜] {ι : Type*}
    {s : Finset ι} {z : ι → 𝕜} (h : ∑ i ∈ s, z i = ((∑ i ∈ s, ‖z i‖ : ℝ) : 𝕜))
    {i : ι} (hi : i ∈ s) : z i = (‖z i‖ : 𝕜) := by
  have hre : ∑ i ∈ s, re (z i) = ∑ i ∈ s, ‖z i‖ := by
    simpa using congrArg re h
  exact norm_le_re_iff_eq_norm.1 <|
    ((Finset.sum_eq_sum_iff_of_le fun j _ ↦ re_le_norm (z j)).1 hre i hi).ge

end RCLike
