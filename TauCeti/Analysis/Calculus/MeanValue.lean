/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue

import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# A directional mean value inequality

The mean value inequality only needs control of the derivative in the direction of the
chord being estimated, not an operator norm bound. This is useful on lower-dimensional
simplices, where derivatives are determined only on tangent directions, and when estimating
a parametrized map in terms of the size of its geometric chord.

The argument follows Mathlib's `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`,
using its one-variable mean value inequality along the same line segment.
-/

public section

open Set

namespace Convex

/-- The mean value inequality with a bound only in the direction of the chord. The bound
is needed only on the segment joining the endpoints. In particular, neither an operator norm
bound nor a full-dimensional domain is required. Derivatives may be taken over a real or
complex scalar field. -/
theorem norm_image_sub_le_of_norm_hasFDerivWithin_apply_le
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {s : Set E} {f : E → F}
    {f' : E → E →L[𝕜] F} {x y : E} {C : ℝ} (hs : Convex ℝ s)
    (hf : ∀ z ∈ s, HasFDerivWithinAt f (f' z) s z)
    (hbound : ∀ z ∈ segment ℝ x y, ‖f' z (y - x)‖ ≤ C)
    (hx : x ∈ s) (hy : y ∈ s) : ‖f y - f x‖ ≤ C := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  let γ : ℝ → E := AffineMap.lineMap x y
  have hγ : MapsTo γ (Icc 0 1) s := hs.mapsTo_lineMap hx hy
  have hd : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (f ∘ γ) (f' (γ t) (y - x)) (Icc 0 1) t := by
    intro t ht
    simpa only [ContinuousLinearMap.coe_restrictScalars'] using
      ((hf _ (hγ ht)).restrictScalars ℝ).comp_hasDerivWithinAt t
        AffineMap.hasDerivWithinAt_lineMap hγ
  have hb : ∀ t ∈ Ico (0 : ℝ) 1, ‖f' (γ t) (y - x)‖ ≤ C := by
    intro t ht
    exact hbound _ (lineMap_mem_segment ℝ _ _ (Ico_subset_Icc_self ht))
  simpa [γ] using norm_image_sub_le_of_norm_deriv_le_segment_01' hd hb

end Convex
