/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# `C¹` regularity across a puncture

A function that is `C¹` on a punctured neighbourhood of a point, has a derivative at the point,
and whose derivative converges to it along the punctured neighbourhoods, is `C¹` at the point
(`TauCeti.contDiffAt_one_of_tendsto_fderiv`).
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {f' : E →L[𝕜] F} {x : E}

/-- A function that is `C¹` at every point of a punctured neighbourhood of `x`, has derivative
`f'` at `x`, and whose derivative tends to `f'` along the punctured neighbourhoods of `x`, is `C¹`
at `x`. -/
theorem contDiffAt_one_of_tendsto_fderiv (hf : ∀ᶠ y in 𝓝[≠] x, ContDiffAt 𝕜 1 f y)
    (hx : HasFDerivAt f f' x) (hlim : Tendsto (fderiv 𝕜 f) (𝓝[≠] x) (𝓝 f')) :
    ContDiffAt 𝕜 1 f x := by
  obtain ⟨u, hu, hfu⟩ := (eventually_nhdsWithin_iff.1 hf).exists_mem
  refine contDiffAt_one_iff.2 ⟨fderiv 𝕜 f, u, hu, fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · rcases eq_or_ne y x with rfl | hyx
    · refine (continuousWithinAt_compl_self.1 ?_).continuousWithinAt
      rwa [ContinuousWithinAt, hx.fderiv]
    · exact ((hfu y hy hyx).fderiv_right (m := 0) le_rfl).continuousAt.continuousWithinAt
  · rcases eq_or_ne y x with rfl | hyx
    · rwa [hx.fderiv]
    · exact ((hfu y hy hyx).differentiableAt one_ne_zero).hasFDerivAt

end TauCeti
