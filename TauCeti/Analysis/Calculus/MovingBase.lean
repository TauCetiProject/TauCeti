/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.Const
public import TauCeti.Analysis.Calculus.ParametricFDeriv

/-!
# Derivatives along a moving base point

If a parameterized function vanishes on its reference slice, moving the base point does not
change its first parameter derivative. In geometric applications, a minimal reference
hypersurface has zero scalar mean curvature, so this removes the first-order contribution
of a tangential reparametrization.
-/

public section

open scoped Topology

namespace TauCeti
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Moving the base point has no first-order effect when the reference slice is zero. -/
theorem HasFDerivAt.hasDerivAt_movingBase_of_zero_slice
    {f : ℝ × E → F} {L : (ℝ × E) →L[ℝ] F} {x : E}
    (hf : HasFDerivAt f L (0, x))
    (hzero : (fun y : E ↦ f (0, y)) =ᶠ[𝓝 x] fun _ ↦ (0 : F))
    {ξ : ℝ → E} {v : E}
    (hξ : HasDerivAt ξ v 0) (hξ0 : ξ 0 = x) :
    HasDerivAt (fun t ↦ f (t, ξ t)) (L (1, 0)) 0 := by
  have hspace : spatialFDeriv (𝕜 := ℝ) f x 0 = 0 :=
    (hasFDerivAt_timeSlice hf.differentiableAt).eq_zero_of_eventually_const hzero
  have hdiff : DifferentiableAt ℝ f (0, ξ 0) := by simpa [hξ0] using hf.differentiableAt
  have hcomp := TauCeti.hasDerivAt_comp_prodMk hdiff hξ
  rw [hξ0, hspace, zero_apply, add_zero, timeFDeriv_apply] at hcomp
  simpa only [hf.fderiv] using hcomp

end TauCeti
