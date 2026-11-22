/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Prod

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

/-- A zero parameter slice has zero spatial derivative in every direction. -/
private theorem zeroSlice_deriv_spatial
    {f : ℝ × E → F} {L : (ℝ × E) →L[ℝ] F} {x v : E}
    (hf : HasFDerivAt f L (0, x))
    (hzero : (fun y : E ↦ f (0, y)) =ᶠ[𝓝 x] fun _ ↦ (0 : F)) :
    L (0, v) = 0 := by
  have hg : HasFDerivAt (fun y : E ↦ ((0 : ℝ), y))
      (ContinuousLinearMap.inr ℝ ℝ E) x := by
    simpa [ContinuousLinearMap.inr] using
      (hasFDerivAt_const (0 : ℝ) x).prodMk (hasFDerivAt_id x)
  have hcomp : HasFDerivAt (fun y : E ↦ f (0, y))
      (L.comp (ContinuousLinearMap.inr ℝ ℝ E)) x := by
    exact hf.comp x hg
  have hL : L.comp (ContinuousLinearMap.inr ℝ ℝ E) = 0 := by
    rw [← hcomp.fderiv, hzero.fderiv_eq]
    simp
  have hv := congrArg (fun A : E →L[ℝ] F ↦ A v) hL
  simpa using hv

/-- The ordinary chain rule for a parameterized function along a moving base point. -/
private theorem hasDerivAt_movingBase
    {f : ℝ × E → F} {L : (ℝ × E) →L[ℝ] F} {x : E}
    (hf : HasFDerivAt f L (0, x))
    {ξ : ℝ → E} {v : E}
    (hξ : HasDerivAt ξ v 0) (hξ0 : ξ 0 = x) :
    HasDerivAt (fun t ↦ f (t, ξ t)) (L (1, v)) 0 := by
  have hinner : HasDerivAt (fun t : ℝ ↦ (t, ξ t)) (1, v) 0 :=
    (hasDerivAt_id 0).prodMk hξ
  have hf' : HasFDerivAt f L ((fun t : ℝ ↦ (t, ξ t)) 0) := by
    simpa [hξ0] using hf
  change HasDerivAt (f ∘ (fun t : ℝ ↦ (t, ξ t))) (L (1, v)) 0
  exact hf'.comp_hasDerivAt 0 hinner

/-- Moving the base point has no first-order effect when the reference slice is zero. -/
theorem HasFDerivAt.hasDerivAt_movingBase_of_zero_slice
    {f : ℝ × E → F} {L : (ℝ × E) →L[ℝ] F} {x : E}
    (hf : HasFDerivAt f L (0, x))
    (hzero : (fun y : E ↦ f (0, y)) =ᶠ[𝓝 x] fun _ ↦ (0 : F))
    {ξ : ℝ → E} {v : E}
    (hξ : HasDerivAt ξ v 0) (hξ0 : ξ 0 = x) :
    HasDerivAt (fun t ↦ f (t, ξ t)) (L (1, 0)) 0 := by
  have hcomp := hasDerivAt_movingBase hf hξ hξ0
  have hdecomp : ((1 : ℝ), v) = (1, (0 : E)) + (0, v) := by simp
  rw [hdecomp, map_add, zeroSlice_deriv_spatial hf hzero, add_zero] at hcomp
  exact hcomp

end TauCeti
