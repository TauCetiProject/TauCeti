/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# Derivatives of maps built from a continuous bilinear map

The quadratic map `z ↦ B z z` attached to a continuous bilinear map `B : E →L[𝕜] E →L[𝕜] F` is
smooth, with derivative at `y` the polarization `B.flip y + B y` of `B` evaluated at `y`; since
that derivative is linear in `y`, the second derivative is the constant continuous linear map
`B.flip + B`. This is the derivative computation behind the local model of a nondegenerate
critical point, but it depends on nothing beyond the bilinear chain rule
`ContinuousLinearMap.hasStrictFDerivAt_of_bilinear` and the smoothness of bounded bilinear maps.

The same chain rule differentiates the pairing `y ↦ B (u y) (∂_w u y)` of a `C²` map `u` with one
of its directional derivatives, the one-form `x ↦ B x` pulled back along `u` and evaluated in the
direction `w`; its derivative involves the second derivative of `u`.

## Main results

* `ContinuousLinearMap.contDiff_apply_self`: `z ↦ B z z` is `C^n` for every `n`, and its
  corollary `ContinuousLinearMap.differentiable_apply_self`.
* `ContinuousLinearMap.hasStrictFDerivAt_apply_self`: `z ↦ B z z` is strictly
  differentiable at `y`, with derivative the polarization of `B` evaluated at `y`.
* `ContinuousLinearMap.hasFDerivAt_apply_self`, and its `fderiv` form
  `ContinuousLinearMap.fderiv_apply_self`.
* `ContinuousLinearMap.fderiv_fderiv_apply_self`: the second derivative of `z ↦ B z z` is
  the constant `B.flip + B`.
* `ContinuousLinearMap.hasFDerivAt_bilinear_fderiv_apply`: the derivative of
  `y ↦ B (u y) (∂_w u y)` at a point where `u` is `C²`.
-/

public section

namespace TauCeti

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : WithTop ℕ∞}


/-- The map `z ↦ B z z` attached to a continuous bilinear map `B` is `C^n` for every `n`. -/
theorem _root_.ContinuousLinearMap.contDiff_apply_self (B : E →L[𝕜] E →L[𝕜] F) : ContDiff 𝕜 n
    (fun z ↦ B z z) :=
  B.isBoundedBilinearMap.contDiff.comp₂ contDiff_id contDiff_id

/-- The map `z ↦ B z z` attached to a continuous bilinear map `B` is differentiable. -/
theorem _root_.ContinuousLinearMap.differentiable_apply_self (B : E →L[𝕜] E →L[𝕜] F) :
    Differentiable 𝕜 (fun z ↦ B z z) :=
  (ContinuousLinearMap.contDiff_apply_self (n := 1) B).differentiable one_ne_zero

/-- The map `z ↦ B z z` attached to a continuous bilinear map `B` is strictly differentiable at
`y`, with derivative the polarization of `B` evaluated at `y`. -/
theorem _root_.ContinuousLinearMap.hasStrictFDerivAt_apply_self (B : E →L[𝕜] E →L[𝕜] F) (y : E) :
    HasStrictFDerivAt (fun z ↦ B z z) (B.flip y + B y) y := by
  have h : HasStrictFDerivAt (fun z ↦ B z z)
      (B.precompR E y (ContinuousLinearMap.id 𝕜 E) +
        B.precompL E (ContinuousLinearMap.id 𝕜 E) y) y :=
    B.hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id y) (hasStrictFDerivAt_id y)
  convert h using 1
  ext v
  simp [add_comm]

/-- The map `z ↦ B z z` attached to a continuous bilinear map `B` is differentiable at `y`, with
derivative the polarization of `B` evaluated at `y`. -/
theorem _root_.ContinuousLinearMap.hasFDerivAt_apply_self (B : E →L[𝕜] E →L[𝕜] F) (y : E) :
    HasFDerivAt (fun z ↦ B z z) (B.flip y + B y) y :=
  (ContinuousLinearMap.hasStrictFDerivAt_apply_self B y).hasFDerivAt

/-- At `y`, the differential of `z ↦ B z z` is `B.flip y + B y`. -/
@[simp]
theorem _root_.ContinuousLinearMap.fderiv_apply_self (B : E →L[𝕜] E →L[𝕜] F) (y : E) :
    fderiv 𝕜 (fun z ↦ B z z) y = B.flip y + B y :=
  (ContinuousLinearMap.hasFDerivAt_apply_self B y).fderiv

/-- The second derivative of `z ↦ B z z` is the constant `B.flip + B`. -/
@[simp]
theorem _root_.ContinuousLinearMap.fderiv_fderiv_apply_self (B : E →L[𝕜] E →L[𝕜] F) (y : E) :
    fderiv 𝕜 (fderiv 𝕜 fun z ↦ B z z) y = B.flip + B := by
  have hEq : (fderiv 𝕜 fun z ↦ B z z) = fun z ↦ (B.flip + B) z := by
    funext z
    rw [ContinuousLinearMap.fderiv_apply_self, add_apply]
  rw [hEq]
  exact (B.flip + B).fderiv

/-- The derivative of `y ↦ B (u y) (∂_w u y)` in the direction `v`, at a point where `u` is `C²`,
is `B (u) (∂_v ∂_w u) + B (∂_v u) (∂_w u)`. -/
theorem _root_.ContinuousLinearMap.hasFDerivAt_bilinear_fderiv_apply (B : F →L[𝕜] F →L[𝕜] G)
    {u : E → F} {z : E} (hu : ContDiffAt 𝕜 2 u z) (w : E) :
    HasFDerivAt (fun y ↦ B (u y) (fderiv 𝕜 u y w))
      (B.precompR E (u z) ((fderiv 𝕜 (fderiv 𝕜 u) z).flip w) +
        B.precompL E (fderiv 𝕜 u z) (fderiv 𝕜 u z w)) z := by
  have hdu : DifferentiableAt 𝕜 (fderiv 𝕜 u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hw : HasFDerivAt (fun y ↦ fderiv 𝕜 u y w) ((fderiv 𝕜 (fderiv 𝕜 u) z).flip w) z := by
    simpa using hdu.hasFDerivAt.clm_apply (hasFDerivAt_const w z)
  exact B.hasFDerivAt_of_bilinear (hu.differentiableAt (by norm_num)).hasFDerivAt hw


end TauCeti

end
