/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity (Gemini 4 Carbon)
-/
module

public import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-!
# Displacement pullback along continuous affine equivalences

This file records basic displacement-pullback lemmas for continuous affine equivalences
(`ContinuousAffineEquiv`):

* `ContinuousAffineEquiv.linear_symm_apply_vsub`: the inverse linear part of a continuous affine
  equivalence pulls back the displacement between image points in an affine torsor.
* `ContinuousAffineEquiv.linear_symm_apply_sub`: the module specialization for differences of
  image points.
-/

public section

namespace ContinuousAffineEquiv

/-- Pulling back the displacement between two images along `e.toAffineEquiv.linear.symm` recovers
the original displacement vector. -/
theorem linear_symm_apply_vsub {𝕜 V W P Q : Type*} [Ring 𝕜] [AddCommGroup V] [AddCommGroup W]
    [Module 𝕜 V] [Module 𝕜 W] [TopologicalSpace P] [TopologicalSpace Q]
    [AddTorsor V P] [AddTorsor W Q] (e : P ≃ᴬ[𝕜] Q) (x y : P) :
    e.toAffineEquiv.linear.symm (e x -ᵥ e y) = x -ᵥ y := by
  simpa using e.toAffineEquiv.symm.toAffineMap.linear_apply_vsub (e x) (e y)

/-- Pulling back the difference of two module images along `e.toAffineEquiv.linear.symm` recovers
the original difference. -/
theorem linear_symm_apply_sub {𝕜 V U : Type*} [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [TopologicalSpace V] [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U]
    (e : V ≃ᴬ[𝕜] U) (x y : V) :
    e.toAffineEquiv.linear.symm (e x - e y) = x - y := by
  simpa only [vsub_eq_sub] using e.linear_symm_apply_vsub x y

end ContinuousAffineEquiv
