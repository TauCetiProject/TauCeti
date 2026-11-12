/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Integral curves through their velocity

This file characterizes Mathlib's integral curves `IsMIntegralCurve γ v` in terms of the named
velocity `TauCeti.Manifold.curveVelocity` of a curve: `γ` is an integral curve of `v` exactly when
it is differentiable at every time with velocity `v (γ t)`. It is kept apart from
`TauCeti.Geometry.Manifold.MFDeriv.Curve`, so that the curve-derivative API does not carry
Mathlib's integral-curve import, and from `TauCeti.Geometry.Manifold.IntegralCurve.Basic`, so that
the latter does not expose the namespace `TauCeti.Manifold` to its importers.

## Main results

* `TauCeti.Manifold.isMIntegralCurve_iff_curveVelocity_eq`: a curve is an integral curve of a
  vector field exactly when it is differentiable with velocity given by the field at every time.
-/

public section

open scoped Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Integral curves through their velocity.** A curve is an integral curve of `v` exactly when
it is differentiable at every time `t` with velocity `v (γ t)`. -/
theorem isMIntegralCurve_iff_curveVelocity_eq {γ : ℝ → M} {v : (x : M) → TangentSpace I x} :
    IsMIntegralCurve γ v ↔ ∀ t, MDifferentiableAt 𝓘(ℝ) I γ t ∧ curveVelocity I γ t = v (γ t) := by
  refine ⟨fun hγ t ↦ ⟨(hγ t).mdifferentiableAt, ?_⟩, fun h t ↦ ?_⟩
  · simpa only [curveVelocityWithin_univ] using
      curveVelocityWithin_eq_of_hasMFDerivWithinAt (hγ t).hasMFDerivWithinAt
        uniqueDiffWithinAt_univ
  · rw [← (h t).2]
    exact hasMFDerivAt_curveVelocity (h t).1

end TauCeti.Manifold
