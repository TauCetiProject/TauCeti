/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus.Orientation

/-!
# The open Möbius band

The open Möbius band is the quotient of the plane `ℝ × ℝ` by `(t + 1, y) ∼ (t, -y)`, the smooth
mapping torus of the reflection `y ↦ -y` of the real line (`TauCeti.MoebiusBand`). As a smooth
mapping torus it is a smooth surface, modelled on `𝓘(ℝ).prod 𝓘(ℝ)`.

The reflection reverses the orientation of `ℝ`, and `ℝ` is connected, so the Möbius band is not
orientable (`TauCeti.MoebiusBand.not_orientable`), by the orientability criterion for mapping tori
`TauCeti.SmoothMappingTorus.orientable_iff_forall_isOrientationPreservingAt`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 15 (the Möbius band is not orientable).
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti

/-- The **open Möbius band**: the quotient of `ℝ × ℝ` by `(t + 1, y) ∼ (t, -y)`, the smooth mapping
torus of the reflection `y ↦ -y` of `ℝ`. -/
abbrev MoebiusBand : Type :=
  SmoothMappingTorus (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ).toDiffeomorph

namespace MoebiusBand

/-- The class of `(t, y)` in the open Möbius band. -/
abbrev mk (t y : ℝ) : MoebiusBand :=
  SmoothMappingTorus.mk _ t y

/-- The identification defining the open Möbius band: `(t + 1, y) ∼ (t, -y)`. -/
theorem mk_add_one (t y : ℝ) : mk (t + 1) y = mk t (-y) :=
  SmoothMappingTorus.mk_add_one _ t y

/-- **The open Möbius band is not orientable.** -/
theorem not_orientable : ¬ Orientable (𝓘(ℝ).prod 𝓘(ℝ)) MoebiusBand :=
  SmoothMappingTorus.not_orientable_of_isOrientationReversingAt _ Manifold.Orientation.real
    (x := 0) (Manifold.Orientation.isOrientationReversingAt_of_det_neg _ _ (by simp) 0)

end MoebiusBand

end TauCeti
