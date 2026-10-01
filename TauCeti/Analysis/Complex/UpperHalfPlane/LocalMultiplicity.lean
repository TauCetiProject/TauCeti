/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.Analysis.Complex.RiemannSurface.LocalMultiplicity

/-!
# Local multiplicities of complex-valued functions on the upper half-plane

The upper half-plane is an open subset of `ℂ`, and its complex-manifold structure has the single
chart given by the inclusion, with inverse `UpperHalfPlane.ofComplex`. So the local multiplicity of
a function `f : ℍ → ℂ` at `z` is the order of vanishing of `f ∘ ofComplex - f z` at `z`
(`TauCeti.UpperHalfPlane.localMultiplicity_eq_analyticOrderNatAt_sub`). This is the form in which
orders of modular forms and modular functions are computed, and the form in which they enter
the ramification theory of the orbit projection.
-/

public section

open UpperHalfPlane TauCeti.RiemannSurface

namespace TauCeti.UpperHalfPlane

/-- On the upper half-plane, the local multiplicity of `f : ℍ → ℂ` at `z` is the order of vanishing
of `f ∘ ofComplex - f z` at `z`. -/
@[simp]
theorem localMultiplicity_eq_analyticOrderNatAt_sub (f : ℍ → ℂ) (z : ℍ) :
    localMultiplicity f z = analyticOrderNatAt (fun w ↦ f (ofComplex w) - f z) z := by
  -- The chart of `ℍ` at every point is the inclusion into `ℂ`, whose inverse is `ofComplex`,
  -- and the chart of `ℂ` at every point is the identity.
  rw [localMultiplicity_def]
  rfl

end TauCeti.UpperHalfPlane
