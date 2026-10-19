/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Plane
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic
public import TauCeti.Geometry.Symplectic.Liouville.Plane

/-!
# The `x dy` identity on the manifold real plane

This module transports the existing flat `d(x dy) = dx ∧ dy` calculation to the self-model
manifold. The flat coordinate forms are defined in the calculus differential-form module; the
`x dy` form remains with its Liouville calculation.
-/

public section

noncomputable section

open scoped Manifold

namespace Prod

/-- The manifold exterior derivative of `x dy` is `dx ∧ dy`. -/
theorem mextDeriv_realPlaneXDy :
    TauCeti.mextDeriv (I := 𝓘(ℝ, ℝ × ℝ)) (M := ℝ × ℝ) (F := ℝ) (k := 1)
        ((fun p ↦ _root_.Prod.realPlaneXDy p) : TauCeti.RoughForm (𝓘(ℝ, ℝ × ℝ))
          (ℝ × ℝ) ℝ 1) =
      TauCeti.RoughForm.wedge
        ((fun p ↦ _root_.Prod.realPlaneDx p) : TauCeti.RoughForm (𝓘(ℝ, ℝ × ℝ))
          (ℝ × ℝ) ℝ 1)
        ((fun p ↦ _root_.Prod.realPlaneDy p) : TauCeti.RoughForm (𝓘(ℝ, ℝ × ℝ))
          (ℝ × ℝ) ℝ 1) := by
  funext p
  have h := TauCeti.mextDeriv_eq_extDeriv
    ((fun p ↦ _root_.Prod.realPlaneXDy p) : TauCeti.RoughForm (𝓘(ℝ, ℝ × ℝ))
      (ℝ × ℝ) ℝ 1) p
  rw [h, _root_.Prod.extDeriv_realPlaneXDy]
  ext v
  rw [show v = ![v 0, v 1] by funext i; fin_cases i <;> rfl]
  rw [ContinuousAlternatingMap.wedge_apply_one_one]
  symm
  exact TauCeti.RoughForm.wedge_apply_one_one
    ((fun q ↦ _root_.Prod.realPlaneDx q) : TauCeti.RoughForm (𝓘(ℝ, ℝ × ℝ))
      (ℝ × ℝ) ℝ 1)
    ((fun q ↦ _root_.Prod.realPlaneDy q) : TauCeti.RoughForm (𝓘(ℝ, ℝ × ℝ))
      (ℝ × ℝ) ℝ 1) p (v 0) (v 1)

end Prod
