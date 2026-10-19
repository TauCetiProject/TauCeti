/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Plane
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
public import TauCeti.Geometry.Symplectic.Liouville.Linear

/-!
# Coordinate one-forms on the real plane

This file defines the linear-coefficient form `realPlaneXDy = x dy` and proves its exterior
derivative identity. The constant coordinate forms and their identities are in
`TauCeti.Analysis.Calculus.DifferentialForm.Plane`.

The computation of `d(x dy)` reuses the radial primitive calculation for a continuous bilinear
form from `TauCeti.Geometry.Symplectic.Liouville.Linear`.
-/

public section

noncomputable section

namespace Prod

/-- The coordinate one-form `x dy` on `ℝ × ℝ`. -/
def realPlaneXDy (p : ℝ × ℝ) : (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ :=
  p.1 • realPlaneDy p

/-- The coordinate one-form `x dy` evaluates to the first coordinate of the base point times the
second component of its argument. -/
@[simp]
theorem realPlaneXDy_apply (p : ℝ × ℝ) (v : Fin 1 → ℝ × ℝ) :
    realPlaneXDy p v = p.1 * (v 0).2 := by
  simp [realPlaneXDy]

private def realPlaneXDyBilinear : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)

private theorem realPlaneXDy_eq_liouvilleFormCLM :
    realPlaneXDy = ContinuousLinearMap.liouvilleFormCLM (2 • realPlaneXDyBilinear) := by
  funext p
  ext v
  simp [realPlaneXDyBilinear]

/-- The exterior derivative of `x dy` is the standard area form `dx ∧ dy`. -/
@[simp]
theorem extDeriv_realPlaneXDy (p : ℝ × ℝ) :
    extDeriv realPlaneXDy p = (realPlaneDx p).wedge (realPlaneDy p) := by
  rw [realPlaneXDy_eq_liouvilleFormCLM]
  ext v
  rw [ContinuousLinearMap.extDeriv_liouvilleFormCLM_apply]
  -- Normalize the two arguments as a tuple so the wedge evaluation simp lemma applies.
  rw [show v = ![v 0, v 1] by funext i; fin_cases i <;> rfl]
  simp [realPlaneXDyBilinear]
  ring_nf

end Prod
