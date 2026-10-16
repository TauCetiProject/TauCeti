/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Const
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
public import TauCeti.Geometry.Symplectic.Liouville.Linear

/-!
# Coordinate one-forms on the real plane

This file defines the constant coordinate one-forms `realPlaneDx` and `realPlaneDy` on
`ℝ × ℝ`, together with the linear-coefficient form `realPlaneXDy = x dy`. Their exterior
derivatives fix the standard planar sign convention:

`d(dx) = 0` and `d(x dy) = dx ∧ dy`.

The computation of `d(x dy)` reuses the radial primitive calculation for a continuous bilinear
form from
`TauCeti.Geometry.Symplectic.Liouville.Linear`.
-/

public section

noncomputable section

namespace Prod

/-- The constant coordinate one-form `dx` on `ℝ × ℝ`. -/
def realPlaneDx (_ : ℝ × ℝ) : (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ) ℝ (0 : Fin 1)
    (ContinuousLinearMap.fst ℝ ℝ ℝ)

/-- The constant coordinate one-form `dy` on `ℝ × ℝ`. -/
def realPlaneDy (_ : ℝ × ℝ) : (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ) ℝ (0 : Fin 1)
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- The coordinate one-form `x dy` on `ℝ × ℝ`. -/
def realPlaneXDy (p : ℝ × ℝ) : (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ :=
  p.1 • realPlaneDy p

/-- The coordinate one-form `dx` evaluates to the first component of its argument. -/
@[simp]
theorem realPlaneDx_apply (p : ℝ × ℝ) (v : Fin 1 → ℝ × ℝ) :
    realPlaneDx p v = (v 0).1 := by
  simp [realPlaneDx]

/-- The coordinate one-form `dy` evaluates to the second component of its argument. -/
@[simp]
theorem realPlaneDy_apply (p : ℝ × ℝ) (v : Fin 1 → ℝ × ℝ) :
    realPlaneDy p v = (v 0).2 := by
  simp [realPlaneDy]

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

/-- The exterior derivative of the constant coordinate one-form `dx` vanishes. -/
@[simp]
theorem extDeriv_realPlaneDx (p : ℝ × ℝ) : extDeriv realPlaneDx p = 0 := by
  have hconst : realPlaneDx = fun _ : ℝ × ℝ ↦ realPlaneDx p := by rfl
  rw [hconst]
  exact ContinuousAlternatingMap.extDeriv_const (realPlaneDx p) p

/-- The exterior derivative of the constant coordinate one-form `dy` vanishes. -/
@[simp]
theorem extDeriv_realPlaneDy (p : ℝ × ℝ) : extDeriv realPlaneDy p = 0 := by
  have hconst : realPlaneDy = fun _ : ℝ × ℝ ↦ realPlaneDy p := by rfl
  rw [hconst]
  exact ContinuousAlternatingMap.extDeriv_const (realPlaneDy p) p

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
