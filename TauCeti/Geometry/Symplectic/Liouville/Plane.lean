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
# The one-form `x dy` on the real plane

This file defines the linear-coefficient form `realPlaneXDy = x dy` and proves its exterior
derivative identity. The constant coordinate forms and their identities are in
`TauCeti.Analysis.Calculus.DifferentialForm.Plane`.

Contracting `d(x dy)` with the vector field `Z = x ∂_x + ∂_y` gives `x dy - dx`
(`Prod.curryLeft_extDeriv_realPlaneXDy`), which differs from `x dy`
(`Prod.curryLeft_extDeriv_realPlaneXDy_ne`).

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

/-- The coordinate one-form `x dy` is smooth, being linear in the base point. -/
theorem contDiff_realPlaneXDy {n : WithTop ℕ∞} : ContDiff ℝ n realPlaneXDy := by
  rw [realPlaneXDy_eq_liouvilleFormCLM]
  exact ContinuousLinearMap.contDiff _

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

/-- For the vector field `Z = x ∂_x + ∂_y`, `ι_Z d(x dy) = x dy - dx`. -/
theorem curryLeft_extDeriv_realPlaneXDy (p : ℝ × ℝ) :
    (extDeriv realPlaneXDy p).curryLeft (p.1, 1) = realPlaneXDy p - realPlaneDx p := by
  ext v
  -- Write the single vector as the one-entry tuple `![v 0]` so the wedge evaluation applies.
  rw [← Matrix.cons_head_tail v, Matrix.empty_eq (Matrix.vecTail v)]
  simp

/-- The vector field `Z = x ∂_x + ∂_y` is not the Liouville field of the primitive `x dy` of
`dx ∧ dy`: `ι_Z d(x dy) ≠ x dy` at every point. -/
theorem curryLeft_extDeriv_realPlaneXDy_ne (p : ℝ × ℝ) :
    (extDeriv realPlaneXDy p).curryLeft (p.1, 1) ≠ realPlaneXDy p := by
  rw [curryLeft_extDeriv_realPlaneXDy, Ne, sub_eq_self]
  intro h
  simpa using congrArg (fun f ↦ f ![(1, 0)]) h

end Prod
