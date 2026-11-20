/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Fin
public import TauCeti.Analysis.Calculus.DifferentialForm.Plane
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
public import TauCeti.Geometry.Symplectic.Liouville.Linear

/-!
# The one-forms `x dy` and `y dx` on the real plane

This file defines the linear-coefficient forms `realPlaneXDy = x dy` and `realPlaneYDx = y dx`
and proves their exterior derivative identities `d(x dy) = dx ∧ dy` and `d(y dx) = -(dx ∧ dy)`.
So `-y dx` and `x dy` are both primitives of the standard area form. The form `y dx` is the
Liouville form `p dq` of the plane read as the cotangent bundle of the line, with position `x` and
momentum `y`. The constant coordinate forms and their identities are in
`TauCeti.Analysis.Calculus.DifferentialForm.Plane`.

Contracting `d(x dy)` with the vector field `Z = x ∂_x + ∂_y` gives `x dy - dx`
(`Prod.curryLeft_extDeriv_realPlaneXDy`), which differs from `x dy`
(`Prod.curryLeft_extDeriv_realPlaneXDy_ne`).

The area form `dx ∧ dy` takes the value `1` on the standard basis of the plane
(`Prod.realPlaneDx_wedge_realPlaneDy_finTwoProd`).

The computation of `d(x dy)` reuses the radial primitive calculation for a continuous bilinear
form from `TauCeti.Geometry.Symplectic.Liouville.Linear`.
-/

public section

noncomputable section

namespace Prod

/-- The area form `dx ∧ dy` takes the value `1` on the standard basis of the plane, so its
pullback by a linear map evaluates there to the determinant. -/
@[simp]
theorem realPlaneDx_wedge_realPlaneDy_finTwoProd (q : ℝ × ℝ) :
    ((realPlaneDx q).wedge (realPlaneDy q)) (Module.Basis.finTwoProd ℝ) = 1 := by
  have hbasis : ⇑(Module.Basis.finTwoProd ℝ) = ![((1 : ℝ), (0 : ℝ)), (0, 1)] := by
    funext i
    fin_cases i <;> simp
  rw [hbasis, ContinuousAlternatingMap.wedge_apply_one_one]
  simp [realPlaneDx_apply, realPlaneDy_apply]

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

/-- The coordinate one-form `y dx` on `ℝ × ℝ`. -/
def realPlaneYDx (p : ℝ × ℝ) : (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ :=
  p.2 • realPlaneDx p

/-- The coordinate one-form `y dx` evaluates to the second coordinate of the base point times the
first component of its argument. -/
@[simp]
theorem realPlaneYDx_apply (p : ℝ × ℝ) (v : Fin 1 → ℝ × ℝ) :
    realPlaneYDx p v = p.2 * (v 0).1 := by
  simp [realPlaneYDx]

/-- The coordinate one-form `y dx` is smooth. -/
theorem contDiff_realPlaneYDx {n : WithTop ℕ∞} : ContDiff ℝ n realPlaneYDx :=
  contDiff_snd.smul contDiff_realPlaneDx

/-- The exterior derivative of `y dx` is minus the standard area form, `d(y dx) = -(dx ∧ dy)`. -/
@[simp]
theorem extDeriv_realPlaneYDx (p : ℝ × ℝ) :
    extDeriv realPlaneYDx p = -(realPlaneDx p).wedge (realPlaneDy p) := by
  ext v
  -- Normalize the two arguments as a tuple so the pair formula for `d` applies.
  rw [show v = ![v 0, v 1] by funext i; fin_cases i <;> rfl,
    TauCeti.extDeriv_apply_pair_of_differentiableAt
      (contDiff_realPlaneYDx (n := 1)).differentiable_one.differentiableAt]
  simp only [realPlaneYDx_apply]
  rw [(hasFDerivAt_snd.mul_const _).fderiv, (hasFDerivAt_snd.mul_const _).fderiv]
  simp

end Prod
