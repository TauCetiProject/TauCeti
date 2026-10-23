/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Const

/-!
# Coordinate one-forms on the real plane

This file defines the constant coordinate one-forms `realPlaneDx` and `realPlaneDy` on
`ℝ × ℝ`, together with their exterior derivative identities.
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

/-- The constant coordinate one-form `dx` is smooth. -/
theorem contDiff_realPlaneDx {n : WithTop ℕ∞} : ContDiff ℝ n realPlaneDx :=
  contDiff_const

/-- The constant coordinate one-form `dy` is smooth. -/
theorem contDiff_realPlaneDy {n : WithTop ℕ∞} : ContDiff ℝ n realPlaneDy :=
  contDiff_const

/-- The coordinate one-form `dx` is independent of its base point. -/
theorem realPlaneDx_eq_const : realPlaneDx = fun _ : ℝ × ℝ ↦ realPlaneDx (0, 0) := by
  funext p
  ext v
  simp

/-- The coordinate one-form `dy` is independent of its base point. -/
theorem realPlaneDy_eq_const : realPlaneDy = fun _ : ℝ × ℝ ↦ realPlaneDy (0, 0) := by
  funext p
  ext v
  simp

/-- The exterior derivative of the constant coordinate one-form `dx` vanishes. -/
@[simp]
theorem extDeriv_realPlaneDx (p : ℝ × ℝ) : extDeriv realPlaneDx p = 0 := by
  rw [realPlaneDx_eq_const]
  exact ContinuousAlternatingMap.extDeriv_const (realPlaneDx (0, 0)) p

/-- The exterior derivative of the constant coordinate one-form `dy` vanishes. -/
@[simp]
theorem extDeriv_realPlaneDy (p : ℝ × ℝ) : extDeriv realPlaneDy p = 0 := by
  rw [realPlaneDy_eq_const]
  exact ContinuousAlternatingMap.extDeriv_const (realPlaneDy (0, 0)) p

end Prod
