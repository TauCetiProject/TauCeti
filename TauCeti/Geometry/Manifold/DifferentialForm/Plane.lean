/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv

/-!
# Constant coordinate one-forms on the manifold real plane

This file defines the constant coordinate forms `dx` and `dy` on the self-model manifold
`ℝ × ℝ` and proves that their manifold exterior derivatives vanish. The forms are written
explicitly in the tangent fibres, so the result remains available across the module-system
opacity boundary. The companion identity `d(x dy) = dx ∧ dy` still requires the variable
coefficient calculation.
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti

namespace Prod

/-- The constant `dx` one-form on the self-model manifold `ℝ × ℝ`. -/
abbrev realPlaneDxForm : RoughForm (𝓘(ℝ, ℝ × ℝ)) (ℝ × ℝ) ℝ 1 := fun _ ↦
  ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ) ℝ (0 : Fin 1)
    (ContinuousLinearMap.fst ℝ ℝ ℝ)

/-- The constant `dy` one-form on the self-model manifold `ℝ × ℝ`. -/
abbrev realPlaneDyForm : RoughForm (𝓘(ℝ, ℝ × ℝ)) (ℝ × ℝ) ℝ 1 := fun _ ↦
  ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ) ℝ (0 : Fin 1)
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- The manifold exterior derivative of `dx` vanishes. -/
@[simp]
theorem mextDeriv_realPlaneDxForm :
    mextDeriv (I := 𝓘(ℝ, ℝ × ℝ)) (M := ℝ × ℝ) (F := ℝ) (k := 1) realPlaneDxForm =
      (0 : RoughForm (𝓘(ℝ, ℝ × ℝ)) (ℝ × ℝ) ℝ 2) := by
  funext p
  rw [mextDeriv_eq_extDeriv]
  exact ContinuousAlternatingMap.extDeriv_const _ p

/-- The manifold exterior derivative of `dy` vanishes. -/
@[simp]
theorem mextDeriv_realPlaneDyForm :
    mextDeriv (I := 𝓘(ℝ, ℝ × ℝ)) (M := ℝ × ℝ) (F := ℝ) (k := 1) realPlaneDyForm =
      (0 : RoughForm (𝓘(ℝ, ℝ × ℝ)) (ℝ × ℝ) ℝ 2) := by
  funext p
  rw [mextDeriv_eq_extDeriv]
  exact ContinuousAlternatingMap.extDeriv_const _ p

end Prod

end TauCeti
