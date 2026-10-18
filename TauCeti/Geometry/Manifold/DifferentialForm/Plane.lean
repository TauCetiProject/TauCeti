/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Symplectic.Liouville.Plane

/-!
# Constant coordinate one-forms on the manifold real plane

This file records the manifold exterior derivative identities for the canonical constant coordinate
forms `dx` and `dy` on the self-model manifold `ℝ × ℝ`. It reuses the flat forms and their
existing exterior derivative lemmas across the model-space identification. The companion identity
`d(x dy) = dx ∧ dy` still requires the variable-coefficient calculation.
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti

namespace Prod

/-- The manifold exterior derivative of `dx` vanishes. -/
@[simp]
theorem mextDeriv_realPlaneDxForm :
    mextDeriv (I := 𝓘(ℝ, ℝ × ℝ)) (M := ℝ × ℝ) (F := ℝ) (k := 1)
        ((fun p ↦ _root_.Prod.realPlaneDx p) : RoughForm (𝓘(ℝ, ℝ × ℝ)) (ℝ × ℝ) ℝ 1) =
      (0 : RoughForm (𝓘(ℝ, ℝ × ℝ)) (ℝ × ℝ) ℝ 2) := by
  funext p
  have h := mextDeriv_eq_extDeriv
    ((fun p ↦ _root_.Prod.realPlaneDx p) : RoughForm (𝓘(ℝ, ℝ × ℝ)) (ℝ × ℝ) ℝ 1) p
  exact h.trans (_root_.Prod.extDeriv_realPlaneDx p)

/-- The manifold exterior derivative of `dy` vanishes. -/
@[simp]
theorem mextDeriv_realPlaneDyForm :
    mextDeriv (I := 𝓘(ℝ, ℝ × ℝ)) (M := ℝ × ℝ) (F := ℝ) (k := 1)
        ((fun p ↦ _root_.Prod.realPlaneDy p) : RoughForm (𝓘(ℝ, ℝ × ℝ)) (ℝ × ℝ) ℝ 1) =
      (0 : RoughForm (𝓘(ℝ, ℝ × ℝ)) (ℝ × ℝ) ℝ 2) := by
  funext p
  have h := mextDeriv_eq_extDeriv
    ((fun p ↦ _root_.Prod.realPlaneDy p) : RoughForm (𝓘(ℝ, ℝ × ℝ)) (ℝ × ℝ) ℝ 1) p
  exact h.trans (_root_.Prod.extDeriv_realPlaneDy p)

end Prod

end TauCeti
