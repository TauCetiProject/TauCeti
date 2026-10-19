/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Analysis.Calculus.DifferentialForm.Plane

/-!
# Constant coordinate one-forms on the manifold real plane

This file records the manifold exterior derivative identities for the canonical constant coordinate
forms `dx` and `dy` on the self-model manifold `ℝ × ℝ`. It reuses the flat forms and their existing
exterior derivative lemmas across the model-space identification.
-/

public section

noncomputable section

open scoped Manifold

namespace Prod

/-- The manifold exterior derivative of `dx` vanishes. -/
@[simp]
theorem mextDeriv_realPlaneDx :
    TauCeti.mextDeriv (I := 𝓘(ℝ, ℝ × ℝ)) (M := ℝ × ℝ) (F := ℝ) (k := 1)
        ((fun p ↦ _root_.Prod.realPlaneDx p) : TauCeti.RoughForm (𝓘(ℝ, ℝ × ℝ))
          (ℝ × ℝ) ℝ 1) =
      (0 : TauCeti.RoughForm (𝓘(ℝ, ℝ × ℝ)) (ℝ × ℝ) ℝ 2) := by
  have hconst : (fun p ↦ _root_.Prod.realPlaneDx p) =
      (fun _ ↦ _root_.Prod.realPlaneDx (0, 0)) := by
    funext p
    ext v
    simp
  rw [hconst]
  exact TauCeti.mextDeriv_const (_root_.Prod.realPlaneDx (0, 0))

/-- The manifold exterior derivative of `dy` vanishes. -/
@[simp]
theorem mextDeriv_realPlaneDy :
    TauCeti.mextDeriv (I := 𝓘(ℝ, ℝ × ℝ)) (M := ℝ × ℝ) (F := ℝ) (k := 1)
        ((fun p ↦ _root_.Prod.realPlaneDy p) : TauCeti.RoughForm (𝓘(ℝ, ℝ × ℝ))
          (ℝ × ℝ) ℝ 1) =
      (0 : TauCeti.RoughForm (𝓘(ℝ, ℝ × ℝ)) (ℝ × ℝ) ℝ 2) := by
  have hconst : (fun p ↦ _root_.Prod.realPlaneDy p) =
      (fun _ ↦ _root_.Prod.realPlaneDy (0, 0)) := by
    funext p
    ext v
    simp
  rw [hconst]
  exact TauCeti.mextDeriv_const (_root_.Prod.realPlaneDy (0, 0))

end Prod
