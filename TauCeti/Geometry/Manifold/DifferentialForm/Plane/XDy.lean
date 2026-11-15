/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Symplectic.Liouville.Plane

/-!
# The variable-coordinate exterior derivative on the real plane

This file transfers the flat calculation `d(x dy) = dx ∧ dy` to the self-model manifold
`ℝ × ℝ`. It supplies the variable-coefficient half of the standard planar exterior-calculus
normalization; the constant-coordinate identity is the companion half of the same calculation.

The proof uses the model-space comparison for `mextDeriv` and the canonical flat calculation;
no new coordinate or wedge construction is introduced here.
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti

namespace Prod

/-- The manifold exterior derivative of `x dy` is the standard area form `dx ∧ dy`. -/
@[simp]
theorem mextDeriv_realPlaneXDy :
    mextDeriv (I := 𝓘(ℝ, ℝ × ℝ)) (M := ℝ × ℝ) (F := ℝ) (k := 1)
        ((fun p ↦ _root_.Prod.realPlaneXDy p) :
          RoughForm (𝓘(ℝ, ℝ × ℝ)) (ℝ × ℝ) ℝ 1) =
      ((fun p ↦ (_root_.Prod.realPlaneDx p).wedge (_root_.Prod.realPlaneDy p)) :
        RoughForm (𝓘(ℝ, ℝ × ℝ)) (ℝ × ℝ) ℝ 2) := by
  funext p
  have h := mextDeriv_eq_extDeriv
    ((fun p ↦ _root_.Prod.realPlaneXDy p) :
      RoughForm (𝓘(ℝ, ℝ × ℝ)) (ℝ × ℝ) ℝ 1) p
  exact h.trans (_root_.Prod.extDeriv_realPlaneXDy p)

end Prod

end TauCeti
