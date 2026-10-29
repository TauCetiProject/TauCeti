/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.Geometry.Manifold.Algebra.SMul

import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# The holomorphic projective action on the upper half-plane

Every element of `PSL(2, ℝ)` acts on the upper half-plane by a biholomorphism. This file expresses
holomorphy as a `ContMDiffConstSMul` instance, so each transformation is packaged by the generic
`Diffeomorph.constSmul` constructor. Subgroups inherit the same holomorphic action through the
generic instance `SetLike.contMDiffConstSMul`, which is the input needed to put complex charts on
their free orbit quotients.

## Main declarations

* `UpperHalfPlane.instContMDiffConstSMulPSL2`: the action of each element of `PSL(2, ℝ)` is
  holomorphic.
-/

public section

noncomputable section

open scoped ContDiff Manifold MatrixGroups UpperHalfPlane

namespace UpperHalfPlane

/-- The action of each element of `PSL(2, ℝ)` on the upper half-plane is holomorphic. -/
instance instContMDiffConstSMulPSL2 : ContMDiffConstSMul 𝓘(ℂ, ℂ) ∞ PSL(2, ℝ) ℍ where
  contMDiff_const_smul q := by
    refine QuotientGroup.induction_on q fun g ↦ ?_
    simpa only [pslMk_smul, Matrix.SpecialLinearGroup.toGL_smul] using
      UpperHalfPlane.contMDiff_smul (n := ∞)
        (g := Matrix.SpecialLinearGroup.toGL g) (by simp)

end UpperHalfPlane

end
