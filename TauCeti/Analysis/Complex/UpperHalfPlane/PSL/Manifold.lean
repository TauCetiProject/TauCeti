/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.Geometry.Manifold.Algebra.SMul

import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# The holomorphic and smooth projective actions on the upper half-plane

Every element of `PSL(2, ℝ)` acts on the upper half-plane by a biholomorphism, and more generally
every element of `PSL(2, R)` (for any `ℝ`-algebra `R`) acts by a real-analytic map for the real
manifold structure `𝓘(ℝ, ℂ)`. This file expresses both properties as `ContMDiffConstSMul`
instances, so each transformation is packaged by the generic `Diffeomorph.constSmul` constructor.
Subgroups inherit the same holomorphic or smooth action through `SetLike.contMDiffConstSMul`,
which is the input needed to put complex or smooth charts on their free orbit quotients.

## Main declarations

* `UpperHalfPlane.instContMDiffConstSMulPSL2`: the action of each element of `PSL(2, ℝ)` is
  holomorphic (`𝓘(ℂ, ℂ)`).
* `TauCeti.UpperHalfPlane.instContMDiffConstSMulPSL2Real`: the action of each element of
  `PSL(2, R)` is real-analytic (`𝓘(ℝ, ℂ)`).
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

namespace TauCeti.UpperHalfPlane

open _root_.UpperHalfPlane

/-- Every element of `PSL(2, R)` acts on `ℍ` by a real-analytic map. -/
instance instContMDiffConstSMulPSL2Real {R : Type*} [CommRing R] [Algebra R ℝ] {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n PSL(2, R) ℍ where
  contMDiff_const_smul q := by
    refine QuotientGroup.induction_on q fun g ↦ ?_
    simpa only [pslMk_smul] using contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := n) g

end TauCeti.UpperHalfPlane

end
