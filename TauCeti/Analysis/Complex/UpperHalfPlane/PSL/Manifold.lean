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

Viewing `ℍ` as a real manifold, every element of `GL(2, ℝ)`, including the antiholomorphic ones of
negative determinant, acts smoothly; this is also recorded as a `ContMDiffConstSMul` instance.

## Main declarations

* `UpperHalfPlane.instContMDiffConstSMulPSL2`: the action of each element of `PSL(2, ℝ)` is
  holomorphic.
* `UpperHalfPlane.instContMDiffConstSMulGL2Real`: the action of each element of `GL(2, ℝ)` is
  smooth for the real manifold structure.
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

/-- Every element of `GL(2, ℝ)` acts smoothly on the upper half-plane as a real manifold,
including the elements of negative determinant, which act antiholomorphically. -/
instance instContMDiffConstSMulGL2Real {n : WithTop ℕ∞} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n (GL (Fin 2) ℝ) ℍ where
  contMDiff_const_smul g := by
    refine ContMDiff.of_le ?_ le_top
    refine ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_coe fun τ ↦ ?_
    have hnum : ContDiff ℂ ω (num g) := by unfold num; fun_prop
    have hden : ContDiff ℂ ω (denom g) := by unfold denom; fun_prop
    have hF : ContDiffAt ℝ ω (fun w : ℂ ↦ σ g (num g w / denom g w)) τ :=
      (σ g).toContinuousLinearEquiv.contDiff.contDiffAt.comp _
        ((hnum.contDiffAt.div hden.contDiffAt (denom_ne_zero g τ)).restrict_scalars ℝ)
    have hcoe : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ω ((↑) : ℍ → ℂ) τ := contMDiffAt_extChartAt
    exact hF.contMDiffAt.comp τ hcoe

end UpperHalfPlane

end
