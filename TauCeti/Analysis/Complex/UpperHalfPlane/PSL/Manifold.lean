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

Viewing `ℍ` as a real manifold, every element of `GL(2, ℝ)` and of `PGL(2, ℝ)` acts by `C^n`
maps for every `n`, including the elements of negative determinant, which act
antiholomorphically.

## Main declarations

* `UpperHalfPlane.instContMDiffConstSMulPSL2`: the action of each element of `PSL(2, ℝ)` is
  holomorphic.
* `TauCeti.UpperHalfPlane.instContMDiffConstSMulGLReal`,
  `TauCeti.UpperHalfPlane.instContMDiffConstSMulPGLReal`: each element of `GL(2, ℝ)` or
  `PGL(2, ℝ)` acts on `ℍ` by `C^n` maps of the underlying real manifold.
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

/-- Every element of `GL(2, ℝ)` acts on the upper half-plane by `C^n` maps, viewing `ℍ` as a real
manifold; the elements of negative determinant act antiholomorphically. -/
instance instContMDiffConstSMulGLReal {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n (GL (Fin 2) ℝ) ℍ where
  contMDiff_const_smul g := by
    apply ContMDiff.of_comp_isOpenEmbedding isOpenEmbedding_coe
    have hcomp : ((↑) ∘ (g • ·) : ℍ → ℂ) =
        (fun w : ℂ ↦ σ g (num g w / denom g w)) ∘ (↑) :=
      funext fun z ↦ coe_smul g z
    rw [hcomp]
    intro z
    have hnum : ContDiff ℂ n (num g) := by unfold num; fun_prop
    have hden : ContDiff ℂ n (denom g) := by unfold denom; fun_prop
    have hF : ContDiffAt ℝ n (fun w : ℂ ↦ σ g (num g w / denom g w)) z :=
      (σ g).toContinuousLinearEquiv.contDiff.contDiffAt.comp _
        ((hnum.contDiffAt.div hden.contDiffAt (denom_ne_zero g z)).restrict_scalars ℝ)
    exact hF.contMDiffAt.comp z contMDiffAt_extChartAt

/-- Every element of `PGL(2, ℝ)` acts on the upper half-plane by `C^n` maps, viewing `ℍ` as a real
manifold. -/
instance instContMDiffConstSMulPGLReal {n : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, ℂ) n PGL(2, ℝ) ℍ where
  contMDiff_const_smul q := by
    induction q using Matrix.ProjGenLinGroup.induction_on with | mk g =>
    simpa only [pglMk_smul] using contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := n) g

end TauCeti.UpperHalfPlane

end
