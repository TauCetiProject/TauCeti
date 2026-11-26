/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Complex.Harmonic.Analytic
import TauCeti.Analysis.Complex.HasPrimitives.SimplyConnected

/-!
# Harmonic conjugates on simply connected domains

A harmonic function `u` on a simply connected open set `U ⊆ ℂ` is the real part of an analytic
function on `U`
(`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_re_eq_of_isSimplyConnected`).

The complex partial `∂ₓu - i ∂ᵧu` of `u` is holomorphic on `U`
(`HarmonicAt.differentiableAt_complex_partial`), so it has a primitive there
(`DifferentiableOn.isExactOn_of_isSimplyConnected`); the real part of the primitive has the
gradient of `u`, so the primitive, suitably normalized, is an analytic `F` with `Re F = u`. This
generalizes Mathlib's `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq` and
`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq` (the same statement on a ball
and on `ℂ`), and its proof adapts the ball case, replacing the primitive on a ball
(`DifferentiableOn.isExactOn_ball`) by the primitive on a simply connected domain.

## Main results

* `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_re_eq_of_isSimplyConnected`: a harmonic
  function on a simply connected open set is the real part of an analytic function there.
-/

public section

noncomputable section

open Complex Set InnerProductSpace

namespace InnerProductSpace.HarmonicOnNhd

/-- **A harmonic function on a simply connected domain is the real part of an analytic function.**
This generalizes Mathlib's `InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq` and
`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_univ_re_eq` from a ball and `ℂ` to any
simply connected open set. -/
theorem exists_analyticOnNhd_re_eq_of_isSimplyConnected {u : ℂ → ℝ} {U : Set ℂ}
    (hu : HarmonicOnNhd u U) (hU : IsOpen U) (hUc : IsSimplyConnected U) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F U ∧ EqOn (fun z ↦ (F z).re) u U := by
  -- the complex partial `∂ₓu - i ∂ᵧu`, and its primitive `G`
  let g : ℂ → ℂ := fun z ↦ fderiv ℝ u z 1 - I * fderiv ℝ u z I
  have hg : DifferentiableOn ℂ g U := fun z hz ↦
    (HarmonicAt.differentiableAt_complex_partial (hu z hz)).differentiableWithinAt
  obtain ⟨G, hG⟩ := hg.isExactOn_of_isSimplyConnected hU hUc
  have hGd : DifferentiableOn ℂ G U := fun z hz ↦
    (hG z hz).differentiableAt.differentiableWithinAt
  obtain ⟨z₀, hz₀⟩ := hUc.nonempty
  -- the real part of `G` is `u` up to the constant `c`
  set c : ℝ := u z₀ - (G z₀).re
  have hre : EqOn (fun z ↦ (G z).re) (fun z ↦ u z - c) U := by
    refine hU.eqOn_of_fderiv_eq hUc.isPathConnected.isConnected.isPreconnected
      (reCLM.differentiable.comp_differentiableOn (hGd.restrictScalars ℝ))
      (fun y hy ↦ (((hu y hy).1.differentiableAt two_ne_zero).sub_const c).differentiableWithinAt)
      (fun y hy ↦ ?_) hz₀ (by simp [c])
    -- both sides have derivative `fderiv ℝ u y` at `y`
    have hu' := ((hu y hy).1.differentiableAt two_ne_zero).hasFDerivAt.sub_const c
    have hGre : HasFDerivAt (fun z ↦ (G z).re) (fderiv ℝ u y) y := by
      refine (reCLM.hasFDerivAt.comp y ((hG y hy).hasFDerivAt.restrictScalars ℝ)).congr_fderiv ?_
      ext a
      conv_rhs => rw [(by simp : a = a.re • (1 : ℂ) + a.im • (I : ℂ)), map_add, map_smul,
        map_smul]
      simp [g]
    rw [hGre.fderiv, hu'.fderiv]
  refine ⟨fun z ↦ G z + c, (hGd.add_const _).analyticOnNhd hU, fun z hz ↦ ?_⟩
  have := hre hz
  simp only [add_re, ofReal_re] at this ⊢
  linarith

end InnerProductSpace.HarmonicOnNhd
