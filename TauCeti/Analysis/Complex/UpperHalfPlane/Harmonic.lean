/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Harmonic.Analytic
import TauCeti.Analysis.Complex.UpperHalfPlane.Primitive

/-!
# Harmonic conjugates on the upper half-plane

A harmonic function `u` on the upper half-plane `ℂ₊` is the imaginary part of a holomorphic
function on `ℂ₊` (`TauCeti.exists_differentiableOn_im_eq_of_harmonicOnNhd`).

The complex partial `∂ₓu - i ∂ᵧu` of `u` is holomorphic on `ℂ₊`
(`HarmonicAt.differentiableAt_complex_partial`), so its wedge integral is a primitive there
(`DifferentiableOn.hasDerivAt_wedgeIntegral_upperHalfPlane`); the real part of the primitive has
the gradient of `u`, and `i` times the primitive, suitably normalized, is a holomorphic `F` with
`Im F = u`. The proof adapts Mathlib's
`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq` (the same statement for the real
part on a ball), replacing the primitive on a ball
(`DifferentiableOn.isExactOn_ball`) by the wedge-integral primitive on `ℂ₊`.

## Main results

* `TauCeti.exists_differentiableOn_im_eq_of_harmonicOnNhd`: a harmonic function on `ℂ₊` is the
  imaginary part of a holomorphic function on `ℂ₊`.
-/

public section

noncomputable section

open Complex Set InnerProductSpace
open UpperHalfPlane (upperHalfPlaneSet)

namespace TauCeti

/-- **A harmonic function on the upper half-plane is the imaginary part of a holomorphic
function.** The proof adapts Mathlib's
`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`, with the wedge-integral
primitive on `ℂ₊` in place of the primitive on a ball. -/
theorem exists_differentiableOn_im_eq_of_harmonicOnNhd {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u upperHalfPlaneSet) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F upperHalfPlaneSet ∧
      EqOn (fun z ↦ (F z).im) u upperHalfPlaneSet := by
  -- the complex partial `∂ₓu - i ∂ᵧu`, and its wedge-integral primitive `G`
  let g : ℂ → ℂ := fun z ↦ fderiv ℝ u z 1 - I * fderiv ℝ u z I
  have hg : DifferentiableOn ℂ g upperHalfPlaneSet := fun z hz ↦
    (HarmonicAt.differentiableAt_complex_partial (hu z hz)).differentiableWithinAt
  let G : ℂ → ℂ := fun w ↦ wedgeIntegral (UpperHalfPlane.I : ℂ) w g
  have hG (z : ℂ) (hz : z ∈ upperHalfPlaneSet) : HasDerivAt G (g z) z :=
    hg.hasDerivAt_wedgeIntegral_upperHalfPlane UpperHalfPlane.I hz
  have hGd : DifferentiableOn ℂ G upperHalfPlaneSet := fun z hz ↦
    (hG z hz).differentiableAt.differentiableWithinAt
  have hI : (I : ℂ) ∈ upperHalfPlaneSet := by simp
  -- the real part of `G` is `u - u(i)`
  have hre : EqOn (fun z ↦ (G z).re) (fun z ↦ u z - u I) upperHalfPlaneSet := by
    have hopen := UpperHalfPlane.isOpen_upperHalfPlaneSet
    refine (convex_halfSpace_im_gt 0).eqOn_of_fderivWithin_eq (𝕜 := ℝ) (x := I)
      (reCLM.differentiable.comp_differentiableOn (hGd.restrictScalars ℝ))
      (fun y hy ↦ (((hu y hy).1.differentiableAt two_ne_zero).sub_const
        (u I)).differentiableWithinAt)
      hopen.uniqueDiffOn (fun y hy ↦ ?_) hI ?_
    · -- both sides have derivative `fderiv ℝ u y` at `y`
      have hu' := ((hu y hy).1.differentiableAt two_ne_zero).hasFDerivAt.sub_const (u I)
      have hGre : HasFDerivAt (fun z ↦ (G z).re) (fderiv ℝ u y) y := by
        refine (reCLM.hasFDerivAt.comp y ((hG y hy).hasFDerivAt.restrictScalars ℝ)).congr_fderiv ?_
        ext a
        conv_rhs => rw [(by simp : a = a.re • (1 : ℂ) + a.im • (I : ℂ)), map_add, map_smul,
          map_smul]
        simp [g]
      rw [hGre.hasFDerivWithinAt.fderivWithin (hopen.uniqueDiffWithinAt hy),
        hu'.hasFDerivWithinAt.fderivWithin (hopen.uniqueDiffWithinAt hy)]
    · simp [G, wedgeIntegral]
  refine ⟨fun z ↦ I * (G z + u I), (hGd.add_const _).const_mul I, fun z hz ↦ ?_⟩
  have := hre hz
  simp only [mul_im, I_re, zero_mul, I_im, one_mul, zero_add, add_re, ofReal_re] at this ⊢
  linarith

end TauCeti
