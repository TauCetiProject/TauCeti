/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ContinuousLinearMap
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# The Cauchy–Riemann criterion in complex normed spaces

A real-differentiable map between complex normed spaces is complex-differentiable precisely
when its real derivative commutes with multiplication by `I`. Unlike the one-variable test
at `1` and `I`, this tests every vector in the domain. No finite-dimensionality is needed.

This generalizes Mathlib's `differentiableWithinAt_complex_iff_differentiableWithinAt_real`
in `Mathlib.Analysis.Complex.Conformal` and adapts its proof using
`differentiableWithinAt_iff_restrictScalars` and the general-domain analogue of
`ContinuousLinearMap.complexOfReal`. These results allow the same test to be applied to
coordinate representatives of manifold maps.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, Chapter I.
-/

public section

namespace TauCeti

open Complex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F} {s : Set E} {x : E}

/-- The Cauchy–Riemann criterion within a set with unique real derivatives: the real derivative
must commute with multiplication by `I` on every vector. -/
theorem differentiableWithinAt_complex_iff_map_I_smul (hs : UniqueDiffWithinAt ℝ s x) :
    DifferentiableWithinAt ℂ f s x ↔ DifferentiableWithinAt ℝ f s x ∧
      ∀ v, fderivWithin ℝ f s x (I • v) = I • fderivWithin ℝ f s x v := by
  constructor
  · intro hf
    refine ⟨hf.restrictScalars ℝ, ?_⟩
    rw [← hf.restrictScalars_fderivWithin ℝ hs]
    intro v
    exact (fderivWithin ℂ f s x).map_smul I v
  · rintro ⟨hf, hI⟩
    exact (differentiableWithinAt_iff_restrictScalars ℝ hf hs).2
      ⟨(fderivWithin ℝ f s x).complexOfRealOfMapISmul hI, by simp⟩

/-- A map between complex normed spaces is complex-differentiable at a point exactly when it
is real-differentiable there and its real derivative commutes with multiplication by `I`. -/
theorem differentiableAt_complex_iff_map_I_smul :
    DifferentiableAt ℂ f x ↔ DifferentiableAt ℝ f x ∧
      ∀ v, fderiv ℝ f x (I • v) = I • fderiv ℝ f x v := by
  simpa only [differentiableWithinAt_univ, fderivWithin_univ] using
    (differentiableWithinAt_complex_iff_map_I_smul
    (f := f) (uniqueDiffWithinAt_univ (𝕜 := ℝ) (x := x)))

/-- Under the Cauchy–Riemann condition, the complex derivative within a set is the real
derivative regarded as a complex-linear map. -/
theorem _root_.DifferentiableWithinAt.fderiv_complex_of_map_I_smul
    (hf : DifferentiableWithinAt ℝ f s x)
    (hI : ∀ v, fderivWithin ℝ f s x (I • v) = I • fderivWithin ℝ f s x v)
    (hs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℂ f s x = (fderivWithin ℝ f s x).complexOfRealOfMapISmul hI := by
  have h := ((differentiableWithinAt_complex_iff_map_I_smul hs).2
    ⟨hf, hI⟩).restrictScalars_fderivWithin ℝ hs
  ext v
  simpa only [ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.coe_complexOfRealOfMapISmul] using DFunLike.congr_fun h v

/-- Under the Cauchy–Riemann condition, the complex derivative is the real derivative
regarded as a complex-linear map. -/
theorem _root_.DifferentiableAt.fderiv_complex_of_map_I_smul (hf : DifferentiableAt ℝ f x)
    (hI : ∀ v, fderiv ℝ f x (I • v) = I • fderiv ℝ f x v) :
    fderiv ℂ f x = (fderiv ℝ f x).complexOfRealOfMapISmul hI := by
  simpa only [fderivWithin_univ] using
    hf.differentiableWithinAt.fderiv_complex_of_map_I_smul
      (by simpa only [fderivWithin_univ] using hI) uniqueDiffWithinAt_univ

end TauCeti
