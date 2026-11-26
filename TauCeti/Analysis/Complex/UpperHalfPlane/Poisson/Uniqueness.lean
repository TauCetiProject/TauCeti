/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Basic
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Uniqueness of the Poisson representation of a positive harmonic function

A nonnegative harmonic function `u` on the upper half-plane `ℂ₊` is `u(z) = c Im z + P[ν](z)` for
a constant `c` and a Poisson-finite measure `ν` (Garnett, *Bounded analytic functions*, Ch. I §3).
This file proves that the pair `(c, ν)` is unique
(`TauCeti.eq_and_eq_of_mul_im_add_upperHalfPlanePoissonIntegral_eq`).

For a representation `(c, ν)` the function `F(z) = c z + i S[ν](z)`, with `S[ν]` the Schwarz
integral, is holomorphic on `ℂ₊` with imaginary part `c Im z + P[ν](z)` and real part `0` at `i`.
Two such functions with the same imaginary part differ by a holomorphic function with real values,
which is constant by the open mapping theorem, hence zero. Since
`i S[ν](z) = (1 / π) ∫ ((x - z)⁻¹ - x / (1 + x ^ 2)) dν(x)`
(`TauCeti.I_mul_upperHalfPlaneSchwarzIntegral`), uniqueness of the Herglotz
representation (`TauCeti.eq_and_eq_of_eq_subtractedResolventKernel_add`,
`TauCeti.eq_of_eq_subtractedResolventKernel_add`) gives `c = c'` and `ν / π = ν' / π`.

## Main results

* `TauCeti.eq_and_eq_of_mul_im_add_upperHalfPlanePoissonIntegral_eq`: uniqueness of `(c, ν)`.

## References

* J. B. Garnett, *Bounded analytic functions*, Ch. I, §3.
-/

public section

open Complex MeasureTheory Set

open scoped Real ENNReal

namespace TauCeti

/-- The function `F(z) = c z + i S[ν](z)` attached to a representation `(c, ν)`. -/
private noncomputable def reprFun (c : ℝ) (ν : Measure ℝ) (z : ℂ) : ℂ :=
  c * z + I * upperHalfPlaneSchwarzIntegral ν z

private theorem differentiableOn_reprFun (c : ℝ) (ν : Measure ℝ) :
    DifferentiableOn ℂ (reprFun c ν) UpperHalfPlane.upperHalfPlaneSet :=
  ((differentiableOn_id.const_mul _).add
    ((differentiableOn_upperHalfPlaneSchwarzIntegral ν).const_mul _))

private theorem im_reprFun (c : ℝ) (ν : Measure ℝ) (z : ℂ) :
    (reprFun c ν z).im = c * z.im + upperHalfPlanePoissonIntegral ν z := by
  simp [reprFun, re_upperHalfPlaneSchwarzIntegral]

private theorem re_reprFun_I (c : ℝ) (ν : Measure ℝ) : (reprFun c ν I).re = 0 := by
  simp [reprFun]

/-- `F(z) = c z + (1 / π) ∫ ((x - z)⁻¹ - x / (1 + x ^ 2)) dν(x)`, a Herglotz representation with
measure `ν / π`. -/
private theorem reprFun_eq (c : ℝ) (ν : Measure ℝ) (z : ℂ) :
    reprFun c ν z = (0 : ℝ) + c * z + ∫ x, subtractedResolventKernel z x
      ∂(ENNReal.ofReal π⁻¹ • ν) := by
  rw [reprFun, I_mul_upperHalfPlaneSchwarzIntegral, ofReal_zero, zero_add]

/-- **Uniqueness of the Poisson representation of a positive harmonic function.** If
`c Im z + P[ν](z) = c' Im z + P[ν'](z)` on the upper half-plane for Poisson-finite measures `ν`
and `ν'`, then `c = c'` and `ν = ν'`. -/
theorem eq_and_eq_of_mul_im_add_upperHalfPlanePoissonIntegral_eq {c c' : ℝ} {ν ν' : Measure ℝ}
    (hν : IsPoissonFinite ν) (hν' : IsPoissonFinite ν')
    (h : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      c * z.im + upperHalfPlanePoissonIntegral ν z =
        c' * z.im + upperHalfPlanePoissonIntegral ν' z) :
    c = c' ∧ ν = ν' := by
  -- The two holomorphic functions differ by a real constant, which vanishes at `i`.
  have hU := UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hI₀ : I ∈ UpperHalfPlane.upperHalfPlaneSet := by simp [UpperHalfPlane.upperHalfPlaneSet]
  obtain ⟨w, hw⟩ := (((differentiableOn_reprFun c ν).sub
    (differentiableOn_reprFun c' ν')).analyticOnNhd hU).eq_const_of_im_eq_const (c₀ := 0)
    (fun z hz ↦ by simp [im_reprFun, h z hz]) hU ((convex_halfSpace_im_gt 0).isConnected ⟨I, hI₀⟩)
  have hI : reprFun c ν I - reprFun c' ν' I = 0 := by
    apply Complex.ext
    · simp [re_reprFun_I]
    · have := h I hI₀
      simp only [I_im, mul_one] at this
      simp [im_reprFun, this]
  have hF : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, reprFun c ν z = reprFun c' ν' z :=
    fun z hz ↦ sub_eq_zero.mp (((hw z hz).trans (hw I hI₀).symm).trans hI)
  have hrep := fun z (_ : z ∈ UpperHalfPlane.upperHalfPlaneSet) ↦ reprFun_eq c ν z
  have hrep' := fun z (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) ↦
    (hF z hz).trans (reprFun_eq c' ν' z)
  refine ⟨(eq_and_eq_of_eq_subtractedResolventKernel_add hrep hrep').2, ?_⟩
  have hfin (μ : Measure ℝ) (hμ : IsPoissonFinite μ) :=
    (isPoissonFinite_iff_lintegral_lt_top _).1 ((isPoissonFinite_iff _).2
      (((isPoissonFinite_iff μ).1 hμ).smul_measure (ENNReal.ofReal_ne_top (r := π⁻¹))))
  have hsmul := eq_of_eq_subtractedResolventKernel_add (hfin ν hν) (hfin ν' hν') hrep hrep'
  have hπ : ENNReal.ofReal π⁻¹ ≠ 0 := by simp [Real.pi_pos]
  ext s _
  have := congrArg (fun μ : Measure ℝ ↦ μ s) hsmul
  simp only [smul_apply, smul_eq_mul] at this
  exact (ENNReal.mul_right_inj hπ ENNReal.ofReal_ne_top).mp this

end TauCeti
