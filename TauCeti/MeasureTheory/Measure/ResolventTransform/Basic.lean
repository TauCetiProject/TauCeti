/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ResolventTransform
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Positivity

/-!
# The resolvent transform on the real line

For a finite measure on the real line, the imaginary part of its resolvent transform
is the integral of the kernel `im z / ((x - re z)² + (im z)²)`.
This kernel is positive in the upper half-plane, so the imaginary part of the transform
is strictly positive there for every nonzero finite measure. We also give uniform bounds
away from the real axis. No moment assumptions are needed.

We use Mathlib's `MeasureTheory.resolventTransform`, with sign `(x - z)⁻¹`, not
`(z - x)⁻¹`.

## References

* Anderson, Guionnet and Zeitouni, *An Introduction to Random Matrices*, §2.4.1,
  for the Stieltjes transform and its inversion (Theorem 2.4.3).
-/

public section

noncomputable section

open MeasureTheory Complex

namespace Complex

/-- The imaginary part of the real resolvent kernel, with sign `(x - z)⁻¹`. -/
theorem im_resolvent_real (z : ℂ) (x : ℝ) :
    (resolvent z x).im = z.im / ((x - z.re) ^ 2 + z.im ^ 2) := by
  simp [resolvent, Ring.inverse_eq_inv', Complex.inv_im, Complex.normSq_apply, sq]

/-- The real resolvent kernel is bounded by the reciprocal distance to the real axis. -/
theorem norm_resolvent_real_le (z : ℂ) (x : ℝ) (hz : z.im ≠ 0) :
    ‖resolvent z x‖ ≤ |z.im|⁻¹ := by
  rw [resolvent, Ring.inverse_eq_inv', norm_inv]
  apply inv_anti₀ (abs_pos.mpr hz)
  simpa using abs_im_le_norm ((x : ℂ) - z)

end Complex

namespace MeasureTheory

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

/-- The real resolvent kernel is integrable for a finite measure off the real axis. -/
theorem integrable_resolvent_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (resolvent (R := ℝ) z) μ := by
  apply integrable_resolvent
  rintro ⟨x, _, hx⟩
  exact hz (by simpa using (congrArg Complex.im hx).symm)

/-- The imaginary part of the transform is the integral of the kernel
`z.im / ((x - z.re)² + z.im²)`, which is the Poisson kernel without the factor `π⁻¹`
when `0 < z.im`. -/
theorem im_resolventTransform {z : ℂ} :
    (resolventTransform μ z).im =
      ∫ x, z.im / ((x - z.re) ^ 2 + z.im ^ 2) ∂μ := by
  by_cases hz : z.im = 0
  · by_cases hi : Integrable (resolvent (R := ℝ) z) μ
    · simpa only [resolventTransform_apply, RCLike.im_eq_complex_im,
        Complex.im_resolvent_real] using (integral_im hi).symm
    · simp [resolventTransform_apply, integral_undef hi, hz]
  · simpa only [resolventTransform_apply, RCLike.im_eq_complex_im,
      Complex.im_resolvent_real] using
      (integral_im (integrable_resolvent_of_im_ne_zero (μ := μ) hz)).symm

/-- A uniform bound for the transform of a finite measure away from the real axis. -/
theorem norm_resolventTransform_le {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolventTransform μ z‖ ≤ |z.im|⁻¹ * μ.real Set.univ := by
  rw [resolventTransform_apply]
  exact norm_integral_le_of_norm_le_const
    (ae_of_all _ fun x => Complex.norm_resolvent_real_le z x hz)

/-- A nonzero finite measure has strictly positive imaginary transform in the upper half-plane. -/
theorem im_resolventTransform_pos (hμ : μ ≠ 0) {z : ℂ} (hz : 0 < z.im) :
    0 < (resolventTransform μ z).im := by
  have hi := integrable_resolvent_of_im_ne_zero (μ := μ) hz.ne'
  have hp (x : ℝ) : 0 < z.im / ((x - z.re) ^ 2 + z.im ^ 2) := by
    exact div_pos hz (by positivity)
  rw [im_resolventTransform]
  apply (integral_pos_iff_support_of_nonneg (fun x => (hp x).le) ?_).2
  · simpa [Function.support, ne_of_gt (hp _)] using (Measure.measure_univ_pos.mpr hμ)
  · simpa only [RCLike.im_eq_complex_im, Complex.im_resolvent_real] using hi.im

end MeasureTheory
