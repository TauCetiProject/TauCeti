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
away from the real axis, and prove affine covariance under pushforward. No moment assumptions are
needed.

We use Mathlib's `MeasureTheory.resolventTransform`, with sign `(x - z)⁻¹`, not
`(z - x)⁻¹`.

## References

* Anderson, Guionnet and Zeitouni, *An Introduction to Random Matrices*, §2.4.1,
  for the Stieltjes transform and its inversion (Theorem 2.4.3).
-/

public section

noncomputable section

open MeasureTheory Complex
open scoped ComplexConjugate

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

/-- Conjugating the spectral parameter conjugates the resolvent transform of a real measure.
No finiteness assumption is needed, since the Bochner integral commutes with conjugation. -/
@[simp]
theorem Measure.resolventTransform_conj (μ : Measure ℝ) (z : ℂ) :
    resolventTransform μ (conj z) = conj (resolventTransform μ z) := by
  simp only [Complex.star_def.symm]
  rw [resolventTransform_apply, resolventTransform_apply]
  calc
    (∫ x, resolvent (R := ℝ) (star z) x ∂μ) =
        ∫ x, star (resolvent (R := ℝ) z x) ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by
            simp [resolvent, Ring.inverse_eq_inv']
    _ = _ := by
      simpa only [RCLike.star_def] using (integral_conj (f := resolvent (R := ℝ) z))

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

omit [IsFiniteMeasure μ] in
/-- The resolvent transform of the pushforward by a real affine map is obtained by the
corresponding affine change of spectral parameter. The identity holds for arbitrary measures,
without finiteness assumptions. -/
theorem resolventTransform_map_affine (a b : ℝ) (hb : b ≠ 0) (z : ℂ) :
    resolventTransform (μ.map (fun x : ℝ => a + b * x)) z =
      (b : ℂ)⁻¹ * resolventTransform μ ((z - a) / b) := by
  let e : ℝ ≃ᵐ ℝ :=
    ((Homeomorph.mulLeft₀ b hb).trans (Homeomorph.addRight a)).toMeasurableEquiv
  have he : (fun x : ℝ => a + b * x) = e := by
    ext x
    simp [e, Homeomorph.coe_mulLeft₀, add_comm]
  have hkernel (x : ℝ) :
      resolvent z (a + b * x) =
        (b : ℂ)⁻¹ * resolvent ((z - a) / b) x := by
    have hfactor :
        (a : ℂ) + (b : ℂ) * x - z = (b : ℂ) * ((x : ℂ) - (z - a) / b) := by
      field_simp [hb]
      ring
    simp only [resolvent, Ring.inverse_eq_inv']
    push_cast
    -- `resolvent` unfolds with `algebraMap ℝ ℂ`; restore the plain coercion so `hfactor` matches.
    simp only [Complex.coe_algebraMap]
    rw [hfactor, mul_inv_rev]
    ring
  calc
    resolventTransform (μ.map (fun x : ℝ => a + b * x)) z =
        ∫ x, resolvent z (e x) ∂μ := by
          rw [resolventTransform_apply, he, integral_map_equiv]
    _ = ∫ x, resolvent z (a + b * x) ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => congrArg (resolvent z) (congrFun he x).symm
    _ = ∫ x, (b : ℂ)⁻¹ * resolvent ((z - a) / b) x ∂μ := by
          exact integral_congr_ae (ae_of_all _ hkernel)
    _ = (b : ℂ)⁻¹ * resolventTransform μ ((z - a) / b) := by
          rw [integral_const_mul, resolventTransform_apply]

end MeasureTheory
