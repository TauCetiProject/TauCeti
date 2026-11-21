/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.KummerLaplace
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Upper
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Laplace representation of the upper incomplete Gamma function

On the slit plane, the rotated Kummer–Laplace integral at `c = 0` equals the normalized
upper incomplete Gamma function. This identifies the value furnished by the initial ratio
of the recurrence for Legendre's continued fraction.

## References

* NIST Digital Library of Mathematical Functions, [8.6.5](https://dlmf.nist.gov/8.6.E5)
  and [8.9.2](https://dlmf.nist.gov/8.9.E2).
-/

public section

open MeasureTheory Set

namespace Complex

private theorem kummerLaplace_zero_integrand_div (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (t : ℝ) :
    z⁻¹ * (cexp (-(t : ℂ)) * (1 + (t : ℂ) / z) ^ (a - 1)) =
      z ^ (-a) * ((z + t) ^ (a - 1) * cexp (-(t : ℂ))) := by
  have hz0 := slitPlane_ne_zero hz
  have hr : 1 + (t : ℂ) / z = (z + t) * z⁻¹ := by
    rw [div_eq_mul_inv, add_mul, mul_inv_cancel₀ hz0]
  -- Translation by a real number preserves the sign of the imaginary part, so the
  -- difference of arguments stays in the principal range.
  have harg : (z + t).arg + z⁻¹.arg ∈ Ioc (-Real.pi) Real.pi := by
    rw [arg_inv, ite_eq_right (slitPlane_arg_ne_pi hz)]
    have him : (z + t).im = z.im := by simp
    rcases le_or_gt 0 z.im with hp | hn
    · exact ⟨by linarith [arg_nonneg_iff.mpr (him.symm ▸ hp),
          (abs_lt.mp (abs_arg_lt_pi_of_mem_slitPlane hz)).2],
        by linarith [arg_nonneg_iff.mpr hp, arg_le_pi (z + t)]⟩
    · exact ⟨by linarith [neg_pi_lt_arg (z + t), arg_neg_iff.mpr hn],
        by linarith [arg_neg_iff.mpr (him.symm ▸ hn), neg_pi_lt_arg z]⟩
  have hpow : z⁻¹ * z⁻¹ ^ (a - 1) = z ^ (-a) := by
    have he : 1 + (a - 1) = a := by ring
    rw [cpow_neg, ← inv_cpow z a (slitPlane_arg_ne_pi hz), ← he, cpow_add _ _ (inv_ne_zero hz0),
      cpow_one, he]
  rw [hr, mul_cpow harg, ← hpow]
  ring

/-- The rotated Laplace integral `K(0, a - 1; z)` equals `z ^ (-a) * exp z * Γ(a, z)` on the
whole slit plane, for every complex parameter `a` (DLMF 8.6.5 and 8.9.2). -/
theorem kummerLaplace_zero_eq_cpow_neg_mul_exp_mul_upperIncompleteGamma (a : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    kummerLaplace 0 (a - 1) z = z ^ (-a) * cexp z * upperIncompleteGamma a z := by
  have hz0 := slitPlane_ne_zero hz
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hrot : cexp ((-(z.arg) : ℝ) * I) = (‖z‖ : ℂ) * z⁻¹ := by
    rw [ofReal_neg, neg_mul, Complex.exp_neg, exp_arg_mul_I hz0, inv_div, div_eq_mul_inv]
  -- Rotating by `-arg z` and then rescaling by `‖z‖` sends the ray parameter to the
  -- positive real shift in the defining integral of `Γ(a, z)`.
  have hθ : |-(z.arg)| < Real.pi := by simpa using abs_arg_lt_pi_of_mem_slitPlane hz
  rw [kummerLaplace_eq_ray_integral 0 (a - 1) hz hθ
      (by rw [add_neg_cancel, abs_zero]; positivity), hrot]
  simp only [pow_zero, mul_one]
  have heq (r : ℝ) :
      cexp (-z * (r * ((‖z‖ : ℂ) * z⁻¹))) * (1 + r * ((‖z‖ : ℂ) * z⁻¹)) ^ (a - 1) =
        cexp (-((‖z‖ * r : ℝ) : ℂ)) * (1 + ((‖z‖ * r : ℝ) : ℂ) / z) ^ (a - 1) := by
    push_cast
    congr 2 <;> field_simp
  simp_rw [heq]
  rw [integral_comp_mul_left_Ioi (fun t : ℝ => cexp (-(t : ℂ)) * (1 + (t : ℂ) / z) ^ (a - 1))
      0 hnorm, mul_zero, real_smul, ofReal_inv, upperIncompleteGamma_def]
  have hscale : (‖z‖ : ℂ) * z⁻¹ * (‖z‖ : ℂ)⁻¹ = z⁻¹ := by
    rw [mul_comm (‖z‖ : ℂ), mul_assoc, mul_inv_cancel₀ (ofReal_ne_zero.mpr hnorm.ne'), mul_one]
  have hexp : cexp z * cexp (-z) = 1 := by rw [← Complex.exp_add, add_neg_cancel, exp_zero]
  rw [← mul_assoc, hscale, mul_assoc (z ^ (-a)), ← mul_assoc (cexp z), hexp, one_mul,
    ← integral_const_mul, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => kummerLaplace_zero_integrand_div a hz t

end Complex
