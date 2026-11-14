/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.ParametricIntegral

/-!
# The complex upper incomplete Gamma function

The principal upper incomplete Gamma function is the integral along the horizontal ray
from `z` to infinity. Its integrand is absolutely integrable for every complex parameter
when `z` belongs to the slit plane. On the positive real axis it agrees with the usual
integral over `(x, ∞)`, including parameters with nonpositive real part.

This integral definition does not use division by Gamma, so it remains meaningful at
nonpositive integral parameters. On the branch cut the same totalized Bochner integral
is used: it need not converge and then takes the junk value zero. No agreement with
analytic continuation on the branch cut is asserted.

## References

* NIST Digital Library of Mathematical Functions, §8.2, especially 8.2.2.
  <https://dlmf.nist.gov/8.2>
-/

public section

open MeasureTheory Set Filter Asymptotics
open scoped Topology

namespace Complex

/-- The principal upper incomplete Gamma function, defined by a horizontal ray integral.
On the nonpositive real axis this still uses the principal complex power and the
Bochner integral, which is zero when the integrand is not integrable; agreement with
analytic continuation there is not asserted. -/
noncomputable def upperIncompleteGamma (a z : ℂ) : ℂ :=
  _root_.Complex.exp (-z) *
    ∫ t in Ioi (0 : ℝ), (z + t) ^ (a - 1) * _root_.Complex.exp (-(t : ℂ))

/-- The defining horizontal-ray integral with its exponential prefactor. -/
theorem upperIncompleteGamma_def (a z : ℂ) :
    upperIncompleteGamma a z =
      _root_.Complex.exp (-z) *
        ∫ t in Ioi (0 : ℝ), (z + t) ^ (a - 1) * _root_.Complex.exp (-(t : ℂ)) := (rfl)

/-- Absolute convergence of the horizontal-ray integrand on the slit plane, for every
complex parameter `a`. -/
theorem integrableOn_upperIncompleteGamma_integrand (a : ℂ) {z : ℂ}
    (hz : z ∈ _root_.Complex.slitPlane) :
    IntegrableOn (fun t : ℝ => (z + t) ^ (a - 1) * _root_.Complex.exp (-(t : ℂ)))
      (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (a - 1).re) (Ioi 1) :=
    integrable_of_isBigO_exp_neg one_half_pos
      (continuousOn_id.neg.rexp.mul (continuousOn_id.rpow_const (by grind)))
      (Real.Gamma_integrand_isLittleO _).isBigO
  have hs := ((measurePreserving_add_left volume (1 : ℝ)).integrableOn_comp_preimage
    (MeasurableEquiv.addLeft (1 : ℝ)).measurableEmbedding).mpr hi
  have hw : IntegrableOn
      (fun t : ℝ => ‖_root_.Complex.exp (-(t : ℂ))‖ * (1 + t) ^ (a - 1).re)
      (Ioi 0) := by
    simpa [IntegrableOn, preimage_const_add_Ioi, Function.comp_def, norm_exp, neg_add, Real.exp_add,
      Real.exp_neg, mul_comm, mul_left_comm, mul_assoc] using hs.const_mul (Real.exp 1)
  simpa only [mul_comm, add_comm] using
    (TauCeti.integrableOn_mul_ofReal_add_cpow_iff_norm_mul_one_add_rpow
      hz (a - 1)).mpr ⟨(by fun_prop : Continuous
        (fun t : ℝ => _root_.Complex.exp (-(t : ℂ)))).aestronglyMeasurable, hw⟩

/-- The defining ray integral with the exponential prefactor absorbed into the integrand
(DLMF 8.2.2). -/
theorem upperIncompleteGamma_eq_integral (a z : ℂ) :
    upperIncompleteGamma a z =
      ∫ t in Ioi (0 : ℝ), (z + t) ^ (a - 1) * _root_.Complex.exp (-(z + t)) := by
  rw [upperIncompleteGamma, ← integral_const_mul]
  congr 1
  ext t
  rw [neg_add, _root_.Complex.exp_add]
  ring

/-- On a real ray, the upper incomplete Gamma function is the usual tail integral.
The identity also holds at the definition's junk values; convergence is guaranteed for `x > 0`. -/
theorem upperIncompleteGamma_ofReal (a : ℂ) (x : ℝ) :
    upperIncompleteGamma a x =
      ∫ t in Ioi x, (t : ℂ) ^ (a - 1) * _root_.Complex.exp (-(t : ℂ)) := by
  rw [upperIncompleteGamma_eq_integral]
  simpa only [preimage_const_add_Ioi, sub_self, _root_.Complex.ofReal_add] using
    (measurePreserving_add_left volume x).setIntegral_preimage_emb
      (MeasurableEquiv.addLeft x).measurableEmbedding
      (fun t : ℝ => (t : ℂ) ^ (a - 1) * _root_.Complex.exp (-(t : ℂ))) (Ioi x)

/-- At shape one the ray integral is an exponential, even on the branch cut. -/
@[simp]
theorem upperIncompleteGamma_one_left (z : ℂ) :
    upperIncompleteGamma 1 z = _root_.Complex.exp (-z) := by
  have hi : (∫ t in Ioi (0 : ℝ), _root_.Complex.exp (-(t : ℂ))) = 1 := by
    simpa using integral_exp_mul_complex_Ioi (a := -1) (by norm_num) 0
  simp [upperIncompleteGamma, hi]

/-- The upper incomplete Gamma function at zero agrees with Gamma in its integral
half-plane. This does not assert convergence at zero for other parameters. -/
@[simp]
theorem upperIncompleteGamma_zero_right {a : ℂ} (ha : 0 < a.re) :
    upperIncompleteGamma a 0 = _root_.Complex.Gamma a := by
  rw [upperIncompleteGamma, _root_.Complex.Gamma_eq_integral ha,
    _root_.Complex.GammaIntegral]
  simp only [neg_zero, _root_.Complex.exp_zero, zero_add, one_mul]
  congr 1
  ext t
  simp [_root_.Complex.ofReal_exp, mul_comm]

/-- Splitting Euler's Gamma integral at a nonnegative real endpoint gives the upper
incomplete Gamma function and Mathlib's `Complex.partialGamma`. -/
theorem partialGamma_add_upperIncompleteGamma {a : ℂ} (ha : 0 < a.re)
    {x : ℝ} (hx : 0 ≤ x) :
    _root_.Complex.partialGamma a x + upperIncompleteGamma a x = _root_.Complex.Gamma a := by
  rw [upperIncompleteGamma_ofReal, _root_.Complex.partialGamma,
    _root_.Complex.Gamma_eq_integral ha, _root_.Complex.GammaIntegral]
  simpa only [_root_.Complex.ofReal_exp, _root_.Complex.ofReal_neg, mul_comm] using
    intervalIntegral.integral_interval_add_Ioi (_root_.Complex.GammaIntegral_convergent ha)
      ((_root_.Complex.GammaIntegral_convergent ha).mono_set (Ioi_subset_Ioi hx))

end Complex
