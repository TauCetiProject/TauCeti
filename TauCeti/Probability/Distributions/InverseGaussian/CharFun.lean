/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.InverseGaussian.Transforms
public import TauCeti.Probability.Moments.ComplexMGF
public import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# Characteristic function of the inverse Gaussian distribution

For positive mean `μ` and shape `lam`, the inverse Gaussian characteristic function is

`exp ((lam / μ) * (1 - sqrt (1 - 2 * I * μ ^ 2 * t / lam)))`.

The square root is the principal complex square root.  Its argument has positive real part on
the half-plane where the inverse Gaussian moment-generating function is finite in the interior.
Analytic continuation of that real transform therefore gives the formula on the imaginary axis.

## References

* R. S. Chhikara, J. L. Folks, *The Inverse Gaussian Distribution: Theory, Methodology, and
  Applications*, Marcel Dekker (1989).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {μ lam : ℝ}

/-- The analytic expression extending the inverse Gaussian moment-generating function to its
natural complex half-plane. -/
private def inverseGaussianComplexMGF (μ lam : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (((lam / μ : ℝ) : ℂ) *
    (1 - Complex.sqrt (1 - ((2 * μ ^ 2 / lam : ℝ) : ℂ) * z)))

private theorem analyticOnNhd_inverseGaussianComplexMGF (hlam : 0 < lam) :
    AnalyticOnNhd ℂ (inverseGaussianComplexMGF μ lam)
      {z : ℂ | z.re ∈ Iio (lam / (2 * μ ^ 2))} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_Iio.preimage Complex.continuous_re)
  intro z hz
  have hre : 0 < (1 - ((2 * μ ^ 2 / lam : ℝ) : ℂ) * z).re := by
    simpa only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, mul_div_right_comm] using
      one_sub_two_mul_sq_mul_div_pos hlam hz
  have hslit : 1 - ((2 * μ ^ 2 / lam : ℝ) : ℂ) * z ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl hre)
  unfold inverseGaussianComplexMGF
  fun_prop (disch := assumption)

private theorem inverseGaussianComplexMGF_ofReal (hμ : 0 < μ) (hlam : 0 < lam)
    {t : ℝ} (ht : t < lam / (2 * μ ^ 2)) :
    inverseGaussianComplexMGF μ lam t = mgf id (inverseGaussianMeasure μ lam) t := by
  have harg : (1 : ℂ) - ((2 * μ ^ 2 / lam : ℝ) : ℂ) * t =
      ((1 - 2 * μ ^ 2 * t / lam : ℝ) : ℂ) := by
    push_cast
    ring
  rw [mgf_id_inverseGaussianMeasure hμ hlam ht.le, inverseGaussianComplexMGF, harg,
    Complex.sqrt_of_nonneg (Complex.zero_le_real.mpr (one_sub_two_mul_sq_mul_div_pos hlam ht).le),
    Complex.ofReal_re]
  norm_cast

/-- The characteristic function of a valid inverse Gaussian law. The square root is the
principal complex square root; its argument has real part one and hence avoids the branch cut. -/
@[simp]
theorem charFun_inverseGaussianMeasure (hμ : 0 < μ) (hlam : 0 < lam) (t : ℝ) :
    charFun (inverseGaussianMeasure μ lam) t =
      Complex.exp (((lam / μ : ℝ) : ℂ) *
        (1 - Complex.sqrt
          (1 - 2 * Complex.I * (μ : ℂ) ^ 2 * t / (lam : ℂ)))) := by
  have hsub : Iio (lam / (2 * μ ^ 2)) ⊆
      integrableExpSet id (inverseGaussianMeasure μ lam) := by
    intro u hu
    rw [integrableExpSet_id_inverseGaussianMeasure hμ hlam]
    exact hu.le
  have hEq := eqOn_complexMGF_of_eqOn_mgf isOpen_Iio
    (convex_Iio (lam / (2 * μ ^ 2))) hsub
    (analyticOnNhd_inverseGaussianComplexMGF hlam)
    (fun u hu ↦ inverseGaussianComplexMGF_ofReal hμ hlam hu)
  have hit : (t : ℂ) * Complex.I ∈
      {z : ℂ | z.re ∈ Iio (lam / (2 * μ ^ 2))} := by
    simp only [Set.mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, mul_one, sub_self, mem_Iio]
    positivity
  have h := hEq hit
  rw [complexMGF_id_mul_I] at h
  have harg : 1 - ((2 * μ ^ 2 / lam : ℝ) : ℂ) * ((t : ℂ) * Complex.I) =
      1 - 2 * Complex.I * (μ : ℂ) ^ 2 * t / (lam : ℂ) := by
    push_cast
    ring
  simpa only [inverseGaussianComplexMGF, harg] using h

end TauCeti.Probability
