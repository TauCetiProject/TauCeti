/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralChiSquared.Transforms
public import TauCeti.Probability.Moments.ComplexMGF

/-!
# Characteristic function of the noncentral chi-squared distribution

For nonnegative degree `k` and noncentrality `l`, the characteristic function is
`(1 - 2 * I * t) ^ (-k / 2) * exp (l * I * t / (1 - 2 * I * t))`.
This includes the mixed degree-zero laws and the point mass at zero when both parameters vanish.
The power is the principal complex power: its base has real part one, so it avoids the branch cut.

The formula supplies a transform for identifying squared Gaussian norms with noncentral
chi-squared laws. We use `TauCeti.eqOn_complexMGF_of_eqOn_mgf`, as in
`TauCeti.Probability.charFun_gammaMeasure`, to continue the existing real mgf to the half-plane
`re z < 1 / 2` and evaluate it on the imaginary axis.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 29.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

variable {k : ℝ} {l : ℝ≥0}

private def noncentralChiSquaredComplexMGF (k : ℝ) (l : ℝ≥0) (z : ℂ) : ℂ :=
  (1 - 2 * z) ^ (-(k : ℂ) / 2) * Complex.exp ((l : ℂ) * z / (1 - 2 * z))

private theorem analyticOnNhd_noncentralChiSquaredComplexMGF (k : ℝ) (l : ℝ≥0) :
    AnalyticOnNhd ℂ (noncentralChiSquaredComplexMGF k l)
      {z : ℂ | z.re ∈ Iio (1 / 2)} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_Iio.preimage Complex.continuous_re)
  intro z hz
  have hz' : z.re < 1 / 2 := hz
  have hre : 0 < (1 - 2 * z).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re]
    norm_num
    linarith
  have hslit : 1 - 2 * z ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl hre)
  have hne : 1 - 2 * z ≠ 0 := Complex.ne_zero_of_re_pos hre
  unfold noncentralChiSquaredComplexMGF
  exact (((by fun_prop : DifferentiableAt ℂ (fun z : ℂ ↦ 1 - 2 * z) z).cpow_const hslit).mul
    (Complex.differentiableAt_exp.comp z
      ((by fun_prop : DifferentiableAt ℂ (fun z : ℂ ↦ (l : ℂ) * z) z).div
        (by fun_prop) hne))).differentiableWithinAt

private theorem noncentralChiSquaredComplexMGF_ofReal (hk : 0 ≤ k) (l : ℝ≥0)
    {t : ℝ} (ht : t < 1 / 2) :
    noncentralChiSquaredComplexMGF k l t = mgf id (noncentralChiSquaredMeasure k l) t := by
  rw [mgf_id_noncentralChiSquaredMeasure hk l (by simpa only [one_div] using ht)]
  have hb : 0 ≤ 1 - 2 * t := by linarith
  unfold noncentralChiSquaredComplexMGF
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hb]
  push_cast
  simp only [neg_div]

/-- The characteristic function of a noncentral chi-squared law, including degree zero.
The complex power is principal, with base of real part one. -/
@[simp]
theorem charFun_noncentralChiSquaredMeasure (hk : 0 ≤ k) (l : ℝ≥0) (t : ℝ) :
    charFun (noncentralChiSquaredMeasure k l) t =
      (1 - 2 * Complex.I * t) ^ (-(k : ℂ) / 2) *
        Complex.exp ((l : ℂ) * Complex.I * t / (1 - 2 * Complex.I * t)) := by
  have hsub : Iio (1 / 2) ⊆ integrableExpSet id (noncentralChiSquaredMeasure k l) := by
    intro u hu
    exact integrable_exp_mul_noncentralChiSquaredMeasure hk l
      (by simpa only [mem_Iio, one_div] using hu)
  have hEq := eqOn_complexMGF_of_eqOn_mgf isOpen_Iio (convex_Iio (1 / 2)) hsub
    (analyticOnNhd_noncentralChiSquaredComplexMGF k l)
    (fun u hu ↦ noncentralChiSquaredComplexMGF_ofReal hk l hu)
  have hit : (t : ℂ) * Complex.I ∈ {z : ℂ | z.re ∈ Iio (1 / 2)} := by
    simp
  have h := hEq hit
  rw [complexMGF_id_mul_I] at h
  simpa only [noncentralChiSquaredComplexMGF, mul_comm, mul_left_comm, mul_assoc] using h

end TauCeti.Probability
