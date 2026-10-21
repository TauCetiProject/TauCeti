/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.PowerBias
public import TauCeti.Probability.Distributions.LogNormal.Basic
import TauCeti.MeasureTheory.Measure.Tilted

/-!
# Power biasing of log-normal laws

Every real power bias of a log-normal law is again log-normal. The exponent shifts the
log-mean by the log-variance times that exponent, including the zero-variance Dirac boundary.
-/

public section

open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

private lemma gaussianPDFReal_mul_exp_div_mgf {m q y : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianPDFReal m v y *
        (Real.exp (q * y) / Real.exp (q * m + q ^ 2 * (v : ℝ) / 2)) =
      gaussianPDFReal (m + q * v) v y := by
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hsqrt : √(2 * π * (v : ℝ)) ≠ 0 := by positivity
  rw [gaussianPDFReal, gaussianPDFReal]
  field_simp [hsqrt, Real.exp_ne_zero]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- Power biasing a log-normal law shifts its log-mean by `q * v`. -/
theorem powerBias_logNormalMeasure (m : ℝ) (v : ℝ≥0) (q : ℝ) :
    (logNormalMeasure m v).powerBias q = logNormalMeasure (m + q * v) v := by
  rw [Measure.powerBias_eq_tilted (ae_pos_logNormalMeasure m v) q]
  rcases eq_or_ne v 0 with rfl | hv
  · simp [logNormalMeasure_zero_var]
  have hZ : ∫ x, Real.exp (q * Real.log x) ∂logNormalMeasure m v =
      Real.exp (q * m + q ^ 2 * (v : ℝ) / 2) := by
    calc
      ∫ x, Real.exp (q * Real.log x) ∂logNormalMeasure m v =
          ∫ x, x ^ q ∂logNormalMeasure m v := by
        apply integral_congr_ae
        filter_upwards [ae_pos_logNormalMeasure m v] with x hx
        simp only [Real.rpow_def_of_pos hx, mul_comm]
      _ = _ := integral_rpow_logNormalMeasure m v q
  rw [logNormalMeasure_eq_withDensity m hv] at hZ
  rw [logNormalMeasure_eq_withDensity m hv,
    TauCeti.tilted_withDensity (measurable_logNormalPDF m v).aemeasurable (by fun_prop),
    hZ, logNormalMeasure_eq_withDensity (m + q * v) hv]
  apply withDensity_congr_ae
  filter_upwards with x
  rcases le_or_gt x 0 with hx | hx
  · rw [logNormalPDF_of_nonpos hx, zero_mul, logNormalPDF_of_nonpos hx]
  · rw [logNormalPDF_eq_ofReal, logNormalPDF_eq_ofReal,
      logNormalPDFReal_eq_gaussianPDFReal hx,
      logNormalPDFReal_eq_gaussianPDFReal hx,
      ← ENNReal.ofReal_mul
        (mul_nonneg (inv_nonneg.mpr hx.le) (gaussianPDFReal_nonneg m v (Real.log x)))]
    congr 1
    rw [mul_assoc, gaussianPDFReal_mul_exp_div_mgf hv]

end TauCeti.Probability
