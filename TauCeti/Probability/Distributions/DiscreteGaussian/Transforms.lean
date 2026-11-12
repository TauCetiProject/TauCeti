/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.DiscreteGaussian.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Transforms of the discrete Gaussian

The real cast of an integer Gaussian has every exponential moment. Its moment-generating
function is a Gaussian exponential multiplied by a ratio of Gaussian lattice sums; the
lattice correction distinguishes this law from the continuous Gaussian. The characteristic
function is given by its absolutely convergent mass series.

The formulas use the real center and width of `discreteGaussianMeasure`, which need not be
the mean and standard deviation.

## References

* C. L. Canonne, G. Kamath and T. Steinke, *The Discrete Gaussian for Differential Privacy*,
  2020, arXiv:2004.00010.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

private theorem discreteGaussianWeightReal_mul_exp (c : ℝ) {s : ℝ} (hs : s ≠ 0)
    (t : ℝ) (k : ℤ) :
    discreteGaussianWeightReal c s k * exp (t * k) =
      (exp (c * t + s ^ 2 * t ^ 2 / 2) / gaussianLatticeSum c s) *
        exp (-((k : ℝ) - (c + s ^ 2 * t)) ^ 2 / (2 * s ^ 2)) := by
  rw [discreteGaussianWeightReal_def]
  simp only [div_mul_eq_mul_div, ← exp_add]
  congr 2
  field_simp [hs]
  ring

/-- Every real exponential moment of the integer Gaussian is finite, including the zero
measure at nonpositive widths. -/
theorem integrable_exp_mul_intCast_discreteGaussianMeasure (c s t : ℝ) :
    Integrable (fun k : ℤ => exp (t * k)) (discreteGaussianMeasure c s) := by
  by_cases hs : 0 < s
  · rw [discreteGaussianMeasure_eq_sum_dirac c hs]
    apply integrable_sum_dirac (fun k => by
      rw [discreteGaussianWeight_def]; exact ENNReal.ofReal_ne_top)
    simp only [discreteGaussianWeight_toReal, Real.norm_eq_abs, abs_exp]
    simp_rw [discreteGaussianWeightReal_mul_exp c hs.ne' t]
    exact (hasSum_gaussianLatticeSum (c + s ^ 2 * t) hs.ne').summable.mul_left _
  · simp [discreteGaussianMeasure_of_nonpos c (not_lt.mp hs)]

/-- The exponential-integrability domain of the real cast is all of `ℝ`. -/
@[simp]
theorem integrableExpSet_intCast_discreteGaussianMeasure (c s : ℝ) :
    integrableExpSet (Int.cast : ℤ → ℝ) (discreteGaussianMeasure c s) = univ := by
  ext t
  simp [integrableExpSet, integrable_exp_mul_intCast_discreteGaussianMeasure]

/-- The discrete Gaussian mgf is a Gaussian exponential times a ratio of lattice sums. -/
theorem mgf_intCast_discreteGaussianMeasure (c : ℝ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    mgf (Int.cast : ℤ → ℝ) (discreteGaussianMeasure c s) t =
      exp (c * t + s ^ 2 * t ^ 2 / 2) *
        gaussianLatticeSum (c + s ^ 2 * t) s / gaussianLatticeSum c s := by
  rw [mgf, integral_countable (integrable_exp_mul_intCast_discreteGaussianMeasure c s t)]
  simp only [discreteGaussianMeasure_real_singleton c hs, smul_eq_mul]
  simp_rw [discreteGaussianWeightReal_mul_exp c hs.ne' t]
  rw [tsum_mul_left, ← gaussianLatticeSum_def]
  ring

/-- The cumulant-generating function retains the lattice correction to the Gaussian cgf. -/
theorem cgf_intCast_discreteGaussianMeasure (c : ℝ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    cgf (Int.cast : ℤ → ℝ) (discreteGaussianMeasure c s) t =
      c * t + s ^ 2 * t ^ 2 / 2 + log (gaussianLatticeSum (c + s ^ 2 * t) s) -
        log (gaussianLatticeSum c s) := by
  rw [cgf, mgf_intCast_discreteGaussianMeasure c hs,
    log_div (mul_ne_zero (exp_ne_zero _) (gaussianLatticeSum_pos _ hs.ne').ne')
      (gaussianLatticeSum_pos c hs.ne').ne',
    log_mul (exp_ne_zero _) (gaussianLatticeSum_pos _ hs.ne').ne', log_exp]

/-- The characteristic function of the real cast is the sum of its weighted characters.
The mass series converges absolutely. -/
theorem hasSum_charFun_map_intCast_discreteGaussianMeasure (c : ℝ) {s : ℝ}
    (hs : 0 < s) (t : ℝ) :
    HasSum (fun k : ℤ => (discreteGaussianWeightReal c s k : ℂ) *
      Complex.exp ((t * k : ℝ) * Complex.I))
      (charFun ((discreteGaussianMeasure c s).map (Int.cast : ℤ → ℝ)) t) := by
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop),
    discreteGaussianMeasure_eq_sum_dirac c hs]
  have hnorm : Summable fun k : ℤ =>
      (discreteGaussianWeight c s k).toReal *
        ‖Complex.exp ((t * k : ℝ) * Complex.I)‖ := by
    simpa [Complex.norm_exp] using (hasSum_discreteGaussianWeightReal c hs.ne').summable
  simpa only [discreteGaussianWeight_toReal, Complex.real_smul, Complex.ofReal_mul, id_eq] using
    hasSum_integral_sum_dirac (f := fun k : ℤ => Complex.exp ((t * k : ℝ) * Complex.I))
      (x := id) (c := discreteGaussianWeight c s)
      (fun k => by rw [discreteGaussianWeight_def]; exact ENNReal.ofReal_ne_top) hnorm

end TauCeti.Probability
