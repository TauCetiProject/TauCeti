/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.BetaNegativeBinomial.Moments
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Transform series of beta-negative-binomial laws

The probability-generating function on `[-1, 1]` and the
characteristic function are absolutely convergent series of the Gamma–Beta masses. The mgf
is the same series at `exp t`: positive shape permits exactly `t ≤ 0`, while shape zero is
Dirac and permits every real argument. The cgf is the logarithm of this mass series.

The `HasSum` statements retain convergence as well as the transform value. Absolute convergence
also follows from their summability, since these series have real or complex values.
The proofs reuse the countable-measure integration and pgf APIs.

## Reference

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {r a b : ℝ}

/-- The pgf on `[-1, 1]` is the convergent mass series, including both endpoints. -/
theorem hasSum_pgf_betaNegativeBinomialMeasure (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b)
    {z : ℝ} (hz : |z| ≤ 1) :
    HasSum (fun k ↦ betaNegativeBinomialWeightReal r a b k * z ^ k)
      (pgf id (betaNegativeBinomialMeasure r a b) z) := by
  have := isProbabilityMeasure_betaNegativeBinomialMeasure hr ha hb
  simpa only [betaNegativeBinomialMeasure_real_singleton hr ha hb] using
    hasSum_pgf (betaNegativeBinomialMeasure r a b) hz

/-- The mgf is the mass series on its exact domain: every real argument at shape zero,
and nonpositive arguments at positive shape. -/
theorem hasSum_mgf_id_map_cast_betaNegativeBinomialMeasure (hr : 0 ≤ r) (ha : 0 < a)
    (hb : 0 < b) {t : ℝ} (ht : r = 0 ∨ t ≤ 0) :
    HasSum (fun k ↦ betaNegativeBinomialWeightReal r a b k * Real.exp t ^ k)
      (mgf id ((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)) t) := by
  have hdom : t ∈ integrableExpSet id
      ((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)) := by
    rw [integrableExpSet_id_map_cast_betaNegativeBinomialMeasure hr ha hb]
    split_ifs with hr0
    · trivial
    · exact ht.resolve_left hr0
  have hi : Integrable (fun k : ℕ ↦ Real.exp t ^ k) (betaNegativeBinomialMeasure r a b) := by
    simpa only [Function.comp_def, id_eq, mul_comm t, Real.exp_nat_mul] using
      (MeasurableEmbedding.natCast.integrable_map_iff.mp hdom)
  rw [mgf_id_map_natCast]
  simpa only [betaNegativeBinomialMeasure_real_singleton hr ha hb] using
    hasSum_pgf_of_integrable (betaNegativeBinomialMeasure r a b) hi

/-- On the exponential-integrability domain the cgf is the logarithm of the mass-series mgf. -/
theorem cgf_id_map_cast_betaNegativeBinomialMeasure (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b)
    {t : ℝ} (ht : r = 0 ∨ t ≤ 0) :
    cgf id ((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)) t =
      Real.log (∑' k, betaNegativeBinomialWeightReal r a b k * Real.exp t ^ k) := by
  rw [cgf, ← (hasSum_mgf_id_map_cast_betaNegativeBinomialMeasure hr ha hb ht).tsum_eq]

/-- The characteristic function is the convergent complex mass series at every real frequency. -/
theorem hasSum_charFun_map_cast_betaNegativeBinomialMeasure (hr : 0 ≤ r) (ha : 0 < a)
    (hb : 0 < b) (t : ℝ) :
    HasSum (fun k ↦ (betaNegativeBinomialWeightReal r a b k : ℂ) *
      Complex.exp ((t : ℂ) * (k : ℝ) * Complex.I))
      (charFun ((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)) t) := by
  have hnorm : Summable (fun k : ℕ ↦ (betaNegativeBinomialWeight r a b k).toReal *
      ‖Complex.exp ((t : ℂ) * (k : ℝ) * Complex.I)‖) := by
    simpa [betaNegativeBinomialWeight_toReal hr ha hb, Complex.norm_exp,
      Complex.mul_re, Complex.mul_im] using
        (hasSum_betaNegativeBinomialWeightReal hr ha hb).summable
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop),
    betaNegativeBinomialMeasure_eq_sum_dirac hr ha hb]
  simpa only [betaNegativeBinomialWeight_toReal hr ha hb, Complex.real_smul, id_eq] using
    hasSum_integral_sum_dirac (x := id)
      (f := fun k : ℕ ↦ Complex.exp ((t : ℂ) * (k : ℝ) * Complex.I))
      (betaNegativeBinomialWeight_ne_top r a b) hnorm

end TauCeti.Probability
