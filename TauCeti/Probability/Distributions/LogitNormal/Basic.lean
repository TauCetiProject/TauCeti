/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.SpecialFunctions.Sigmoid
public import TauCeti.Probability.Distributions.Gaussian.Cdf
public import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# The logit-normal distribution

The logit-normal law is the sigmoid image of a real Gaussian. It is carried by the open unit
interval, and its logit has the original Gaussian law. At zero variance it is the Dirac mass
at the sigmoid of the location parameter. Reflection about one half negates that parameter.

This file gives the construction, parameter measurability, CDF, and natural moments as Gaussian
integrals of powers of the sigmoid. Boundedness supplies moment integrability and the full
exponential-integrability domain; no elementary closed form for the mean or variance is asserted.

## References

* J. Aitchison and S. M. Shen, *Logistic-normal distributions: Some properties and uses*,
  Biometrika 67(2), 261–272, 1980.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {v : ℝ≥0} {x : ℝ}

/-- The logit-normal law with Gaussian location `m` and Gaussian variance `v`. -/
def logitNormalMeasure (m : ℝ) (v : ℝ≥0) : Measure ℝ :=
  (gaussianReal m v).map Real.sigmoid

/-- The logit-normal law is the sigmoid image of its Gaussian source. -/
theorem logitNormalMeasure_def (m : ℝ) (v : ℝ≥0) :
    logitNormalMeasure m v = (gaussianReal m v).map Real.sigmoid := (rfl)

instance isProbabilityMeasure_logitNormalMeasure (m : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (logitNormalMeasure m v) := by
  rw [logitNormalMeasure_def]
  infer_instance

/-- At zero variance the logit-normal law is a point mass. -/
@[simp]
theorem logitNormalMeasure_zero_var (m : ℝ) :
    logitNormalMeasure m 0 = Measure.dirac (Real.sigmoid m) := by
  rw [logitNormalMeasure_def, gaussianReal_zero_var, Measure.map_dirac' (by fun_prop)]

/-- A logit-normal variable lies strictly between zero and one, including at zero variance. -/
theorem ae_mem_Ioo_logitNormalMeasure (m : ℝ) (v : ℝ≥0) :
    ∀ᵐ x ∂logitNormalMeasure m v, x ∈ Ioo 0 1 := by
  rw [logitNormalMeasure_def]
  exact (ae_map_iff (by fun_prop) measurableSet_Ioo).mpr
    (ae_of_all _ fun y ↦ ⟨Real.sigmoid_pos y, Real.sigmoid_lt_one y⟩)

/-- Taking the logit recovers the Gaussian source law. -/
@[simp]
theorem map_logit_logitNormalMeasure (m : ℝ) (v : ℝ≥0) :
    (logitNormalMeasure m v).map (fun x ↦ Real.log (x / (1 - x))) = gaussianReal m v := by
  rw [logitNormalMeasure_def, Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, Real.log_sigmoid_div_one_sub, Measure.map_id']

/-- Reflecting a logit-normal variable about one half negates its Gaussian location. -/
@[simp]
theorem map_one_sub_logitNormalMeasure (m : ℝ) (v : ℝ≥0) :
    (logitNormalMeasure m v).map (fun x ↦ 1 - x) = logitNormalMeasure (-m) v := by
  rw [logitNormalMeasure_def, logitNormalMeasure_def, ← gaussianReal_map_neg,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, Real.sigmoid_neg]

/-- The whole logit-normal family, including its Dirac boundary, is Giry measurable. -/
@[fun_prop]
theorem measurable_logitNormalMeasure :
    Measurable (fun p : ℝ × ℝ≥0 ↦ logitNormalMeasure p.1 p.2) :=
  (Measure.measurable_map _ (by fun_prop)).comp ProbabilityTheory.measurable_gaussianReal

/-- Below the open unit interval the logit-normal CDF is zero. -/
@[simp]
theorem cdf_logitNormalMeasure_of_nonpos (hx : x ≤ 0) (m : ℝ) (v : ℝ≥0) :
    cdf (logitNormalMeasure m v) x = 0 := by
  rw [cdf_eq_real, logitNormalMeasure_def, Measure.real,
    Measure.map_apply (by fun_prop) measurableSet_Iic]
  have h : Real.sigmoid ⁻¹' Iic x = ∅ := by
    ext y
    simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
    exact not_le.mpr (hx.trans_lt (Real.sigmoid_pos y))
  simp [h]

/-- At and above one the logit-normal CDF is one. -/
@[simp]
theorem cdf_logitNormalMeasure_of_one_le (hx : 1 ≤ x) (m : ℝ) (v : ℝ≥0) :
    cdf (logitNormalMeasure m v) x = 1 := by
  rw [cdf_eq_real, logitNormalMeasure_def, Measure.real,
    Measure.map_apply (by fun_prop) measurableSet_Iic]
  have h : Real.sigmoid ⁻¹' Iic x = univ := by
    ext y
    simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
    exact (Real.sigmoid_le_one y).trans hx
  simp [h]

/-- Inside the unit interval, the CDF is the Gaussian CDF evaluated at the logit.
This formula includes zero variance. -/
theorem cdf_logitNormalMeasure (hx : x ∈ Ioo 0 1) (m : ℝ) (v : ℝ≥0) :
    cdf (logitNormalMeasure m v) x =
      cdf (gaussianReal m v) (Real.log (x / (1 - x))) := by
  have h : Real.sigmoid ⁻¹' Iic x = Iic (Real.log (x / (1 - x))) := by
    ext y
    simpa only [mem_preimage, mem_Iic, Real.sigmoid_log_div_one_sub hx.1 hx.2] using
      (Real.sigmoid_le_iff (a := y) (b := Real.log (x / (1 - x))))
  rw [cdf_eq_real, logitNormalMeasure_def, Measure.real,
    Measure.map_apply (by fun_prop) measurableSet_Iic, h, ← Measure.real, ← cdf_eq_real]

/-- The nondegenerate logit-normal CDF in terms of the error function. -/
theorem cdf_logitNormalMeasure_eq (m : ℝ) (hv : v ≠ 0) (x : ℝ) :
    cdf (logitNormalMeasure m v) x =
      if x ≤ 0 then 0 else if x < 1 then
        (1 + TauCeti.Real.erf ((Real.log (x / (1 - x)) - m) / √(2 * (v : ℝ)))) / 2
      else 1 := by
  split_ifs with h0 h1
  · exact cdf_logitNormalMeasure_of_nonpos h0 m v
  · rw [cdf_logitNormalMeasure ⟨lt_of_not_ge h0, h1⟩, cdf_gaussianReal_eq m hv]
  · exact cdf_logitNormalMeasure_of_one_le (le_of_not_gt h1) m v

/-- Every natural raw moment of a logit-normal variable is integrable. -/
theorem integrable_pow_logitNormalMeasure (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x ↦ x ^ n) (logitNormalMeasure m v) := by
  refine Integrable.of_bound (by fun_prop) 1 ?_
  filter_upwards [ae_mem_Ioo_logitNormalMeasure m v] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx.1.le n)]
  exact pow_le_one₀ hx.1.le hx.2.le

/-- Natural moments are Gaussian integrals of powers of the sigmoid. -/
theorem integral_pow_logitNormalMeasure (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    ∫ x, x ^ n ∂logitNormalMeasure m v = ∫ y, Real.sigmoid y ^ n ∂gaussianReal m v := by
  rw [logitNormalMeasure_def, integral_map (by fun_prop) (by fun_prop)]

/-- The mean is the Gaussian integral of the sigmoid. -/
theorem integral_id_logitNormalMeasure (m : ℝ) (v : ℝ≥0) :
    ∫ x, x ∂logitNormalMeasure m v = ∫ y, Real.sigmoid y ∂gaussianReal m v := by
  simpa using integral_pow_logitNormalMeasure m v 1

/-- The variance is the difference between the second sigmoid moment and the square of its
first moment under the Gaussian source. -/
theorem variance_id_logitNormalMeasure (m : ℝ) (v : ℝ≥0) :
    variance id (logitNormalMeasure m v) =
      (∫ y, Real.sigmoid y ^ 2 ∂gaussianReal m v) -
        (∫ y, Real.sigmoid y ∂gaussianReal m v) ^ 2 := by
  have hmem : MemLp id 2 (logitNormalMeasure m v) :=
    memLp_of_bounded ((ae_mem_Ioo_logitNormalMeasure m v).mono fun _ hx ↦
      ⟨hx.1.le, hx.2.le⟩) measurable_id.aestronglyMeasurable 2
  simpa only [Pi.pow_apply, id_eq, integral_pow_logitNormalMeasure,
    integral_id_logitNormalMeasure] using variance_eq_sub hmem

/-- Bounded support gives every real exponential moment, including at zero variance. -/
@[simp]
theorem integrableExpSet_id_logitNormalMeasure (m : ℝ) (v : ℝ≥0) :
    integrableExpSet id (logitNormalMeasure m v) = univ := by
  ext t
  simp only [integrableExpSet, mem_ofPred_eq, mem_univ, iff_true, id_eq]
  exact integrable_exp_mul_of_mem_Icc measurable_id.aemeasurable
    ((ae_mem_Ioo_logitNormalMeasure m v).mono fun _ hx ↦ ⟨hx.1.le, hx.2.le⟩)

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

/-- The sigmoid of a Gaussian variable has the corresponding logit-normal law. -/
theorem sigmoid_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {m : ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal m v) P) :
    HasLaw (fun ω ↦ Real.sigmoid (X ω)) (TauCeti.Probability.logitNormalMeasure m v) P := by
  rw [TauCeti.Probability.logitNormalMeasure_def]
  exact (hasLaw_map (by fun_prop : Measurable Real.sigmoid).aemeasurable).comp hX

end ProbabilityTheory.HasLaw
