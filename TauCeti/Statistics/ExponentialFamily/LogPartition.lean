/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.Covariance
public import TauCeti.Analysis.Analytic.ExponentialIntegral
public import TauCeti.Statistics.ExponentialFamily.Moments

import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Moments.Variance

/-!
# Derivatives of the log partition function

At an interior natural parameter, the log partition function is analytic. Its gradient
is the mean of the statistic and its Hessian is the covariance of its linear projections,
both taken under the tilted law. In a minimal family the Hessian is positive definite.

## References

* L. D. Brown, *Fundamentals of Statistical Exponential Families* (1986), Theorems 2.2 and 2.7.
* M. J. Schervish, *Theory of Statistics* (1995), Theorem 2.64.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal RealInnerProductSpace Topology

namespace TauCeti

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ν : Measure X} {T : X → E} {η : E}

private theorem exists_hasFPowerSeriesOnBall_partition
    (hη : η ∈ interior (naturalParameterSpace ν T)) :
    ∃ r : ℝ≥0, 0 < r ∧
      (Integrable (fun x ↦ exp (⟪η, T x⟫ + (r : ℝ) * ‖T x‖)) ν) ∧
      HasFPowerSeriesOnBall (fun t ↦ ∫ x, exp ⟪t, T x⟫ ∂ν)
        (exponentialIntegralSeries ν T (fun _ ↦ 1) η) η r := by
  have hT := aestronglyMeasurable_of_mem_interior_naturalParameterSpace hη
  obtain ⟨r, hr, h⟩ := exists_integrable_exp_inner_add_mul_norm hη
  let radius : ℝ≥0 := ⟨r, hr.le⟩
  have hpos : 0 < radius := hr
  have hi : Integrable (fun x ↦ exp (⟪η, T x⟫ + (radius : ℝ) * ‖T x‖)) ν := h
  refine ⟨radius, hpos, hi, ?_⟩
  simpa using hasFPowerSeriesOnBall_exponentialIntegral hT
    (w := fun _ ↦ 1) aestronglyMeasurable_const hpos (by simpa only [norm_one, mul_one] using hi)

/-- The log partition function is analytic throughout the interior of its natural domain. -/
theorem analyticOnNhd_logPartition :
    AnalyticOnNhd ℝ (logPartition ν T) (interior (naturalParameterSpace ν T)) := by
  intro η hη
  obtain rfl | hν := eq_zero_or_neZero ν
  · simpa only [logPartition_zero_measure, Pi.zero_def] using
      (analyticAt_const (𝕜 := ℝ) (v := (0 : ℝ)) (x := η))
  obtain ⟨_, _, _, hp⟩ := exists_hasFPowerSeriesOnBall_partition hη
  rw [funext (logPartition_def ν T)]
  let Z : E → ℝ := fun t ↦ ∫ x, exp ⟪t, T x⟫ ∂ν
  have ha : AnalyticAt ℝ Z η := hp.analyticAt
  have hpos : 0 < Z η := integral_exp_pos (mem_naturalParameterSpace.mp (interior_subset hη))
  simpa only [Function.comp_def, Z] using (analyticAt_log hpos).comp ha

private theorem fderiv_logPartition_apply_eq_integral
    (hη : η ∈ interior (naturalParameterSpace ν T)) (v : E) :
    fderiv ℝ (logPartition ν T) η v = ∫ x, ⟪v, T x⟫ ∂exponentialFamilyMeasure ν T η := by
  obtain rfl | hν := eq_zero_or_neZero ν
  · simp
  have hT := aestronglyMeasurable_of_mem_interior_naturalParameterSpace hη
  obtain ⟨r, hr, h, hp⟩ := exists_hasFPowerSeriesOnBall_partition hη
  have hz := hp.hasFPowerSeriesAt.differentiableAt.hasFDerivAt
  have hlog := hz.log (integral_exp_pos (mem_naturalParameterSpace.mp (interior_subset hη))).ne'
  have hmoment :
      fderiv ℝ (fun t ↦ ∫ x, exp ⟪t, T x⟫ ∂ν) η v = ∫ x, exp ⟪η, T x⟫ * ⟪v, T x⟫ ∂ν := by
    simpa using fderiv_exponentialIntegral_apply hT
      (w := fun _ ↦ 1) aestronglyMeasurable_const hr (by simpa using h) v
  rw [funext (logPartition_def ν T), hlog.fderiv, smul_apply, smul_eq_mul,
    hmoment, integral_exponentialFamilyMeasure_eq_div, div_eq_inv_mul]

/-- The gradient of the log partition function is the mean under the tilted law. -/
theorem hasFDerivAt_logPartition
    (hη : η ∈ interior (naturalParameterSpace ν T)) :
    HasFDerivAt (logPartition ν T)
      (innerSL ℝ (∫ x, T x ∂exponentialFamilyMeasure ν T η)) η := by
  have hmean := (memLp_exponentialFamilyMeasure hη 1).integrable (by simp)
  refine ((analyticOnNhd_logPartition η hη).differentiableAt.hasFDerivAt).congr_fderiv ?_
  ext v
  rw [fderiv_logPartition_apply_eq_integral hη, innerSL_apply_apply, real_inner_comm v _]
  exact (innerSL ℝ v).integral_comp_comm hmean

private theorem exists_integrable_exp_mul_norm_inner
    (hη : η ∈ interior (naturalParameterSpace ν T)) (v : E) :
    ∃ r : ℝ≥0, 0 < r ∧
      Integrable (fun x ↦ exp (⟪η, T x⟫ + (r : ℝ) * ‖T x‖) * ‖⟪v, T x⟫‖) ν := by
  have hT := aestronglyMeasurable_of_mem_interior_naturalParameterSpace hη
  obtain ⟨s, hs, h⟩ := exists_integrable_exp_inner_add_mul_norm hη
  let r : ℝ≥0 := ⟨s / 2, by positivity⟩
  have hr : 0 < (r : ℝ) := half_pos hs
  refine ⟨r, by exact_mod_cast hr, (h.const_mul (‖v‖ / r)).mono' (by fun_prop)
    (ae_of_all _ fun x ↦ ?_)⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hbound : ‖T x‖ ≤ ((r : ℝ)⁻¹) * exp ((r : ℝ) * ‖T x‖) := by
    rw [← div_eq_inv_mul, le_div_iff₀ hr, mul_comm]
    exact (lt_of_lt_of_le (lt_add_one _) (add_one_le_exp _)).le
  calc
    _ ≤ exp (⟪η, T x⟫ + (r : ℝ) * ‖T x‖) *
        (‖v‖ * ((r : ℝ)⁻¹ * exp ((r : ℝ) * ‖T x‖))) := by
      gcongr
      exact (norm_inner_le_norm v (T x)).trans (mul_le_mul_of_nonneg_left hbound (norm_nonneg v))
    _ = (‖v‖ / r) * (exp (⟪η, T x⟫ + (r : ℝ) * ‖T x‖) *
        exp ((r : ℝ) * ‖T x‖)) := by ring
    _ = _ := by
      rw [← exp_add]
      congr 2
      have hr' : (r : ℝ) = s / 2 := (rfl)
      rw [hr']
      ring

/-- The Hessian of the log partition function is the covariance of the corresponding
linear projections under the tilted law. -/
theorem fderiv_fderiv_logPartition_apply
    (hη : η ∈ interior (naturalParameterSpace ν T)) (u v : E) :
    fderiv ℝ (fderiv ℝ (logPartition ν T)) η u v =
      cov[fun x ↦ ⟪u, T x⟫, fun x ↦ ⟪v, T x⟫; exponentialFamilyMeasure ν T η] := by
  obtain rfl | hν := eq_zero_or_neZero ν
  · simp
  let _ := isProbabilityMeasure_exponentialFamilyMeasure (interior_subset hη)
  have hm := memLp_exponentialFamilyMeasure hη 2
  have hu : MemLp (fun x ↦ ⟪u, T x⟫) 2 (exponentialFamilyMeasure ν T η) :=
    hm.continuousLinearMap_comp (innerSL ℝ u)
  have hv : MemLp (fun x ↦ ⟪v, T x⟫) 2 (exponentialFamilyMeasure ν T η) :=
    hm.continuousLinearMap_comp (innerSL ℝ v)
  let Z : E → ℝ := fun t ↦ ∫ x, exp ⟪t, T x⟫ ∂ν
  let A : E → ℝ := fun t ↦ ∫ x, exp ⟪t, T x⟫ * ⟪v, T x⟫ ∂ν
  have hZ0 : Z η ≠ 0 :=
    (integral_exp_pos (mem_naturalParameterSpace.mp (interior_subset hη))).ne'
  have hT := aestronglyMeasurable_of_mem_interior_naturalParameterSpace hη
  obtain ⟨r, hr, hi, hp⟩ := exists_hasFPowerSeriesOnBall_partition hη
  have hZ : DifferentiableAt ℝ Z η := hp.analyticAt.differentiableAt
  obtain ⟨s, hs, hj⟩ := exists_integrable_exp_mul_norm_inner hη v
  have hA : DifferentiableAt ℝ A η :=
    (hasFPowerSeriesOnBall_exponentialIntegral hT hT.const_inner hs hj).analyticAt.differentiableAt
  have hquot := hA.hasFDerivAt.mul ((hasDerivAt_inv hZ0).comp_hasFDerivAt η hZ.hasFDerivAt)
  have heq : (fun t ↦ fderiv ℝ (logPartition ν T) t v) =ᶠ[𝓝 η] (fun t ↦ A t * (Z t)⁻¹) := by
    filter_upwards [isOpen_interior.mem_nhds hη] with t ht
    rw [fderiv_logPartition_apply_eq_integral ht, integral_exponentialFamilyMeasure_eq_div]
    exact div_eq_mul_inv _ _
  have hslot :
      fderiv ℝ (fun t ↦ (fderiv ℝ (logPartition ν T) t) v) η =
        (ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ (logPartition ν T)) η) := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
      ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp η
        (analyticOnNhd_logPartition η hη).fderiv.differentiableAt.hasFDerivAt).fderiv
  have hmoment : fderiv ℝ Z η u = ∫ x, exp ⟪η, T x⟫ * ⟪u, T x⟫ ∂ν := by
    simpa [Z] using fderiv_exponentialIntegral_apply hT
      (w := fun _ ↦ 1) aestronglyMeasurable_const hr (by simpa using hi) u
  have hmoment' : fderiv ℝ A η u =
      ∫ x, exp ⟪η, T x⟫ * (⟪u, T x⟫ * ⟪v, T x⟫) ∂ν := by
    simpa [A, mul_comm, mul_left_comm, mul_assoc] using
      fderiv_exponentialIntegral_apply hT hT.const_inner hs hj u
  have hslot_apply := congrArg (fun f : E →L[ℝ] ℝ ↦ f u) hslot
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at hslot_apply
  rw [← hslot_apply]
  rw [(hquot.congr_of_eventuallyEq heq).fderiv, covariance_eq_sub hu hv]
  simp only [add_apply, smul_apply, smul_eq_mul, Function.comp_apply,
    hmoment, hmoment', integral_exponentialFamilyMeasure_eq_div, Pi.mul_apply, A, Z]
  have hne : (∫ x, exp ⟪η, T x⟫ ∂ν) ≠ 0 := hZ0
  field_simp [hne]
  ring

/-- For a minimal family, the Hessian of the log partition
function is positive in every nonzero direction at every interior parameter. -/
theorem IsMinimalExponentialFamily.fderiv_fderiv_logPartition_pos
    (hmin : IsMinimalExponentialFamily ν T)
    (hη : η ∈ interior (naturalParameterSpace ν T))
    {v : E} (hv : v ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (logPartition ν T)) η v v := by
  have : NeZero ν := ⟨fun hzero ↦ isMinimalExponentialFamily_iff.mp hmin v hv 0
    (by simp [hzero])⟩
  let _ := isProbabilityMeasure_exponentialFamilyMeasure (interior_subset hη)
  have hm : MemLp (fun x ↦ ⟪v, T x⟫) 2 (exponentialFamilyMeasure ν T η) :=
    (memLp_exponentialFamilyMeasure hη 2).continuousLinearMap_comp (innerSL ℝ v)
  rw [fderiv_fderiv_logPartition_apply hη, covariance_self hm.aemeasurable]
  apply lt_of_le_of_ne (variance_nonneg _ _)
  intro hzero
  have hae := ae_eq_integral_of_variance_eq_zero hm hzero.symm
  have hac : ν ≪ exponentialFamilyMeasure ν T η := by
    rw [exponentialFamilyMeasure_def]
    exact absolutelyContinuous_tilted (mem_naturalParameterSpace.mp (interior_subset hη))
  exact isMinimalExponentialFamily_iff.mp hmin v hv _ (hac.ae_le hae)

end TauCeti
