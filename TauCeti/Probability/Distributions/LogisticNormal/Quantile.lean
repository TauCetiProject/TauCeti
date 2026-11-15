/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Quantile
public import TauCeti.Probability.Distributions.LogisticNormal.Reference

/-!
# Quantiles of simplex logistic-normal log ratios

Every additive log ratio of a simplex logistic-normal vector has a scalar Gaussian law.
Consequently its interior quantile is explicit in terms of `Real.erfInv`. The formulas include
singular covariance matrices and log ratios with zero variance.

The first group of results uses the reference category appearing in the law's parameters. The
second group permits any reference category by applying the canonical linear change of
log-ratio coordinates. The one-sided endpoint limits distinguish a constant log ratio from a
nonconstant Gaussian one.

## References

* J. Aitchison and S. M. Shen, *Logistic-normal distributions: Some properties and uses*,
  Biometrika 67(2), 261–272, 1980.

The scalar formulas use `TauCeti.Probability.quantile_gaussianReal` and its endpoint limits.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quantile of an additive log ratio to the parameter reference category, including a
log ratio with zero variance. -/
theorem quantile_map_log_div_logisticNormalMeasure (r : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hS : S.PosSemidef) (j : {i // i ≠ r}) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((logisticNormalMeasure r m S).map (fun x ↦ Real.log (x j / x r))).quantile u =
      m j + √(2 * S j j) * Real.erfInv (2 * u - 1) := by
  rw [map_log_div_logisticNormalMeasure r m hS j, quantile_gaussianReal _ _ hu,
    Real.coe_toNNReal _ hS.diag_nonneg]

/-- At level zero a reference log-ratio quantile tends to minus infinity, or to its constant
value when its variance vanishes. -/
theorem tendsto_quantile_map_log_div_logisticNormalMeasure_nhdsGT_zero (r : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hS : S.PosSemidef) (j : {i // i ≠ r}) :
    Tendsto (fun u ↦
      (((logisticNormalMeasure r m S).map
        (fun x ↦ Real.log (x j / x r))).quantile u : EReal))
      (nhdsWithin 0 (Ioi 0)) (nhds (if S j j = 0 then (m j : EReal) else ⊥)) := by
  rw [map_log_div_logisticNormalMeasure r m hS j]
  simpa only [← NNReal.coe_eq_zero, Real.coe_toNNReal _ hS.diag_nonneg] using
    tendsto_quantile_gaussianReal_nhdsGT_zero (m j) (S j j).toNNReal

/-- At level one a reference log-ratio quantile tends to plus infinity, or to its constant
value when its variance vanishes. -/
theorem tendsto_quantile_map_log_div_logisticNormalMeasure_nhdsLT_one (r : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hS : S.PosSemidef) (j : {i // i ≠ r}) :
    Tendsto (fun u ↦
      (((logisticNormalMeasure r m S).map
        (fun x ↦ Real.log (x j / x r))).quantile u : EReal))
      (nhdsWithin 1 (Iio 1)) (nhds (if S j j = 0 then (m j : EReal) else ⊤)) := by
  rw [map_log_div_logisticNormalMeasure r m hS j]
  simpa only [← NNReal.coe_eq_zero, Real.coe_toNNReal _ hS.diag_nonneg] using
    tendsto_quantile_gaussianReal_nhdsLT_one (m j) (S j j).toNNReal

/-- The quantile of an additive log ratio to any reference category. Its Gaussian parameters
are obtained by the canonical reference-coordinate change. -/
theorem quantile_map_log_div_logisticNormalMeasure_reference (r s : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hS : S.PosSemidef) (j : {i // i ≠ s}) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((logisticNormalMeasure r m S).map (fun x ↦ Real.log (x j / x s))).quantile u =
      logisticNormalReferenceEquiv r s m j +
        √(2 * (logisticNormalReferenceMatrix r s * S *
          (logisticNormalReferenceMatrix r s).transpose) j j) * Real.erfInv (2 * u - 1) := by
  rw [logisticNormalMeasure_change_reference r s]
  exact quantile_map_log_div_logisticNormalMeasure s _
    ((posSemidef_logisticNormalReferenceMatrix_iff r s S).mpr hS) j hu

/-- At level zero an arbitrary-reference log-ratio quantile has the Gaussian lower endpoint
determined by the transformed covariance. -/
theorem tendsto_quantile_map_log_div_logisticNormalMeasure_reference_nhdsGT_zero (r s : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hS : S.PosSemidef) (j : {i // i ≠ s}) :
    Tendsto (fun u ↦
      (((logisticNormalMeasure r m S).map
        (fun x ↦ Real.log (x j / x s))).quantile u : EReal))
      (nhdsWithin 0 (Ioi 0)) (nhds (if
        (logisticNormalReferenceMatrix r s * S *
          (logisticNormalReferenceMatrix r s).transpose) j j = 0
        then (logisticNormalReferenceEquiv r s m j : EReal) else ⊥)) := by
  rw [logisticNormalMeasure_change_reference r s]
  exact tendsto_quantile_map_log_div_logisticNormalMeasure_nhdsGT_zero s _
    ((posSemidef_logisticNormalReferenceMatrix_iff r s S).mpr hS) j

/-- At level one an arbitrary-reference log-ratio quantile has the Gaussian upper endpoint
determined by the transformed covariance. -/
theorem tendsto_quantile_map_log_div_logisticNormalMeasure_reference_nhdsLT_one (r s : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hS : S.PosSemidef) (j : {i // i ≠ s}) :
    Tendsto (fun u ↦
      (((logisticNormalMeasure r m S).map
        (fun x ↦ Real.log (x j / x s))).quantile u : EReal))
      (nhdsWithin 1 (Iio 1)) (nhds (if
        (logisticNormalReferenceMatrix r s * S *
          (logisticNormalReferenceMatrix r s).transpose) j j = 0
        then (logisticNormalReferenceEquiv r s m j : EReal) else ⊤)) := by
  rw [logisticNormalMeasure_change_reference r s]
  exact tendsto_quantile_map_log_div_logisticNormalMeasure_nhdsLT_one s _
    ((posSemidef_logisticNormalReferenceMatrix_iff r s S).mpr hS) j

end TauCeti.Probability
