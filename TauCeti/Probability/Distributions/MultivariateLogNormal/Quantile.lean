/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.MultivariateLogNormal.Moments
public import TauCeti.Probability.Distributions.LogNormal.Quantile

import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Quantiles of multivariate log-normal observables

Coordinates and products of real powers of coordinates of a multivariate log-normal vector
have scalar log-normal laws. Their interior quantiles are therefore explicit in terms of
`Real.erfInv`, the log-mean, and the log-covariance quadratic form. Negative exponents are
allowed because every coordinate is positive almost surely.

The one-sided endpoint limits lie in `EReal`. Positive log-variance gives limits zero and
plus infinity; zero log-variance gives the same positive constant at both endpoints. In
particular, the monomial formulas include singular covariances, the constant monomial, and
empty coordinate types.

The results specialize `map_eval_multivariateLogNormalMeasure` and
`map_prod_rpow_multivariateLogNormalMeasure` using the scalar quantile and endpoint theorems
in `TauCeti.Probability.Distributions.LogNormal.Quantile`.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The quantile of a coordinate, including a coordinate with zero log-variance. -/
theorem quantile_map_eval_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i : ι) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((multivariateLogNormalMeasure m S).map (fun x ↦ x i)).quantile u =
      Real.exp (m i + √(2 * S i i) * Real.erfInv (2 * u - 1)) := by
  rw [map_eval_multivariateLogNormalMeasure m hS i, quantile_logNormalMeasure _ _ hu,
    Real.coe_toNNReal _ hS.diag_nonneg]

/-- The quantile of a real-power monomial, including zero directional log-variance. -/
theorem quantile_map_prod_rpow_multivariateLogNormalMeasure (m q : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((multivariateLogNormalMeasure m S).map (fun x ↦ ∏ i, (x i) ^ (q i))).quantile u =
      Real.exp (⟪q, m⟫ + √(2 * ⟪q, S.toEuclideanLin q⟫) * Real.erfInv (2 * u - 1)) := by
  have hnonneg := (Matrix.isPositive_toEuclideanLin_iff.mpr hS).inner_nonneg_right q
  rw [map_prod_rpow_multivariateLogNormalMeasure m q hS, quantile_logNormalMeasure _ _ hu,
    Real.coe_toNNReal _ hnonneg]

/-- At level zero a coordinate quantile tends to zero, or to its atom if its log-variance
vanishes. -/
theorem tendsto_quantile_map_eval_multivariateLogNormalMeasure_nhdsGT_zero
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i : ι) :
    Tendsto (fun u ↦
      (((multivariateLogNormalMeasure m S).map (fun x ↦ x i)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 (if S i i = 0 then (Real.exp (m i) : EReal) else 0)) := by
  rw [map_eval_multivariateLogNormalMeasure m hS i]
  simpa only [← NNReal.coe_eq_zero, Real.coe_toNNReal _ hS.diag_nonneg] using
    tendsto_quantile_logNormalMeasure_nhdsGT_zero (m i) (S i i).toNNReal

/-- At level one a coordinate quantile tends to plus infinity, or to its atom if its
log-variance vanishes. -/
theorem tendsto_quantile_map_eval_multivariateLogNormalMeasure_nhdsLT_one
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i : ι) :
    Tendsto (fun u ↦
      (((multivariateLogNormalMeasure m S).map (fun x ↦ x i)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (if S i i = 0 then (Real.exp (m i) : EReal) else ⊤)) := by
  rw [map_eval_multivariateLogNormalMeasure m hS i]
  simpa only [← NNReal.coe_eq_zero, Real.coe_toNNReal _ hS.diag_nonneg] using
    tendsto_quantile_logNormalMeasure_nhdsLT_one (m i) (S i i).toNNReal

/-- At level zero a monomial quantile tends to zero, or to its atom if its directional
log-variance vanishes. -/
theorem tendsto_quantile_map_prod_rpow_multivariateLogNormalMeasure_nhdsGT_zero
    (m q : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    Tendsto (fun u ↦ (((multivariateLogNormalMeasure m S).map
      (fun x ↦ ∏ i, (x i) ^ (q i))).quantile u : EReal))
      (𝓝[>] 0) (𝓝 (if ⟪q, S.toEuclideanLin q⟫ = 0 then
        (Real.exp ⟪q, m⟫ : EReal) else 0)) := by
  have hnonneg := (Matrix.isPositive_toEuclideanLin_iff.mpr hS).inner_nonneg_right q
  rw [map_prod_rpow_multivariateLogNormalMeasure m q hS]
  simpa only [← NNReal.coe_eq_zero, Real.coe_toNNReal _ hnonneg] using
    tendsto_quantile_logNormalMeasure_nhdsGT_zero ⟪q, m⟫ (⟪q, S.toEuclideanLin q⟫).toNNReal

/-- At level one a monomial quantile tends to plus infinity, or to its atom if its
directional log-variance vanishes. -/
theorem tendsto_quantile_map_prod_rpow_multivariateLogNormalMeasure_nhdsLT_one
    (m q : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    Tendsto (fun u ↦ (((multivariateLogNormalMeasure m S).map
      (fun x ↦ ∏ i, (x i) ^ (q i))).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (if ⟪q, S.toEuclideanLin q⟫ = 0 then
        (Real.exp ⟪q, m⟫ : EReal) else ⊤)) := by
  have hnonneg := (Matrix.isPositive_toEuclideanLin_iff.mpr hS).inner_nonneg_right q
  rw [map_prod_rpow_multivariateLogNormalMeasure m q hS]
  simpa only [← NNReal.coe_eq_zero, Real.coe_toNNReal _ hnonneg] using
    tendsto_quantile_logNormalMeasure_nhdsLT_one ⟪q, m⟫ (⟪q, S.toEuclideanLin q⟫).toNNReal

end TauCeti.Probability
