/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Quantile
public import TauCeti.Probability.Distributions.MatrixNormal.Transforms

/-!
# Quantiles of matrix normal linear statistics

For a matrix normal matrix `X` with mean `M`, row covariance `U` and column covariance `V`, the
Frobenius linear statistic `trace (Tᵀ X)` is Gaussian. Its lower quantile is its mean plus the
square root of its covariance quadratic form times the standard Gaussian quantile. This remains
valid for singular positive-semidefinite covariances, when a statistic may be constant.

The coordinate specialization gives the quantile of `X i j`, whose variance is
`U i i * V j j`. One-sided endpoint limits distinguish a constant statistic from a
positive-variance Gaussian statistic.

## References

* A. K. Gupta and D. K. Nagar, *Matrix Variate Distributions*, Chapman & Hall/CRC, 2000,
  chapter 2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology
open scoped Matrix NNReal

namespace Matrix

open TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The quantile of a real linear statistic of a matrix normal law is its directional mean plus
its directional standard deviation times the standard Gaussian quantile. This includes
zero-variance statistics. -/
theorem quantile_map_trace_transpose_mul_matrixNormalMeasure (M T : Matrix ι κ ℝ)
    {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ} (hU : U.PosSemidef) (hV : V.PosSemidef)
    {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((matrixNormalMeasure M U V).map (fun X ↦ (Tᵀ * X).trace)).quantile u =
      (Tᵀ * M).trace + √(Tᵀ * U * T * V).trace * (gaussianReal 0 1).quantile u := by
  rw [map_trace_transpose_mul_matrixNormalMeasure M T hU hV,
    quantile_gaussianReal_eq_add_mul _ _ hu,
    Real.coe_toNNReal _ (hU.trace_transpose_mul_mul_mul_nonneg hV T)]

/-- The quantile of an entry of a matrix normal law is its mean plus its standard deviation
times the standard Gaussian quantile. -/
theorem quantile_map_apply_matrixNormalMeasure (M : Matrix ι κ ℝ)
    {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ} (hU : U.PosSemidef) (hV : V.PosSemidef)
    (i : ι) (j : κ) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((matrixNormalMeasure M U V).map (fun X ↦ X i j)).quantile u =
      M i j + √(U i i * V j j) * (gaussianReal 0 1).quantile u := by
  rw [map_apply_matrixNormalMeasure M hU hV i j,
    quantile_gaussianReal_eq_add_mul _ _ hu,
    Real.coe_toNNReal _ (mul_nonneg hU.diag_nonneg hV.diag_nonneg)]

/-- At level zero, a matrix normal linear statistic tends to its constant value when its
variance vanishes and to minus infinity otherwise. -/
theorem tendsto_quantile_map_trace_transpose_mul_matrixNormalMeasure_nhdsGT_zero
    (M T : Matrix ι κ ℝ) {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ}
    (hU : U.PosSemidef) (hV : V.PosSemidef) :
    Tendsto (fun u ↦
        (((matrixNormalMeasure M U V).map (fun X ↦ (Tᵀ * X).trace)).quantile u : EReal))
      (𝓝[>] 0)
      (𝓝 (if (Tᵀ * U * T * V).trace = 0 then ((Tᵀ * M).trace : EReal) else ⊥)) := by
  have hnonneg := hU.trace_transpose_mul_mul_mul_nonneg hV T
  have hzero : ((Tᵀ * U * T * V).trace.toNNReal = 0) ↔
      (Tᵀ * U * T * V).trace = 0 := by
    rw [Real.toNNReal_eq_zero]
    exact ⟨fun h ↦ le_antisymm h hnonneg, fun h ↦ h.le⟩
  rw [map_trace_transpose_mul_matrixNormalMeasure M T hU hV]
  simpa only [hzero] using
    tendsto_quantile_gaussianReal_nhdsGT_zero (Tᵀ * M).trace
      (Tᵀ * U * T * V).trace.toNNReal

/-- At level one, a matrix normal linear statistic tends to its constant value when its
variance vanishes and to plus infinity otherwise. -/
theorem tendsto_quantile_map_trace_transpose_mul_matrixNormalMeasure_nhdsLT_one
    (M T : Matrix ι κ ℝ) {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ}
    (hU : U.PosSemidef) (hV : V.PosSemidef) :
    Tendsto (fun u ↦
        (((matrixNormalMeasure M U V).map (fun X ↦ (Tᵀ * X).trace)).quantile u : EReal))
      (𝓝[<] 1)
      (𝓝 (if (Tᵀ * U * T * V).trace = 0 then ((Tᵀ * M).trace : EReal) else ⊤)) := by
  have hnonneg := hU.trace_transpose_mul_mul_mul_nonneg hV T
  have hzero : ((Tᵀ * U * T * V).trace.toNNReal = 0) ↔
      (Tᵀ * U * T * V).trace = 0 := by
    rw [Real.toNNReal_eq_zero]
    exact ⟨fun h ↦ le_antisymm h hnonneg, fun h ↦ h.le⟩
  rw [map_trace_transpose_mul_matrixNormalMeasure M T hU hV]
  simpa only [hzero] using
    tendsto_quantile_gaussianReal_nhdsLT_one (Tᵀ * M).trace
      (Tᵀ * U * T * V).trace.toNNReal

end Matrix
