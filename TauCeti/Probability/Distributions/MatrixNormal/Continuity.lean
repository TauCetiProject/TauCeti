/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Continuity
public import TauCeti.Probability.Distributions.MatrixNormal.Basic
public import TauCeti.Topology.Instances.Matrix

/-!
# Weak continuity of matrix normal laws

Matrix normal laws depend jointly weakly continuously on their mean and positive semidefinite
row and column covariances. Both covariances may be singular or zero, and either index type
may be empty. In particular, covariance limits that lose rank remain within this family.

The statements use `ProbabilityMeasure` and the inherited topology on each positive
semidefinite cone. The vectorized mean and Kronecker covariance vary continuously, so the
result follows from `TauCeti.Probability.continuous_multivariateGaussian` and Mathlib's
`ProbabilityMeasure.continuous_map`, applied to inverse vectorization.

## References

* A. K. Gupta and D. K. Nagar, *Matrix Variate Distributions*, Chapman & Hall/CRC, 2000,
  chapter 2, for the Gaussian vectorization of the matrix normal law.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped Kronecker

namespace TauCeti.Probability

/-- Matrix normal laws depend jointly weakly continuously on their mean and positive
semidefinite row and column covariances, including singular and zero covariances. -/
theorem continuous_matrixNormalMeasure {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] :
    Continuous (fun p : Matrix ι κ ℝ × {U : Matrix ι ι ℝ // U.PosSemidef} ×
        {V : Matrix κ κ ℝ // V.PosSemidef} ↦
      (matrixNormalMeasure p.1 p.2.1.1 p.2.2.1).toProbabilityMeasure) := by
  have hmean : Continuous (fun p : Matrix ι κ ℝ ×
      {U : Matrix ι ι ℝ // U.PosSemidef} × {V : Matrix κ κ ℝ // V.PosSemidef} ↦
        WithLp.toLp 2 p.1.vec) := by
    apply (PiLp.continuous_toLp 2 _).comp
    -- `Matrix.vec` is definitionally column stacking: `p.1.vec ij = p.1 ij.2 ij.1`.
    exact continuous_pi fun ij ↦ continuous_fst.matrix_elem ij.2 ij.1
  have hcov : Continuous (fun p : Matrix ι κ ℝ ×
      {U : Matrix ι ι ℝ // U.PosSemidef} × {V : Matrix κ κ ℝ // V.PosSemidef} ↦
        p.2.2.1 ⊗ₖ p.2.1.1) := by
    exact (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).matrix_kronecker
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  have hread : Continuous ((TauCeti.matrixVecMeasurableEquiv 2).symm :
      EuclideanSpace ℝ (κ × ι) → Matrix ι κ ℝ) := by
    have h : Continuous (fun x : EuclideanSpace ℝ (κ × ι) ↦
        Matrix.of fun i j ↦ x (j, i)) :=
      continuous_matrix fun i j ↦ PiLp.continuous_apply 2 _ (j, i)
    exact h.congr fun x ↦ (TauCeti.matrixVecMeasurableEquiv_symm_apply 2 x).symm
  have h := (ProbabilityMeasure.continuous_map hread).comp
    (hmean.multivariateGaussian hcov fun p ↦ p.2.2.2.kronecker p.2.1.2)
  refine h.congr fun p ↦ ?_
  apply ProbabilityMeasure.toMeasure_injective
  simp only [Function.comp_apply, ProbabilityMeasure.toMeasure_map,
    Measure.coe_toProbabilityMeasure]
  exact (matrixNormalMeasure_of_posSemidef p.1 p.2.1.2 p.2.2.2).symm

end TauCeti.Probability

namespace Continuous

variable {T : Type*} [TopologicalSpace T]

/-- Continuous matrix means and positive semidefinite row and column covariances give a
weakly continuous matrix normal family, including at singular covariances. -/
@[fun_prop]
theorem matrixNormalMeasure {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {M : T → Matrix ι κ ℝ} {U : T → Matrix ι ι ℝ} {V : T → Matrix κ κ ℝ}
    (hM : Continuous M) (hU : Continuous U) (hV : Continuous V)
    (hU_pos : ∀ t, (U t).PosSemidef) (hV_pos : ∀ t, (V t).PosSemidef) :
    Continuous (fun t ↦
      (TauCeti.Probability.matrixNormalMeasure (M t) (U t) (V t)).toProbabilityMeasure) := by
  simpa only [Function.comp_def] using
    TauCeti.Probability.continuous_matrixNormalMeasure.comp
      (hM.prodMk ((hU.subtype_mk hU_pos).prodMk (hV.subtype_mk hV_pos)))

end Continuous
