/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.MatrixNormal.Basic
public import TauCeti.Probability.Distributions.Gaussian.Transforms
public import TauCeti.LinearAlgebra.Matrix.Vec

/-!
# Directional transforms of matrix normal laws

For a matrix normal matrix `X` with mean `M`, row covariance `U` and column covariance `V`,
the real linear statistic `trace (Tᵀ * X)` is Gaussian with mean `trace (Tᵀ * M)` and variance
`trace (Tᵀ * U * T * V)`. This identifies its moment-generating, cumulant-generating and
characteristic functions through column-stacking vectorization. Positive semidefinite
covariances suffice, including singular covariances and empty row or column types.

Every directional exponential moment exists, also for invalid covariance parameters, where
the matrix normal law is the point mass at its mean.

## References

* A. K. Gupta and D. K. Nagar, *Matrix Variate Distributions*, Chapman & Hall/CRC, 2000,
  chapter 2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Kronecker Matrix NNReal RealInnerProductSpace

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
private lemma coe_toNNReal_trace_transpose_mul_mul_mul {U : Matrix ι ι ℝ}
    {V : Matrix κ κ ℝ} (hU : U.PosSemidef) (hV : V.PosSemidef) (T : Matrix ι κ ℝ) :
    ((Tᵀ * U * T * V).trace.toNNReal : ℝ) = (Tᵀ * U * T * V).trace :=
  Real.coe_toNNReal _ (hU.trace_transpose_mul_mul_mul_nonneg hV T)

private lemma hasLaw_trace_transpose_mul_matrixNormalMeasure (M T : Matrix ι κ ℝ)
    {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ} (hU : U.PosSemidef) (hV : V.PosSemidef) :
    HasLaw (fun X : Matrix ι κ ℝ ↦ (Tᵀ * X).trace)
      (gaussianReal (Tᵀ * M).trace (Tᵀ * U * T * V).trace.toNNReal)
      (matrixNormalMeasure M U V) := by
  have hpair (X : Matrix ι κ ℝ) :
      ⟪WithLp.toLp 2 T.vec, WithLp.toLp 2 X.vec⟫ = (Tᵀ * X).trace := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial]
    rw [dotProduct_comm, Matrix.vec_dotProduct_vec]
  have hquad :
      ⟪WithLp.toLp 2 T.vec, (V ⊗ₖ U).toEuclideanLin (WithLp.toLp 2 T.vec)⟫ =
        (Tᵀ * U * T * V).trace := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, star_trivial]
    rw [dotProduct_comm, hV.isHermitian.isSymm.vec_dotProduct_kronecker_mulVec_vec]
  refine ⟨(continuous_const.matrix_mul continuous_id).matrix_trace.measurable.aemeasurable, ?_⟩
  have h := map_inner_multivariateGaussian (WithLp.toLp 2 M.vec) (WithLp.toLp 2 T.vec)
    (hV.kronecker hU)
  rw [← map_vec_matrixNormalMeasure M hU hV,
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  simpa only [Function.comp_def, hpair, hquad] using h

/-- Each real linear statistic of a matrix normal law is Gaussian. Its variance may vanish;
no invertibility assumption is needed. -/
@[simp]
theorem map_trace_transpose_mul_matrixNormalMeasure (M T : Matrix ι κ ℝ)
    {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ} (hU : U.PosSemidef) (hV : V.PosSemidef) :
    (matrixNormalMeasure M U V).map (fun X ↦ (Tᵀ * X).trace) =
      gaussianReal (Tᵀ * M).trace (Tᵀ * U * T * V).trace.toNNReal :=
  (hasLaw_trace_transpose_mul_matrixNormalMeasure M T hU hV).map_eq

/-- A linear statistic of a random matrix with a matrix normal law has the corresponding
scalar Gaussian law. -/
theorem _root_.ProbabilityTheory.HasLaw.matrixNormal_trace_transpose_mul
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Matrix ι κ ℝ}
    {M : Matrix ι κ ℝ} {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ}
    (hX : HasLaw X (matrixNormalMeasure M U V) P) (T : Matrix ι κ ℝ)
    (hU : U.PosSemidef) (hV : V.PosSemidef) :
    HasLaw (fun ω ↦ (Tᵀ * X ω).trace)
      (gaussianReal (Tᵀ * M).trace (Tᵀ * U * T * V).trace.toNNReal) P :=
  (hasLaw_trace_transpose_mul_matrixNormalMeasure M T hU hV).fun_comp hX

/-- Every matrix normal linear statistic has every finite moment, including on the invalid
covariance branch. -/
theorem memLp_trace_transpose_mul_matrixNormalMeasure (M T : Matrix ι κ ℝ)
    (U : Matrix ι ι ℝ) (V : Matrix κ κ ℝ) (p : ℝ≥0) :
    MemLp (fun X ↦ (Tᵀ * X).trace) p (matrixNormalMeasure M U V) := by
  classical
  by_cases h : U.PosSemidef ∧ V.PosSemidef
  · exact ((HasLaw.id (μ := matrixNormalMeasure M U V)).matrixNormal_trace_transpose_mul
      T h.1 h.2).memLp (memLp_id_gaussianReal p)
  · rw [matrixNormalMeasure_of_not_posSemidef M h]
    exact memLp_dirac enorm_lt_top

/-- The variance of a matrix normal linear statistic is its covariance quadratic form. -/
@[simp]
theorem variance_trace_transpose_mul_matrixNormalMeasure (M T : Matrix ι κ ℝ)
    {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ} (hU : U.PosSemidef) (hV : V.PosSemidef) :
    Var[fun X ↦ (Tᵀ * X).trace; matrixNormalMeasure M U V] =
      (Tᵀ * U * T * V).trace := by
  have hstat := hasLaw_trace_transpose_mul_matrixNormalMeasure M T hU hV
  rw [← variance_id_map (X := fun X : Matrix ι κ ℝ ↦ (Tᵀ * X).trace)
      hstat.aemeasurable,
    map_trace_transpose_mul_matrixNormalMeasure M T hU hV, variance_id_gaussianReal,
    coe_toNNReal_trace_transpose_mul_mul_mul hU hV T]

/-- Every matrix normal linear statistic has finite exponential moments of all real orders,
including the point-mass fallback for invalid covariances. -/
@[simp]
theorem integrableExpSet_trace_transpose_mul_matrixNormalMeasure (M T : Matrix ι κ ℝ)
    (U : Matrix ι ι ℝ) (V : Matrix κ κ ℝ) :
    integrableExpSet (fun X ↦ (Tᵀ * X).trace) (matrixNormalMeasure M U V) = Set.univ := by
  classical
  by_cases h : U.PosSemidef ∧ V.PosSemidef
  · ext t
    simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ((HasLaw.id (μ := matrixNormalMeasure M U V)).matrixNormal_trace_transpose_mul
      T h.1 h.2).integrable_fun_comp (integrable_exp_mul_gaussianReal t)
  · rw [matrixNormalMeasure_of_not_posSemidef M h]
    ext t
    simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact integrable_dirac enorm_lt_top

/-- The directional mgf of a matrix normal law is the exponential of its linear mean term
plus half its covariance quadratic form. The formula holds for every real order. -/
theorem mgf_trace_transpose_mul_matrixNormalMeasure (M T : Matrix ι κ ℝ)
    {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ} (hU : U.PosSemidef) (hV : V.PosSemidef) (t : ℝ) :
    mgf (fun X ↦ (Tᵀ * X).trace) (matrixNormalMeasure M U V) t =
      Real.exp ((Tᵀ * M).trace * t + (Tᵀ * U * T * V).trace * t ^ 2 / 2) := by
  have hstat := hasLaw_trace_transpose_mul_matrixNormalMeasure M T hU hV
  rw [← mgf_id_map (X := fun X : Matrix ι κ ℝ ↦ (Tᵀ * X).trace)
      hstat.aemeasurable,
    map_trace_transpose_mul_matrixNormalMeasure M T hU hV,
    mgf_id_gaussianReal, coe_toNNReal_trace_transpose_mul_mul_mul hU hV T]

/-- The directional cgf of a matrix normal law is the quadratic polynomial determined by its
directional mean and variance. -/
@[simp]
theorem cgf_trace_transpose_mul_matrixNormalMeasure (M T : Matrix ι κ ℝ)
    {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ} (hU : U.PosSemidef) (hV : V.PosSemidef) (t : ℝ) :
    cgf (fun X ↦ (Tᵀ * X).trace) (matrixNormalMeasure M U V) t =
      (Tᵀ * M).trace * t + (Tᵀ * U * T * V).trace * t ^ 2 / 2 := by
  rw [cgf, mgf_trace_transpose_mul_matrixNormalMeasure M T hU hV, Real.log_exp]

/-- The characteristic function of a matrix normal linear statistic, with kernel `exp (itx)`.
The variance term retains its value at singular covariance parameters. -/
theorem charFun_map_trace_transpose_mul_matrixNormalMeasure (M T : Matrix ι κ ℝ)
    {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ} (hU : U.PosSemidef) (hV : V.PosSemidef) (t : ℝ) :
    charFun ((matrixNormalMeasure M U V).map (fun X ↦ (Tᵀ * X).trace)) t =
      Complex.exp (t * (Tᵀ * M).trace * Complex.I -
        (Tᵀ * U * T * V).trace * t ^ 2 / 2) := by
  rw [map_trace_transpose_mul_matrixNormalMeasure M T hU hV, charFun_gaussianReal,
    coe_toNNReal_trace_transpose_mul_mul_mul hU hV T]

end TauCeti.Probability
