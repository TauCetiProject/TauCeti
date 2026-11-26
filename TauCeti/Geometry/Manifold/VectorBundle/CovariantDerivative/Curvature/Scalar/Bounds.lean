/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar.OperatorTrace
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Norm.Basic
public import TauCeti.Analysis.InnerProductSpace.Positive.Trace

/-!
# Scalar control of nonnegative curvature operators

Quadratic nonnegativity of the curvature endomorphism gives the bound
`⟪Rop z, z⟫ ≤ (Scal / 2) * ‖z‖²`; this quadratic-form bound does not require symmetry.
For a symmetric endomorphism with nonnegative quadratic form, its operator norm is at most
`Scal / 2`, and this controls four-vector curvature pairings and the vector `R(u,v)w`.
Scalar curvature then vanishes exactly at flat points. No completeness or positive dimension
is assumed.

The metric-level pointwise consequences for a scalar cap and nonnegative curvature operator,
including the full curvature-norm estimate, are provided in
`TauCeti.Geometry.Manifold.Riemannian.Curvature.Bounds`.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Chapter 4.
* B. Kleiner and J. Lott, *Notes on Perelman's papers*, Section 41.
* [frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions):
  the scalar and operator estimates adapt
  `PoincareMT.LeviCivitaData.curvatureOperatorBound_scalarCurvature`, using the native
  exterior-square normalization in which scalar curvature is twice the operator trace.
* [frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

variable [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov)

/-- Quadratic nonnegativity bounds the curvature quadratic form at `z` by
`(Scal / 2) * ‖z‖²`, without requiring symmetry. -/
theorem inner_curvatureEndomorphism_le_scalarCurvature_div_two_mul
    (x : M)
    (hpos : ∀ z : ⋀[ℝ]^2 (TangentSpace I x),
      0 ≤ ⟪cov.curvatureEndomorphism hcov x z, z⟫)
    (z : ⋀[ℝ]^2 (TangentSpace I x)) :
    ⟪cov.curvatureEndomorphism hcov x z, z⟫ ≤ cov.scalarCurvature x / 2 * ‖z‖ ^ 2 := by
  rw [cov.scalarCurvature_eq_two_mul_trace_curvatureEndomorphism hcov x,
    mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  simpa only [RCLike.re_to_real, real_inner_comm] using
    (cov.curvatureEndomorphism hcov x).re_inner_le_re_trace_mul_norm_sq
      (fun w ↦ by simpa only [RCLike.re_to_real, real_inner_comm] using hpos w) z

/-- The operator norm of a symmetric curvature endomorphism with nonnegative quadratic form
is at most half the scalar curvature. -/
theorem norm_curvatureEndomorphism_le_scalarCurvature_div_two
    (x : M) (hpos : (cov.curvatureEndomorphism hcov x).IsPositive) :
    ‖LinearMap.toContinuousLinearMap (cov.curvatureEndomorphism hcov x)‖ ≤
      cov.scalarCurvature x / 2 := by
  rw [cov.scalarCurvature_eq_two_mul_trace_curvatureEndomorphism hcov x,
    mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  simpa only [RCLike.re_to_real] using hpos.norm_toContinuousLinearMap_le_re_trace

/-- A positive curvature endomorphism bounds every curvature pairing by half the scalar
curvature times the norms of its two pure bivectors. -/
theorem abs_inner_curvatureTensor_le_scalarCurvature_div_two_mul_norm_ιMulti
    (x : M) (hpos : (cov.curvatureEndomorphism hcov x).IsPositive)
    (u v w z : TangentSpace I x) :
    |⟪cov.curvatureTensor x u v w, z⟫| ≤
      cov.scalarCurvature x / 2 * ‖exteriorPower.ιMulti ℝ 2 ![u, v]‖ *
        ‖exteriorPower.ιMulti ℝ 2 ![z, w]‖ := by
  refine (cov.abs_inner_curvatureTensor_le_norm_curvatureEndomorphism_mul_norm_ιMulti
    hcov x u v w z).trans ?_
  gcongr
  exact cov.norm_curvatureEndomorphism_le_scalarCurvature_div_two hcov x hpos

/-- For a symmetric curvature endomorphism with nonnegative quadratic form, every curvature
pairing is bounded by half the scalar curvature times the four vector norms. -/
theorem abs_inner_curvatureTensor_le_scalarCurvature_div_two_mul
    (x : M) (hpos : (cov.curvatureEndomorphism hcov x).IsPositive)
    (u v w z : TangentSpace I x) :
    |⟪cov.curvatureTensor x u v w, z⟫| ≤
      cov.scalarCurvature x / 2 * ‖u‖ * ‖v‖ * ‖w‖ * ‖z‖ := by
  refine (cov.abs_inner_curvatureTensor_le_norm_curvatureEndomorphism_mul hcov x u v w z).trans ?_
  gcongr
  exact cov.norm_curvatureEndomorphism_le_scalarCurvature_div_two hcov x hpos

/-- A positive curvature endomorphism bounds `R(u,v)w` by half the scalar curvature times
`‖u ∧ v‖ * ‖w‖`. -/
theorem norm_curvatureTensor_le_scalarCurvature_div_two_mul_norm_ιMulti
    (x : M) (hpos : (cov.curvatureEndomorphism hcov x).IsPositive)
    (u v w : TangentSpace I x) :
    ‖cov.curvatureTensor x u v w‖ ≤
      cov.scalarCurvature x / 2 * ‖exteriorPower.ιMulti ℝ 2 ![u, v]‖ * ‖w‖ := by
  refine (cov.norm_curvatureTensor_le_norm_curvatureEndomorphism_mul_norm_ιMulti
    hcov x u v w).trans ?_
  gcongr
  exact cov.norm_curvatureEndomorphism_le_scalarCurvature_div_two hcov x hpos

/-- For a symmetric curvature endomorphism with nonnegative quadratic form, half the scalar
curvature times the three input norms bounds the actual vector `R(u,v)w`. -/
theorem norm_curvatureTensor_le_scalarCurvature_div_two_mul
    (x : M) (hpos : (cov.curvatureEndomorphism hcov x).IsPositive)
    (u v w : TangentSpace I x) :
    ‖cov.curvatureTensor x u v w‖ ≤ cov.scalarCurvature x / 2 * ‖u‖ * ‖v‖ * ‖w‖ := by
  refine (cov.norm_curvatureTensor_le_norm_curvatureEndomorphism_mul hcov x u v w).trans ?_
  gcongr
  exact cov.norm_curvatureEndomorphism_le_scalarCurvature_div_two hcov x hpos

/-- A positive curvature endomorphism bounds the full Riemann curvature norm by
`n² * (Scal / 2)`, where `n` is the model dimension. -/
theorem riemannCurvatureNorm_le_finrank_sq_mul_scalarCurvature_div_two
    (x : M) (hpos : (cov.curvatureEndomorphism hcov x).IsPositive) :
    cov.riemannCurvatureNorm x ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
      (cov.scalarCurvature x / 2) := by
  exact cov.riemannCurvatureNorm_le_finrank_sq_mul_of_norm_curvatureTensor_le x
    (cov.norm_curvatureTensor_le_scalarCurvature_div_two_mul hcov x hpos)

/-- For a symmetric curvature endomorphism with nonnegative quadratic form, scalar curvature
vanishes exactly at flat points. -/
theorem scalarCurvature_eq_zero_iff_curvatureTensor_eq_zero
    (x : M) (hpos : (cov.curvatureEndomorphism hcov x).IsPositive) :
    cov.scalarCurvature x = 0 ↔ cov.curvatureTensor x = 0 := by
  refine ⟨fun hscalar ↦ ?_, cov.scalarCurvature_eq_zero_of_curvatureTensor_eq_zero x⟩
  ext u v w
  have hnorm : ‖cov.curvatureTensor x u v w‖ ≤ 0 := by
    simpa only [hscalar, zero_div, zero_mul] using
      cov.norm_curvatureTensor_le_scalarCurvature_div_two_mul hcov x hpos u v w
  exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))

end CovariantDerivative
