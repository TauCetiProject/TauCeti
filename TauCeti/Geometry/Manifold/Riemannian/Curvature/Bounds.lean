/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar.Bounds
public import TauCeti.Geometry.Manifold.Riemannian.Curvature.Norm
public import TauCeti.Geometry.Manifold.Riemannian.Curvature.Operator

/-!
# Pointwise scalar bounds for nonnegative curvature operators

At a point where a metric has nonnegative curvature operator and scalar curvature at most `C`,
the native curvature vector is bounded by `C / 2` times the three input norms and its full
Riemann curvature norm is bounded by `n² * (C / 2)`, where `n` is the model dimension.
These statements use only the hypotheses at the displayed point; no family-wide assumptions are
needed. The corresponding connection-level estimates are supplied by `Scalar.Bounds`.
-/

public noncomputable section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))

/-- A pointwise scalar cap and nonnegative curvature operator bound `R(u,v)w` by the product
of the three tangent norms, all measured using `g` at `x`. -/
theorem norm_curvatureTensor_le_div_two_mul_of_scalarCurvature_le
    (x : M) {C : ℝ} (hpos : g.HasNonnegativeCurvatureOperatorAt x)
    (hscalar : g.scalarCurvature x ≤ C) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    ∀ (u v w : TangentSpace I x),
      ‖(CovariantDerivative.leviCivitaConnection I M).curvatureTensor x u v w‖ ≤
        C / 2 * ‖u‖ * ‖v‖ * ‖w‖ := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro u v w
  have hbound :=
    CovariantDerivative.norm_curvatureTensor_le_scalarCurvature_div_two_mul
      (CovariantDerivative.leviCivitaConnection I M)
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x
      ((g.hasNonnegativeCurvatureOperatorAt_iff_isPositive x).mp hpos) u v w
  have hscalar' :
      (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x ≤ C := by
    simpa only [g.scalarCurvature_eq_scalarCurvature_leviCivitaConnection rfl] using hscalar
  exact hbound.trans (by
    gcongr
  )

/-- A pointwise scalar cap and nonnegative curvature operator bound the full Riemann curvature
norm by `n² * (C / 2)`, where `n` is the model dimension. -/
theorem riemannCurvatureNorm_le_finrank_sq_mul_div_two_of_scalarCurvature_le
    (x : M) {C : ℝ} (hpos : g.HasNonnegativeCurvatureOperatorAt x)
    (hscalar : g.scalarCurvature x ≤ C) :
    g.riemannCurvatureNorm x ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (C / 2) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  rw [g.riemannCurvatureNorm_def]
  have hbound :=
    CovariantDerivative.riemannCurvatureNorm_le_finrank_sq_mul_scalarCurvature_div_two
      (CovariantDerivative.leviCivitaConnection I M)
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) x
      ((g.hasNonnegativeCurvatureOperatorAt_iff_isPositive x).mp hpos)
  refine hbound.trans ?_
  gcongr
  simpa only [g.scalarCurvature_eq_scalarCurvature_leviCivitaConnection rfl] using hscalar

end Bundle.ContMDiffRiemannianMetric
