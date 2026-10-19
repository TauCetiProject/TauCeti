/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity

/-!
# Scalar curvature of a smooth metric and positive scalar curvature

The scalar curvature of a smooth Riemannian metric `g` on the tangent bundle is the scalar
curvature of the Levi-Civita connection of `g`, computed with the inner products of `g` itself.
Recording it as a function of `g`, rather than of an ambient `RiemannianBundle` instance, lets
several metrics on one manifold be compared, as is needed for spaces and families of metrics.

A smooth metric has positive scalar curvature when its scalar curvature is positive at every
point. Since scalar curvature is a smooth function of the point, on a compact manifold such a
metric has scalar curvature bounded below by a positive constant. No assumption on the boundary
is made.

## Main definitions and results

* `Bundle.ContMDiffRiemannianMetric.scalarCurvature`: the scalar curvature of a smooth metric.
* `Bundle.ContMDiffRiemannianMetric.contMDiff_scalarCurvature`: it is a smooth function.
* `Bundle.ContMDiffRiemannianMetric.HasPositiveScalarCurvature`: positivity at every point.
* `Bundle.ContMDiffRiemannianMetric.hasPositiveScalarCurvature_iff_exists_pos_le`: on a compact
  manifold, positive scalar curvature is equivalent to a uniform positive lower bound.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive
  scalar curvature*, Ann. of Math. 111 (1980), 423–434.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7, for the scalar-curvature convention.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- The scalar curvature of a smooth Riemannian metric `g`: the scalar curvature of the
Levi-Civita connection of `g`, with `g` as the fibre inner product. -/
def scalarCurvature (x : M) : ℝ :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x

/-- The scalar curvature of `g` is that of its Levi-Civita connection, with `g` installed as the
fibre inner product. -/
theorem scalarCurvature_def (x : M) :
    g.scalarCurvature x =
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x :=
  (rfl)

/-- The scalar curvature of a smooth Riemannian metric is a smooth function. -/
theorem contMDiff_scalarCurvature : ContMDiff I 𝓘(ℝ) ∞ g.scalarCurvature := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact (CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature

/-- The scalar curvature of a smooth Riemannian metric is continuous. -/
theorem continuous_scalarCurvature : Continuous g.scalarCurvature :=
  g.contMDiff_scalarCurvature.continuous

/-- A smooth Riemannian metric has positive scalar curvature if its scalar curvature is positive
at every point. -/
def HasPositiveScalarCurvature : Prop :=
  ∀ x, 0 < g.scalarCurvature x

/-- A metric has positive scalar curvature exactly when its scalar curvature is positive at
every point. -/
theorem hasPositiveScalarCurvature_iff :
    g.HasPositiveScalarCurvature ↔ ∀ x, 0 < g.scalarCurvature x :=
  Iff.rfl

variable {g} in
/-- On a compact manifold, a metric of positive scalar curvature has scalar curvature bounded
below by a positive constant. -/
theorem HasPositiveScalarCurvature.exists_pos_le [CompactSpace M]
    (h : g.HasPositiveScalarCurvature) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, ε ≤ g.scalarCurvature x := by
  simpa only [Set.mem_univ, forall_const] using
    isCompact_univ.exists_forall_le' g.continuous_scalarCurvature.continuousOn
      fun x _ ↦ h x

/-- On a compact manifold, a metric has positive scalar curvature exactly when its scalar
curvature has a uniform positive lower bound. -/
theorem hasPositiveScalarCurvature_iff_exists_pos_le [CompactSpace M] :
    g.HasPositiveScalarCurvature ↔ ∃ ε : ℝ, 0 < ε ∧ ∀ x, ε ≤ g.scalarCurvature x :=
  ⟨HasPositiveScalarCurvature.exists_pos_le, fun ⟨_, hε, h⟩ x ↦ hε.trans_le (h x)⟩

end Bundle.ContMDiffRiemannianMetric
