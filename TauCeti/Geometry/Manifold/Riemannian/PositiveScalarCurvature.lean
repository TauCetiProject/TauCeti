/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback

/-!
# Positive scalar curvature

A smooth Riemannian metric `g` on the tangent bundle has positive scalar curvature when its
scalar curvature `Bundle.ContMDiffRiemannianMetric.scalarCurvature`, that of the Levi-Civita
connection of `g`, is positive at every point. Since scalar curvature is a smooth function of
the point, on a compact manifold such a metric has scalar curvature bounded below by a positive
constant. Scalar curvature is invariant under diffeomorphisms, so pulling a metric back along a
diffeomorphism preserves and reflects positive scalar curvature. No assumption on the
boundary is made.

## Main definitions and results

* `Bundle.ContMDiffRiemannianMetric.HasPositiveScalarCurvature`: positivity at every point.
* `Bundle.ContMDiffRiemannianMetric.HasPositiveScalarCurvature.exists_pos_le`: on a compact
  manifold, positive scalar curvature has a uniform positive lower bound.
* `Bundle.ContMDiffRiemannianMetric.hasPositiveScalarCurvature_iff_exists_pos_le`: on a compact
  manifold, positive scalar curvature is equivalent to a uniform positive lower bound.
* `Bundle.ContMDiffRiemannianMetric.hasPositiveScalarCurvature_pullback_iff`: the pullback of a
  metric along a diffeomorphism has positive scalar curvature exactly when the metric does.

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

section Pullback

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- The pullback of a metric along a diffeomorphism has positive scalar curvature exactly when the
metric does. -/
@[simp]
theorem hasPositiveScalarCurvature_pullback_iff
    (g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y))
    (Φ : M ≃ₘ^∞⟮I, J⟯ N) (hf : ContMDiff I J (∞ + 1) Φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J Φ x)) :
    (g.pullback Φ hf hinj).HasPositiveScalarCurvature ↔ g.HasPositiveScalarCurvature := by
  simp only [hasPositiveScalarCurvature_iff, scalarCurvature_pullback]
  exact ⟨fun h y ↦ by simpa using h (Φ.symm y), fun h x ↦ h (Φ x)⟩

variable {g : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)} in
/-- Pulling a metric of positive scalar curvature back along a diffeomorphism gives a metric of
positive scalar curvature. -/
theorem HasPositiveScalarCurvature.pullback (h : g.HasPositiveScalarCurvature)
    (Φ : M ≃ₘ^∞⟮I, J⟯ N) (hf : ContMDiff I J (∞ + 1) Φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J Φ x)) :
    (g.pullback Φ hf hinj).HasPositiveScalarCurvature :=
  (hasPositiveScalarCurvature_pullback_iff g Φ hf hinj).2 h

end Pullback

end Bundle.ContMDiffRiemannianMetric
