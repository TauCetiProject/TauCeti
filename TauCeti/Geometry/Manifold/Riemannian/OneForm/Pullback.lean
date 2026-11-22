/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.OneForm.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local

/-!
# Metric duals under local isometries

The differential of a local Riemannian isometry takes the metric dual of a pulled-back
one-form to the original metric dual. This relates the vector fields that generate the
positive and negative metric-dual flows on a covering with its pullback metric.

The inner-product characterization parallels `IsLocalRiemannianIsometry.mfderiv_mgradient_comp`
for gradients of functions.
-/

public section

open Bundle
open scoped Manifold

namespace TauCeti.IsLocalRiemannianIsometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J 1 N] [RiemannianBundle (fun y : N ↦ TangentSpace J y)] {p : M → N}

/-- The differential of a local isometry sends the dual of the pulled-back one-form to
the dual of the original form. This holds pointwise for any rough one-form. -/
@[simp]
theorem mfderiv_metricDual_mpullback (hp : IsLocalRiemannianIsometry I J p)
    (α : RoughForm J N ℝ 1) (x : M) :
    mfderiv I J p x ((mpullback I J p α).metricDual x) = α.metricDual (p x) := by
  apply ext_inner_right ℝ
  intro v
  obtain ⟨w, rfl⟩ := hp.mfderiv_surjective x v
  simp only [hp.inner_mfderiv, RoughForm.inner_metricDual, mpullback_apply,
    Matrix.vec_single_eq_const]

end TauCeti.IsLocalRiemannianIsometry
