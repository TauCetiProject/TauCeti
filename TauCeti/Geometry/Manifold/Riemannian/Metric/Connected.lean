/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Otis Chodosh
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Minimizing

/-!
# Connectedness of intrinsic Riemannian balls

An intrinsic open ball is preconnected when the exponential map is defined on the tangent ball:
the exponential image of that ball is the intrinsic ball. In particular, compactness of the
closed ball supplies the required exponential domain by compact continuation. No completeness
or connectedness assumption is used.
-/

public section

open Bundle Manifold Metric Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}

section Ball

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] {p : M} {R : ℝ}

include I in
/-- An intrinsic open ball is preconnected when the exponential map is defined on the tangent
ball of the same radius. This includes empty balls and requires no completeness assumption. -/
theorem isPreconnected_ball_of_ball_subset_expDomain
    (hdom : ball (0 : TangentSpace I p) R ⊆ expDomain I M p) :
    IsPreconnected (ball p R) := by
  rw [← image_riemannianExp_ball_of_ball_subset_expDomain hdom]
  exact (convex_ball (0 : TangentSpace I p) R).isPreconnected.image _
    ((continuousOn_riemannianExp p).mono hdom)

include I in
/-- An intrinsic open ball is preconnected when the closed ball of the same radius is compact.
This includes empty balls and requires no completeness assumption. -/
theorem isPreconnected_ball_of_isCompact_closedBall (hK : IsCompact (closedBall p R)) :
    IsPreconnected (ball p R) := by
  exact isPreconnected_ball_of_ball_subset_expDomain (I := I)
    (ball_subset_closedBall.trans (closedBall_subset_expDomain_of_isCompact_closedBall hK))

end Ball

end TauCeti.Manifold
