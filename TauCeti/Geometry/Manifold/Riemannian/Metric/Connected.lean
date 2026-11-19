/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Minimizing

/-!
# Connectedness from finite Riemannian distance

When an ordinary pseudometric agrees with the Riemannian distance, every pair of points can
be joined by a path. A chosen point supplies the nonemptiness needed for path connectedness.

An intrinsic open ball with compact closed ball is preconnected: compact continuation makes
the exponential map defined on the tangent ball, and its image is the intrinsic ball. No
completeness or connectedness assumption is used.
-/

public section

open Bundle Manifold Metric Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}

section FiniteDistance

variable [PseudoMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

include I in
/-- Finite native Riemannian distances give path connectedness; a chosen point supplies
nonemptiness. -/
theorem pathConnectedSpace_of_isRiemannianManifold (p : M) : PathConnectedSpace M := by
  refine ⟨⟨p⟩, fun x y ↦ joined_of_riemannianEDist_lt_top (I := I) ?_⟩
  rw [← IsRiemannianManifold.out (I := I) x y]
  exact edist_lt_top x y

end FiniteDistance

section Ball

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] {p : M} {R : ℝ}

include I in
/-- An intrinsic open ball is preconnected when the closed ball of the same radius is compact.
This includes empty balls and requires no completeness assumption. -/
theorem isPreconnected_ball_of_isCompact_closedBall (hK : IsCompact (closedBall p R)) :
    IsPreconnected (ball p R) := by
  have hdom : ball (0 : TangentSpace I p) R ⊆ expDomain I M p :=
    ball_subset_closedBall.trans (closedBall_subset_expDomain_of_isCompact_closedBall hK)
  rw [← image_riemannianExp_ball_of_ball_subset_expDomain hdom]
  exact (convex_ball (0 : TangentSpace I p) R).isPreconnected.image _
    ((continuousOn_riemannianExp p).mono hdom)

end Ball

end TauCeti.Manifold
