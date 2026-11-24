/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Hessian.Eikonal

/-!
# The radial Hessian of the distance on a normal ball

On a metric normal ball the distance from the centre is smooth away from the centre, and its
gradient is the unit radial velocity. These first-order results are developed in
`TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance`. The constant norm of the gradient
implies that the Hessian of the distance vanishes in the radial direction. At the centre the
gradient vanishes, so the radial Hessian also vanishes there. Completeness is not assumed.

## Main results

* `TauCeti.Manifold.IsNormalDomain.hessian_dist_mgradient_eq_zero`: the radial direction lies
  in the kernel of the Hessian of the distance on a metric normal ball.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Springer, 2018, Chapters 6
  and 11.
-/

public section

open Bundle Filter Metric Set
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {p q : M} {U : Set (TangentSpace I p)} {r : ℝ}

namespace IsNormalDomain

/-- The radial direction, the gradient of the distance from the centre, lies in the kernel of the
Hessian of the distance on a metric normal ball. -/
theorem hessian_dist_mgradient_eq_zero (h : IsNormalDomain I M p U) (hU : Metric.ball 0 r ⊆ U)
    (hq : q ∈ Metric.ball p r) (w : TangentSpace I q) :
    hessian I (fun x ↦ dist p x) q (mgradient I (fun x ↦ dist p x) q) w = 0 := by
  rcases eq_or_ne q p with rfl | hne
  · simp [I.hessian_eq_inner_leviCivitaConnection_mgradient]
  apply hessian_mgradient_eq_zero_of_eventually_norm_sq_eq_const
    ((h.contMDiffAt_dist hU hq hne).of_le (by simp)) (c := 1)
  have hq' : q ∈ Metric.ball p r \ {p} := ⟨hq, hne⟩
  filter_upwards [(isOpen_ball.sdiff isClosed_singleton).mem_nhds hq'] with x hx
  rw [h.norm_mgradient_dist hU hx.1 hx.2, one_pow]

end IsNormalDomain

end TauCeti.Manifold
