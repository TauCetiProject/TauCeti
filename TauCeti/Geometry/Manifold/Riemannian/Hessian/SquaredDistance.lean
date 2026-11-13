/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.MFDeriv.Inner
import TauCeti.Geometry.Manifold.Riemannian.Hessian.NormSq
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Squared distance on a normal ball

Let `U` be a normal domain at `p` containing the open tangent ball of radius `r`. On the metric
ball of radius `r > 0` about `p`, the distance from `p` is the norm of the Riemannian logarithm.
The logarithm is smooth across `p`, as is the squared norm on the tangent space, so the squared
distance `q ↦ dist p q ^ 2` is smooth on that ball. Since the logarithm vanishes
at `p` with identity differential there, and every point is the centre of such a ball, the
Hessian of the squared distance from any point `p` at `p` is twice the Riemannian metric.

## Main results

* `TauCeti.Manifold.hessian_dist_sq_self`: the Hessian of the squared distance from any point at
  that point is `2 g_p`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Chs. 5–6 and 11.
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {p : M} {U : Set (TangentSpace I p)} {r : ℝ}

/-- The Hessian of the squared distance from `p` at `p` is twice the Riemannian inner product. -/
@[simp] theorem hessian_dist_sq_self (p : M) (v w : TangentSpace I p) :
    hessian I (fun q ↦ dist p q ^ 2) p v w = 2 * inner ℝ v w := by
  obtain ⟨r, hr, h⟩ := exists_isNormalDomain_ball (I := I) p
  have hp : p ∈ Metric.ball p r := Metric.mem_ball_self hr
  have hlog : ContMDiffAt I 𝓘(ℝ, TangentSpace I p) 2 (riemannianLog I M p (Metric.ball 0 r)) p :=
    (h.contMDiffOn_riemannianLog.contMDiffAt
      (h.isOpen_image.mem_nhds h.self_mem_image)).of_le (by simp)
  have heq : (fun q ↦ dist p q ^ 2) =ᶠ[𝓝 p]
      fun q ↦ ‖riemannianLog I M p (Metric.ball 0 r) q‖ ^ 2 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hp] with q hq
    rw [h.dist_eq_norm_riemannianLog_of_mem_ball subset_rfl hq]
  have hdist : ContMDiffAt I 𝓘(ℝ) 2 (fun q ↦ dist p q ^ 2) p :=
    (contMDiffAt_dist_sq_self p).of_le (by simp)
  have hnorm : ContMDiffAt I 𝓘(ℝ) 2
      (fun q ↦ ‖riemannianLog I M p (Metric.ball 0 r) q‖ ^ 2) p :=
    (contDiff_norm_sq ℝ).contDiffAt.contMDiffAt.comp p hlog
  have hcrit := mvfderiv_norm_sq_comp_eq_zero_of_eq_zero (hlog.mdifferentiableAt (by simp))
    h.riemannianLog_self
  rw [hessian_eq_criticalHessian hdist (mvfderiv_dist_sq_self p),
    criticalHessian_congr_of_eventuallyEq heq, ← hessian_eq_criticalHessian hnorm hcrit,
    hessian_norm_sq_comp_of_eq_zero hlog h.riemannianLog_self]
  simp only [h.mvfderiv_riemannianLog_self, ContinuousLinearMap.id_apply]

end TauCeti.Manifold
