/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Hessian.NormSq
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Squared distance on a normal ball

Let `U` be a normal domain at `p` containing the open tangent ball of radius `r`. On the metric
ball of radius `r` about `p`, the distance from `p` is the norm of the Riemannian logarithm, which
is smooth, including at `p` itself. Hence the squared distance `q ↦ dist p q ^ 2` is smooth on
that ball, although the distance itself is not differentiable at `p`. Since the logarithm vanishes
at `p` with identity differential there, the Hessian of the squared distance at `p` is twice the
Riemannian metric.

## Main results

In the namespace `TauCeti.Manifold.IsNormalDomain`:

* `contMDiffOn_dist_sq`: the squared distance from the centre is smooth on the metric ball.
* `hessian_dist_sq_self`: the Hessian of the squared distance at the centre is `2 g_p`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 6.
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold.IsNormalDomain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {p : M} {U : Set (TangentSpace I p)} {r : ℝ}

/-- If the open tangent ball of radius `r` lies in a normal domain at `p`, then the squared
distance from `p` is smooth on the metric ball of radius `r` about `p`, including at `p`. -/
theorem contMDiffOn_dist_sq (h : IsNormalDomain I M p U) (hU : Metric.ball 0 r ⊆ U) :
    ContMDiffOn I 𝓘(ℝ) ∞ (fun q ↦ dist p q ^ 2) (Metric.ball p r) := by
  have hsub : Metric.ball p r ⊆ riemannianExp I M p '' U := by
    rw [← h.image_riemannianExp_ball_eq_ball hU]
    exact image_mono hU
  refine ((contDiff_norm_sq ℝ).contMDiff.comp_contMDiffOn
    (h.contMDiffOn_riemannianLog.mono hsub)).congr fun q hq ↦ ?_
  simp only [Function.comp_apply, h.dist_eq_norm_riemannianLog hU hq]

/-- If the open tangent ball of radius `r > 0` lies in a normal domain at `p`, then the Hessian
of the squared distance from `p` at `p` is twice the Riemannian inner product. -/
theorem hessian_dist_sq_self (h : IsNormalDomain I M p U) (hU : Metric.ball 0 r ⊆ U) (hr : 0 < r)
    (v w : TangentSpace I p) :
    hessian I (fun q ↦ dist p q ^ 2) p v w = 2 * inner ℝ v w := by
  have hp : p ∈ Metric.ball p r := Metric.mem_ball_self hr
  have hlog : ContMDiffAt I 𝓘(ℝ, TangentSpace I p) 2 (riemannianLog I M p U) p :=
    (h.contMDiffOn_riemannianLog.contMDiffAt
      (h.isOpen_image.mem_nhds h.self_mem_image)).of_le (by simp)
  have heq : (fun q ↦ dist p q ^ 2) =ᶠ[𝓝 p] fun q ↦ ‖riemannianLog I M p U q‖ ^ 2 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hp] with q hq
    rw [h.dist_eq_norm_riemannianLog hU hq]
  have hdist : ContMDiffAt I 𝓘(ℝ) 2 (fun q ↦ dist p q ^ 2) p :=
    ((h.contMDiffOn_dist_sq hU).contMDiffAt (Metric.isOpen_ball.mem_nhds hp)).of_le (by simp)
  have hnorm : ContMDiffAt I 𝓘(ℝ) 2 (fun q ↦ ‖riemannianLog I M p U q‖ ^ 2) p :=
    (contDiff_norm_sq ℝ).contDiffAt.contMDiffAt.comp p hlog
  have hcrit : mvfderiv I (fun q ↦ ‖riemannianLog I M p U q‖ ^ 2) p = 0 := by
    ext a
    simpa only [Function.comp_def, fderiv_norm_sq_apply, h.riemannianLog_self, map_zero,
      smul_zero, zero_apply] using
      mvfderiv_comp_apply_of_differentiableAt (φ := fun z : TangentSpace I p ↦ ‖z‖ ^ 2)
        ((contDiff_norm_sq ℝ (n := 2)).differentiable (by norm_num)).differentiableAt
        (hlog.mdifferentiableAt (by simp)) a
  rw [hessian_eq_criticalHessian hdist (heq.mvfderiv_eq.trans hcrit),
    criticalHessian_congr_of_eventuallyEq heq, ← hessian_eq_criticalHessian hnorm hcrit,
    hessian_norm_sq_comp_of_eq_zero hlog h.riemannianLog_self]
  exact congrArg₂ (fun a b ↦ 2 * inner ℝ a b) (h.mfderiv_riemannianLog_self_apply v)
    (h.mfderiv_riemannianLog_self_apply w)

end TauCeti.Manifold.IsNormalDomain
