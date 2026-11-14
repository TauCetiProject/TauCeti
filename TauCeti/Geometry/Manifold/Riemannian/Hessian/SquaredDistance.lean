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
# The Hessian of squared distance at its centre

The Hessian of the squared Riemannian distance from any point `p`, evaluated at `p`, is twice
the Riemannian metric: `Hess(d_p²)_p = 2 g_p`. Its Laplace–Beltrami trace is twice the dimension.
These values supply the centre terms for local convexity and Hessian comparison of squared
distance.

## Main results

* `TauCeti.Manifold.hessian_dist_sq_self`: the Hessian of the squared distance from any point at
  that point is `2 g_p`.
* `TauCeti.Manifold.laplaceBeltrami_dist_sq_self`: its Laplace–Beltrami operator at that point is
  twice the dimension.

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
  obtain ⟨r, _, h⟩ := exists_isNormalDomain_ball (I := I) p
  have hlog : ContMDiffAt I 𝓘(ℝ, TangentSpace I p) 2 (riemannianLog I M p (Metric.ball 0 r)) p :=
    (h.contMDiffOn_riemannianLog.contMDiffAt
      (h.isOpen_image.mem_nhds h.self_mem_image)).of_le (by simp)
  have heq := h.dist_sq_eventuallyEq_norm_riemannianLog_sq
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

/-- The Laplace–Beltrami operator of squared distance at its centre is twice the dimension. -/
@[simp] theorem laplaceBeltrami_dist_sq_self (p : M) :
    laplaceBeltrami I (fun q ↦ dist p q ^ 2) p = 2 * (Module.finrank ℝ E : ℝ) := by
  simpa only [mul_comm] using
    laplaceBeltrami_eq_finrank_mul_of_hessian_eq_mul_inner (hessian_dist_sq_self p)

end TauCeti.Manifold
