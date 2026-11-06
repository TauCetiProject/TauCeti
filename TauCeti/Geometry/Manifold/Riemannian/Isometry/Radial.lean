/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Betweenness
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance

/-!
# Distance-preserving maps send radial geodesics to radial geodesics

Let `f : M → N` preserve the Riemannian distances, with `N` complete, and let `v` be a tangent
vector at `p` whose radial geodesic `t ↦ exp_p (t • v)`, `t ∈ [0, 1]`, is minimizing. If the
tangent ball of radius `r > ‖v‖` lies in a normal domain at `f p`, then `f (exp_p v)` lies in the
corresponding normal neighbourhood, and with `w = log_{f p} (f (exp_p v))` we have

`‖w‖ = ‖v‖` and `f (exp_p (t • v)) = exp_{f p} (t • w)` for `t ∈ [0, 1]`.

Indeed the minimizing radial geodesic is a metric geodesic segment, `f` carries it to a metric
geodesic segment from `f p`, and a metric geodesic segment from the centre of a normal ball is the
radial geodesic (`TauCeti.Manifold.IsNormalDomain.eqOn_riemannianExp_smul_of_isGeodesicSegment`).
Only the distance is used, not any smoothness of `f`.

Hence the map `v ↦ log_{f p} (f (exp_p v))` preserves norms and is homogeneous along each ray.
This is the first step of the theorem of Myers and Steenrod that a distance-preserving map
between Riemannian manifolds is smooth: once this map is shown to be a linear isometry, `f` is
`exp_{f p} ∘ A ∘ log_p` near `p`.

## Main results

* `Isometry.norm_riemannianLog_apply_riemannianExp`: `‖log_{f p} (f (exp_p v))‖ = ‖v‖`.
* `Isometry.apply_riemannianExp_smul`: `f (exp_p (t • v)) = exp_{f p} (t • w)` for `t ∈ [0, 1]`.
* `Isometry.riemannianLog_apply_riemannianExp_smul`: the logarithm of `f (exp_p (t • v))` is
  `t • w` for `t ∈ [0, 1]`.

## References

* S. B. Myers and N. E. Steenrod, *The group of isometries of a Riemannian manifold*, Ann. of
  Math. 40 (1939), 400–416.
* R. S. Palais, *On the differentiability of isometries*, Proc. Amer. Math. Soc. 8 (1957),
  805–807.
* S. Kobayashi, *Transformation Groups in Differential Geometry*, Springer, 1972, Ch. II, §1.
-/

public section

open Bundle Manifold Set TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Isometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)] [IsRiemannianManifold J N]

variable {f : M → N} {p : M} {v : TangentSpace I p} {U : Set (TangentSpace J (f p))} {r : ℝ}

/-- The image of the endpoint of a minimizing radial geodesic of length less than `r` is the
exponential of a vector of the same length in the tangent ball of radius `r` at `f p`. -/
private theorem exists_riemannianExp_eq_apply_riemannianExp (hf : Isometry f)
    (h : IsNormalDomain J N (f p) U) (hU : Metric.ball 0 r ⊆ U)
    (hmin : ‖v‖ ≤ dist p (riemannianExp I M p v)) (hvr : ‖v‖ < r) :
    ∃ w ∈ Metric.ball (0 : TangentSpace J (f p)) r,
      riemannianExp J N (f p) w = f (riemannianExp I M p v) ∧ ‖w‖ = ‖v‖ := by
  have hdist : dist (f p) (f (riemannianExp I M p v)) = ‖v‖ := by
    rw [hf.dist_eq]
    exact le_antisymm (dist_riemannianExp_le p v) hmin
  have hmem : f (riemannianExp I M p v) ∈ riemannianExp J N (f p) '' Metric.ball 0 r := by
    rw [h.image_riemannianExp_ball hU, Metric.eball_ofReal, Metric.mem_ball, dist_comm, hdist]
    exact hvr
  obtain ⟨w, hw, hwv⟩ := hmem
  exact ⟨w, hw, hwv, by rw [← h.dist_riemannianExp_eq_of_mem_ball hU hw, hwv, hdist]⟩

/-- **A distance-preserving map preserves the length of short minimizing radial vectors.** If
`f` preserves distances, the radial geodesic of `v` at `p` is minimizing and `‖v‖ < r` for a
tangent ball of radius `r` in a normal domain at `f p`, then the logarithm at `f p` of
`f (exp_p v)` has norm `‖v‖`. -/
theorem norm_riemannianLog_apply_riemannianExp (hf : Isometry f) (h : IsNormalDomain J N (f p) U)
    (hU : Metric.ball 0 r ⊆ U) (hmin : ‖v‖ ≤ dist p (riemannianExp I M p v)) (hvr : ‖v‖ < r) :
    ‖riemannianLog J N (f p) U (f (riemannianExp I M p v))‖ = ‖v‖ := by
  obtain ⟨w, hw, hwv, hwn⟩ := exists_riemannianExp_eq_apply_riemannianExp hf h hU hmin hvr
  rw [← hwv, h.riemannianLog_riemannianExp (hU hw), hwn]

variable [CompleteSpace N]

/-- **A distance-preserving map sends minimizing radial geodesics to radial geodesics.** Let `f`
preserve distances into a complete manifold, let the radial geodesic of `v` on `[0, 1]` be
minimizing, and let `‖v‖ < r` for a tangent ball of radius `r` in a normal domain at `f p`. Then
`f (exp_p (t • v)) = exp_{f p} (t • w)` for `t ∈ [0, 1]`, where `w` is the logarithm at `f p` of
`f (exp_p v)`. -/
theorem apply_riemannianExp_smul (hf : Isometry f) (h : IsNormalDomain J N (f p) U)
    (hU : Metric.ball 0 r ⊆ U)
    (hmin : ‖v‖ ≤ dist p (riemannianExp I M p v)) (hvr : ‖v‖ < r) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    f (riemannianExp I M p (t • v)) =
      riemannianExp J N (f p) (t • riemannianLog J N (f p) U (f (riemannianExp I M p v))) := by
  obtain ⟨w, hw, hwv, -⟩ := exists_riemannianExp_eq_apply_riemannianExp hf h hU hmin hvr
  rw [← hwv, h.riemannianLog_riemannianExp (hU hw)]
  have hseg :=
    (isGeodesicSegment_maximalGeodesic (mem_expDomain_of_norm_le_dist hmin) hmin).comp_isometry hf
  rw [← hwv] at hseg
  rw [riemannianExp_smul, ← Function.comp_apply (f := f)]
  exact h.eqOn_riemannianExp_smul_of_isGeodesicSegment hU hw hseg ht

/-- **The radial map of a distance-preserving map is homogeneous along rays.** Under the
hypotheses of `Isometry.apply_riemannianExp_smul`, the logarithm at `f p` of `f (exp_p (t • v))`
is `t` times that of `f (exp_p v)`, for `t ∈ [0, 1]`. -/
theorem riemannianLog_apply_riemannianExp_smul (hf : Isometry f) (h : IsNormalDomain J N (f p) U)
    (hU : Metric.ball 0 r ⊆ U)
    (hmin : ‖v‖ ≤ dist p (riemannianExp I M p v)) (hvr : ‖v‖ < r) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    riemannianLog J N (f p) U (f (riemannianExp I M p (t • v))) =
      t • riemannianLog J N (f p) U (f (riemannianExp I M p v)) := by
  rw [hf.apply_riemannianExp_smul h hU hmin hvr ht, h.riemannianLog_riemannianExp (hU ?_)]
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1,
    hf.norm_riemannianLog_apply_riemannianExp h hU hmin hvr]
  exact (mul_le_of_le_one_left (norm_nonneg v) ht.2).trans_lt hvr

end Isometry
