/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Escape
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Minimization

/-!
# The Riemannian distance on a normal ball

Let `U` be a normal domain at `p` containing the closed tangent ball of radius `r`.  A `C¹` curve
from `p` to `exp_p v`, with `‖v‖ ≤ r`, either stays in the normal neighbourhood `exp_p '' U`,
where the radial geodesic minimizes length, or leaves it, and is then longer than `r` by the
escape estimate.  Since the Riemannian distance is the infimum of the lengths of such curves,
the radial geodesic `t ↦ exp_p (t • v)` realizes the distance from `p` to `exp_p v`:

`edist p (exp_p v) = ‖v‖`.

Consequently the geodesic balls `exp_p '' ball 0 r` and `exp_p '' closedBall 0 r` are the metric
balls of radius `r` about `p`.  Moreover, a curve from `p` to a point `q` outside the geodesic ball
must cross the geodesic sphere `exp_p '' sphere 0 r`, which gives

`edist p q = r + infEDist q (exp_p '' sphere 0 r)`.

This last identity is the step by which the distance to a far point is propagated along a
minimizing geodesic in the proof that an everywhere-defined exponential map yields minimizing
geodesics between any two points.

## Main results

In the namespace `TauCeti.Manifold.IsNormalDomain`:

* `edist_riemannianExp_eq`: `exp_p` preserves the distance from the centre of a normal ball, and
  `dist_riemannianExp_eq` its version for an ordinary metric.
* `pathELength_riemannianExp_smul_eq_edist`: the radial geodesic segment realizes the distance
  between its endpoints.
* `edist_eq_enorm_riemannianLog`: the distance from `p` is the norm of the logarithm.
* `image_riemannianExp_ball` and `image_riemannianExp_closedBall`: geodesic balls are metric
  balls.
* `edist_eq_ofReal_add_infEDist`: the distance to a point outside a geodesic ball is its radius
  plus the distance to the geodesic sphere.

## References

* The Apache-2.0 `frenzymath/Poincare-Conjecture` formalization, revision
  `24f32e4d600878bfaac6bc2f2f9324175571c321`, especially
  `DoCarmoLib/Riemannian/Exponential/NormalBallEDist.lean`.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3, Proposition 3.6 and its
  corollary, and Ch. 7, §2, the proof of Theorem 2.8.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 6, Proposition 6.11 and
  Corollary 6.13.
-/

public section

open Bundle Manifold Metric Set
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [T2Space (TangentBundle I M)]

namespace IsNormalDomain

variable {p : M} {U : Set (TangentSpace I p)} {r : ℝ} {v : TangentSpace I p} {q : M}

/-- Every `C¹` curve from `p` to `exp_p v` has length at least `‖v‖`, when `v` lies in a closed
tangent ball contained in a normal domain. -/
private theorem enorm_le_pathELength (h : IsNormalDomain I M p U) (hU : closedBall 0 r ⊆ U)
    (hv : v ∈ closedBall 0 r) {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1))
    (hγ0 : γ 0 = p) (hγ1 : γ 1 = riemannianExp I M p v) :
    ‖v‖ₑ ≤ pathELength I γ 0 1 := by
  have hvr : ‖v‖ ≤ r := mem_closedBall_zero_iff.1 hv
  rcases eq_or_lt_of_le ((norm_nonneg v).trans hvr) with hr | hr
  · -- A closed ball of radius zero only contains the origin.
    have hv0 : ‖v‖ₑ = 0 := by
      rw [← ofReal_norm, ENNReal.ofReal_eq_zero]
      exact hr ▸ hvr
    simp [hv0]
  by_cases hmaps : MapsTo γ (Icc 0 1) (riemannianExp I M p '' U)
  · -- A curve staying in the normal neighbourhood is no shorter than the radial geodesic.
    rw [← pathELength_riemannianExp_smul_zero_one h (hU hv)]
    exact h.pathELength_riemannianExp_smul_le (hU hv) zero_le_one hγ hmaps hγ0 hγ1
  · -- A curve leaving the normal neighbourhood has length at least `r`.
    simp only [MapsTo, not_forall] at hmaps
    obtain ⟨t, ht, hγt⟩ := hmaps
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal hvr).trans (h.pathELength_escape hr hU hγ hγ0 ⟨t, ht, hγt⟩)

/-- A continuous curve from `p` which ends outside the geodesic ball of radius `r` meets the
geodesic sphere of radius `r`. -/
private theorem exists_mem_riemannianExp_image_sphere (h : IsNormalDomain I M p U)
    (hU : closedBall 0 r ⊆ U) (hr : 0 ≤ r) {γ : ℝ → M} (hγ : ContinuousOn γ (Icc 0 1))
    (hγ0 : γ 0 = p) (hγ1 : γ 1 ∉ riemannianExp I M p '' Metric.ball 0 r) :
    ∃ t ∈ Icc (0 : ℝ) 1, γ t ∈ riemannianExp I M p '' sphere 0 r := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · exact ⟨0, left_mem_Icc.2 zero_le_one, 0, by simp, by rw [hγ0, riemannianExp_zero]⟩
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hball : IsNormalDomain I M p (Metric.ball 0 r) :=
    h.ball hU hr
  have hK : IsClosed (riemannianExp I M p '' closedBall 0 r) :=
    (isCompact_riemannianExp_image_closedBall p (hU.trans h.subset_expDomain)).isClosed
  -- The image of the curve is connected, meets the open geodesic ball at `p`, and contains no
  -- limit point of the ball outside it, since such a point would lie on the geodesic sphere.
  have hsub : γ '' Icc 0 1 ⊆ riemannianExp I M p '' Metric.ball 0 r := by
    refine (isPreconnected_Icc.image γ hγ).subset_of_closure_inter_subset hball.isOpen_image
      ⟨p, ⟨0, left_mem_Icc.2 zero_le_one, hγ0⟩, hball.self_mem_image⟩ ?_
    rintro x ⟨hx, t, ht, rfl⟩
    have hclosure := hK.closure_subset_iff.2 (image_mono Metric.ball_subset_closedBall) hx
    rw [← Metric.ball_union_sphere, image_union] at hclosure
    rcases hclosure with hball | hsphere
    · exact hball
    · exact absurd hsphere (hno t ht)
  exact hγ1 (hsub ⟨1, right_mem_Icc.2 zero_le_one, rfl⟩)

variable [IsRiemannianManifold I M]

/-- **Radial geodesics realize the distance on a normal ball.**  If the closed tangent ball of
radius `r` lies in a normal domain at `p`, then for every `v` in that ball the distance from `p`
to `exp_p v` is `‖v‖`. -/
theorem edist_riemannianExp_eq (h : IsNormalDomain I M p U) (hU : closedBall 0 r ⊆ U)
    (hv : v ∈ closedBall 0 r) :
    edist p (riemannianExp I M p v) = ‖v‖ₑ := by
  refine le_antisymm (edist_riemannianExp_le p v) ?_
  rw [IsRiemannianManifold.out (I := I)]
  exact le_riemannianEDist_of_forall_le_pathELength fun γ hγ0 hγ1 hγ ↦
    h.enorm_le_pathELength hU hv hγ hγ0 hγ1

/-- **A radial geodesic segment in a normal ball is minimizing:** its length is the distance
between its endpoints. -/
theorem pathELength_riemannianExp_smul_eq_edist (h : IsNormalDomain I M p U)
    (hU : closedBall 0 r ⊆ U) (hv : v ∈ closedBall 0 r) :
    pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 1 =
      edist p (riemannianExp I M p v) := by
  rw [pathELength_riemannianExp_smul_zero_one h (hU hv), h.edist_riemannianExp_eq hU hv]

/-- On a normal ball the distance from the centre is the norm of the Riemannian logarithm. -/
theorem edist_eq_enorm_riemannianLog (h : IsNormalDomain I M p U) (hU : closedBall 0 r ⊆ U)
    (hq : q ∈ riemannianExp I M p '' closedBall 0 r) :
    edist p q = ‖riemannianLog I M p U q‖ₑ := by
  obtain ⟨v, hv, rfl⟩ := hq
  rw [h.riemannianLog_riemannianExp (hU hv), h.edist_riemannianExp_eq hU hv]

/-- **The distance to a point outside a geodesic ball.**  If the closed tangent ball of radius
`r ≥ 0` lies in a normal domain at `p` and `q` lies outside the geodesic ball
`exp_p '' ball 0 r`, then the distance from `p` to `q` is `r` plus the distance from `q` to the
geodesic sphere `exp_p '' sphere 0 r`. -/
theorem edist_eq_ofReal_add_infEDist (h : IsNormalDomain I M p U) (hU : closedBall 0 r ⊆ U)
    (hr : 0 ≤ r) (hq : q ∉ riemannianExp I M p '' Metric.ball 0 r) :
    edist p q = ENNReal.ofReal r + infEDist q (riemannianExp I M p '' sphere 0 r) := by
  have hsphere : ∀ z ∈ sphere (0 : TangentSpace I p) r,
      edist p (riemannianExp I M p z) = ENNReal.ofReal r := fun z hz ↦ by
    rw [h.edist_riemannianExp_eq hU (sphere_subset_closedBall hz), ← ofReal_norm,
      mem_sphere_zero_iff_norm.1 hz]
  refine le_antisymm ?_ ?_
  · -- Going through any point of the geodesic sphere bounds the distance from above.
    refine tsub_le_iff_left.1 (le_infEDist.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    refine tsub_le_iff_left.2 ?_
    rw [← hsphere z hz, edist_comm q]
    exact edist_triangle _ _ _
  · -- Every curve from `p` to `q` crosses the geodesic sphere; split it there.
    rw [IsRiemannianManifold.out (I := I)]
    refine le_riemannianEDist_of_forall_le_pathELength fun γ hγ0 hγ1 hγ ↦ ?_
    obtain ⟨t, ht, z, hz, hzt⟩ :=
      h.exists_mem_riemannianExp_image_sphere hU hr hγ.continuousOn hγ0 (by rwa [hγ1])
    rw [← pathELength_add ht.1 ht.2]
    gcongr
    · calc ENNReal.ofReal r = edist (γ 0) (γ t) := by rw [hγ0, ← hzt, hsphere z hz]
        _ ≤ pathELength I γ 0 t :=
          IsRiemannianManifold.edist_le_pathELength (hγ.mono (Icc_subset_Icc le_rfl ht.2)) ht.1
    · calc infEDist q (riemannianExp I M p '' sphere 0 r) ≤ edist (γ t) (γ 1) := by
            rw [hγ1, edist_comm]
            exact infEDist_le_edist_of_mem ⟨z, hz, hzt⟩
        _ ≤ pathELength I γ t 1 :=
          IsRiemannianManifold.edist_le_pathELength (hγ.mono (Icc_subset_Icc ht.1 le_rfl)) ht.2

/-- **Geodesic balls are metric balls.**  If the closed tangent ball of radius `r` lies in a
normal domain at `p`, then `exp_p` maps the open tangent ball of radius `r` onto the open metric
ball of radius `r` about `p`. -/
theorem image_riemannianExp_ball (h : IsNormalDomain I M p U) (hU : closedBall 0 r ⊆ U) :
    riemannianExp I M p '' Metric.ball 0 r = eball p (ENNReal.ofReal r) := by
  ext q
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hvr : ‖v‖ < r := mem_ball_zero_iff.1 hv
    rw [mem_eball', h.edist_riemannianExp_eq hU (Metric.ball_subset_closedBall hv), ← ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff ((norm_nonneg v).trans_lt hvr)).2 hvr
  · intro hq
    rw [mem_eball'] at hq
    have hr : 0 < r := ENNReal.ofReal_pos.1 (pos_of_gt hq)
    by_contra hqV
    rw [h.edist_eq_ofReal_add_infEDist hU hr.le hqV] at hq
    exact (le_self_add).not_gt hq

/-- **Closed geodesic balls are closed metric balls.**  If the closed tangent ball of radius
`r ≥ 0` lies in a normal domain at `p`, then `exp_p` maps it onto the closed metric ball of radius
`r` about `p`. -/
theorem image_riemannianExp_closedBall (h : IsNormalDomain I M p U) (hU : closedBall 0 r ⊆ U)
    (hr : 0 ≤ r) :
    riemannianExp I M p '' closedBall 0 r = closedEBall p (ENNReal.ofReal r) := by
  ext q
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_closedEBall', h.edist_riemannianExp_eq hU hv, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (mem_closedBall_zero_iff.1 hv)
  · intro hq
    rw [mem_closedEBall'] at hq
    by_cases hqV : q ∈ riemannianExp I M p '' Metric.ball 0 r
    · exact image_mono Metric.ball_subset_closedBall hqV
    -- Outside the open geodesic ball, `q` is at distance zero from the compact geodesic sphere.
    rw [h.edist_eq_ofReal_add_infEDist hU hr hqV] at hq
    have hzero : infEDist q (riemannianExp I M p '' sphere 0 r) = 0 :=
      nonpos_iff_eq_zero.1 <| (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).1 <| by
        rwa [add_zero]
    have hS : IsClosed (riemannianExp I M p '' sphere 0 r) :=
      (isCompact_riemannianExp_image_sphere p
        (sphere_subset_closedBall.trans (hU.trans h.subset_expDomain))).isClosed
    exact image_mono sphere_subset_closedBall ((mem_iff_infEDist_zero_of_closed hS).2 hzero)

end IsNormalDomain

section Metric

variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [T2Space (TangentBundle I M)] [IsRiemannianManifold I M]
  {p : M} {U : Set (TangentSpace I p)} {r : ℝ} {v : TangentSpace I p}

/-- If the closed tangent ball of radius `r` lies in a normal domain at `p`, then the distance
from `p` to `exp_p v` is `‖v‖` for every `v` in that ball; see `edist_riemannianExp_eq`. -/
theorem IsNormalDomain.dist_riemannianExp_eq (h : IsNormalDomain I M p U)
    (hU : closedBall 0 r ⊆ U) (hv : v ∈ closedBall 0 r) :
    dist p (riemannianExp I M p v) = ‖v‖ := by
  rw [dist_edist, h.edist_riemannianExp_eq hU hv, toReal_enorm]

end Metric

end TauCeti.Manifold

end
