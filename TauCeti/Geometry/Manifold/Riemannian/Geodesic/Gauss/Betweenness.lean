/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Rigidity
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.MetricSegment
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Length

/-!
# Points between the centre of a normal ball and another point

Let `M` be a complete Riemannian manifold, let `exp_p` restrict to a normal domain at `p`
containing the tangent ball of radius `r`, and let `y = exp_p w` with `‖w‖ < r`, so that
`dist p y = ‖w‖`. If a point `x` lies metrically between `p` and `y`, that is
`dist p x + dist x y = dist p y`, then `x` lies on the radial geodesic:

`x = exp_p ((dist p x / ‖w‖) • w)`.

Indeed, the radial geodesic from `p` to `x` followed by a minimizing geodesic from `x` to `y` is a
piecewise `C¹` curve from `p` to `y` of length `dist p y` inside the normal ball, so by the rigidity
of minimizers in a normal neighbourhood its corner `x` lies on the radial segment.

Consequently a metric geodesic segment from the centre of a normal ball, a curve parametrised
proportionally to arc length that realises the distance between its endpoints, is the radial
geodesic itself. No smoothness of the segment is assumed: the metric conditions alone determine
it. This is how a map that only preserves the Riemannian distance is seen to carry radial
geodesics to radial geodesics.

## Main results

* `TauCeti.Manifold.IsNormalDomain.eq_riemannianExp_smul_of_dist_add_dist_le`: a point between
  the centre `p` of a normal ball and `exp_p w` is `exp_p ((dist p x / ‖w‖) • w)`.
* `TauCeti.Manifold.IsNormalDomain.eqOn_riemannianExp_smul_of_isGeodesicSegment`: a metric
  geodesic segment from `p` to `exp_p w` is the radial geodesic `t ↦ exp_p (t • w)` on `[0, 1]`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §3, Proposition 3.6.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2nd ed., 2018, Ch. 6,
  Proposition 6.11.
* R. S. Palais, *On the differentiability of isometries*, Proc. Amer. Math. Soc. 8 (1957),
  805–807, for the use of this fact to show that distance-preserving maps send radial geodesics
  to radial geodesics.
-/

public section

open Bundle Manifold Metric Set
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable {p : M} {U : Set (TangentSpace I p)} {r : ℝ} {w : TangentSpace I p}

/-! ### Broken geodesics -/

/-- The broken geodesic that follows the geodesic from `p` with initial velocity `u` on `[0, 1]`,
and then the geodesic from `exp_p u` with initial velocity `z` on `[1, 2]`. -/
private def brokenGeodesic (p : M) (u : TangentSpace I p)
    (z : TangentSpace I (riemannianExp I M p u)) (t : ℝ) : M :=
  if t ≤ 1 then maximalGeodesic I M p u t else maximalGeodesic I M (riemannianExp I M p u) z (t - 1)

variable {u : TangentSpace I p} {z : TangentSpace I (riemannianExp I M p u)}

private theorem eqOn_brokenGeodesic_Icc_zero_one :
    EqOn (brokenGeodesic p u z) (maximalGeodesic I M p u) (Icc 0 1) := fun _ ht ↦
  ite_eq_left ht.2

private theorem brokenGeodesic_one : brokenGeodesic p u z 1 = riemannianExp I M p u := by
  simp [brokenGeodesic, ← riemannianExp_def]

variable [I.Boundaryless]

private theorem eqOn_brokenGeodesic_Icc_one_two :
    EqOn (brokenGeodesic p u z)
      (maximalGeodesic I M (riemannianExp I M p u) z ∘ fun t ↦ t - 1) (Icc 1 2) := by
  intro t ht
  rcases ht.1.eq_or_lt with rfl | ht1
  · simp [brokenGeodesic, ← riemannianExp_def]
  · exact ite_eq_right (not_le.2 ht1)

private theorem brokenGeodesic_zero : brokenGeodesic p u z 0 = p := by
  simp [brokenGeodesic]

private theorem brokenGeodesic_two :
    brokenGeodesic p u z 2 = riemannianExp I M (riemannianExp I M p u) z := by
  rw [eqOn_brokenGeodesic_Icc_one_two ⟨one_le_two, le_rfl⟩, Function.comp_apply,
    ← one_add_one_eq_two, add_sub_cancel_right, ← riemannianExp_def]

variable [IsRiemannianManifold I M]

/-- The broken geodesic stays within the sum of the speeds of its pieces from its start. -/
private theorem dist_brokenGeodesic_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    dist p (brokenGeodesic p u z t) ≤ ‖u‖ + ‖z‖ := by
  have hsmul {q : M} (v : TangentSpace I q) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
      dist q (maximalGeodesic I M q v s) ≤ ‖v‖ := by
    rw [← riemannianExp_smul]
    refine (dist_riemannianExp_le q _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hs.1]
    exact mul_le_of_le_one_left (norm_nonneg v) hs.2
  rcases le_total t 1 with ht1 | ht1
  · rw [eqOn_brokenGeodesic_Icc_zero_one ⟨ht.1, ht1⟩]
    exact (hsmul u ⟨ht.1, ht1⟩).trans (le_add_of_nonneg_right (norm_nonneg z))
  · rw [eqOn_brokenGeodesic_Icc_one_two ⟨ht1, ht.2⟩, Function.comp_apply]
    calc dist p (maximalGeodesic I M (riemannianExp I M p u) z (t - 1))
        ≤ dist p (riemannianExp I M p u) +
            dist (riemannianExp I M p u) (maximalGeodesic I M (riemannianExp I M p u) z (t - 1)) :=
          dist_triangle _ _ _
      _ ≤ ‖u‖ + ‖z‖ := add_le_add (dist_riemannianExp_le p u)
          (hsmul z ⟨sub_nonneg.2 ht1, by linarith [ht.2]⟩)

variable [CompleteSpace M]

private theorem isPiecewiseContMDiffOn_brokenGeodesic :
    IsPiecewiseContMDiffOn I 1 (brokenGeodesic p u z) 0 2 := by
  have hsmooth (q : M) (v : TangentSpace I q) : ContMDiff 𝓘(ℝ, ℝ) I 1 (maximalGeodesic I M q v) :=
    (contMDiffOn_univ.1
      (isGeodesicCurveOnFrom_maximalGeodesic_univ q v).isGeodesicCurveOn.contMDiffOn).of_le
      (by norm_num)
  exact (IsPiecewiseContMDiffOn.of_contMDiffOn zero_lt_one
    ((hsmooth p u).contMDiffOn.congr eqOn_brokenGeodesic_Icc_zero_one)).trans_contMDiffOn
    one_lt_two (((hsmooth _ z).comp (contMDiff_iff_contDiff.2 (by fun_prop))).contMDiffOn.congr
      eqOn_brokenGeodesic_Icc_one_two)

/-- The length of the broken geodesic is the sum of the speeds of its two pieces. -/
private theorem pathELength_brokenGeodesic :
    pathELength I (brokenGeodesic p u z) 0 2 = ‖u‖ₑ + ‖z‖ₑ := by
  have hJ (q : M) (v : TangentSpace I q) : geodesicInterval I M q v = univ := by
    rw [geodesicInterval_eq_preimage_expDomain, expDomain_eq_univ_of_completeSpace,
      preimage_univ]
  have hmd := (isGeodesicCurveOnFrom_maximalGeodesic_univ _ z).isGeodesicCurveOn.mdifferentiableOn
  rw [← pathELength_add zero_le_one one_le_two, pathELength_congr eqOn_brokenGeodesic_Icc_zero_one,
    pathELength_congr eqOn_brokenGeodesic_Icc_one_two,
    pathELength_comp_of_monotoneOn one_le_two (fun _ _ _ _ h ↦ by simpa using h) (by fun_prop)
      (hmd.mono (subset_univ _)),
    pathELength_maximalGeodesic (hJ p u ▸ mem_univ _) (hJ p u ▸ mem_univ _),
    pathELength_maximalGeodesic (hJ _ z ▸ mem_univ _) (hJ _ z ▸ mem_univ _)]
  norm_num

/-! ### Betweenness in a normal ball -/

/-- **A point between the centre of a normal ball and another point is on the radial
geodesic.** On a complete manifold, let `U` be a normal domain at `p` containing the tangent ball
of radius `r`, and let `w` lie in that ball. If `dist p x + dist x (exp_p w) ≤ ‖w‖`, then `x` is
the point `exp_p ((dist p x / ‖w‖) • w)` of the radial geodesic to `exp_p w`. -/
theorem IsNormalDomain.eq_riemannianExp_smul_of_dist_add_dist_le (h : IsNormalDomain I M p U)
    (hU : Metric.ball 0 r ⊆ U) (hw : w ∈ Metric.ball 0 r) {x : M}
    (hx : dist p x + dist x (riemannianExp I M p w) ≤ ‖w‖) :
    x = riemannianExp I M p ((dist p x / ‖w‖) • w) := by
  have hwr : ‖w‖ < r := mem_ball_zero_iff.1 hw
  -- Points within `‖w‖` of `p` lie in the geodesic ball of radius `r`.
  have hmem {q : M} (hq : dist p q ≤ ‖w‖) : q ∈ riemannianExp I M p '' Metric.ball 0 r := by
    rw [h.image_riemannianExp_ball hU, eball_ofReal, mem_ball, dist_comm]
    exact hq.trans_lt hwr
  -- So `x = exp_p u` with `‖u‖ = dist p x`.
  obtain ⟨u, hu, rfl⟩ := hmem ((le_add_of_nonneg_right dist_nonneg).trans hx)
  have hux : dist p (riemannianExp I M p u) = ‖u‖ := h.dist_riemannianExp_eq_of_mem_ball hU hu
  -- A minimizing geodesic from `x` to `exp_p w`, with initial velocity `z`.
  obtain ⟨z, hzy, hz⟩ := exists_riemannianExp_eq_and_norm_eq_dist
    (expDomain_eq_univ_of_completeSpace (I := I) (riemannianExp I M p u)) (riemannianExp I M p w)
  have hsum : ‖u‖ + ‖z‖ ≤ ‖w‖ := by rwa [← hux, hz]
  have hγ2 : brokenGeodesic p u z 2 = riemannianExp I M p w := brokenGeodesic_two.trans hzy
  -- The broken geodesic through `x` stays in the normal ball and is no longer than the radial
  -- geodesic to `exp_p w`, so it is a minimizer.
  have hγU : MapsTo (brokenGeodesic p u z) (Icc 0 2) (riemannianExp I M p '' U) := fun t ht ↦
    image_mono hU (hmem ((dist_brokenGeodesic_le ht).trans hsum))
  have hlen : pathELength I (brokenGeodesic p u z) 0 2 =
      pathELength I (fun t : ℝ ↦ riemannianExp I M p (t • w)) 0 1 := by
    refine le_antisymm ?_ (h.pathELength_riemannianExp_smul_le_of_piecewise (hU hw)
      isPiecewiseContMDiffOn_brokenGeodesic hγU brokenGeodesic_zero hγ2)
    rw [pathELength_brokenGeodesic, pathELength_riemannianExp_smul_zero_one h (hU hw),
      ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hsum
  -- By rigidity of minimizers, its corner `x` lies on the radial segment.
  have key := h.eq_riemannianExp_smul_of_pathELength_eq_of_piecewise (hU hw)
    isPiecewiseContMDiffOn_brokenGeodesic hγU brokenGeodesic_zero hγ2 hlen (t := 1)
    ⟨zero_le_one, one_le_two⟩
  rwa [brokenGeodesic_one, h.riemannianLog_riemannianExp (hU hu), ← hux] at key

/-- **Metric geodesic segments from the centre of a normal ball are radial.** On a complete
manifold, let `U` be a normal domain at `p` containing the tangent ball of radius `r`, and let `w`
lie in that ball. A metric geodesic segment from `p` to `exp_p w` is the radial geodesic
`t ↦ exp_p (t • w)` on `[0, 1]`. -/
theorem IsNormalDomain.eqOn_riemannianExp_smul_of_isGeodesicSegment (h : IsNormalDomain I M p U)
    (hU : Metric.ball 0 r ⊆ U) (hw : w ∈ Metric.ball 0 r) {γ : ℝ → M}
    (hγ : IsGeodesicSegment γ p (riemannianExp I M p w)) :
    EqOn γ (fun t ↦ riemannianExp I M p (t • w)) (Icc 0 1) := by
  intro t ht
  have hpw : dist p (riemannianExp I M p w) = ‖w‖ := h.dist_riemannianExp_eq_of_mem_ball hU hw
  have hsum : dist p (γ t) + dist (γ t) (riemannianExp I M p w) = ‖w‖ := by
    rw [hγ.dist_source_apply ht, hγ.dist_apply_target ht, hpw]
    ring
  rw [h.eq_riemannianExp_smul_of_dist_add_dist_le hU hw hsum.le, hγ.dist_source_apply ht, hpw]
  rcases eq_or_ne w 0 with rfl | hw0
  · simp
  · rw [mul_div_cancel_right₀ t (norm_ne_zero_iff.2 hw0)]

end TauCeti.Manifold
