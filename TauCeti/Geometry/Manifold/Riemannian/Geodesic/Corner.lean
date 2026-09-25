/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness
import Mathlib.Analysis.InnerProductSpace.Convex
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Broken radial geodesics through the base point are not minimizing

Let `v` and `w` be tangent vectors at `p` in the natural domain of the exponential map.  Following
the radial geodesic from `exp_p v` back to `p` and then the radial geodesic from `p` out to
`exp_p w` gives a path of length `‖v‖ + ‖w‖`.  When `v` and `w` are nonzero and do not point in
opposite directions, this path has a genuine corner at `p`, and it is not minimizing:

`edist (exp_p v) (exp_p w) < ‖v‖ + ‖w‖`.

The corner is cut near `p`.  For a small `t > 0` the two radial legs are followed only from
`exp_p v` to `exp_p (t • v)` and from `exp_p (t • w)` to `exp_p w`, which saves `t (‖v‖ + ‖w‖)`,
while the points `exp_p (t • v)` and `exp_p (t • w)` are joined by the exponential image of the
chord from `t • v` to `t • w`.  The differential of `exp_p` at the origin is the identity and it
depends continuously on the point of `T_p M` at which it is taken, so for small `t` this chord has
length at most `t (‖v - w‖ + η)` for any prescribed `η > 0`.  As `‖v - w‖ < ‖v‖ + ‖w‖` exactly
when `v` and `-w` do not lie on the same ray, the saving wins.

This is the local rigidity needed to extend a minimizing geodesic segment in the proof that an
everywhere-defined exponential map yields minimizing geodesics: a path through a point which
realizes the distance between points on either side of it, and consists of radial geodesics
from that point, has to leave it in the direction in which it arrived.

## Main results

* `TauCeti.Manifold.eventually_edist_riemannianExp_smul_le`: near the origin, `exp_p` lengthens
  the chord from `t • v` to `t • w` by at most a factor arbitrarily close to `1`.
* `TauCeti.Manifold.edist_riemannianExp_lt_enorm_add_enorm` and
  `TauCeti.Manifold.dist_riemannianExp_lt_norm_add_norm`: **a broken radial path through `p` whose
  legs are not opposite is strictly longer than the distance between its endpoints.**

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §2, proof of Thm. 2.8, the step
  showing that the minimizing direction propagates.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 6, proof of Thm. 6.19.
-/

public section

open Bundle Filter Manifold Set
open scoped ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable [FiniteDimensional ℝ E] [I.Boundaryless]

section EMetric

variable {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [T2Space (TangentBundle I M)] [IsRiemannianManifold I M]

/-- Near the origin the exponential map lengthens chords by at most a factor close to `1`: for
every `η > 0`, if `t > 0` is small enough then `exp_p (t • v)` and `exp_p (t • w)` are at distance
at most `t * (‖w - v‖ + η)`. -/
theorem eventually_edist_riemannianExp_smul_le (p : M) (v w : TangentSpace I p) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), edist (riemannianExp I M p (t • v)) (riemannianExp I M p (t • w)) ≤
      ENNReal.ofReal (t * (‖w - v‖ + η)) := by
  have hdom : expDomain I M p ∈ 𝓝 (0 : TangentSpace I p) :=
    (isOpen_expDomain p).mem_nhds (zero_mem_expDomain p)
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := E)
    (V := fun x : M ↦ TangentSpace I x)
  have hcont : ContinuousAt
      (fun z ↦ ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) z (w - v)‖) 0 :=
    ((contMDiffOn_riemannianExp p).continuousOn_norm_mfderiv (by simp) (isOpen_expDomain p)
      (w - v)).continuousAt hdom
  have hgood : ∀ᶠ z in 𝓝 (0 : TangentSpace I p), z ∈ expDomain I M p ∧
      ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) z (w - v)‖ < ‖w - v‖ + η := by
    refine (Filter.eventually_mem_set.2 hdom).and (hcont.eventually (eventually_lt_nhds ?_))
    simp only [mfderiv_riemannianExp_apply_zero]
    rw [riemannianExp_zero]
    exact lt_add_of_pos_right (‖w - v‖) hη
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hgood
  have hsmul : ∀ u : TangentSpace I p, ∀ᶠ t in 𝓝[>] (0 : ℝ), t • u ∈ Metric.ball 0 ρ := by
    intro u
    have ht : Tendsto (fun t : ℝ ↦ t • u) (𝓝 0) (𝓝 0) :=
      (by fun_prop : Continuous fun t : ℝ ↦ t • u).tendsto' 0 0 (zero_smul ℝ u)
    exact (ht.mono_left nhdsWithin_le_nhds).eventually (Metric.ball_mem_nhds 0 hρ)
  filter_upwards [hsmul v, hsmul w, self_mem_nhdsWithin] with t hv hw (ht : 0 < t)
  have hseg : segment ℝ (t • v) (t • w) ⊆ Metric.ball 0 ρ :=
    (convex_ball 0 ρ).segment_subset hv hw
  refine IsRiemannianManifold.edist_le_of_norm_mfderiv_le
    (fun z hz ↦ (contMDiffAt_riemannianExp (hball _ (hseg hz)).1).of_le (by simp)) fun z hz ↦ ?_
  have hlin : mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) z (t • w - t • v) =
      t • mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) z (w - v) :=
    (congrArg (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) z)
      (smul_sub t w v).symm).trans
      ((mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) z).map_smul t (w - v))
  rw [hlin, norm_smul, Real.norm_of_nonneg ht.le]
  exact mul_le_mul_of_nonneg_left (hball _ (hseg hz)).2.le ht.le

/-- **A broken radial path through the base point is not minimizing.** Let `v` and `w` lie in the
natural domain of `exp_p`, with `v` and `-w` not on a common ray: both are nonzero and they do not
point in opposite directions.  Then `exp_p v` and `exp_p w` are at distance strictly less than
`‖v‖ + ‖w‖`, the length of the path which follows the radial geodesic from `exp_p v` back to `p`
and then the radial geodesic from `p` to `exp_p w`. -/
theorem edist_riemannianExp_lt_enorm_add_enorm {p : M} {v w : TangentSpace I p}
    (hv : v ∈ expDomain I M p) (hw : w ∈ expDomain I M p) (hvw : ¬SameRay ℝ v (-w)) :
    edist (riemannianExp I M p v) (riemannianExp I M p w) < ‖v‖ₑ + ‖w‖ₑ := by
  have hlt : ‖v - w‖ < ‖v‖ + ‖w‖ := by
    simpa [sub_eq_add_neg] using norm_add_lt_of_not_sameRay hvw
  set δ := ‖v‖ + ‖w‖ - ‖v - w‖ with hδ_def
  have hδ : 0 < δ := by linarith
  obtain ⟨t, hchord, ht⟩ := ((eventually_edist_riemannianExp_smul_le p v w (half_pos hδ)).and
    (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  -- the radial leg from `exp_p u` back to `exp_p (t • u)` has length `(1 - t) * ‖u‖`
  have hleg : ∀ u ∈ expDomain I M p, edist (riemannianExp I M p u)
      (riemannianExp I M p (t • u)) ≤ ENNReal.ofReal ((1 - t) * ‖u‖) := by
    intro u hu
    have h1 : (1 : ℝ) ∈ geodesicInterval I M p u := mem_expDomain_iff.1 hu
    have ht' : t ∈ geodesicInterval I M p u :=
      ordConnected_geodesicInterval.out zero_mem_geodesicInterval h1 ⟨ht.1.le, ht.2.le⟩
    rw [riemannianExp_def, riemannianExp_smul]
    calc
      edist (maximalGeodesic I M p u 1) (maximalGeodesic I M p u t) ≤ ‖u‖₊ * edist 1 t :=
        lipschitzOnWith_maximalGeodesic h1 ht'
      _ = ENNReal.ofReal ((1 - t) * ‖u‖) := by
        rw [edist_dist, Real.dist_eq, abs_of_pos (by linarith [ht.2]), mul_comm,
          ENNReal.ofReal_mul (by linarith [ht.2]), ofReal_norm, enorm_eq_nnnorm]
  have hsum : (1 - t) * ‖v‖ + t * (‖w - v‖ + δ / 2) + (1 - t) * ‖w‖ =
      ‖v‖ + ‖w‖ - t * δ / 2 := by
    rw [hδ_def, norm_sub_rev w v]
    ring
  calc
    edist (riemannianExp I M p v) (riemannianExp I M p w) ≤
        edist (riemannianExp I M p v) (riemannianExp I M p (t • v)) +
          edist (riemannianExp I M p (t • v)) (riemannianExp I M p (t • w)) +
            edist (riemannianExp I M p (t • w)) (riemannianExp I M p w) :=
      edist_triangle4 _ _ _ _
    _ ≤ ENNReal.ofReal ((1 - t) * ‖v‖) + ENNReal.ofReal (t * (‖w - v‖ + δ / 2)) +
          ENNReal.ofReal ((1 - t) * ‖w‖) := by
      rw [edist_comm (riemannianExp I M p (t • w))]
      gcongr
      · exact hleg v hv
      · exact hleg w hw
    _ = ENNReal.ofReal (‖v‖ + ‖w‖ - t * δ / 2) := by
      have h1t : 0 ≤ 1 - t := by linarith [ht.2]
      have hv' : 0 ≤ (1 - t) * ‖v‖ := mul_nonneg h1t (norm_nonneg _)
      have hw' : 0 ≤ (1 - t) * ‖w‖ := mul_nonneg h1t (norm_nonneg _)
      have hc : 0 ≤ t * (‖w - v‖ + δ / 2) := mul_nonneg ht.1.le (by positivity)
      rw [← hsum, ENNReal.ofReal_add (add_nonneg hv' hc) hw', ENNReal.ofReal_add hv' hc]
    _ < ENNReal.ofReal (‖v‖ + ‖w‖) :=
      (ENNReal.ofReal_lt_ofReal_iff ((norm_nonneg _).trans_lt hlt)).2
        (by nlinarith [mul_pos ht.1 hδ])
    _ = ‖v‖ₑ + ‖w‖ₑ := by
      rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ofReal_norm,
        ofReal_norm]

end EMetric

section Metric

variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [T2Space (TangentBundle I M)] [IsRiemannianManifold I M]

/-- A broken radial path through the base point whose legs are not opposite is strictly longer
than the distance between its endpoints; see `edist_riemannianExp_lt_enorm_add_enorm`. -/
theorem dist_riemannianExp_lt_norm_add_norm {p : M} {v w : TangentSpace I p}
    (hv : v ∈ expDomain I M p) (hw : w ∈ expDomain I M p) (hvw : ¬SameRay ℝ v (-w)) :
    dist (riemannianExp I M p v) (riemannianExp I M p w) < ‖v‖ + ‖w‖ := by
  have h := edist_riemannianExp_lt_enorm_add_enorm hv hw hvw
  rwa [edist_dist, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)] at h

end Metric

end TauCeti.Manifold

end
