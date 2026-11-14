/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Distance
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Distance
import TauCeti.Geometry.Manifold.Riemannian.MetricBridge

/-!
# Norm distortion in normal coordinates

On a sufficiently small normal ball at any point, the differential of the exponential map
and that of its inverse logarithm distort norms by arbitrarily little, uniformly over all
tangent directions. These estimates allow derivative bounds to be transferred between a
Riemannian manifold and its normal coordinates, for example in local smoothing arguments.
They require neither completeness nor a curvature bound. When the manifold carries its
intrinsic Riemannian distance, the exponential map on such a ball also has Lipschitz constant
arbitrarily close to one; on a metric space it distorts distances by a factor arbitrarily close
to one in both directions
(`TauCeti.Manifold.exists_isNormalDomain_ball_dist_riemannianExp_bounds`). This two-sided bound
shows that a map preserving the Riemannian distance is linear in normal coordinates.

The logarithm bounds are differential estimates on the image of the normal ball under the
exponential map.

## References

* D. Azagra, J. Ferrera, F. López-Mesas and Y. Rangel,
  *Smooth approximation of Lipschitz functions on Riemannian manifolds*,
  J. Math. Anal. Appl. 326 (2007), 1370–1378, Section 2.
-/

public section

open Bundle Filter Manifold Set
open scoped ContDiff ENNReal Manifold Topology NNReal

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Close to the zero vector, the exponential differential distorts every tangent norm by
at most any prescribed factor greater than one, uniformly in the tangent direction. -/
theorem eventually_norm_mfderiv_riemannianExp_bounds (p : M) {c : ℝ} (hc : 1 < c) :
    ∀ᶠ v in 𝓝 (0 : TangentSpace I p), ∀ w : TangentSpace I p,
      c⁻¹ * ‖w‖ ≤ ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ ∧
      ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ ≤ c * ‖w‖ := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := E)
      (V := fun x : M ↦ TangentSpace I x)
  have hcont := (contMDiffOn_riemannianExp (I := I) (M := M) p).continuousOn_norm_mfderiv_apply
    (by simp) (isOpen_expDomain p)
  have hunit : ∀ᶠ v in 𝓝 (0 : TangentSpace I p), ∀ w ∈ Metric.sphere (0 : TangentSpace I p) 1,
      c⁻¹ < ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ ∧
      ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ < c := by
    apply (isCompact_sphere (0 : TangentSpace I p) 1).eventually_forall_of_forall_eventually
    intro w hw
    have hn : ‖w‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
    have hz : expDomain I M p ×ˢ (univ : Set (TangentSpace I p)) ∈ 𝓝 (0, w) :=
      (isOpen_expDomain p).prod isOpen_univ |>.mem_nhds ⟨zero_mem_expDomain p, mem_univ w⟩
    refine (hcont.continuousAt hz).eventually (p := fun y ↦ c⁻¹ < y ∧ y < c) ?_
    simp only [mfderiv_riemannianExp_apply_zero]
    rw [riemannianExp_zero, hn]
    exact Ioo_mem_nhds (inv_lt_one_of_one_lt₀ hc) hc
  filter_upwards [hunit] with v hv w
  -- Compose with the canonical identification of the tangent space of a normed space;
  -- this exposes linearity with the fixed source norm rather than its tangent-space copy.
  let A := (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v).comp
    (NormedSpace.fromTangentSpace v).symm.toContinuousLinearMap
  have hA (z : TangentSpace I p) : A z =
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v z := by
    simp only [A, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      NormedSpace.fromTangentSpace_symm_apply]
  rw [← hA]
  by_cases hw : w = 0
  · simp [hw]
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let u := ‖w‖⁻¹ • w
  have hu : u ∈ Metric.sphere (0 : TangentSpace I p) 1 := by
    simp [u, norm_smul, hn.ne']
  have hwu : w = ‖w‖ • u := by simp [u, smul_smul, hn.ne']
  have h := hv u hu
  rw [← hA] at h
  have hAw := A.map_smul ‖w‖ u
  rw [← hwu] at hAw
  rw [hAw, norm_smul, Real.norm_eq_abs, abs_of_pos hn]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h.1.le hn.le]
  · nlinarith [mul_le_mul_of_nonneg_left h.2.le hn.le]

/-- Every point has a normal ball on which the differentials of both the exponential map
and its inverse logarithm distort norms by at most a prescribed factor greater than one. -/
theorem exists_isNormalDomain_ball_norm_mfderiv_bounds (p : M) {c : ℝ} (hc : 1 < c) :
    ∃ r > 0, IsNormalDomain I M p (Metric.ball 0 r) ∧
      (∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ w : TangentSpace I p,
        c⁻¹ * ‖w‖ ≤ ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ ∧
        ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ ≤ c * ‖w‖) ∧
      (∀ q ∈ riemannianExp I M p '' Metric.ball 0 r, ∀ w : TangentSpace I q,
        c⁻¹ * ‖w‖ ≤ ‖mfderiv I 𝓘(ℝ, TangentSpace I p)
          (riemannianLog I M p (Metric.ball 0 r)) q w‖ ∧
        ‖mfderiv I 𝓘(ℝ, TangentSpace I p)
          (riemannianLog I M p (Metric.ball 0 r)) q w‖ ≤ c * ‖w‖) := by
  obtain ⟨R, hR, hnormal⟩ := exists_isNormalDomain_ball (I := I) (M := M) p
  obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_norm_mfderiv_riemannianExp_bounds (I := I) p hc)
  let r := min R δ
  have hr : 0 < r := lt_min hR hδ
  have hsub : Metric.ball (0 : TangentSpace I p) r ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hsmall : Metric.ball (0 : TangentSpace I p) r ⊆ Metric.ball 0 δ :=
    Metric.ball_subset_ball (min_le_right _ _)
  have hn := hnormal.ball hsub hr
  have hb : ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ w : TangentSpace I p,
      c⁻¹ * ‖w‖ ≤ ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ ∧
      ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ ≤ c * ‖w‖ :=
    fun v hv ↦ hbound v (hsmall hv)
  refine ⟨r, hr, hn, hb, ?_⟩
  rintro q ⟨v, hv, rfl⟩ w
  have hcomp : mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v
      (mfderiv I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p (Metric.ball 0 r))
        (riemannianExp I M p v) w) = w :=
    DFunLike.congr_fun (hn.mfderiv_riemannianExp_comp_mfderiv_riemannianLog hv) w
  have hw := hb v hv (mfderiv I 𝓘(ℝ, TangentSpace I p)
    (riemannianLog I M p (Metric.ball 0 r)) (riemannianExp I M p v) w)
  rw [hcomp] at hw
  have hpos : 0 < c := lt_trans zero_lt_one hc
  constructor
  · exact (inv_mul_le_iff₀ hpos).mpr hw.2
  · have hh := mul_le_mul_of_nonneg_left hw.1 hpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at hh
    exact hh

section EMetric

variable {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- The exponential map is Lipschitz on a sufficiently small normal ball, with any prescribed
constant greater than one. Distances on the target are its intrinsic Riemannian distances. -/
theorem exists_isNormalDomain_ball_lipschitzOnWith_riemannianExp (p : M) {c : ℝ≥0}
    (hc : 1 < c) :
    ∃ r > 0, IsNormalDomain I M p (Metric.ball 0 r) ∧
      LipschitzOnWith c (riemannianExp I M p) (Metric.ball 0 r) := by
  obtain ⟨r, hr, hn, hb, -⟩ := exists_isNormalDomain_ball_norm_mfderiv_bounds (I := I) p
    (by exact_mod_cast hc)
  refine ⟨r, hr, hn, ?_⟩
  intro a ha b hb'
  have hseg := (convex_ball (0 : TangentSpace I p) r).segment_subset ha hb'
  have hle := IsRiemannianManifold.edist_le_of_norm_mfderiv_le
    (I := I) (f := riemannianExp I M p)
    (fun z hz ↦ (contMDiffAt_riemannianExp (hn.subset_expDomain (hseg hz))).of_le (by simp))
    (fun z hz ↦ (hb z (hseg hz) (b - a)).2)
  simpa [edist_dist, dist_eq_norm, norm_sub_rev, ENNReal.ofReal_mul] using hle

end EMetric

section Metric

variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- If the logarithm of a normal ball of radius `R` at `p` stretches tangent vectors by at most
`c`, then it moves by at most `c * δ` between two points `q, q'` with `dist q q' < δ`, as long as
`dist p q + δ ≤ R`: a `C¹` path from `q` to `q'` of length less than `δ` stays in the normal
ball. -/
private theorem norm_riemannianLog_sub_le_of_dist_lt {R c : ℝ}
    (hn : IsNormalDomain I M p (Metric.ball 0 R)) (hc0 : 0 < c)
    (hlog : ∀ q ∈ riemannianExp I M p '' Metric.ball 0 R, ∀ w : TangentSpace I q,
      ‖mfderiv I 𝓘(ℝ, TangentSpace I p) (riemannianLog I M p (Metric.ball 0 R)) q w‖ ≤ c * ‖w‖)
    {q q' : M} {δ : ℝ} (hqδ : dist p q + δ ≤ R) (hδ : dist q q' < δ) :
    ‖riemannianLog I M p (Metric.ball 0 R) q' - riemannianLog I M p (Metric.ball 0 R) q‖ ≤
      c * δ := by
  have hδ0 : 0 < δ := dist_nonneg.trans_lt hδ
  have hE : riemannianEDist I q q' < ENNReal.ofReal δ := by
    rwa [← IsRiemannianManifold.out (I := I), edist_dist, ENNReal.ofReal_lt_ofReal_iff hδ0]
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, -, -⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hE zero_lt_one
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ riemannianExp I M p '' Metric.ball 0 R := by
    intro s hs
    rw [hn.image_riemannianExp_ball_eq_ball subset_rfl, Metric.mem_ball, dist_comm]
    have h1 : riemannianEDist I q (γ s) < ENNReal.ofReal δ :=
      calc riemannianEDist I q (γ s) ≤ pathELength I γ 0 s :=
            riemannianEDist_le_pathELength hγ.contMDiffOn hγ0 rfl hs.1
        _ ≤ pathELength I γ 0 1 := pathELength_mono le_rfl hs.2
        _ < ENNReal.ofReal δ := hlen
    rw [← IsRiemannianManifold.out (I := I), edist_dist, ENNReal.ofReal_lt_ofReal_iff hδ0] at h1
    linarith [dist_triangle p q (γ s)]
  have hC : ((c.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal c := rfl
  have hbound := enorm_sub_le_mul_pathELength (I := I)
    (f := riemannianLog I M p (Metric.ball 0 R)) zero_le_one
    (hγ.contMDiffOn.mdifferentiableOn one_ne_zero)
    ((hn.contMDiffOn_riemannianLog.of_le (by simp)).comp hγ.contMDiffOn fun s hs ↦ hmem s hs)
    (fun t ht ↦ hn.mdifferentiableAt_riemannianLog (hmem t ht)) (C := c.toNNReal)
    fun t ht ↦ by
      rw [hC, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hc0.le]
      exact ENNReal.ofReal_le_ofReal (hlog _ (hmem t ht) _)
  rw [hγ0, hγ1, hC] at hbound
  have hle := hbound.trans (mul_le_mul_right hlen.le _)
  rwa [← ofReal_norm, ← ENNReal.ofReal_mul hc0.le,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle

/-- **The exponential map nearly preserves distances near the origin.** For every `c > 1`, on a
sufficiently small normal ball the exponential map distorts distances by at most the factor `c`
in each direction: `‖v - w‖ ≤ c * dist (exp_p v) (exp_p w)` and
`dist (exp_p v) (exp_p w) ≤ c * ‖v - w‖`. Distances on `M` are its intrinsic Riemannian
distances. -/
theorem exists_isNormalDomain_ball_dist_riemannianExp_bounds (p : M) {c : ℝ} (hc : 1 < c) :
    ∃ r > 0, IsNormalDomain I M p (Metric.ball 0 r) ∧
      ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ w ∈ Metric.ball (0 : TangentSpace I p) r,
        ‖v - w‖ ≤ c * dist (riemannianExp I M p v) (riemannianExp I M p w) ∧
          dist (riemannianExp I M p v) (riemannianExp I M p w) ≤ c * ‖v - w‖ := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  obtain ⟨R, hR, hn, -, hlog⟩ := exists_isNormalDomain_ball_norm_mfderiv_bounds (I := I) p hc
  obtain ⟨R', hR', -, hlip⟩ := exists_isNormalDomain_ball_lipschitzOnWith_riemannianExp
    (I := I) (M := M) p (c := c.toNNReal) (Real.one_lt_toNNReal.2 hc)
  set r := min (R / 3) R'
  have hr : 0 < r := lt_min (by positivity) hR'
  have hrR : r ≤ R / 3 := min_le_left _ _
  refine ⟨r, hr, hn.ball (Metric.ball_subset_ball (by linarith)) hr, fun v hv w hw ↦ ⟨?_, ?_⟩⟩
  · have hball : Metric.ball (0 : TangentSpace I p) r ⊆ Metric.ball 0 R :=
      Metric.ball_subset_ball (by linarith)
    have hpv : dist p (riemannianExp I M p v) < r :=
      (dist_riemannianExp_le p v).trans_lt (mem_ball_zero_iff.1 hv)
    have hpw : dist p (riemannianExp I M p w) < r :=
      (dist_riemannianExp_le p w).trans_lt (mem_ball_zero_iff.1 hw)
    have hd : dist (riemannianExp I M p v) (riemannianExp I M p w) < 2 * r := by
      linarith [dist_triangle_left (riemannianExp I M p v) (riemannianExp I M p w) p]
    -- Between `exp_p v` and `exp_p w` the logarithm moves by at most `c * δ` for every `δ`
    -- between their distance and `2 r`.
    rw [← div_le_iff₀' hc0]
    refine le_of_forall_gt_imp_ge_of_dense fun a ha ↦ ?_
    have key := norm_riemannianLog_sub_le_of_dist_lt hn hc0 (fun q hq u ↦ (hlog q hq u).2)
      (δ := min a (2 * r)) (by linarith [min_le_right a (2 * r)]) (lt_min ha hd)
    rw [hn.riemannianLog_riemannianExp (hball hv), hn.riemannianLog_riemannianExp (hball hw),
      norm_sub_rev] at key
    rw [div_le_iff₀' hc0]
    exact key.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hc0.le)
  · have h := hlip.dist_le_mul v (Metric.ball_subset_ball (min_le_right _ _) hv) w
      (Metric.ball_subset_ball (min_le_right _ _) hw)
    rwa [Real.coe_toNNReal _ hc0.le, dist_eq_norm] at h

end Metric

end TauCeti.Manifold
