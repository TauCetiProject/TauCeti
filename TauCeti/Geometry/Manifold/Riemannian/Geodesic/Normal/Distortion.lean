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
intrinsic Riemannian distance, the exponential map on such a ball and the logarithm on its
image both have Lipschitz constant arbitrarily close to one. Thus the Riemannian distance
between two nearby points agrees with the distance between their normal coordinates up to a
factor arbitrarily close to one.

The logarithm bounds are first differential estimates on the image of the normal ball under the
exponential map. The Lipschitz bound for the logarithm integrates them along curves, which may
leave the normal ball: a curve which does so between points of a ball of a third of the radius is
longer than their normal coordinates are apart.

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

omit [T2Space M] in
/-- A `C¹` curve which starts at `exp_p v` for `v` in the tangent ball of radius `R / 3` and leaves
the normal neighbourhood `exp_p '' ball 0 R` is at least as long as the distance from `v` to any
`w` in the ball of radius `R / 3`. -/
private theorem IsNormalDomain.edist_le_pathELength_of_not_mapsTo {p : M} {R : ℝ}
    (hn : IsNormalDomain I M p (Metric.ball 0 R)) {v w : TangentSpace I p}
    (hv : v ∈ Metric.ball 0 (R / 3)) (hw : w ∈ Metric.ball 0 (R / 3)) {γ : ℝ → M}
    (hγ : CMDiff[Icc 0 1] 1 γ) (hγ0 : γ 0 = riemannianExp I M p v)
    (hmaps : ¬MapsTo γ (Icc 0 1) (riemannianExp I M p '' Metric.ball 0 R)) :
    edist v w ≤ pathELength I γ 0 1 := by
  have hr : 0 < R / 3 := Metric.pos_of_mem_ball hv
  simp only [MapsTo, not_forall] at hmaps
  obtain ⟨t, ht, hγt⟩ := hmaps
  rw [hn.image_riemannianExp_ball subset_rfl, Metric.mem_eball', not_lt] at hγt
  have hp0 : edist p (γ 0) < ENNReal.ofReal (R / 3) := by
    rw [hγ0, hn.edist_riemannianExp_eq_of_mem_ball subset_rfl
      (Metric.ball_subset_ball (by linarith) hv), ← ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).2 (mem_ball_zero_iff.1 hv)
  -- The normal coordinates of the endpoints are at most `2 R / 3` apart.
  have hvw : edist v w ≤ ENNReal.ofReal (2 * (R / 3)) := by
    rw [eDist_eq_eNorm_sub, ← ofReal_norm, two_mul]
    exact ENNReal.ofReal_le_ofReal ((norm_sub_le v w).trans
      (add_le_add (mem_ball_zero_iff.1 hv).le (mem_ball_zero_iff.1 hw).le))
  have hR3 : ENNReal.ofReal R = ENNReal.ofReal (R / 3) + ENNReal.ofReal (2 * (R / 3)) := by
    rw [← ENNReal.ofReal_add hr.le (by positivity)]
    ring_nf
  -- The curve travels from `γ 0` to the point `γ t` at distance at least `R` from `p`.
  calc edist v w ≤ ENNReal.ofReal (2 * (R / 3)) := hvw
    _ ≤ edist (γ 0) (γ t) := by
      have htri := hγt.trans (edist_triangle p (γ 0) (γ t))
      rw [hR3] at htri
      exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).1 (htri.trans (by gcongr))
    _ ≤ pathELength I γ 0 t :=
      IsRiemannianManifold.edist_le_pathELength (hγ.mono (Icc_subset_Icc le_rfl ht.2)) ht.1
    _ ≤ pathELength I γ 0 1 := by
      rw [← pathELength_add ht.1 ht.2]
      exact le_self_add

/-- The logarithm is Lipschitz on the image of a sufficiently small normal ball, with any
prescribed constant greater than one. Distances on the source are its intrinsic Riemannian
distances. -/
theorem exists_isNormalDomain_ball_lipschitzOnWith_riemannianLog (p : M) {c : ℝ≥0}
    (hc : 1 < c) :
    ∃ r > 0, IsNormalDomain I M p (Metric.ball 0 r) ∧
      LipschitzOnWith c (riemannianLog I M p (Metric.ball 0 r))
        (riemannianExp I M p '' Metric.ball 0 r) := by
  obtain ⟨R, hR, hn, -, hlog⟩ := exists_isNormalDomain_ball_norm_mfderiv_bounds (I := I) p
    (c := c) (by exact_mod_cast hc)
  have hr : 0 < R / 3 := by positivity
  have hsub : Metric.ball (0 : TangentSpace I p) (R / 3) ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball (by linarith)
  have hnr := hn.ball hsub hr
  refine ⟨R / 3, hr, hnr, ?_⟩
  rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
  rw [hnr.riemannianLog_riemannianExp hv, hnr.riemannianLog_riemannianExp hw,
    IsRiemannianManifold.out (I := I) (riemannianExp I M p v)]
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hc).ne'
  suffices key : edist v w / c ≤ riemannianEDist I (riemannianExp I M p v)
      (riemannianExp I M p w) by
    calc edist v w = c * (edist v w / c) := (ENNReal.mul_div_cancel hc0 ENNReal.coe_ne_top).symm
      _ ≤ _ := by gcongr
  refine le_riemannianEDist_of_forall_le_pathELength fun γ hγ0 hγ1 hγ ↦
    ENNReal.div_le_of_le_mul' ?_
  by_cases hmaps : MapsTo γ (Icc 0 1) (riemannianExp I M p '' Metric.ball 0 R)
  · -- Inside the larger normal ball, the logarithm stretches tangent vectors by at most `c`.
    have h := enorm_sub_le_mul_pathELength (f := riemannianLog I M p (Metric.ball 0 R))
      zero_le_one (hγ.mdifferentiableOn one_ne_zero)
      ((hn.contMDiffOn_riemannianLog.of_le (by simp)).comp hγ hmaps)
      (fun t ht ↦ hn.mdifferentiableAt_riemannianLog (hmaps ht))
      (C := c) fun t ht ↦ by
        have hb := (hlog (γ t) (hmaps ht) (mfderiv[Icc 0 1] γ t 1)).2
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal hb
    rwa [hγ0, hγ1, hn.riemannianLog_riemannianExp (hsub hv),
      hn.riemannianLog_riemannianExp (hsub hw), ← eDist_eq_eNorm_sub, edist_comm] at h
  · -- A curve leaving the larger normal ball is longer than the endpoints' coordinates differ.
    exact (hn.edist_le_pathELength_of_not_mapsTo hv hw hγ hγ0 hmaps).trans
      (le_mul_of_one_le_left' (by exact_mod_cast hc.le))

end EMetric

end TauCeti.Manifold
