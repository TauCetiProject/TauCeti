/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Distance
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# Norm distortion in normal coordinates

On a sufficiently small normal ball at any point, the differential of the exponential map
and that of its inverse logarithm distort norms by arbitrarily little, uniformly over all
tangent directions. These estimates allow derivative bounds to be transferred between a
Riemannian manifold and its normal coordinates, for example in local smoothing arguments.
They require neither completeness nor a curvature bound. When the manifold carries its
intrinsic Riemannian distance, the exponential map on such a ball also has Lipschitz constant
arbitrarily close to one.

The logarithm bounds are differential estimates on the image of the normal ball under the
exponential map.

## References

* D. Azagra, J. Ferrera, F. López-Mesas and Y. Rangel,
  *Smooth approximation of Lipschitz functions on Riemannian manifolds*,
  J. Math. Anal. Appl. 326 (2007), 1370–1378, Section 2.
-/

public section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology NNReal

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

end TauCeti.Manifold
