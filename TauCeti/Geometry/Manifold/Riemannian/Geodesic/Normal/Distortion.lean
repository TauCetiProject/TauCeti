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
intrinsic Riemannian distance, the exponential map on such a ball is bi-Lipschitz with both
constants arbitrarily close to one. The lower bound compares a path between two points of a
smaller ball with its logarithm when the path stays in the normal neighbourhood, and with the
distance to the boundary of the normal neighbourhood when it leaves it
(`TauCeti.Manifold.IsNormalDomain.ofReal_le_enorm_add_pathELength`).

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

omit [T2Space M] in
/-- A path that starts at `exp_p v` and leaves the normal neighbourhood `exp_p '' ball 0 R` has
length at least `R - ‖v‖`. -/
theorem IsNormalDomain.ofReal_le_enorm_add_pathELength {p : M} {R : ℝ}
    (hn : IsNormalDomain I M p (Metric.ball 0 R)) {v : TangentSpace I p}
    (hv : v ∈ Metric.ball 0 R) {γ : ℝ → M} (hγ : CMDiff[Icc 0 1] 1 γ)
    (hγ0 : γ 0 = riemannianExp I M p v) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hγt : γ t ∉ riemannianExp I M p '' Metric.ball 0 R) :
    ENNReal.ofReal R ≤ ‖v‖ₑ + pathELength I γ 0 1 := by
  rw [hn.image_riemannianExp_ball subset_rfl, Metric.mem_eball, not_lt, edist_comm] at hγt
  calc ENNReal.ofReal R ≤ edist p (γ t) := hγt
    _ ≤ edist p (γ 0) + edist (γ 0) (γ t) := edist_triangle _ _ _
    _ ≤ ‖v‖ₑ + pathELength I γ 0 1 := by
      gcongr
      · rw [hγ0, hn.edist_riemannianExp_eq_of_mem_ball subset_rfl hv]
      exact (IsRiemannianManifold.edist_le_pathELength (hγ.mono (Icc_subset_Icc_right ht.2))
        ht.1).trans (pathELength_mono le_rfl ht.2)

/-- The exponential map is antilipschitz on a sufficiently small normal ball, with any prescribed
constant greater than one: it shrinks distances by at most that factor. Distances on the target
are its intrinsic Riemannian distances. -/
theorem exists_isNormalDomain_ball_antilipschitzWith_riemannianExp (p : M) {c : ℝ≥0}
    (hc : 1 < c) :
    ∃ r > 0, IsNormalDomain I M p (Metric.ball 0 r) ∧
      AntilipschitzWith c ((Metric.ball (0 : TangentSpace I p) r).domRestrict
        (riemannianExp I M p)) := by
  obtain ⟨R, hR, hn, -, hlog⟩ := exists_isNormalDomain_ball_norm_mfderiv_bounds (I := I) p
    (by exact_mod_cast hc)
  have hsub : Metric.ball (0 : TangentSpace I p) (R / 3) ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball (by linarith)
  refine ⟨R / 3, by positivity, hn.ball hsub (by positivity), ?_⟩
  rintro ⟨v, hv⟩ ⟨w, hw⟩
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hc).ne'
  -- It suffices to bound `c⁻¹ * edist v w` by the length of every path from `exp v` to `exp w`.
  suffices h : (c : ℝ≥0∞)⁻¹ * edist v w ≤
      edist (riemannianExp I M p v) (riemannianExp I M p w) by
    calc edist (⟨v, hv⟩ : Metric.ball (0 : TangentSpace I p) (R / 3)) ⟨w, hw⟩
        = c * ((c : ℝ≥0∞)⁻¹ * edist v w) :=
          (ENNReal.mul_inv_cancel_left hc0 ENNReal.coe_ne_top).symm
      _ ≤ c * edist (riemannianExp I M p v) (riemannianExp I M p w) := by gcongr
  rw [IsRiemannianManifold.out (I := I) (riemannianExp I M p v)]
  refine le_riemannianEDist_of_forall_le_pathELength fun γ hγ0 hγ1 hγ ↦ ?_
  suffices h : edist v w ≤ c * pathELength I γ 0 1 by
    calc (c : ℝ≥0∞)⁻¹ * edist v w ≤ (c : ℝ≥0∞)⁻¹ * (c * pathELength I γ 0 1) := by gcongr
      _ = pathELength I γ 0 1 := ENNReal.inv_mul_cancel_left hc0 ENNReal.coe_ne_top
  by_cases hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ riemannianExp I M p '' Metric.ball 0 R
  · -- The path stays in the normal neighbourhood: its logarithm joins `v` to `w`, and the
    -- logarithm stretches tangent vectors by at most `c`.
    have hle := enorm_sub_le_mul_pathELength (f := riemannianLog I M p (Metric.ball 0 R))
      zero_le_one (hγ.mdifferentiableOn one_ne_zero)
      ((hn.contMDiffOn_riemannianLog.of_le (by simp)).comp hγ fun t ht ↦ hγU t ht)
      (fun t ht ↦ hn.mdifferentiableAt_riemannianLog (hγU t ht)) (C := c) fun t ht ↦ by
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal ((hlog _ (hγU t ht) _).2)
    rwa [hγ0, hγ1, hn.riemannianLog_riemannianExp (hsub hw),
      hn.riemannianLog_riemannianExp (hsub hv), ← eDist_eq_eNorm_sub, edist_comm] at hle
  · -- The path leaves the normal neighbourhood, the open ball of radius `R` about `p`, so it is
    -- longer than `2 R / 3`, while `v` and `w` are closer than that.
    push Not at hγU
    obtain ⟨t, ht, hγt⟩ := hγU
    have hvR : ‖v‖ₑ ≤ ENNReal.ofReal (R / 3) := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (mem_ball_zero_iff.1 hv).le
    have hlen : ENNReal.ofReal R ≤ ENNReal.ofReal (R / 3) + pathELength I γ 0 1 :=
      (hn.ofReal_le_enorm_add_pathELength (hsub hv) hγ hγ0 ht hγt).trans (by gcongr)
    have hR3 : ENNReal.ofReal R = ENNReal.ofReal (R / 3) + ENNReal.ofReal (2 * R / 3) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      ring_nf
    rw [hR3, ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top] at hlen
    have hvw : edist v w ≤ ENNReal.ofReal (2 * R / 3) := by
      rw [edist_dist]
      refine ENNReal.ofReal_le_ofReal ((dist_triangle v 0 w).trans ?_)
      rw [dist_zero_right, dist_zero_left]
      linarith [mem_ball_zero_iff.1 hv, mem_ball_zero_iff.1 hw]
    exact (hvw.trans hlen).trans
      (le_mul_of_one_le_left zero_le (by exact_mod_cast hc.le))

end EMetric

section Metric

variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- On a sufficiently small normal ball the exponential map distorts distances by at most a
prescribed factor `c > 1`, in both directions. Distances on the target are its intrinsic
Riemannian distances. -/
theorem exists_isNormalDomain_ball_dist_riemannianExp_le (p : M) {c : ℝ} (hc : 1 < c) :
    ∃ r > 0, IsNormalDomain I M p (Metric.ball 0 r) ∧
      ∀ v ∈ Metric.ball (0 : TangentSpace I p) r, ∀ w ∈ Metric.ball (0 : TangentSpace I p) r,
        dist (riemannianExp I M p v) (riemannianExp I M p w) ≤ c * dist v w ∧
        dist v w ≤ c * dist (riemannianExp I M p v) (riemannianExp I M p w) := by
  have hc' : 1 < c.toNNReal := by simpa using hc
  obtain ⟨r₁, hr₁, hn₁, hlip⟩ :=
    exists_isNormalDomain_ball_lipschitzOnWith_riemannianExp (I := I) p hc'
  obtain ⟨r₂, hr₂, -, hanti⟩ :=
    exists_isNormalDomain_ball_antilipschitzWith_riemannianExp (I := I) p hc'
  have hcc : (c.toNNReal : ℝ) = c := Real.coe_toNNReal c (zero_le_one.trans hc.le)
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂,
    hn₁.ball (Metric.ball_subset_ball (min_le_left _ _)) (lt_min hr₁ hr₂), fun v hv w hw ↦ ?_⟩
  have h₁ : Metric.ball (0 : TangentSpace I p) (min r₁ r₂) ⊆ Metric.ball 0 r₁ :=
    Metric.ball_subset_ball (min_le_left r₁ r₂)
  have h₂ : Metric.ball (0 : TangentSpace I p) (min r₁ r₂) ⊆ Metric.ball 0 r₂ :=
    Metric.ball_subset_ball (min_le_right r₁ r₂)
  constructor
  · simpa [hcc] using hlip.dist_le_mul v (h₁ hv) w (h₁ hw)
  · simpa [hcc, Subtype.dist_eq] using hanti.le_mul_dist ⟨v, h₂ hv⟩ ⟨w, h₂ hw⟩

end Metric

end TauCeti.Manifold
