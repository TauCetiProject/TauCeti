/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.InjectivityRadius.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.InjectivityRadius.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Conjugate.ConstantCurvature
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Geodesic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Radius
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.Comparison

/-!
# The injectivity radius of the round sphere

This file computes the pointwise and global injectivity radius of the round unit `n`-sphere
`sphere (0 : E) 1` (`finrank ℝ E = n + 1`), its rescaled version of radius `r > 0`
(`sphereRoundMetricOfRadius r hr`), and the antipodal sharpness phenomena at distance `π`:

* `n = 0`: `inj(p) = inj(S⁰) = ⊤` (`injectivityRadiusAt_eq_top_of_subsingleton`,
  `injectivityRadius_eq_top_of_subsingleton`).
* Every `n : ℕ`: `Metric.ball 0 Real.pi` is a normal domain (`isNormalDomain_ball_sphere_pi`) via
  constant sectional curvature `1` and the explicit formula for `exp_p`.
* `1 ≤ n`: antipodal collision at norm `π` yields `inj(p) = inj(Sⁿ) = ENNReal.ofReal Real.pi`
  (`injectivityRadiusAt_sphere_of_one_le`, `injectivityRadius_sphere_of_one_le`), and rescaling to
  radius `r > 0` yields `ENNReal.ofReal (r * Real.pi)`
  (`injectivityRadiusAt_withMetric_sphereRoundMetricOfRadius`,
  `injectivityRadius_withMetric_sphereRoundMetricOfRadius`,
  `injectivityRadiusAt_sphereRoundMetricOfRadius`, `injectivityRadius_sphereRoundMetricOfRadius`).
* Antipodal sharpness (`1 ≤ n`): conjugate multiplicity `n - 1` at `t = 1`
  (`conjugateMultiplicity_sphere_of_norm_eq_pi`), `riemannianEDist (𝓡 n) p (-p) = ENNReal.ofReal π`
  (`riemannianEDist_sphere_neg_self`), and two distinct minimizing geodesics from `p` to `-p`
  (`exists_two_minimizing_geodesics_sphere_antipode`).

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 2nd ed., World Scientific (2007),
  Definition 4.1.23 and Example 4.1.25, pp. 151–152.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapters 6
  and 10.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser (1992), Chapters 5 and 13.
-/

public section

open Bundle CovariantDerivative Function Manifold Metric Module Set TauCeti.Manifold
open scoped ContDiff ENNReal InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-! ### Normal tangent ball of radius `π` -/

/-- `riemannianExp` at `p : Sⁿ` is injective on the open tangent ball of radius `π`. -/
theorem injOn_riemannianExp_sphere_ball_pi (p : sphere (0 : E) 1) :
    InjOn (riemannianExp (𝓡 n) (sphere (0 : E) 1) p) (Metric.ball 0 Real.pi) := by
  intro v hv w hw heq; rw [mem_ball_zero_iff] at hv hw
  have hnorm : ‖v‖ = ‖w‖ := by
    rw [← Real.arccos_cos (norm_nonneg v) hv.le, ← Real.arccos_cos (norm_nonneg w) hw.le,
      ← inner_coe_riemannianExp_sphere p v, ← inner_coe_riemannianExp_sphere p w, heq]
  rcases eq_or_ne v 0 with rfl | hv0
  · exact (norm_eq_zero.1 (by simpa only [norm_zero] using hnorm.symm)).symm
  · have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    have hcoe := congrArg Subtype.val heq
    simp only [coe_riemannianExp_sphere, ← hnorm] at hcoe
    exact injective_mvfderiv_subtypeVal_sphere p (smul_right_injective E
      (div_ne_zero (Real.sin_pos_of_pos_of_lt_pi hpos hv).ne' hpos.ne') (add_left_cancel hcoe))

/-- For every `n : ℕ` and `p : Sⁿ`, the open tangent ball `Metric.ball 0 Real.pi` is a normal
domain at `p`. -/
theorem isNormalDomain_ball_sphere_pi (p : sphere (0 : E) 1) :
    IsNormalDomain (𝓡 n) (sphere (0 : E) 1) p (Metric.ball 0 Real.pi) :=
  isNormalDomain_ball_of_sectionalCurvature_le Real.pi_pos (fun _ ↦ by simp) (by simp)
    (injOn_riemannianExp_sphere_ball_pi p) fun _ _ _ _ u huv ↦
    (hasConstantSectionalCurvature_sphere.hasSectionalCurvatureAt _).sectionalCurvature_eq _ _
      huv |>.le

/-- The differential of `riemannianExp` at `p : Sⁿ` is injective at every `v` with `‖v‖ < π`. -/
theorem injective_mfderiv_riemannianExp_sphere_of_norm_lt_pi {p : sphere (0 : E) 1}
    {v : TangentSpace (𝓡 n) p} (hv : ‖v‖ < Real.pi) :
    Function.Injective (mfderiv 𝓘(ℝ, TangentSpace (𝓡 n) p) (𝓡 n)
      (riemannianExp (𝓡 n) (sphere (0 : E) 1) p) v) :=
  (isNormalDomain_ball_sphere_pi p).injective_mfderiv_riemannianExp (mem_ball_zero_iff.2 hv)

/-- `riemannianExp` at `p : Sⁿ` is a smooth local diffeomorphism at every `v` with `‖v‖ < π`. -/
theorem isLocalDiffeomorphAt_riemannianExp_sphere_of_norm_lt_pi {p : sphere (0 : E) 1}
    {v : TangentSpace (𝓡 n) p} (hv : ‖v‖ < Real.pi) :
    IsLocalDiffeomorphAt 𝓘(ℝ, TangentSpace (𝓡 n) p) (𝓡 n) ∞
      (riemannianExp (𝓡 n) (sphere (0 : E) 1) p) v :=
  (isNormalDomain_ball_sphere_pi p).isLocalDiffeomorphOn ⟨v, mem_ball_zero_iff.2 hv⟩

/-- At every point of `Sⁿ` (for all `n : ℕ`, including `n = 0`), the injectivity radius is at least
`ENNReal.ofReal Real.pi`. -/
theorem ofReal_pi_le_injectivityRadiusAt_sphere (p : sphere (0 : E) 1) :
    ENNReal.ofReal Real.pi ≤ injectivityRadiusAt (𝓡 n) (sphere (0 : E) 1) p :=
  (isNormalDomain_ball_sphere_pi p).ofReal_le_injectivityRadiusAt

/-! ### Exact injectivity radius for `1 ≤ n` and rescaled spheres -/

/-- When `1 ≤ n`, every tangent space of `Sⁿ` contains a vector of norm `π` distinct from its
negation. -/
private theorem exists_norm_eq_pi_tangentSpace_sphere (hn : 1 ≤ n) (p : sphere (0 : E) 1) :
    ∃ v : TangentSpace (𝓡 n) p, ‖v‖ = Real.pi ∧ v ≠ -v := by
  have : Nontrivial (TangentSpace (𝓡 n) p) := Module.nontrivial_of_finrank_pos (R := ℝ) <| by
    rw [(tangentSpaceCastModel (𝓡 n) p).toLinearEquiv.finrank_eq, finrank_euclideanSpace_fin]; omega
  obtain ⟨v, hv⟩ := exists_norm_eq (TangentSpace (𝓡 n) p) Real.pi_pos.le
  refine ⟨v, hv, fun h ↦ Real.pi_pos.ne ?_⟩
  simpa [(smul_eq_zero.1 (two_smul ℝ v ▸ add_eq_zero_iff_eq_neg.2 h)).resolve_left two_ne_zero]
    using hv

/-- **Pointwise injectivity radius of the round unit `n`-sphere (`1 ≤ n`).** -/
@[simp] theorem injectivityRadiusAt_sphere_of_one_le (hn : 1 ≤ n) (p : sphere (0 : E) 1) :
    injectivityRadiusAt (𝓡 n) (sphere (0 : E) 1) p = ENNReal.ofReal Real.pi := by
  refine le_antisymm ?_ (ofReal_pi_le_injectivityRadiusAt_sphere p)
  obtain ⟨v, hv, hne⟩ := exists_norm_eq_pi_tangentSpace_sphere hn p
  simpa only [← ofReal_norm, hv] using injectivityRadiusAt_le_of_riemannianExp_eq_of_enorm_le hne
    (by rw [← ofReal_norm, ← ofReal_norm, norm_neg]) (by
      rw [riemannianExp_sphere_eq_neg_of_norm_eq_pi hv,
        riemannianExp_sphere_eq_neg_of_norm_eq_pi (by rwa [norm_neg])])

/-- **Global injectivity radius of the round unit `n`-sphere (`1 ≤ n`).** -/
@[simp] theorem injectivityRadius_sphere_of_one_le (hn : 1 ≤ n) :
    injectivityRadius (𝓡 n) (sphere (0 : E) 1) = ENNReal.ofReal Real.pi := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E = n + 1)
  have : Nonempty (sphere (0 : E) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  simp [injectivityRadius_def, injectivityRadiusAt_sphere_of_one_le hn]

/-- **Pointwise injectivity radius of the round `n`-sphere of radius `r > 0` (`WithMetric` form,
`1 ≤ n`).** -/
@[simp] theorem injectivityRadiusAt_withMetric_sphereRoundMetricOfRadius (hn : 1 ≤ n) {r : ℝ}
    (hr : 0 < r) (p : sphere (0 : E) 1) :
    injectivityRadiusAt (𝓡 n) (WithMetric (sphereRoundMetricOfRadius (E := E) (n := n) r hr))
        (WithMetric.toWithMetric _ p) = ENNReal.ofReal (r * Real.pi) := by
  rw [sphereRoundMetricOfRadius_def hr,
    WithMetric.injectivityRadiusAt_rescale_const _ (pow_pos hr 2) p,
    WithMetric.injectivityRadiusAt_toWithMetric _ (fun _ _ _ ↦ by simp) p,
    injectivityRadiusAt_sphere_of_one_le hn p, Real.sqrt_sq hr.le, ← ENNReal.ofReal_mul hr.le]

/-- **Global injectivity radius of the round `n`-sphere of radius `r > 0` (`WithMetric` form,
`1 ≤ n`).** -/
@[simp] theorem injectivityRadius_withMetric_sphereRoundMetricOfRadius (hn : 1 ≤ n) {r : ℝ}
    (hr : 0 < r) :
    injectivityRadius (𝓡 n) (WithMetric (sphereRoundMetricOfRadius (E := E) (n := n) r hr)) =
      ENNReal.ofReal (r * Real.pi) := by
  rw [sphereRoundMetricOfRadius_def hr,
    WithMetric.injectivityRadius_rescale_const _ (pow_pos hr 2),
    WithMetric.injectivityRadius_eq _ (fun _ _ _ ↦ by simp),
    injectivityRadius_sphere_of_one_le hn, Real.sqrt_sq hr.le, ← ENNReal.ofReal_mul hr.le]

/-- **Pointwise injectivity radius of the round `n`-sphere of radius `r > 0` (`letI` form,
`1 ≤ n`).** -/
theorem injectivityRadiusAt_sphereRoundMetricOfRadius (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r)
    (p : sphere (0 : E) 1) :
    (letI : RiemannianBundle (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
        ⟨(sphereRoundMetricOfRadius r hr).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
          (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
        Bundle.instIsContMDiffRiemannianBundle _;
      injectivityRadiusAt (𝓡 n) (sphere (0 : E) 1) p) = ENNReal.ofReal (r * Real.pi) := by
  rw [Bundle.ContMDiffRiemannianMetric.injectivityRadiusAt_eq_withMetric
      (sphereRoundMetricOfRadius r hr) p,
    injectivityRadiusAt_withMetric_sphereRoundMetricOfRadius hn hr p]

/-- **Global injectivity radius of the round `n`-sphere of radius `r > 0` (`letI` form,
`1 ≤ n`).** -/
theorem injectivityRadius_sphereRoundMetricOfRadius (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    (letI : RiemannianBundle (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
        ⟨(sphereRoundMetricOfRadius r hr).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
          (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
        Bundle.instIsContMDiffRiemannianBundle _;
      injectivityRadius (𝓡 n) (sphere (0 : E) 1)) = ENNReal.ofReal (r * Real.pi) := by
  rw [Bundle.ContMDiffRiemannianMetric.injectivityRadius_eq_withMetric
      (sphereRoundMetricOfRadius r hr),
    injectivityRadius_withMetric_sphereRoundMetricOfRadius hn hr]

/-! ### Antipodal conjugate multiplicity and non-uniqueness of minimizing geodesics -/

/-- Along any radial geodesic `t ↦ exp_p (t • v)` on `Sⁿ` with `‖v‖ = π`, the antipodal parameter
`1` has conjugate multiplicity `n - 1` (`0` on `S¹`, and `n - 1 > 0` for `2 ≤ n`). -/
theorem conjugateMultiplicity_sphere_of_norm_eq_pi {p : sphere (0 : E) 1}
    {v : TangentSpace (𝓡 n) p} (hv : ‖v‖ = Real.pi) :
    conjugateMultiplicity (isGeodesicCurveOn_riemannianExp_smul_sphere_univ p v)
      isPreconnected_univ (mem_univ (0 : ℝ)) (1 : ℝ) = n - 1 := by
  have hvel : ‖curveVelocityWithin (𝓡 n)
      (fun t : ℝ ↦ riemannianExp (𝓡 n) (sphere (0 : E) 1) p (t • v)) univ 0‖ = Real.pi := by
    rw [curveVelocityWithin_univ, curveVelocity_riemannianExp_smul_zero]
    rw [zero_smul, riemannianExp_zero, hv]
  have hS : curvatureSine ((1 : ℝ) * ‖curveVelocityWithin (𝓡 n)
      (fun t : ℝ ↦ riemannianExp (𝓡 n) (sphere (0 : E) 1) p (t • v)) univ 0‖ ^ 2) 1 = 0 := by
    rw [hvel, one_mul, curvatureSine_of_pos (sq_pos_of_pos Real.pi_pos)]
    simp [Real.sqrt_sq Real.pi_pos.le]
  simpa only [finrank_euclideanSpace_fin] using
    conjugateMultiplicity_eq_finrank_sub_one_of_curvatureSine_eq_zero
      (hγ := isGeodesicCurveOn_riemannianExp_smul_sphere_univ p v) isPreconnected_univ (by simp)
      (mem_univ 0) (mem_univ 1) one_ne_zero
      (fun _ _ ↦ hasConstantSectionalCurvature_sphere.hasSectionalCurvatureAt _) hS

/-- For any `w : TangentSpace (𝓡 n) p` with `‖w‖ = π`, the radial curve `t ↦ exp_p (t • w)` is a
geodesic on `[0, 1]` from `p` to `-p` of length `ENNReal.ofReal Real.pi`. -/
private theorem isGeodesicCurveOn_riemannianExp_smul_sphere_Icc_of_norm_eq_pi
    {p : sphere (0 : E) 1} {w : TangentSpace (𝓡 n) p} (hw : ‖w‖ = Real.pi) :
    let γ := fun t : ℝ ↦ riemannianExp (𝓡 n) (sphere (0 : E) 1) p (t • w)
    IsGeodesicCurveOn (𝓡 n) γ (Icc 0 1) ∧ γ 0 = p ∧ γ 1 = -p ∧
      pathELength (𝓡 n) γ 0 1 = ENNReal.ofReal Real.pi :=
  ⟨(isGeodesicCurveOn_riemannianExp_smul_sphere_univ p w).mono (uniqueDiffOn_Icc zero_lt_one)
      (subset_univ _),
    by simp,
    by simpa only [one_smul] using riemannianExp_sphere_eq_neg_of_norm_eq_pi hw,
    by rw [pathELength_riemannianExp_smul_sphere_zero_one, ← ofReal_norm, hw]⟩

/-- **Antipodal Riemannian distance on `Sⁿ` (`1 ≤ n`).** The Riemannian distance between `p : Sⁿ`
and its antipode `-p` is `ENNReal.ofReal Real.pi` (equal to `injectivityRadiusAt p`). -/
@[simp] theorem riemannianEDist_sphere_neg_self (hn : 1 ≤ n) (p : sphere (0 : E) 1) :
    riemannianEDist (𝓡 n) p (-p) = ENNReal.ofReal Real.pi := by
  refine le_antisymm ?_ ?_
  · obtain ⟨v, hv, -⟩ := exists_norm_eq_pi_tangentSpace_sphere hn p
    obtain ⟨hgeo, h0, h1, hlen⟩ :=
      isGeodesicCurveOn_riemannianExp_smul_sphere_Icc_of_norm_eq_pi hv
    exact (riemannianEDist_le_pathELength (hgeo.contMDiffOn.of_le one_le_two) h0 h1
      zero_le_one).trans_eq hlen
  · by_contra! hlt; obtain ⟨v, ⟨hv_lt_inj, hv_exp⟩, -⟩ :=
      existsUnique_riemannianExp_eq_of_riemannianEDist_lt_injectivityRadiusAt
        (by rwa [injectivityRadiusAt_sphere_of_one_le hn p])
    have hv_lt : ‖v‖ < Real.pi := by
      rwa [← ofReal_norm, injectivityRadiusAt_sphere_of_one_le hn p,
        ENNReal.ofReal_lt_ofReal_iff Real.pi_pos] at hv_lt_inj
    have hcos := (inner_coe_riemannianExp_sphere p v).symm
    rw [hv_exp, coe_neg_sphere, inner_neg_right, real_inner_self_eq_norm_sq,
      mem_sphere_zero_iff_norm.1 p.property, one_pow] at hcos
    linarith [Real.cos_pi ▸ Real.strictAntiOn_cos ⟨norm_nonneg v, hv_lt.le⟩
      ⟨Real.pi_pos.le, le_rfl⟩ hv_lt]

/-- **Sharpness at the injectivity radius on `Sⁿ` (`1 ≤ n`).** At distance `π = inj(p)` from
`p : Sⁿ`, the antipode `-p` is joined to `p` by two distinct minimizing geodesics on `[0, 1]`
(disagreeing at their midpoint `t = 1 / 2`). -/
theorem exists_two_minimizing_geodesics_sphere_antipode (hn : 1 ≤ n) (p : sphere (0 : E) 1) :
    ∃ γ₁ γ₂ : ℝ → sphere (0 : E) 1,
      γ₁ (1 / 2) ≠ γ₂ (1 / 2) ∧
      IsGeodesicCurveOn (𝓡 n) γ₁ (Icc 0 1) ∧ γ₁ 0 = p ∧ γ₁ 1 = -p ∧
      pathELength (𝓡 n) γ₁ 0 1 = riemannianEDist (𝓡 n) p (-p) ∧
      IsGeodesicCurveOn (𝓡 n) γ₂ (Icc 0 1) ∧ γ₂ 0 = p ∧ γ₂ 1 = -p ∧
      pathELength (𝓡 n) γ₂ 0 1 = riemannianEDist (𝓡 n) p (-p) := by
  obtain ⟨v, hv, hne⟩ := exists_norm_eq_pi_tangentSpace_sphere hn p
  have hdist := riemannianEDist_sphere_neg_self hn p
  obtain ⟨h1a, h1b, h1c, h1d⟩ := isGeodesicCurveOn_riemannianExp_smul_sphere_Icc_of_norm_eq_pi hv
  obtain ⟨h2a, h2b, h2c, h2d⟩ :=
    isGeodesicCurveOn_riemannianExp_smul_sphere_Icc_of_norm_eq_pi (w := -v) (by rwa [norm_neg])
  have hball {w : TangentSpace (𝓡 n) p} (hw : ‖w‖ = Real.pi) :
      (1 / 2 : ℝ) • w ∈ Metric.ball 0 Real.pi := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (by norm_num), hw]; linarith [Real.pi_pos]
  exact ⟨_, _, fun hmid ↦ hne <| smul_right_injective _ (by norm_num : (1 / 2 : ℝ) ≠ 0) <|
    injOn_riemannianExp_sphere_ball_pi p (hball hv) (hball (by rwa [norm_neg])) hmid,
    h1a, h1b, h1c, h1d.trans hdist.symm, h2a, h2b, h2c, h2d.trans hdist.symm⟩

end TauCeti

end
