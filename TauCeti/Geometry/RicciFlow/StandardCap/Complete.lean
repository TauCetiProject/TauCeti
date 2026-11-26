/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Distance
public import TauCeti.Geometry.RicciFlow.StandardCap.Metric
import TauCeti.Geometry.Manifold.Riemannian.MetricBridge
import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Curve

/-!
# Completeness of the standard cap metric

The standard cap metric `dr² + f(r)² g_(Sⁿ)` on a finite-dimensional real inner product space `V`
is complete. The radial direction has unit length, and every other direction is at least as long
as its radial component (`TauCeti.IsStandardCapProfile.metric_inner_smul_self` and
`TauCeti.IsStandardCapProfile.sq_inner_le_sq_norm_mul_metric_inner`). Hence the norm `‖x‖` is
`1`-Lipschitz for the Riemannian distance of the cap, and it is exactly the distance from the tip:
the rays `t ↦ t x` from the tip are minimizing. Bounded sets for the cap distance are therefore
bounded in `V`, hence relatively compact, so Cauchy sequences converge, and every maximal geodesic
of the standard cap is defined for all time.

The norm is not differentiable at the tip, so the Lipschitz bound is first proved for the smooth
functions `√(ε² + ‖x‖²)` with `ε > 0`, whose differentials have cap norm at most one, and then
passed to the limit `ε → 0`.

The cap metric lives on the copy `TauCeti.WithMetric (hf.metric V)` of `V`, which carries it as
its Riemannian metric; the space `V` itself keeps its Euclidean metric.

## Main results

* `TauCeti.IsStandardCapProfile.edist_norm_le_riemannianEDist`,
  `TauCeti.IsStandardCapProfile.riemannianEDist_toWithMetric_le`: the norm is `1`-Lipschitz for the
  cap distance, and `toWithMetric` is `1`-Lipschitz from the Euclidean distance.
* `TauCeti.IsStandardCapProfile.riemannianEDist_zero_left`: the cap distance from the tip is the
  norm.
* `TauCeti.IsStandardCapProfile.completeSpace_withMetric`: the standard cap is complete for its
  Riemannian distance.
* `TauCeti.IsStandardCapProfile.isGeodesicallyCompleteAt_withMetric`: every maximal geodesic of
  the standard cap is defined for all time.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics
  Monographs 3 (2007), Definition 12.1.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §2, Thm. 2.8.
-/

public noncomputable section

open Bundle Filter Manifold Set TauCeti.Manifold TauCeti.WithMetric
open scoped ContDiff ENNReal Manifold InnerProductSpace NNReal Topology

namespace TauCeti.IsStandardCapProfile

variable {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
include hf

variable [FiniteDimensional ℝ V]

/-! ### The cap distance and the norm -/

/-- For `ε > 0`, the smooth function `√(ε² + ‖x‖²)` is `1`-Lipschitz for the cap distance. -/
private theorem edist_sqrt_le_riemannianEDist {ε : ℝ} (hε : 0 < ε) (x y : V) :
    edist √(ε ^ 2 + ‖x‖ ^ 2) √(ε ^ 2 + ‖y‖ ^ 2) ≤
      riemannianEDist 𝓘(ℝ, V) (toWithMetric (hf.metric V) x)
        (toWithMetric (hf.metric V) y) := by
  set φ : V → ℝ := fun z ↦ √(ε ^ 2 + ‖z‖ ^ 2)
  have hpos (z : V) : 0 < ε ^ 2 + ‖z‖ ^ 2 := by positivity
  have hφ (z : V) : HasFDerivAt φ ((1 / (2 * φ z)) • (2 • innerSL ℝ z)) z :=
    ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add (ε ^ 2)).sqrt (hpos z).ne'
  have hφd : ContDiff ℝ 1 φ :=
    (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt fun z ↦ (hpos z).ne'
  -- The differential `⟪z, w⟫ / φ z` has absolute value at most the cap length of `w`.
  have hbound (z : V) (w : TangentSpace 𝓘(ℝ, V) z) :
      |fderiv ℝ φ z (NormedSpace.fromTangentSpace z w)| ≤ √((hf.metric V).inner z w w) := by
    have hφz : 0 < φ z := Real.sqrt_pos.2 (hpos z)
    have hg : 0 ≤ (hf.metric V).inner z w w := by
      rcases eq_or_ne w 0 with rfl | hw
      · simp
      · exact ((hf.metric V).pos z w hw).le
    have h1 := hf.sq_inner_le_sq_norm_mul_metric_inner z w
    simp only [(hφ z).fderiv, smul_apply, innerSL_apply_apply, nsmul_eq_mul, smul_eq_mul,
      Nat.cast_ofNat]
    set c := ⟪z, NormedSpace.fromTangentSpace z w⟫_ℝ
    have hφsq : φ z ^ 2 = ε ^ 2 + ‖z‖ ^ 2 := Real.sq_sqrt (hpos z).le
    have hc : 1 / (2 * φ z) * (2 * c) = c / φ z := by field_simp
    rw [hc, abs_div, abs_of_pos hφz, div_le_iff₀ hφz]
    -- Compare squares: `c² ≤ ‖z‖² g ≤ (ε² + ‖z‖²) g = (φ z)² g`.
    have hsq : |c| ^ 2 ≤ (√((hf.metric V).inner z w w) * φ z) ^ 2 := by
      rw [sq_abs, mul_pow, Real.sq_sqrt hg, hφsq]
      nlinarith [mul_nonneg (sq_nonneg ε) hg]
    exact (pow_le_pow_iff_left₀ (abs_nonneg c) (by positivity) two_ne_zero).1 hsq
  have hle := edist_le_mul_riemannianEDist (I := 𝓘(ℝ, V)) (f := φ ∘ ofWithMetric)
    (hφd.contMDiff.comp contMDiff_ofWithMetric) one_ne_zero
    (fun z v ↦ by
      rw [ENNReal.coe_one, one_mul, ← ofReal_norm, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      simpa only [mvfderiv_comp_ofWithMetric_apply, mvfderiv_eq_fderiv,
        ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Real.norm_eq_abs,
        norm_eq_sqrt_real_inner v, inner_def] using hbound _ _)
    (toWithMetric (hf.metric V) x) (toWithMetric (hf.metric V) y)
  simpa only [Function.comp_apply, ofWithMetric_toWithMetric, ENNReal.coe_one, one_mul] using hle

/-- **The norm is `1`-Lipschitz for the cap distance**: the norms of two points of the standard
cap differ by at most their Riemannian distance. -/
theorem edist_norm_le_riemannianEDist (x y : V) :
    edist ‖x‖ ‖y‖ ≤
      riemannianEDist 𝓘(ℝ, V) (toWithMetric (hf.metric V) x)
        (toWithMetric (hf.metric V) y) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  have hδ : (0 : ℝ) < ε / 2 := by positivity
  -- `√((ε/2)² + r²)` is within `ε / 2` of `r ≥ 0`.
  have happrox (r : ℝ) (hr : 0 ≤ r) : r ≤ √((ε / 2 : ℝ) ^ 2 + r ^ 2) ∧
      √((ε / 2 : ℝ) ^ 2 + r ^ 2) ≤ r + ε / 2 := by
    constructor
    · exact Real.le_sqrt_of_sq_le (by nlinarith)
    · exact Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  have hx := happrox ‖x‖ (norm_nonneg x)
  have hy := happrox ‖y‖ (norm_nonneg y)
  have hreal : |‖x‖ - ‖y‖| ≤
      |√((ε / 2 : ℝ) ^ 2 + ‖x‖ ^ 2) - √((ε / 2 : ℝ) ^ 2 + ‖y‖ ^ 2)| + ε := by
    rw [abs_le]
    constructor <;> cases abs_cases (√((ε / 2 : ℝ) ^ 2 + ‖x‖ ^ 2) -
      √((ε / 2 : ℝ) ^ 2 + ‖y‖ ^ 2)) <;> linarith
  calc edist ‖x‖ ‖y‖ = ENNReal.ofReal |‖x‖ - ‖y‖| := by
        rw [edist_dist, Real.dist_eq]
    _ ≤ ENNReal.ofReal (|√((ε / 2 : ℝ) ^ 2 + ‖x‖ ^ 2) - √((ε / 2 : ℝ) ^ 2 + ‖y‖ ^ 2)| + ε) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = edist √((ε / 2 : ℝ) ^ 2 + ‖x‖ ^ 2) √((ε / 2 : ℝ) ^ 2 + ‖y‖ ^ 2) + ε := by
        rw [ENNReal.ofReal_add (abs_nonneg _) ε.coe_nonneg, edist_dist, Real.dist_eq,
          ENNReal.ofReal_coe_nnreal]
    _ ≤ _ := by
        gcongr
        exact hf.edist_sqrt_le_riemannianEDist hδ x y

/-- **The map `toWithMetric` is `1`-Lipschitz**: because `g_x(v, v) ≤ ‖v‖²` everywhere, the
Riemannian distance on the standard cap is at most the Euclidean distance on `V`. -/
theorem riemannianEDist_toWithMetric_le (x y : V) :
    riemannianEDist 𝓘(ℝ, V) (toWithMetric (hf.metric V) x)
      (toWithMetric (hf.metric V) y) ≤ edist x y := by
  rw [IsRiemannianManifold.out (I := 𝓘(ℝ, V)) x y,
    ← one_mul (riemannianEDist 𝓘(ℝ, V) x y), ← ENNReal.coe_one]
  refine TauCeti.Manifold.riemannianEDist_le_mul (C := (1 : NNReal))
    contMDiff_toWithMetric one_ne_zero (fun z v ↦ ?_) x y
  rw [NNReal.coe_one, one_mul]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [← real_inner_self_eq_norm_sq, inner_def, ofWithMetric_toWithMetric,
    mfderiv_ofWithMetric_mfderiv_toWithMetric, norm_tangentSpace_vectorSpace]
  exact hf.metric_inner_self_le z v

/-- **The cap distance from the tip is the norm**: the ray `t ↦ t x`, `0 ≤ t ≤ 1`, from the tip
to `x` has cap length `‖x‖`, and by `edist_norm_le_riemannianEDist` no curve is shorter. -/
theorem riemannianEDist_zero_left (x : V) :
    riemannianEDist 𝓘(ℝ, V) (toWithMetric (hf.metric V) 0) (toWithMetric (hf.metric V) x) =
      ‖x‖ₑ := by
  refine le_antisymm ?_ ?_
  · set γ : ℝ → V := fun t ↦ t • x
    have hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, V) 1 (toWithMetric (hf.metric V) ∘ γ) :=
      contMDiff_toWithMetric.comp (contDiff_id.smul contDiff_const).contMDiff
    refine (riemannianEDist_le_pathELength hγ.contMDiffOn (by simp [γ]) (by simp [γ])
      zero_le_one).trans_eq ?_
    rw [hγ.contMDiffOn.pathELength_eq_ofReal_integral_norm_curveVelocityWithin (subset_univ _)]
    -- The ray has constant cap speed `‖x‖`.
    have hspeed (t : ℝ) :
        ‖curveVelocityWithin 𝓘(ℝ, V) (toWithMetric (hf.metric V) ∘ γ) univ t‖ = ‖x‖ := by
      have hd : deriv γ t = x := by
        rw [deriv_smul_const differentiableAt_id, deriv_id'', one_smul]
      have hv : curveVelocity 𝓘(ℝ, V) γ t = (NormedSpace.fromTangentSpace (γ t)).symm x := by
        rw [curveVelocity_eq_deriv, NormedSpace.fromTangentSpace_symm_apply]
        exact hd
      rw [curveVelocityWithin_univ, ContMDiffRiemannianMetric.norm_curveVelocity_toWithMetric, hv]
      exact (congrArg Real.sqrt (hf.metric_inner_smul_self t x)).trans
        (Real.sqrt_sq (norm_nonneg x))
    simp only [hspeed, intervalIntegral.integral_const, sub_zero, one_smul, ofReal_norm]
  · simpa [edist_dist, Real.dist_eq, ofReal_norm] using
      hf.edist_norm_le_riemannianEDist 0 x

/-! ### Completeness -/

variable (V) in
/-- **The standard cap is complete** for its Riemannian distance. -/
theorem completeSpace_withMetric :
    letI : EMetricSpace (WithMetric (hf.metric V)) :=
      .ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
    CompleteSpace (WithMetric (hf.metric V)) := by
  let : EMetricSpace (WithMetric (hf.metric V)) :=
    .ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
  refine EMetric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  -- A Cauchy sequence eventually stays in a cap ball, which lies over a compact Euclidean ball.
  obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff'.1 hu 1 one_pos
  set K := toWithMetric (hf.metric V) '' Metric.closedBall (0 : V) (‖(u N).ofWithMetric‖ + 1)
  have hK : IsCompact K := (isCompact_closedBall _ _).image continuous_toWithMetric
  have hmem : ∀ᶠ n in atTop, u n ∈ K := eventually_atTop.2 ⟨N, fun n hn ↦ by
    refine ⟨(u n).ofWithMetric, ?_, toWithMetric_ofWithMetric _ (u n)⟩
    have h := (hf.edist_norm_le_riemannianEDist (u n).ofWithMetric (u N).ofWithMetric).trans_lt
      (by
        simpa only [toWithMetric_ofWithMetric, ← IsRiemannianManifold.out (I := 𝓘(ℝ, V))]
          using hN n hn)
    rw [edist_dist, Real.dist_eq, ENNReal.ofReal_lt_one, abs_lt] at h
    rw [mem_closedBall_zero_iff]
    linarith⟩
  obtain ⟨x, -, hx⟩ := hK.isComplete _ hu (tendsto_principal.2 hmem)
  exact ⟨x, hx⟩

/-- **The standard cap is geodesically complete**: every maximal geodesic of the standard cap
metric is defined for all time. -/
theorem isGeodesicallyCompleteAt_withMetric (p : WithMetric (hf.metric V)) :
    IsGeodesicallyCompleteAt 𝓘(ℝ, V) (WithMetric (hf.metric V)) p := by
  let : EMetricSpace (WithMetric (hf.metric V)) :=
    .ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
  have := hf.completeSpace_withMetric V
  exact isGeodesicallyCompleteAt_of_completeSpace (I := 𝓘(ℝ, V)) p

end TauCeti.IsStandardCapProfile
