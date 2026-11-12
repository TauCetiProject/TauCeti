/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Maximal
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
import TauCeti.Geometry.Manifold.Riemannian.MetricBridge

/-!
# The rate of gradient convergence depends on the metric

A negative gradient trajectory converging to a nondegenerate critical point converges to it
exponentially fast in the Riemannian distance
(`TauCeti.exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient`). The Hessian and
the Morse index at a critical point do not depend on the metric, but the gradient, its
trajectories and the distance do, and so does the rate. This file computes the trajectories of
`f(x) = x²` on `ℝ` for the constant metric `c dx²`, `c > 0` (`TauCeti.scaledLineMetric`).

* **The gradient.** For `c dx²` the gradient of `f` is `2 x / c`
  (`TauCeti.mgradient_sq_scaledLineMetric`), so the trajectory of `-grad f` through `x₀` is
  `t ↦ x₀ exp (-2 t / c)` (`TauCeti.maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric`).
* **The distance.** The Riemannian distance of `c dx²` is `√c |x - y|`
  (`TauCeti.riemannianEDist_scaledLineMetric`): the map `y ↦ √c y` preserves the length of tangent
  vectors, and the segment from `x` to `y` has length `√c |x - y|`.
* **The rate.** Hence the trajectory through `x₀` is at distance exactly `√c |x₀| exp (-2 t / c)`
  from the critical point `0`
  (`TauCeti.riemannianEDist_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric`), and for
  `x₀ ≠ 0` no rate faster than `2 / c` holds
  (`not_exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric`).
  The rate `2 / c` is the eigenvalue of the Hessian `2 dx²` with respect to the metric `c dx²`.
* **The tail length.** After the time `t` the trajectory has length `√c |x₀| exp (-2 t / c)`
  (`TauCeti.iSup_pathELength_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric`), which is
  `√c` times the square root of the energy `f (γ t) - f 0 = x₀² exp (-4 t / c)`. So the constant
  in the bound of the tail length by the square root of the energy
  (`TauCeti.exists_pathELength_le_mul_sqrt_maximalIntegralCurve_neg_mgradient`) depends on the
  metric as well. For the standard metric, `c = 1`, the trajectory is `x₀ exp (-2 t)`, its energy
  `x₀² exp (-4 t)` and its tail length `|x₀| exp (-2 t)`.

For the metric `4 dx²`, the negative gradient is `-x / 2`, the trajectory through `x₀` is
`x₀ exp (-t / 2)` and its distance to `0` is `2 |x₀| exp (-t / 2)`: the rate `2` of the standard
metric `dx²` is not preserved under rescaling the metric, while the critical point and its
Hessian are unchanged.

The metric `c dx²` is the standard metric of `ℝ` rescaled by the constant `c`
(`Bundle.ContMDiffRiemannianMetric.rescale`), so it is smooth and the convergence theorems for
smooth metrics apply to it.

## References

* M. W. Hirsch, S. Smale and R. L. Devaney, *Differential Equations, Dynamical Systems, and an
  Introduction to Chaos*, second edition, Academic Press, 2004, Chapter 9 (gradient systems).
-/

public section

open Bundle Filter MeasureTheory Set Topology TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti

variable {c : ℝ}

/-- **The metric `c dx²` on the line**, for `c > 0`: the inner product of the tangent vectors `v`
and `w` at every point is `c v w`. It is the standard metric of `ℝ` rescaled by the constant `c`,
so it is smooth. -/
noncomputable def scaledLineMetric (hc : 0 < c) :
    ContMDiffRiemannianMetric 𝓘(ℝ, ℝ) ω ℝ (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
  (riemannianMetricVectorSpace ℝ).rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc

/-- The inner products of `scaledLineMetric`: `⟪v, w⟫ₓ = c v w`. -/
@[simp]
theorem scaledLineMetric_inner (hc : 0 < c) (x v w : ℝ) :
    (scaledLineMetric hc).inner x v w = c * (v * w) := by
  have h := Bundle.ContMDiffRiemannianMetric.rescale_inner (riemannianMetricVectorSpace ℝ)
    (fun _ ↦ c) contMDiff_const (fun _ ↦ hc) x v w
  rw [scaledLineMetric, h]
  simp only [riemannianMetricVectorSpace]
  exact congrArg (c * ·) ((innerSL_apply_apply ℝ v w).trans (by simp [mul_comm]))

/-- For the metric `scaledLineMetric`, a tangent vector has length `√c` times its length as a
real number. -/
private theorem enorm_scaledLineMetric (hc : 0 < c) (x : ℝ) (v : TangentSpace 𝓘(ℝ, ℝ) x) :
    let _ : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
      ⟨(scaledLineMetric hc).toRiemannianMetric⟩
    ‖v‖ₑ = ENNReal.ofReal √c * ‖NormedSpace.fromTangentSpace x v‖ₑ := by
  intro _
  have h : ‖v‖ = √c * ‖NormedSpace.fromTangentSpace x v‖ := by
    rw [norm_eq_sqrt_real_inner]
    -- The inner product of the installed metric is `c v v`.
    have h2 : inner ℝ v v =
        c * (NormedSpace.fromTangentSpace x v * NormedSpace.fromTangentSpace x v) :=
      scaledLineMetric_inner hc x v v
    rw [h2, Real.sqrt_mul hc.le, Real.sqrt_mul_self_eq_abs, Real.norm_eq_abs]
  rw [← ofReal_norm, h, ENNReal.ofReal_mul (Real.sqrt_nonneg _), ofReal_norm]

/-- For the metric `scaledLineMetric`, the gradient of `f(x) = x²` is `2 x / c`. -/
theorem mgradient_sq_scaledLineMetric (hc : 0 < c) (x : ℝ) :
    let _ : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
      ⟨(scaledLineMetric hc).toRiemannianMetric⟩
    mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2) x = (2 / c * x : ℝ) := by
  intro _
  have h := inner_mgradient_model_space (fun y : ℝ ↦ y ^ 2) x 1
  obtain ⟨m, hm⟩ : ∃ m : ℝ, mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2) x = m := ⟨_, rfl⟩
  rw [hm] at h ⊢
  have h2 : fderiv ℝ (fun y : ℝ ↦ y ^ 2) x 1 = 2 * x := by simp
  rw [h2] at h
  -- The inner product of the installed metric is `c v w`.
  have h' : (scaledLineMetric hc).inner x m (1 : ℝ) = 2 * x := h
  rw [scaledLineMetric_inner, mul_one] at h'
  field_simp
  linarith

/-- The derivative of `t ↦ a exp (-2 t / c)`. -/
private theorem hasDerivAt_mul_exp_neg_two_div_mul (a c t : ℝ) :
    HasDerivAt (fun t ↦ a * Real.exp (-(2 / c * t))) (a * (Real.exp (-(2 / c * t)) * -(2 / c)))
      t := by
  simpa using (((hasDerivAt_id t).const_mul (2 / c)).neg.exp).const_mul a

/-- For the metric `scaledLineMetric`, the negative gradient of `f(x) = x²` is `-2 x / c`. -/
private theorem neg_mgradient_sq_scaledLineMetric_apply (hc : 0 < c) (x : ℝ) :
    let _ : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
      ⟨(scaledLineMetric hc).toRiemannianMetric⟩
    (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x = (-(2 / c * x) : ℝ) := by
  intro _
  rw [Pi.neg_apply, mgradient_sq_scaledLineMetric]
  -- Both sides are the real number `-(2 / c * x)`, read in `ℝ` and in its tangent space.
  rfl

/-- For the metric `scaledLineMetric`, the curve `t ↦ x₀ exp (-2 t / c)` is a trajectory of
`-grad f`, for `f(x) = x²`, defined for all time: it solves `x' = -2 x / c`. -/
theorem isMIntegralCurve_neg_mgradient_sq_scaledLineMetric (hc : 0 < c) (x₀ : ℝ) :
    let _ : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
      ⟨(scaledLineMetric hc).toRiemannianMetric⟩
    IsMIntegralCurve (fun t ↦ x₀ * Real.exp (-(2 / c * t)))
      (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) := by
  intro _
  rw [isMIntegralCurve_iff_isMIntegralCurveOn, isMIntegralCurveOn_iff_isIntegralCurveOn]
  intro t _
  have e : x₀ * (Real.exp (-(2 / c * t)) * -(2 / c)) =
      -(2 / c * (x₀ * Real.exp (-(2 / c * t)))) := by ring
  exact (hasDerivAt_mul_exp_neg_two_div_mul x₀ c t).hasDerivWithinAt.congr_deriv
    (e.trans (neg_mgradient_sq_scaledLineMetric_apply hc _).symm)

/-- **The trajectories of `-grad x²` for the metric `c dx²`.** The trajectory of `-grad f`, for
`f(x) = x²` and the metric `scaledLineMetric`, through `x₀` is `t ↦ x₀ exp (-2 t / c)`. -/
theorem maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric (hc : 0 < c) (x₀ t : ℝ) :
    let _ : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
      ⟨(scaledLineMetric hc).toRiemannianMetric⟩
    maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀ t =
      x₀ * Real.exp (-(2 / c * t)) := by
  intro _
  have : IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ω ℝ (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
    Bundle.instIsContMDiffRiemannianBundle (scaledLineMetric hc)
  have hb : 0 < |t| + 1 := by positivity
  exact (isMIntegralCurve_neg_mgradient_sq_scaledLineMetric hc x₀).isMIntegralCurveOn
    (Ioo (-(|t| + 1)) (|t| + 1)) |>.eqOn_maximalIntegralCurve
    (contMDiff_neg_mgradient_one (contDiff_id.pow 2).contMDiff) ⟨neg_lt_zero.2 hb, hb⟩
    (by simp) ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

/-- **The distance of the metric `c dx²`.** The Riemannian distance of `scaledLineMetric` between
`x` and `y` is `√c |x - y|`. -/
theorem riemannianEDist_scaledLineMetric (hc : 0 < c) (x y : ℝ) :
    let _ : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
      ⟨(scaledLineMetric hc).toRiemannianMetric⟩
    Manifold.riemannianEDist 𝓘(ℝ, ℝ) x y = ENNReal.ofReal (√c * |x - y|) := by
  intro _
  apply le_antisymm
  · -- The segment from `x` to `y` has length `√c |x - y|`.
    let γ : ℝ → ℝ := fun t ↦ x + t * (y - x)
    have hγ : ContDiff ℝ 1 γ := by fun_prop
    refine (Manifold.riemannianEDist_le_pathELength (I := 𝓘(ℝ, ℝ)) (x := x) (y := y)
      (hγ.contMDiff.contMDiffOn (s := Icc 0 1)) (by simp [γ]) (by simp [γ]) zero_le_one).trans_eq
      ?_
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    have hd (t : ℝ) : ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) γ t 1‖ₑ = ENNReal.ofReal (√c * |x - y|) := by
      rw [enorm_scaledLineMetric hc, mfderiv_eq_fderiv]
      -- The tangent vector `1` at `t` is the real number `1`.
      have h1 : |NormedSpace.fromTangentSpace (𝕜 := ℝ) t 1| = 1 := abs_one
      simp [γ, Real.enorm_eq_ofReal_abs, abs_sub_comm, h1]
    simp_rw [hd]
    simp
  · -- The map `y ↦ √c y` preserves the length of tangent vectors, so it does not increase
    -- distances.
    have h := edist_le_mul_riemannianEDist (I := 𝓘(ℝ, ℝ)) (f := fun y : ℝ ↦ √c * y)
      (contDiff_const.mul contDiff_id).contMDiff one_ne_zero (fun z v ↦ ?_) x y
    · rw [ENNReal.coe_one, one_mul, edist_dist, Real.dist_eq, ← mul_sub, abs_mul,
        abs_of_nonneg (Real.sqrt_nonneg _)] at h
      exact h
    · have hf : fderiv ℝ (fun y : ℝ ↦ √c * y) z = ContinuousLinearMap.toSpanSingleton ℝ √c := by
        simpa using ((hasDerivAt_id z).const_mul √c).hasFDerivAt.fderiv
      rw [enorm_scaledLineMetric hc, mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply, hf,
        ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, enorm_mul, ENNReal.coe_one,
        one_mul, mul_comm, Real.enorm_of_nonneg (Real.sqrt_nonneg _)]
      -- The two sides differ only in the coercion of `NormedSpace.fromTangentSpace z`.
      exact le_rfl

/-- **The distance to the critical point decays at the rate `2 / c`.** For the metric
`scaledLineMetric`, the trajectory of `-grad x²` through `x₀` is at Riemannian distance exactly
`√c |x₀| exp (-2 t / c)` from the critical point `0` at time `t`. -/
theorem riemannianEDist_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric (hc : 0 < c)
    (x₀ t : ℝ) :
    let _ : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
      ⟨(scaledLineMetric hc).toRiemannianMetric⟩
    Manifold.riemannianEDist 𝓘(ℝ, ℝ)
        (maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀ t) 0 =
      ENNReal.ofReal (√c * |x₀| * Real.exp (-(2 / c * t))) := by
  intro _
  rw [maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric hc, riemannianEDist_scaledLineMetric,
    sub_zero, abs_mul, Real.abs_exp, mul_assoc]

/-- **The rate `2 / c` is sharp.** For the metric `scaledLineMetric`, `x₀ ≠ 0` and `μ > 2 / c`,
the distance from the trajectory of `-grad x²` through `x₀` to the critical point `0` is not
bounded by `C exp (-μ t)` for large `t`, for any `C > 0`. For `c = 4` this excludes the rate `2`
of the standard metric. -/
theorem not_exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric
    (hc : 0 < c) {x₀ μ : ℝ} (hx₀ : x₀ ≠ 0) (hμ : 2 / c < μ) :
    let _ : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
      ⟨(scaledLineMetric hc).toRiemannianMetric⟩
    ¬ ∃ C > 0, ∀ᶠ t in atTop,
      Manifold.riemannianEDist 𝓘(ℝ, ℝ)
          (maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀ t) 0 ≤
        ENNReal.ofReal (C * Real.exp (-(μ * t))) := by
  intro _
  rintro ⟨C, hC, h⟩
  have hK : 0 < √c * |x₀| := mul_pos (Real.sqrt_pos.2 hc) (abs_pos.2 hx₀)
  have hgrow : Tendsto (fun t : ℝ ↦ Real.exp ((μ - 2 / c) * t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (sub_pos.2 hμ))
  obtain ⟨t, ht, hbig⟩ := (h.and (hgrow.eventually_gt_atTop (C / (√c * |x₀|)))).exists
  rw [riemannianEDist_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric hc,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at ht
  -- Multiplying the bound by `exp (μ t)` gives `√c |x₀| exp ((μ - 2 / c) t) ≤ C`.
  have hle : √c * |x₀| * Real.exp ((μ - 2 / c) * t) ≤ C :=
    calc √c * |x₀| * Real.exp ((μ - 2 / c) * t) =
          √c * |x₀| * Real.exp (-(2 / c * t)) * Real.exp (μ * t) := by
          rw [mul_assoc (√c * |x₀|), ← Real.exp_add]
          ring_nf
      _ ≤ C * Real.exp (-(μ * t)) * Real.exp (μ * t) := by gcongr
      _ = C := by simp [Real.exp_neg]
  linarith [(div_lt_iff₀ hK).1 hbig]

/-- **The length of a trajectory.** For the metric `scaledLineMetric` and `t ≤ s`, the trajectory
of `-grad x²` through `x₀` has Riemannian length `√c |x₀| (exp (-2 t / c) - exp (-2 s / c))`
between the times `t` and `s`. -/
theorem pathELength_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric (hc : 0 < c) (x₀ : ℝ)
    {t s : ℝ} (hts : t ≤ s) :
    let _ : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
      ⟨(scaledLineMetric hc).toRiemannianMetric⟩
    Manifold.pathELength 𝓘(ℝ, ℝ)
        (maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀) t s =
      ENNReal.ofReal (√c * |x₀| * (Real.exp (-(2 / c * t)) - Real.exp (-(2 / c * s)))) := by
  intro _
  have hγ : maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀ =
      fun τ ↦ x₀ * Real.exp (-(2 / c * τ)) :=
    funext (maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric hc x₀)
  rw [hγ, Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  -- The speed of the trajectory at time `τ`.
  set g : ℝ → ℝ := fun τ ↦ √c * |x₀| * (2 / c) * Real.exp (-(2 / c * τ))
  have hd (τ : ℝ) : ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun τ ↦ x₀ * Real.exp (-(2 / c * τ))) τ 1‖ₑ =
      ENNReal.ofReal (g τ) := by
    rw [enorm_scaledLineMetric hc, mfderiv_eq_fderiv,
      (hasDerivAt_mul_exp_neg_two_div_mul x₀ c τ).hasFDerivAt.fderiv]
    -- The tangent vector `1` at `τ` is the real number `1`.
    have h1 : NormedSpace.fromTangentSpace (𝕜 := ℝ) τ 1 = 1 := rfl
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.toSpanSingleton_apply, h1,
      one_smul]
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.norm_eq_abs, abs_mul,
      abs_mul, abs_neg, Real.abs_exp, abs_of_pos (by positivity : (0 : ℝ) < 2 / c)]
    congr 1
    simp only [g]
    ring
  simp_rw [hd]
  -- The length is the integral of the speed, computed from an antiderivative.
  have hG (τ : ℝ) : HasDerivAt (fun τ ↦ -(√c * |x₀| * Real.exp (-(2 / c * τ)))) (g τ) τ := by
    exact (hasDerivAt_mul_exp_neg_two_div_mul (√c * |x₀|) c τ).neg.congr_deriv
      (by simp only [g]; ring)
  rw [← ofReal_integral_eq_lintegral_ofReal, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hts,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ ↦ hG τ)]
  · congr 1
    ring
  · exact (by fun_prop : Continuous g).intervalIntegrable _ _
  · exact (by fun_prop : Continuous g).integrableOn_Icc
  · exact ae_of_all _ fun τ ↦ by simp only [g]; positivity

/-- **The tail length of a trajectory.** For the metric `scaledLineMetric`, the trajectory of
`-grad x²` through `x₀` has Riemannian length `√c |x₀| exp (-2 t / c)` after the time `t`. This is
`√c` times the square root of the energy `f (γ t) - f 0 = x₀² exp (-4 t / c)`. -/
theorem iSup_pathELength_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric (hc : 0 < c)
    (x₀ t : ℝ) :
    let _ : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
      ⟨(scaledLineMetric hc).toRiemannianMetric⟩
    ⨆ s, Manifold.pathELength 𝓘(ℝ, ℝ)
        (maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀) t s =
      ENNReal.ofReal (√c * |x₀| * Real.exp (-(2 / c * t))) := by
  intro _
  apply le_antisymm
  · refine iSup_le fun s ↦ ?_
    rcases le_or_gt t s with hts | hst
    · rw [pathELength_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric hc x₀ hts]
      gcongr
      linarith [Real.exp_pos (-(2 / c * s))]
    · rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc, Icc_eq_empty hst.not_ge,
        Measure.restrict_empty, lintegral_zero_measure]
      exact zero_le
  · -- The lengths up to the times `s → ∞` tend to the claimed value.
    have hlim : Tendsto (fun s ↦ ENNReal.ofReal
        (√c * |x₀| * (Real.exp (-(2 / c * t)) - Real.exp (-(2 / c * s))))) atTop
        (𝓝 (ENNReal.ofReal (√c * |x₀| * Real.exp (-(2 / c * t))))) := by
      refine ENNReal.tendsto_ofReal ?_
      have hexp : Tendsto (fun s ↦ Real.exp (-(2 / c * s))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp
          (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop (by positivity)))
      simpa using (tendsto_const_nhds.sub hexp).const_mul (√c * |x₀|)
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨t, fun s hs ↦ ?_⟩)
    rw [← pathELength_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric hc x₀ hs]
    exact le_iSup (fun s ↦ Manifold.pathELength 𝓘(ℝ, ℝ)
      (maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀) t s) s

end TauCeti
