/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Maximal
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.ArcLength
import TauCeti.Geometry.Manifold.Riemannian.Scaling

/-!
# The rate of gradient convergence depends on the metric

A negative gradient trajectory converging to a nondegenerate critical point converges to it
exponentially fast in the Riemannian distance
(`TauCeti.exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient`). The Hessian and
the Morse index at a critical point do not depend on the metric, but the gradient, its
trajectories and the distance do, and so does the rate. This file computes the trajectories of
`f(x) = x²` on `ℝ` for the constant metric `c dx²`, `c > 0` (`TauCeti.scaledLineMetric`).

* **The gradient.** For `c dx²` the gradient of `f` is `1 / c` times its standard gradient `2 x`
  (`TauCeti.mgradient_sq_scaledLineMetric`), so the trajectory of `-grad f` through `x₀` is
  `t ↦ x₀ exp (-2 t / c)` (`TauCeti.maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric`).
* **The distance.** The Riemannian distance of `c dx²` is `√c |x - y|`
  (`TauCeti.riemannianEDist_scaledLineMetric`): rescaling a metric by the constant `c` multiplies
  its distance by `√c` (`Bundle.ContMDiffRiemannianMetric.riemannianEDist_rescale_const`), and the
  standard metric induces the usual distance.
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

The construction follows two existing examples. The metric is installed by a local
`RiemannianBundle` instance, as for `TauCeti.singularLineMetric` in
`TauCeti/Geometry/Manifold/Morse/Examples/Trajectory.lean`. The explicit trajectory, its distance
to the critical point and the sharpness of the rate are adapted from
`TauCeti.maximalIntegralCurve_neg_mgradient_sq_sub_sq`,
`TauCeti.riemannianEDist_maximalIntegralCurve_neg_mgradient_sq_sub_sq` and
`TauCeti.not_exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_sq_sub_sq` in
`TauCeti/Geometry/Manifold/Morse/Examples/ExponentialConvergence.lean`.

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

/-- For the metric `scaledLineMetric`, the gradient of `f(x) = x²` is `2 x / c`. -/
theorem mgradient_sq_scaledLineMetric (hc : 0 < c) (x : ℝ) :
    let _ : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
      ⟨(scaledLineMetric hc).toRiemannianMetric⟩
    mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2) x = (2 / c * x : ℝ) := by
  refine ((riemannianMetricVectorSpace ℝ).mgradient_rescale_const hc _ x).trans ?_
  rw [mgradient_eq_gradient, gradient_eq_deriv']
  simp only [deriv_pow_field]
  -- The tangent space of `ℝ` at `x` is `ℝ`, so the scalar multiplication is multiplication.
  exact (by rw [smul_eq_mul]; push_cast; ring : c⁻¹ • ((2 : ℕ) * x ^ (2 - 1) : ℝ) = 2 / c * x)

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
  have hd : HasDerivAt (fun t ↦ x₀ * Real.exp (-(2 / c * t)))
      (x₀ * (Real.exp (-(2 / c * t)) * -(2 / c))) t := by
    simpa using (((hasDerivAt_id t).const_mul (2 / c)).neg.exp).const_mul x₀
  have e : x₀ * (Real.exp (-(2 / c * t)) * -(2 / c)) =
      -(2 / c * (x₀ * Real.exp (-(2 / c * t)))) := by ring
  exact hd.hasDerivWithinAt.congr_deriv
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
  simpa using IsMIntegralCurve.maximalIntegralCurve_eq
    (contMDiff_neg_mgradient_one (contDiff_id.pow 2).contMDiff)
    (isMIntegralCurve_neg_mgradient_sq_scaledLineMetric hc x₀) t

/-- **The distance of the metric `c dx²`.** The Riemannian distance of `scaledLineMetric` between
`x` and `y` is `√c |x - y|`. -/
theorem riemannianEDist_scaledLineMetric (hc : 0 < c) (x y : ℝ) :
    let _ : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
      ⟨(scaledLineMetric hc).toRiemannianMetric⟩
    Manifold.riemannianEDist 𝓘(ℝ, ℝ) x y = ENNReal.ofReal (√c * |x - y|) := by
  -- For the standard metric, the Riemannian distance is the usual distance.
  have h₀ := IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ)) x y
  intro _
  -- The distance of `c dx²` is `√c` times the standard one.
  refine ((riemannianMetricVectorSpace ℝ).riemannianEDist_rescale_const hc x y).trans ?_
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← Real.dist_eq, ← edist_dist]
  exact congrArg (ENNReal.ofReal √c * ·) h₀.symm

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
bounded by `C exp (-μ t)` for large `t`, for any `C`. For `c = 4` this excludes the rate `2`
of the standard metric. -/
theorem not_exists_riemannianEDist_le_mul_exp_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric
    (hc : 0 < c) {x₀ μ : ℝ} (hx₀ : x₀ ≠ 0) (hμ : 2 / c < μ) :
    let _ : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
      ⟨(scaledLineMetric hc).toRiemannianMetric⟩
    ¬ ∃ C, ∀ᶠ t in atTop,
      Manifold.riemannianEDist 𝓘(ℝ, ℝ)
          (maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀ t) 0 ≤
        ENNReal.ofReal (C * Real.exp (-(μ * t))) := by
  intro _
  rintro ⟨C, h⟩
  have hK : 0 < √c * |x₀| := mul_pos (Real.sqrt_pos.2 hc) (abs_pos.2 hx₀)
  have hgrow : Tendsto (fun t : ℝ ↦ Real.exp ((μ - 2 / c) * t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (sub_pos.2 hμ))
  obtain ⟨t, ht, hbig⟩ := (h.and (hgrow.eventually_gt_atTop (C / (√c * |x₀|)))).exists
  rw [riemannianEDist_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric hc,
    ENNReal.ofReal_le_ofReal_iff', or_iff_left (not_le.2 (by positivity))] at ht
  -- Multiplying the bound by `exp (μ t)` gives `√c |x₀| exp ((μ - 2 / c) t) ≤ C`.
  have hle : √c * |x₀| * Real.exp ((μ - 2 / c) * t) ≤ C :=
    calc √c * |x₀| * Real.exp ((μ - 2 / c) * t) =
          √c * |x₀| * Real.exp (-(2 / c * t)) * Real.exp (μ * t) := by
          rw [mul_assoc (√c * |x₀|), ← Real.exp_add]
          ring_nf
      _ ≤ C * Real.exp (-(μ * t)) * Real.exp (μ * t) := by gcongr
      _ = C := by simp [Real.exp_neg]
  linarith [(div_lt_iff₀ hK).1 hbig]

/-- **The length of a trajectory.** For the metric `scaledLineMetric`, the trajectory of `-grad x²`
through `x₀` has Riemannian length `√c |x₀| (exp (-2 t / c) - exp (-2 s / c))` between the times
`t` and `s`; for `s < t` both sides vanish. -/
theorem pathELength_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric (hc : 0 < c)
    (x₀ t s : ℝ) :
    let _ : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
      ⟨(scaledLineMetric hc).toRiemannianMetric⟩
    Manifold.pathELength 𝓘(ℝ, ℝ)
        (maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀) t s =
      ENNReal.ofReal (√c * |x₀| * (Real.exp (-(2 / c * t)) - Real.exp (-(2 / c * s)))) := by
  -- For the standard metric, the line `u ↦ x₀ u` has constant speed `|x₀|`.
  have hline (a b : ℝ) : Manifold.pathELength 𝓘(ℝ, ℝ) (fun u ↦ x₀ * u) a b =
      ENNReal.ofReal |x₀| * ENNReal.ofReal (b - a) :=
    pathELength_eq_of_norm_curveVelocity_eq fun u _ ↦ by
      -- The velocity is the tangent vector `x₀`, which is the real number `x₀`.
      rw [norm_tangentSpace_vectorSpace]
      simpa using congrArg abs (NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) (x₀ * u) x₀)
  intro _
  have hf : Antitone fun τ : ℝ ↦ Real.exp (-(2 / c * τ)) := fun _ _ h ↦
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left h (by positivity)))
  rcases lt_or_ge s t with hst | hts
  · rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc, Icc_eq_empty hst.not_ge,
      Measure.restrict_empty, lintegral_zero_measure, eq_comm, ENNReal.ofReal_eq_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.2 (hf hst.le))
  -- The trajectory is the line `u ↦ x₀ u` reparametrized by the antitone `τ ↦ exp (-2 τ / c)`.
  have hγ : maximalIntegralCurve (-mgradient 𝓘(ℝ, ℝ) (fun y : ℝ ↦ y ^ 2)) x₀ =
      (fun u ↦ x₀ * u) ∘ fun τ ↦ Real.exp (-(2 / c * τ)) :=
    funext (maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric hc x₀)
  rw [hγ, Manifold.pathELength_comp_of_antitoneOn hts (hf.antitoneOn _) (by fun_prop)
    ((by fun_prop : ContDiff ℝ 1 fun u : ℝ ↦ x₀ * u).contMDiff.mdifferentiable
      one_ne_zero).mdifferentiableOn]
  -- The length for `c dx²` is `√c` times the standard one.
  refine ((riemannianMetricVectorSpace ℝ).pathELength_rescale_const hc _ _ _).trans
    ((congrArg (ENNReal.ofReal √c * ·) (hline _ _)).trans ?_)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), mul_assoc]

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
  -- The lengths up to the times `s → ∞` increase to the claimed value.
  refine tendsto_nhds_unique (tendsto_atTop_iSup fun _ _ h ↦ Manifold.pathELength_mono le_rfl h)
    ((ENNReal.tendsto_ofReal ?_).congr fun s ↦
      (pathELength_maximalIntegralCurve_neg_mgradient_sq_scaledLineMetric hc x₀ t s).symm)
  have hexp : Tendsto (fun s ↦ Real.exp (-(2 / c * s))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (by positivity))
  simpa using (tendsto_const_nhds.sub hexp).const_mul (√c * |x₀|)

end TauCeti
