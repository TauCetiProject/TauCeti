/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Conformal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic

/-!
# The torpedo metric

The *torpedo metric* of Gromov and Lawson is a rotationally symmetric metric of positive scalar
curvature on `ℝⁿ`, `n ≥ 3`, which is a round spherical cap near the centre and the product cylinder
`ℝ × S^(n - 1)` outside a ball. Torpedo metrics are the building blocks of the Gromov–Lawson
surgery construction, where they are glued in along a product boundary collar.

Here the metric is built in conformal coordinates. On a real inner product space `F` of dimension
`n`, `TauCeti.torpedoMetric F` is the Euclidean metric multiplied by `e^(2 Φ(‖y‖))`, with
`Φ = TauCeti.torpedoExponent`. In the logarithmic radial variable `s = log ‖y‖` the Euclidean metric
is `e^(2 s) (ds² + g_(S^(n - 1)))`, so the torpedo metric is `e^(2 w(s)) (ds² + g_(S^(n - 1)))`
with the *torpedo profile* `w = TauCeti.torpedoProfile`, `Φ(ρ) = w(log ρ) - log ρ`:

* for `s ≤ -2`, `w(s) = log R - log (cosh s)` with `R = TauCeti.torpedoCapRadius`, and the metric
  is the round metric `(2 R / (1 + ‖y‖²))² ⟪v, w⟫` of the sphere of radius `R` in stereographic
  coordinates;
* for `s ≥ -1`, `w(s) = 0`, and the metric is the cylinder metric `‖y‖⁻² ⟪v, w⟫ = ds² + dθ²`.

The slope `v = w' = TauCeti.torpedoSlope` is `-tanh s` on the cap, cut off by a smooth step, so it
is antitone with `0 ≤ v < 1`. By the conformal change formula, away from the centre the scalar
curvature is `(n - 1) e^(-2 w) ((n - 2) (1 - v²) - 2 v')`, which is positive for `n ≥ 3`; it is
`(n - 1) (n - 2)` on the cylindrical end. A compactness argument on the transition region gives a
uniform positive lower bound. In the arclength radial coordinate `r = ∫ e^w ds` the metric takes
the form `dr² + f(r)² g_(S^(n - 1))`, `f = e^w`, in which it is usually described.

## Main definitions

* `TauCeti.torpedoSlope`, `TauCeti.torpedoProfile`: the slope `v` and the profile `w`.
* `TauCeti.torpedoCapRadius`: the radius `R` of the round cap.
* `TauCeti.torpedoExponent`: the conformal exponent `Φ`.
* `TauCeti.torpedoMetric`: the torpedo metric on `F`.

## Main results

* `TauCeti.torpedoMetric_inner_of_le`, `TauCeti.torpedoMetric_inner_of_ge`: the round cap and the
  cylindrical end.
* `TauCeti.scalarCurvature_torpedoMetric_of_ne_zero`: the scalar curvature away from the centre.
* `TauCeti.scalarCurvature_torpedoMetric_of_ge`: the scalar curvature of the cylindrical end.
* `TauCeti.exists_pos_le_scalarCurvature_torpedoMetric`: a uniform positive lower bound for the
  scalar curvature in dimension at least `3`.
* `TauCeti.hasPositiveScalarCurvature_torpedoMetric`: the torpedo metric has positive scalar
  curvature in dimension at least `3`.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive scalar
  curvature*, Ann. of Math. 111 (1980), 423–434.
* M. Walsh, *Metrics of positive scalar curvature and generalised Morse functions, Part I*,
  Mem. Amer. Math. Soc. 209 (2011), no. 983, Section 1.
-/

public section

noncomputable section

open Real Set
open scoped ContDiff Manifold InnerProductSpace
open Bundle

namespace TauCeti

/-! ### The torpedo profile -/

/-- The slope `v = w'` of the torpedo profile `w`, in the logarithmic radial variable
`s = log ‖y‖`: it is `-tanh s` for `s ≤ -2`, the slope of the round metric, and `0` for
`s ≥ -1`, the slope of the cylinder; in between `-tanh s` is cut off by a smooth step. -/
def torpedoSlope (s : ℝ) : ℝ :=
  -tanh s * (1 - smoothTransition (s + 2))

/-- On the round cap the slope is `-tanh s`, the slope of `-log (cosh s)`. -/
theorem torpedoSlope_of_le {s : ℝ} (hs : s ≤ -2) : torpedoSlope s = -tanh s := by
  rw [torpedoSlope, smoothTransition.zero_of_nonpos (by linarith), sub_zero, mul_one]

/-- On the cylindrical end the slope vanishes. -/
theorem torpedoSlope_of_ge {s : ℝ} (hs : -1 ≤ s) : torpedoSlope s = 0 := by
  rw [torpedoSlope, smoothTransition.one_of_one_le (by linarith), sub_self, mul_zero]

/-- The slope is smooth. -/
theorem contDiff_torpedoSlope : ContDiff ℝ ∞ torpedoSlope :=
  Real.contDiff_tanh.neg.mul (contDiff_const.sub (smoothTransition.contDiff.comp
    (contDiff_id.add contDiff_const)))

/-- The slope is nonnegative. -/
theorem torpedoSlope_nonneg (s : ℝ) : 0 ≤ torpedoSlope s := by
  rcases le_or_gt (-1) s with hs | hs
  · rw [torpedoSlope_of_ge hs]
  · refine mul_nonneg ?_ (sub_nonneg.2 (smoothTransition.le_one _))
    have hs0 : s < 0 := by linarith
    have := tanh_strictMono hs0
    rw [tanh_zero] at this
    linarith

/-- The slope is less than `1`, so `1 - v²` is positive. -/
theorem torpedoSlope_lt_one (s : ℝ) : torpedoSlope s < 1 := by
  have h1 : -tanh s < 1 := by linarith [neg_one_lt_tanh s]
  rcases le_or_gt (-tanh s) 0 with h | h
  · rw [torpedoSlope]
    nlinarith [smoothTransition.nonneg (s + 2), smoothTransition.le_one (s + 2)]
  · calc torpedoSlope s ≤ -tanh s := mul_le_of_le_one_right h.le (by
          linarith [smoothTransition.nonneg (s + 2)])
      _ < 1 := h1

/-- The slope is antitone: it decreases from `-tanh s` on the cap to `0` on the cylindrical
end. -/
theorem antitone_torpedoSlope : Antitone torpedoSlope := by
  intro a b hab
  rcases le_or_gt (-1) b with hb | hb
  · rw [torpedoSlope_of_ge hb]
    exact torpedoSlope_nonneg a
  · have hta : tanh b < 0 := by
      have hb0 : b < 0 := by linarith
      have := tanh_strictMono hb0
      rwa [tanh_zero] at this
    refine mul_le_mul (neg_le_neg (tanh_strictMono.monotone hab))
      (sub_le_sub_left (smoothTransition.monotone (by linarith)) _)
      (sub_nonneg.2 (smoothTransition.le_one _)) ?_
    have := tanh_strictMono.monotone hab
    linarith

/-- The derivative of the slope is nonpositive. -/
theorem deriv_torpedoSlope_nonpos (s : ℝ) : deriv torpedoSlope s ≤ 0 :=
  ((contDiff_torpedoSlope.differentiable (by simp)) s).hasDerivAt.nonpos_of_antitone
    antitone_torpedoSlope

/-- The slope is stationary on the cylindrical end, where it attains its minimum `0`. -/
theorem deriv_torpedoSlope_of_ge {s : ℝ} (hs : -1 ≤ s) : deriv torpedoSlope s = 0 := by
  refine IsLocalMin.deriv_eq_zero (Filter.Eventually.of_forall fun τ ↦ ?_)
  rw [torpedoSlope_of_ge hs]
  exact torpedoSlope_nonneg τ

/-- The torpedo profile `w`: the primitive of the slope `TauCeti.torpedoSlope` vanishing at `-1`,
hence on the whole cylindrical end `[-1, ∞)`. -/
def torpedoProfile (s : ℝ) : ℝ :=
  ∫ τ in (-1 : ℝ)..s, torpedoSlope τ

/-- The torpedo profile is a primitive of the slope. -/
theorem hasDerivAt_torpedoProfile (s : ℝ) : HasDerivAt torpedoProfile (torpedoSlope s) s :=
  (contDiff_torpedoSlope.continuous.integral_hasStrictDerivAt (-1) s).hasDerivAt

/-- The derivative of the torpedo profile is the slope. -/
@[simp]
theorem deriv_torpedoProfile : deriv torpedoProfile = torpedoSlope :=
  funext fun s ↦ (hasDerivAt_torpedoProfile s).deriv

/-- The torpedo profile is smooth. -/
theorem contDiff_torpedoProfile : ContDiff ℝ ∞ torpedoProfile :=
  contDiff_infty_iff_deriv.2 ⟨fun s ↦ (hasDerivAt_torpedoProfile s).differentiableAt,
    deriv_torpedoProfile ▸ contDiff_torpedoSlope⟩

/-- The torpedo profile vanishes on the cylindrical end. -/
theorem torpedoProfile_of_ge {s : ℝ} (hs : -1 ≤ s) : torpedoProfile s = 0 := by
  rw [torpedoProfile, intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)),
    intervalIntegral.integral_zero]
  intro τ hτ
  rw [uIcc_of_le hs] at hτ
  exact torpedoSlope_of_ge hτ.1

/-- The radius `R` of the round cap of the torpedo metric, the constant for which
`w(s) = log R - log (cosh s)` on the cap `s ≤ -2`. -/
def torpedoCapRadius : ℝ :=
  cosh 2 * exp (torpedoProfile (-2))

/-- The radius of the round cap is positive. -/
theorem torpedoCapRadius_pos : 0 < torpedoCapRadius :=
  mul_pos (cosh_pos 2) (exp_pos _)

/-- On the round cap the torpedo profile is `log R - log (cosh s)`, so that the metric
`e^(2 w(s)) (ds² + g_(S^(n - 1)))` is the round metric of radius `R`. -/
theorem torpedoProfile_of_le {s : ℝ} (hs : s ≤ -2) :
    torpedoProfile s = log torpedoCapRadius - log (cosh s) := by
  have hint : IntervalIntegrable torpedoSlope MeasureTheory.volume (-1) (-2) :=
    contDiff_torpedoSlope.continuous.intervalIntegrable _ _
  have hint' : IntervalIntegrable torpedoSlope MeasureTheory.volume (-2) s :=
    contDiff_torpedoSlope.continuous.intervalIntegrable _ _
  have hcap : ∫ τ in (-2 : ℝ)..s, torpedoSlope τ = -log (cosh s) - -log (cosh (-2)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun τ ↦ -log (cosh τ))
      (fun τ hτ ↦ ?_) hint'
    rw [uIcc_of_ge hs] at hτ
    rw [torpedoSlope_of_le hτ.2, tanh_eq_sinh_div_cosh]
    simpa [neg_div] using ((hasDerivAt_cosh τ).log (cosh_pos τ).ne').fun_neg
  rw [torpedoProfile, ← intervalIntegral.integral_add_adjacent_intervals hint hint', hcap,
    torpedoCapRadius, log_mul (cosh_pos 2).ne' (exp_pos _).ne', log_exp, cosh_neg]
  simp only [torpedoProfile]
  ring

/-! ### The conformal exponent -/

/-- The exponent `Φ` of the conformal factor `e^(2 Φ(‖y‖))` of the torpedo metric, as a function of
the radius `ρ = ‖y‖`: `Φ(ρ) = w(log ρ) - log ρ` for `ρ ≠ 0`, with the torpedo profile `w`, and
`Φ(0) = log (2 R)`, with `R` the radius of the round cap. -/
def torpedoExponent (ρ : ℝ) : ℝ :=
  if ρ = 0 then log (2 * torpedoCapRadius) else torpedoProfile (log ρ) - log ρ

/-- Away from the centre the conformal exponent is `w(log ρ) - log ρ`. -/
theorem torpedoExponent_of_ne_zero {ρ : ℝ} (hρ : ρ ≠ 0) :
    torpedoExponent ρ = torpedoProfile (log ρ) - log ρ := by
  simp [torpedoExponent, hρ]

/-- At the centre the conformal exponent is `log (2 R)`. -/
@[simp]
theorem torpedoExponent_zero : torpedoExponent 0 = log (2 * torpedoCapRadius) := by
  simp [torpedoExponent]

/-- On the round cap `ρ ≤ e⁻²` the conformal factor `e^(2 Φ(ρ))` is `(2 R / (1 + ρ²))²`, that of
the round sphere of radius `R` in stereographic coordinates. -/
theorem torpedoExponent_of_le {ρ : ℝ} (h₀ : 0 ≤ ρ) (h : ρ ≤ exp (-2)) :
    torpedoExponent ρ = log (2 * torpedoCapRadius / (1 + ρ ^ 2)) := by
  rcases h₀.eq_or_lt with rfl | hρ
  · simp
  have hR := torpedoCapRadius_pos
  have hc : 0 < (ρ + ρ⁻¹) / 2 := by positivity
  have hfrac : 2 * torpedoCapRadius / (1 + ρ ^ 2) = torpedoCapRadius / ((ρ + ρ⁻¹) / 2 * ρ) := by
    field_simp
    ring
  rw [torpedoExponent_of_ne_zero hρ.ne', torpedoProfile_of_le ((log_le_iff_le_exp hρ).2 h),
    cosh_log hρ, hfrac, log_div hR.ne' (by positivity), log_mul hc.ne' hρ.ne']
  ring

/-- On the cylindrical end `e⁻¹ ≤ ρ` the conformal factor `e^(2 Φ(ρ))` is `ρ⁻²`. -/
theorem torpedoExponent_of_ge {ρ : ℝ} (h : exp (-1) ≤ ρ) : torpedoExponent ρ = -log ρ := by
  have hρ : 0 < ρ := (exp_pos _).trans_le h
  rw [torpedoExponent_of_ne_zero hρ.ne', torpedoProfile_of_ge ((le_log_iff_exp_le hρ).2 h),
    zero_sub]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

open Filter Topology in
/-- The conformal exponent `y ↦ Φ(‖y‖)` is smooth, also at the centre. -/
theorem contDiff_torpedoExponent_norm : ContDiff ℝ ∞ fun y : F ↦ torpedoExponent ‖y‖ := by
  rw [contDiff_iff_contDiffAt]
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · -- Near the centre the exponent is `log (2 R / (1 + ‖y‖²))`.
    have hev : (fun z : F ↦ torpedoExponent ‖z‖) =ᶠ[𝓝 0]
        fun z ↦ log (2 * torpedoCapRadius / (1 + ‖z‖ ^ 2)) := by
      filter_upwards [Metric.closedBall_mem_nhds (0 : F) (exp_pos (-2))] with z hz
      exact torpedoExponent_of_le (norm_nonneg z) (by simpa using hz)
    have hR := torpedoCapRadius_pos
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    exact ((contDiff_const.div (contDiff_const.add (contDiff_norm_sq ℝ))
      fun z ↦ by positivity).log fun z ↦ (div_pos (mul_pos two_pos hR) (by positivity)).ne'
      ).contDiffAt
  · have hev : (fun z : F ↦ torpedoExponent ‖z‖) =ᶠ[𝓝 y]
        fun z ↦ torpedoProfile (log ‖z‖) - log ‖z‖ := by
      filter_upwards [isOpen_ne.mem_nhds hy] with z hz
      exact torpedoExponent_of_ne_zero (norm_ne_zero_iff.2 hz)
    have hlog : ContDiffAt ℝ ∞ (fun z : F ↦ log ‖z‖) y :=
      (contDiffAt_log.2 (norm_ne_zero_iff.2 hy)).comp y (contDiffAt_norm ℝ hy)
    exact ((contDiff_torpedoProfile.contDiffAt.comp y hlog).sub hlog).congr_of_eventuallyEq hev

/-! ### The torpedo metric -/

variable (F) in
/-- The **torpedo metric** on a real inner product space `F`: the Euclidean metric multiplied by
the conformal factor `e^(2 Φ(‖y‖))`. It is the round metric of radius `torpedoCapRadius` in
stereographic coordinates on the ball of radius `e⁻²`, and the cylinder metric `‖y‖⁻² ⟪v, w⟫` of
`ℝ × S^(n - 1)` outside the ball of radius `e⁻¹`. -/
def torpedoMetric : ContMDiffRiemannianMetric 𝓘(ℝ, F) ∞ F (fun y : F ↦ TangentSpace 𝓘(ℝ, F) y) :=
  ((riemannianMetricVectorSpace F).ofLE le_top).rescale (fun y ↦ exp (2 * torpedoExponent ‖y‖))
    (contDiff_const.mul contDiff_torpedoExponent_norm).exp.contMDiff fun _ ↦ exp_pos _

/-- The torpedo metric is the Euclidean metric multiplied by `e^(2 Φ(‖y‖))`. -/
theorem torpedoMetric_inner (y : F) (v w : TangentSpace 𝓘(ℝ, F) y) :
    (torpedoMetric F).inner y v w = exp (2 * torpedoExponent ‖y‖) *
      ⟪NormedSpace.fromTangentSpace y v, NormedSpace.fromTangentSpace y w⟫_ℝ := by
  rw [torpedoMetric, ContMDiffRiemannianMetric.rescale_inner,
    ContMDiffRiemannianMetric.ofLE_inner]
  rfl

/-- On the ball of radius `e⁻²` the torpedo metric is `(2 R / (1 + ‖y‖²))² ⟪v, w⟫`, the round
metric of the sphere of radius `R = torpedoCapRadius` in stereographic coordinates. -/
theorem torpedoMetric_inner_of_le {y : F} (h : ‖y‖ ≤ exp (-2)) (v w : TangentSpace 𝓘(ℝ, F) y) :
    (torpedoMetric F).inner y v w = (2 * torpedoCapRadius / (1 + ‖y‖ ^ 2)) ^ 2 *
      ⟪NormedSpace.fromTangentSpace y v, NormedSpace.fromTangentSpace y w⟫_ℝ := by
  have hR := torpedoCapRadius_pos
  have ha : 0 < 2 * torpedoCapRadius / (1 + ‖y‖ ^ 2) := by positivity
  rw [torpedoMetric_inner, torpedoExponent_of_le (norm_nonneg y) h, mul_comm (2 : ℝ), exp_mul,
    exp_log ha, rpow_two]

/-- Outside the ball of radius `e⁻¹` the torpedo metric is the cylinder metric `‖y‖⁻² ⟪v, w⟫`:
in the coordinates `y = e^s θ`, with `s ∈ ℝ` and `θ` in the unit sphere, it is `ds² + dθ²`. -/
theorem torpedoMetric_inner_of_ge {y : F} (h : exp (-1) ≤ ‖y‖) (v w : TangentSpace 𝓘(ℝ, F) y) :
    (torpedoMetric F).inner y v w = (‖y‖ ^ 2)⁻¹ *
      ⟪NormedSpace.fromTangentSpace y v, NormedSpace.fromTangentSpace y w⟫_ℝ := by
  have hρ : 0 < ‖y‖ := (exp_pos _).trans_le h
  rw [torpedoMetric_inner, torpedoExponent_of_ge h, mul_neg, exp_neg, mul_comm (2 : ℝ), exp_mul,
    exp_log hρ, rpow_two]

/-! ### Scalar curvature -/

section ScalarCurvature

open InnerProductSpace Laplacian Module
open scoped Gradient

omit [InnerProductSpace ℝ F] in
open Filter Topology in
/-- Away from the centre the conformal exponent is `ψ (log ‖y‖)` with `ψ(s) = w(s) - s`. -/
private theorem torpedoExponent_norm_eventuallyEq {y : F} (hy : y ≠ 0) :
    (fun z : F ↦ torpedoExponent ‖z‖) =ᶠ[𝓝 y]
      (fun s ↦ torpedoProfile s - s) ∘ fun z : F ↦ log ‖z‖ := by
  filter_upwards [isOpen_ne.mem_nhds hy] with z hz
  exact torpedoExponent_of_ne_zero (norm_ne_zero_iff.2 hz)

private theorem deriv_torpedoProfile_sub_id :
    deriv (fun s ↦ torpedoProfile s - s) = fun s ↦ torpedoSlope s - 1 := by
  funext s
  exact ((hasDerivAt_torpedoProfile s).sub (hasDerivAt_id s)).deriv

variable [FiniteDimensional ℝ F]

/-- The Laplacian of the conformal exponent away from the centre. -/
private theorem laplacian_torpedoExponent_norm {y : F} (hy : y ≠ 0) :
    Δ (fun z : F ↦ torpedoExponent ‖z‖) y =
      (deriv torpedoSlope (log ‖y‖) + (torpedoSlope (log ‖y‖) - 1) * (finrank ℝ F - 2)) /
        ‖y‖ ^ 2 := by
  have hψ : ContDiffAt ℝ 2 (fun s ↦ torpedoProfile s - s) (log ‖y‖) :=
    (contDiff_torpedoProfile.sub contDiff_id).contDiffAt.of_le (by simp)
  rw [(laplacian_congr_nhds (torpedoExponent_norm_eventuallyEq hy)).eq_of_nhds,
    ContDiffAt.laplacian_comp (q := fun z : F ↦ log ‖z‖) hψ
      ((contDiffAt_log.2 (norm_ne_zero_iff.2 hy)).comp y (contDiffAt_norm ℝ hy)),
    deriv_torpedoProfile_sub_id,
    laplacian_log_norm_of_ne hy, norm_gradient_eq_norm_fderiv, norm_fderiv_log_norm_of_ne hy]
  simp only [deriv_sub_const]
  have : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  field_simp

/-- The norm of the gradient of the conformal exponent away from the centre. -/
private theorem norm_gradient_torpedoExponent_norm {y : F} (hy : y ≠ 0) :
    ‖∇ (fun z : F ↦ torpedoExponent ‖z‖) y‖ = |torpedoSlope (log ‖y‖) - 1| * ‖y‖⁻¹ := by
  have hd : HasFDerivAt (fun z : F ↦ torpedoExponent ‖z‖)
      ((torpedoSlope (log ‖y‖) - 1) • fderiv ℝ (fun z : F ↦ log ‖z‖) y) y := by
    refine HasFDerivAt.congr_of_eventuallyEq ?_ (torpedoExponent_norm_eventuallyEq hy)
    exact ((hasDerivAt_torpedoProfile _).sub (hasDerivAt_id _)).comp_hasFDerivAt y
      (hasFDerivAt_log_norm_of_ne hy).differentiableAt.hasFDerivAt
  rw [norm_gradient_eq_norm_fderiv, hd.fderiv, norm_smul, norm_fderiv_log_norm_of_ne hy,
    Real.norm_eq_abs]

/-- **Scalar curvature of the torpedo metric.** Away from the centre, with `s = log ‖y‖`, the
torpedo profile `w` and its slope `v = w'`, the scalar curvature of the torpedo metric on a space
of dimension `n` is `(n - 1) e^(-2 w(s)) ((n - 2) (1 - v(s)²) - 2 v'(s))`. -/
theorem scalarCurvature_torpedoMetric_of_ne_zero {y : F} (hy : y ≠ 0) :
    (torpedoMetric F).scalarCurvature y =
      (finrank ℝ F - 1) * exp (-2 * torpedoProfile (log ‖y‖)) *
        ((finrank ℝ F - 2) * (1 - torpedoSlope (log ‖y‖) ^ 2) -
          2 * deriv torpedoSlope (log ‖y‖)) := by
  have hgrad : DifferentiableAt ℝ (∇ fun z : F ↦ torpedoExponent ‖z‖) y :=
    ((contDiff_torpedoExponent_norm.gradient_right (m := 1) (by simp)).differentiable
      (by simp)) y
  -- The conformal change formula, applied to the flat Euclidean metric `g`, involves only the
  -- Laplacian and the gradient of `Φ(‖·‖)` for `g`. The formula installs `g` with lowered
  -- smoothness; the flat identifications are transported along `toRiemannianMetric_ofLE`.
  rw [torpedoMetric, ContMDiffRiemannianMetric.scalarCurvature_rescale _ _ _
    (φ := fun z ↦ torpedoExponent ‖z‖) (fun _ ↦ rfl) y]
  have hscal : ((riemannianMetricVectorSpace F).ofLE
      (le_top : (∞ : WithTop ℕ∞) ≤ ω)).scalarCurvature y = 0 := by
    rw [ContMDiffRiemannianMetric.scalarCurvature_eq_scalarCurvature_leviCivitaConnection _
      (by rw [ContMDiffRiemannianMetric.toRiemannianMetric_ofLE]; rfl),
      TauCeti.Manifold.scalarCurvature_leviCivitaConnection_model_space]
  have hm := ContMDiffRiemannianMetric.toRiemannianMetric_ofLE (riemannianMetricVectorSpace F)
    (le_top : (∞ : WithTop ℕ∞) ≤ ω)
  have hΔ : (letI : RiemannianBundle (fun z : F ↦ TangentSpace 𝓘(ℝ, F) z) :=
      ⟨((riemannianMetricVectorSpace F).ofLE (le_top : (∞ : WithTop ℕ∞) ≤ ω)).toRiemannianMetric⟩
      Manifold.laplaceBeltrami 𝓘(ℝ, F) (fun z ↦ torpedoExponent ‖z‖) y) =
      Δ (fun z : F ↦ torpedoExponent ‖z‖) y :=
    TauCeti.Manifold.laplaceBeltrami_eq_laplacian_of_eq
      (inst := ⟨((riemannianMetricVectorSpace F).ofLE le_top).toRiemannianMetric⟩) hm hgrad
  have hG : (letI : RiemannianBundle (fun z : F ↦ TangentSpace 𝓘(ℝ, F) z) :=
      ⟨((riemannianMetricVectorSpace F).ofLE (le_top : (∞ : WithTop ℕ∞) ≤ ω)).toRiemannianMetric⟩
      ‖Manifold.mgradient 𝓘(ℝ, F) (fun z ↦ torpedoExponent ‖z‖) y‖) =
      ‖∇ (fun z : F ↦ torpedoExponent ‖z‖) y‖ :=
    TauCeti.Manifold.norm_mgradient_eq_norm_gradient_of_eq (inst := ⟨_⟩) hm _ _
  have hρ : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hexp : (exp (2 * torpedoExponent ‖y‖))⁻¹ =
      exp (-2 * torpedoProfile (log ‖y‖)) * ‖y‖ ^ 2 := by
    have harg : -(2 * (torpedoProfile (log ‖y‖) - log ‖y‖)) =
        -2 * torpedoProfile (log ‖y‖) + log (‖y‖ ^ 2) := by
      rw [log_pow]
      push_cast
      ring
    rw [torpedoExponent_of_ne_zero hρ.ne', ← exp_neg, harg, exp_add, exp_log (by positivity)]
  rw [hscal, hΔ, hG, hexp, laplacian_torpedoExponent_norm hy,
    norm_gradient_torpedoExponent_norm hy, mul_pow, sq_abs]
  field_simp
  ring

/-- On the cylindrical end the torpedo metric has the scalar curvature `(n - 1) (n - 2)` of the
cylinder `ℝ × S^(n - 1)`. -/
theorem scalarCurvature_torpedoMetric_of_ge {y : F} (h : exp (-1) ≤ ‖y‖) :
    (torpedoMetric F).scalarCurvature y = (finrank ℝ F - 1) * (finrank ℝ F - 2) := by
  have hρ : 0 < ‖y‖ := (exp_pos _).trans_le h
  have hs : -1 ≤ log ‖y‖ := (le_log_iff_exp_le hρ).2 h
  rw [scalarCurvature_torpedoMetric_of_ne_zero (norm_pos_iff.1 hρ), torpedoProfile_of_ge hs,
    torpedoSlope_of_ge hs, deriv_torpedoSlope_of_ge hs]
  simp

/-- A uniform positive lower bound for the positive factor `e^(-2 w) (1 - v²)` of the scalar
curvature: it is `R⁻²` on the round cap, `1` on the cylindrical end, and positive on the compact
transition interval. -/
private theorem exists_pos_le_exp_mul_one_sub_torpedoSlope_sq :
    ∃ c > 0, ∀ s, c ≤ exp (-2 * torpedoProfile s) * (1 - torpedoSlope s ^ 2) := by
  set m := fun s ↦ exp (-2 * torpedoProfile s) * (1 - torpedoSlope s ^ 2)
  have hm_pos : ∀ s, 0 < m s := fun s ↦ mul_pos (exp_pos _) (by
    nlinarith [torpedoSlope_nonneg s, torpedoSlope_lt_one s])
  have hm_cont : Continuous m :=
    ((continuous_const.mul contDiff_torpedoProfile.continuous).rexp).mul
      (continuous_const.sub (contDiff_torpedoSlope.continuous.pow 2))
  obtain ⟨s₀, -, hs₀⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (by norm_num : (-2 : ℝ) ≤ -1))
    hm_cont.continuousOn
  have hR := torpedoCapRadius_pos
  refine ⟨min (m s₀) (min 1 (torpedoCapRadius ^ 2)⁻¹), lt_min (hm_pos s₀) (lt_min one_pos
    (by positivity)), fun s ↦ ?_⟩
  rcases le_or_gt s (-2) with hs | hs
  · -- On the round cap `e^(-2 w) = cosh² s / R²` and `1 - v² = 1 / cosh² s`.
    refine (min_le_right _ _).trans ((min_le_right _ _).trans_eq ?_)
    have hc := cosh_pos s
    simp only [torpedoProfile_of_le hs, torpedoSlope_of_le hs, neg_sq, tanh_eq_sinh_div_cosh]
    have harg : -2 * (log torpedoCapRadius - log (cosh s)) =
        log (cosh s ^ 2) - log (torpedoCapRadius ^ 2) := by
      rw [log_pow, log_pow]
      push_cast
      ring
    rw [harg, exp_sub, exp_log (by positivity), exp_log (by positivity)]
    field_simp
    linear_combination (-1 : ℝ) * cosh_sq s
  rcases le_or_gt (-1) s with hs' | hs'
  · refine (min_le_right _ _).trans ((min_le_left _ _).trans_eq ?_)
    simp [torpedoProfile_of_ge hs', torpedoSlope_of_ge hs']
  · exact (min_le_left _ _).trans (hs₀ ⟨hs.le, hs'.le⟩)

/-- **The torpedo metric has uniformly positive scalar curvature** in dimension `n ≥ 3`: its scalar
curvature is bounded below by a positive constant. -/
theorem exists_pos_le_scalarCurvature_torpedoMetric (hn : 3 ≤ finrank ℝ F) :
    ∃ c > 0, ∀ y, c ≤ (torpedoMetric F).scalarCurvature y := by
  obtain ⟨c, hc, hle⟩ := exists_pos_le_exp_mul_one_sub_torpedoSlope_sq
  have hn' : (3 : ℝ) ≤ finrank ℝ F := by exact_mod_cast hn
  refine ⟨(finrank ℝ F - 1) * (finrank ℝ F - 2) * c, by
    have : (0 : ℝ) < (finrank ℝ F - 1) * (finrank ℝ F - 2) := by nlinarith
    positivity, ?_⟩
  -- The bound holds away from the centre, by the formula for the scalar curvature.
  have hne : ∀ y : F, y ≠ 0 →
      (finrank ℝ F - 1) * (finrank ℝ F - 2) * c ≤ (torpedoMetric F).scalarCurvature y := by
    intro y hy
    rw [scalarCurvature_torpedoMetric_of_ne_zero hy]
    have h1 := hle (log ‖y‖)
    have h2 := deriv_torpedoSlope_nonpos (log ‖y‖)
    have h3 := exp_pos (-2 * torpedoProfile (log ‖y‖))
    have h4 : 0 ≤ (finrank ℝ F - 1 : ℝ) := by linarith
    have h5 : 0 ≤ (finrank ℝ F - 2 : ℝ) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg h4 h5),
      mul_nonneg h4 (mul_nonneg h3.le (neg_nonneg.2 h2))]
  -- It extends to the centre by continuity, since the punctured space is dense.
  have : Nontrivial F := Module.nontrivial_of_finrank_pos (lt_of_lt_of_le (by norm_num) hn)
  have hclosed := isClosed_le (f := fun _ : F ↦ (finrank ℝ F - 1 : ℝ) * (finrank ℝ F - 2) * c)
    continuous_const (torpedoMetric F).continuous_scalarCurvature
  intro y
  have hy : y ∈ closure ({0}ᶜ : Set F) := by rw [closure_compl_singleton]; trivial
  exact hclosed.closure_subset_iff.2 (fun z hz ↦ hne z hz) hy

/-- **The torpedo metric has positive scalar curvature** in dimension `n ≥ 3`. -/
theorem hasPositiveScalarCurvature_torpedoMetric (hn : 3 ≤ finrank ℝ F) :
    (torpedoMetric F).HasPositiveScalarCurvature := by
  obtain ⟨c, hc, hle⟩ := exists_pos_le_scalarCurvature_torpedoMetric hn
  exact (ContMDiffRiemannianMetric.hasPositiveScalarCurvature_iff _).2 fun y ↦ hc.trans_le (hle y)

end ScalarCurvature

end TauCeti
