/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Cylinder
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Distance
public import TauCeti.Geometry.RicciFlow.StandardCap.PuncturedMetric
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import TauCeti.Analysis.Normed.Operator.Coercive
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.Riemannian.Coercive
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Restriction
import TauCeti.Geometry.Manifold.Riemannian.MetricBridge
import TauCeti.Geometry.Manifold.Riemannian.Restriction.Real
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Topology.EMetricSpace.LocalComparison
import TauCeti.Topology.VectorBundle.Riemannian.Basic

/-!
# The complete smooth standard cap metric

Let `f : ℝ → ℝ` be a standard cap profile (`TauCeti.IsStandardCapProfile f`) and `V` a real inner
product space. Away from the origin, writing `r = ‖x‖` and decomposing a tangent vector `v ∈ V`
into its radial component `(⟪x, v⟫ / r²) x` and its spherical component `v - (⟪x, v⟫ / r²) x`, the
warped-product metric `dr² + f(r)² g_(Sⁿ)` takes the global Cartesian form

`g_x(v, w) = (f ‖x‖ / ‖x‖)² ⟪v, w⟫ + ((1 - (f ‖x‖ / ‖x‖)²) / ‖x‖²) ⟪x, v⟫ ⟪x, w⟫`,

extended to the Euclidean inner product `⟪v, w⟫` at `x = 0`. Because `f(r) = 2 sin (r / 2)` near
`0`, both radial coefficients `(2 sin (r / 2) / r)²` and `(1 - (2 sin (r / 2) / r)²) / r²` are
analytic functions of `s = r² = ‖x‖²` near `s = 0` (constructed via `dslope` from the even power
series `∑ (-1)^k s^k / (2k)!` of `cos √s`), so `g` extends smoothly across the tip `0 ∈ V`.

From the concavity and unit-slope bounds of `f` on `[0, ∞)` we prove:

* `g_x(v, v) ≤ ‖v‖²` everywhere, `(f B / B)² ‖v‖² ≤ g_x(v, v)` on `{‖x‖ ≤ B}`, and the radial
  escape lower bound `⟪x, v⟫² / (1 + ‖x‖²) ≤ g_x(v, v)`;
* polar coordinates `(r, u) ↦ r • u` define a smooth Riemannian isometry from
  `hf.puncturedMetric V` on `(0, ∞) × Sⁿ` onto the restriction of `hf.metric V` to `V ∖ {0}`;
* on a finite-dimensional space `V`, `WithMetric (hf.metric V)` is complete for its Riemannian
  extended metric and ordinary metric, hence geodesically complete at every point (despite the
  angular decay `g_x(v, v) = (2 / ‖x‖²) ‖v‖² → 0` on the cylindrical end, where uniform Euclidean
  coercivity fails);
* every tangent two-plane on `V` (including at the tip `0`) has nonnegative sectional curvature,
  constant sectional curvature `1 / 4` near `0`, nonnegative scalar curvature everywhere, scalar
  curvature `d (d - 1) / 4` near `0` (`3 / 2` in dimension `3`), and scalar curvature
  `(d - 1) (d - 2) / 2` on the cylindrical end (`1` in dimension `3`);
* conversely, if a continuous Riemannian metric on `V` pulls back along `u ↦ r • u` on concentric
  spheres `Sⁿ` (`n > 0`) to `f(r)² g_(Sⁿ)` for small `r > 0`, then `|f(r)| → 0` as `r → 0⁺`, so a
  profile with `f(0) > 0` cannot describe a continuous metric across the tip.

## Main definitions

* `TauCeti.IsStandardCapProfile.metric`: the smooth standard cap Riemannian metric on `V`.
* `TauCeti.radialSphereDiffeomorph`: polar coordinates `(r, u) ↦ r • u` as a diffeomorphism from
  `(0, ∞) × Sⁿ` onto `V ∖ {0}`.
* `TauCeti.IsStandardCapProfile.polarRiemannianIsometry`: polar coordinates as a Riemannian
  isometry from `hf.puncturedMetric V` onto the punctured standard cap metric on `V ∖ {0}`.

## Main results

* `TauCeti.IsStandardCapProfile.completeSpace_withMetric`,
  `TauCeti.IsStandardCapProfile.completeSpace_withMetric_metricSpace`,
  `TauCeti.IsStandardCapProfile.isGeodesicallyCompleteAt_withMetric`: metric and geodesic
  completeness of the standard cap.
* `TauCeti.IsStandardCapProfile.sectionalCurvature_withMetric_nonneg`,
  `TauCeti.IsStandardCapProfile.exists_hasSectionalCurvatureAt_withMetric_round`: global
  nonnegative sectional curvature and constant sectional curvature `1 / 4` near the tip.
* `TauCeti.IsStandardCapProfile.scalarCurvature_metric_nonneg`,
  `TauCeti.IsStandardCapProfile.exists_scalarCurvature_metric_eq_round`,
  `TauCeti.IsStandardCapProfile.exists_scalarCurvature_metric_eq_cylinder`: global scalar curvature
  bounds and round-tip / cylindrical-end values, with three-dimensional specializations and
  `TauCeti.exists_standardCapMetric`.
* `TauCeti.tendsto_abs_of_spherical_pullback`, `TauCeti.eq_zero_of_spherical_pullback`: the
  tip-obstruction theorem ruling out `f(0) > 0` in dimension at least `2`.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Clay Mathematics Monographs 3
  (2007), Definition 12.1.
* G. Perelman, *Ricci flow with surgery on three-manifolds*, arXiv:math/0303109 (2003), §2.
* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171 (2016), §1.4.4 (smoothness of
  rotationally symmetric metrics at the origin).
-/

public noncomputable section

open Bundle CovariantDerivative Filter Manifold Metric Module Real Set TopologicalSpace
open scoped ContDiff ENNReal InnerProductSpace Manifold Matrix NNReal Topology

namespace TauCeti

/-! ### Secant bounds for standard cap profiles -/

namespace IsStandardCapProfile

variable {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
include hf

/-- Because `f(0) = 0` and `f' ≤ 1` on `[0, ∞)`, a standard cap profile satisfies `f(r) ≤ r` for
`r ≥ 0`. -/
theorem apply_le_self {r : ℝ} (hr : 0 ≤ r) : f r ≤ r := by
  have hmono : MonotoneOn (id - f) (Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (continuous_id.sub hf.contDiff.continuous).continuousOn
      (differentiable_id.sub hf.differentiable).differentiableOn fun s hs ↦ by
        rw [deriv_sub differentiableAt_id (hf.differentiable s), deriv_id]
        linarith [hf.deriv_le_one (interior_subset hs)]
  have h0 := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hr) hr
  simp only [Pi.sub_apply, id_eq, hf.apply_zero, sub_self] at h0
  linarith

/-- Concavity of `f` on `[0, ∞)` and `f(0) = 0` make the secant ratio `r ↦ f(r) / r` antitone on
`(0, ∞)`. -/
theorem antitoneOn_div_self : AntitoneOn (fun r ↦ f r / r) (Ioi 0) := by
  intro a ha b hb hab
  have hsec := hf.concaveOn.neg.secant_mono (a := 0) (x := a) (y := b) (mem_Ici.2 le_rfl)
    (mem_Ici.2 ha.le) (mem_Ici.2 hb.le) ha.ne' hb.ne' hab
  simp only [Pi.neg_apply, hf.apply_zero, neg_zero, sub_zero, neg_div] at hsec
  linarith

/-- Away from `0`, the secant ratio `f(r) / r` is positive. -/
theorem div_self_pos {r : ℝ} (hr : r ≠ 0) : 0 < f r / r := by
  rcases lt_or_gt_of_ne hr with hlt | hgt
  · have hodd : f r / r = f (-r) / (-r) := by
      have h := hf.odd (-r)
      rw [neg_neg] at h
      rw [h]
      ring
    rw [hodd]
    exact div_pos (hf.apply_pos (neg_pos.2 hlt)) (neg_pos.2 hlt)
  · exact div_pos (hf.apply_pos hgt) hgt

/-- Everywhere on `ℝ`, the secant ratio `f(r) / r` is at most one. -/
theorem div_self_le_one (r : ℝ) : f r / r ≤ 1 := by
  rcases lt_trichotomy r 0 with hlt | rfl | hgt
  · have hodd : f r / r = f (-r) / (-r) := by
      have h := hf.odd (-r)
      rw [neg_neg] at h
      rw [h]
      ring
    rw [hodd]
    exact (div_le_one (neg_pos.2 hlt)).2 (hf.apply_le_self (neg_pos.2 hlt).le)
  · simp
  · exact (div_le_one hgt).2 (hf.apply_le_self hgt.le)

end IsStandardCapProfile

/-! ### Analytic difference quotients at the tip -/

/-- The formal power series `∑ (-1)^k s^k / (2k)!`, whose sum at `r²` is `cos r`. -/
private def evenCosSeries : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ fun k ↦ (-1 : ℝ) ^ k / (2 * k).factorial

private theorem evenCosSeries_radius : evenCosSeries.radius = ⊤ := by
  refine evenCosSeries.radius_eq_top_of_summable_norm fun r ↦ ?_
  have hcosh := (Real.hasSum_cosh √(r : ℝ)).summable
  refine hcosh.congr fun k ↦ ?_
  rw [evenCosSeries, FormalMultilinearSeries.ofScalars_norm, norm_div, norm_pow, norm_neg,
    norm_one, one_pow, Real.norm_natCast, pow_mul, Real.sq_sqrt r.coe_nonneg]
  ring

private theorem analyticAt_evenCosSeries_sum : AnalyticAt ℝ evenCosSeries.sum 0 :=
  (evenCosSeries.hasFPowerSeriesOnBall
    (by rw [evenCosSeries_radius]; exact ENNReal.zero_lt_top)).hasFPowerSeriesAt.analyticAt

private theorem evenCosSeries_sum_sq (r : ℝ) : evenCosSeries.sum (r ^ 2) = cos r := by
  change FormalMultilinearSeries.ofScalarsSum _ (r ^ 2) = cos r
  rw [FormalMultilinearSeries.ofScalars_sum_eq, Real.cos_eq_tsum r]
  refine tsum_congr fun k ↦ ?_
  rw [smul_eq_mul, ← pow_mul]
  ring

/-- The analytic difference quotient `s ↦ 2 (1 - evenCosSeries.sum s) / s`, equal to
`(2 sin (r / 2) / r)²` at `s = r²`. -/
private def evenSinSqQuot : ℝ → ℝ :=
  dslope (fun s : ℝ ↦ 2 * (1 - evenCosSeries.sum s)) 0

private theorem analyticAt_evenSinSqQuot : AnalyticAt ℝ evenSinSqQuot 0 :=
  (analyticAt_const.mul (analyticAt_const.sub analyticAt_evenCosSeries_sum)).dslope 0

private theorem evenSinSqQuot_sq_of_ne_zero {r : ℝ} (hr : r ≠ 0) :
    evenSinSqQuot (r ^ 2) = (2 * sin (r / 2) / r) ^ 2 := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have h0 : evenCosSeries.sum 0 = 1 := by simpa using evenCosSeries_sum_sq 0
  have hcos : cos r = cos (2 * (r / 2)) := by ring_nf
  have htrig : 2 * (1 - cos r) = (2 * sin (r / 2)) ^ 2 := by
    rw [hcos, cos_two_mul', cos_sq']
    ring
  rw [evenSinSqQuot, dslope_of_ne _ hr2, slope_def_field, h0, sub_self, mul_zero, sub_zero,
    sub_zero, evenCosSeries_sum_sq, htrig, div_pow]

private theorem evenSinSqQuot_zero : evenSinSqQuot 0 = 1 := by
  have hcont : ContinuousAt (fun r : ℝ ↦ evenSinSqQuot (r ^ 2)) 0 :=
    ContinuousAt.comp (g := evenSinSqQuot) (f := fun r : ℝ ↦ r ^ 2)
      (by simpa using analyticAt_evenSinSqQuot.continuousAt) (continuous_pow 2).continuousAt
  have hsinc : ContinuousAt (fun r : ℝ ↦ sinc (r / 2) ^ 2) 0 :=
    ((continuous_sinc.comp (continuous_id.div_const 2)).pow 2).continuousAt
  have heq : ∀ᶠ r in 𝓝[≠] (0 : ℝ), evenSinSqQuot (r ^ 2) = sinc (r / 2) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [evenSinSqQuot_sq_of_ne_zero hr, sinc_of_ne_zero (div_ne_zero hr two_ne_zero)]
    congr 1
    field_simp [hr]
  have h1 := (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' heq
  have h2 : Tendsto (fun r : ℝ ↦ sinc (r / 2) ^ 2) (𝓝[≠] 0) (𝓝 1) := by
    simpa using hsinc.tendsto.mono_left nhdsWithin_le_nhds
  simpa using tendsto_nhds_unique h1 h2

/-- The second analytic difference quotient `s ↦ (1 - evenSinSqQuot s) / s`, equal to
`(1 - (2 sin (r / 2) / r)²) / r²` at `s = r²` (`r ≠ 0`). -/
private def evenRadialQuot : ℝ → ℝ :=
  dslope (fun s : ℝ ↦ 1 - evenSinSqQuot s) 0

private theorem analyticAt_evenRadialQuot : AnalyticAt ℝ evenRadialQuot 0 :=
  (analyticAt_const.sub analyticAt_evenSinSqQuot).dslope 0

private theorem evenRadialQuot_sq_of_ne_zero {r : ℝ} (hr : r ≠ 0) :
    evenRadialQuot (r ^ 2) = (1 - (2 * sin (r / 2) / r) ^ 2) / r ^ 2 := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  rw [evenRadialQuot, dslope_of_ne _ hr2, slope_def_field, evenSinSqQuot_zero, sub_self, sub_zero,
    sub_zero, evenSinSqQuot_sq_of_ne_zero hr]

/-! ### The Cartesian bilinear form of the standard cap -/

section BilinForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

open Classical in
private def capAngularCoeff (f : ℝ → ℝ) (x : V) : ℝ :=
  if x = 0 then 1 else (f ‖x‖ / ‖x‖) ^ 2

open Classical in
private def capRadialCoeff (f : ℝ → ℝ) (x : V) : ℝ :=
  if x = 0 then evenRadialQuot 0 else (1 - (f ‖x‖ / ‖x‖) ^ 2) / ‖x‖ ^ 2

private theorem contDiff_capAngularCoeff {f : ℝ → ℝ} (hf : IsStandardCapProfile f) :
    ContDiff ℝ ∞ (capAngularCoeff f : V → ℝ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · obtain ⟨r₀, hr₀, hsin⟩ := hf.exists_eq_two_mul_sin
    have hev : (capAngularCoeff f : V → ℝ) =ᶠ[𝓝 0] fun y ↦ evenSinSqQuot (‖y‖ ^ 2) := by
      filter_upwards [Metric.ball_mem_nhds (0 : V) hr₀] with y hy
      rcases eq_or_ne y 0 with rfl | hy0
      · simp [capAngularCoeff, evenSinSqQuot_zero]
      · simp only [capAngularCoeff, hy0, ↓reduceIte]
        rw [hsin ‖y‖ ⟨norm_nonneg y, by simpa using hy⟩,
          evenSinSqQuot_sq_of_ne_zero (norm_ne_zero_iff.2 hy0)]
    have h0 : ContDiffAt ℝ ∞ (fun y : V ↦ evenSinSqQuot (‖y‖ ^ 2)) 0 := by
      have hsq : ‖(0 : V)‖ ^ 2 = 0 := by simp
      exact (hsq ▸ analyticAt_evenSinSqQuot.contDiffAt).comp 0 (contDiff_norm_sq ℝ).contDiffAt
    exact h0.congr_of_eventuallyEq hev
  · have hev : (capAngularCoeff f : V → ℝ) =ᶠ[𝓝 x] fun y ↦ (f ‖y‖ / ‖y‖) ^ 2 := by
      filter_upwards [isOpen_ne.mem_nhds hx] with y hy
      simp [capAngularCoeff, hy]
    have hnorm : ContDiffAt ℝ ∞ (fun y : V ↦ ‖y‖) x := contDiffAt_norm ℝ hx
    exact (((hf.contDiff.contDiffAt.comp x hnorm).div hnorm
      (norm_ne_zero_iff.2 hx)).pow 2).congr_of_eventuallyEq hev

private theorem contDiff_capRadialCoeff {f : ℝ → ℝ} (hf : IsStandardCapProfile f) :
    ContDiff ℝ ∞ (capRadialCoeff f : V → ℝ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · obtain ⟨r₀, hr₀, hsin⟩ := hf.exists_eq_two_mul_sin
    have hev : (capRadialCoeff f : V → ℝ) =ᶠ[𝓝 0] fun y ↦ evenRadialQuot (‖y‖ ^ 2) := by
      filter_upwards [Metric.ball_mem_nhds (0 : V) hr₀] with y hy
      rcases eq_or_ne y 0 with rfl | hy0
      · simp [capRadialCoeff]
      · simp only [capRadialCoeff, hy0, ↓reduceIte]
        rw [hsin ‖y‖ ⟨norm_nonneg y, by simpa using hy⟩,
          evenRadialQuot_sq_of_ne_zero (norm_ne_zero_iff.2 hy0)]
    have h0 : ContDiffAt ℝ ∞ (fun y : V ↦ evenRadialQuot (‖y‖ ^ 2)) 0 := by
      have hsq : ‖(0 : V)‖ ^ 2 = 0 := by simp
      exact (hsq ▸ analyticAt_evenRadialQuot.contDiffAt).comp 0 (contDiff_norm_sq ℝ).contDiffAt
    exact h0.congr_of_eventuallyEq hev
  · have hev : (capRadialCoeff f : V → ℝ) =ᶠ[𝓝 x]
        fun y ↦ (1 - (f ‖y‖ / ‖y‖) ^ 2) / ‖y‖ ^ 2 := by
      filter_upwards [isOpen_ne.mem_nhds hx] with y hy
      simp [capRadialCoeff, hy]
    have hnorm : ContDiffAt ℝ ∞ (fun y : V ↦ ‖y‖) x := contDiffAt_norm ℝ hx
    have hne := norm_ne_zero_iff.2 hx
    have hquot := ((hf.contDiff.contDiffAt.comp x hnorm).div hnorm hne).pow 2
    exact ((contDiffAt_const.sub hquot).div (hnorm.pow 2)
      (pow_ne_zero 2 hne)).congr_of_eventuallyEq hev

private def realInnerCLM (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    V →L[ℝ] V →L[ℝ] ℝ :=
  innerSL ℝ

@[simp]
private theorem realInnerCLM_apply (x y : V) : realInnerCLM V x y = ⟪x, y⟫_ℝ :=
  (rfl)

private def capBilinForm (f : ℝ → ℝ) (x : V) : V →L[ℝ] V →L[ℝ] ℝ :=
  capAngularCoeff f x • realInnerCLM V +
    capRadialCoeff f x • (realInnerCLM V x).smulRight (realInnerCLM V x)

private theorem capBilinForm_apply (f : ℝ → ℝ) (x v w : V) :
    capBilinForm f x v w =
      capAngularCoeff f x * ⟪v, w⟫_ℝ + capRadialCoeff f x * (⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ) := by
  simp [capBilinForm, mul_comm ⟪x, v⟫_ℝ ⟪x, w⟫_ℝ]

private theorem contDiff_capBilinForm {f : ℝ → ℝ} (hf : IsStandardCapProfile f) :
    ContDiff ℝ ∞ (capBilinForm f : V → V →L[ℝ] V →L[ℝ] ℝ) := by
  let _ : NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
  let _ : NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
  let _ : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
  let _ : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
  have hinner : ContDiff ℝ ∞ (fun x : V ↦ realInnerCLM V x) := (realInnerCLM V).contDiff
  exact ((contDiff_capAngularCoeff hf).smul contDiff_const).add
    ((contDiff_capRadialCoeff hf).smul (hinner.smulRight hinner))

private theorem capBilinForm_symm (f : ℝ → ℝ) (x v w : V) :
    capBilinForm f x v w = capBilinForm f x w v := by
  rw [capBilinForm_apply, capBilinForm_apply, real_inner_comm w v, mul_comm ⟪x, w⟫_ℝ ⟪x, v⟫_ℝ]

/-- Orthogonal decomposition of the quadratic form `capBilinForm f x v v` away from `0`. -/
private theorem capBilinForm_self_of_ne_zero (f : ℝ → ℝ) {x : V} (hx : x ≠ 0) (v : V) :
    capBilinForm f x v v =
      (f ‖x‖ / ‖x‖) ^ 2 * (‖v‖ ^ 2 - ⟪x, v⟫_ℝ ^ 2 / ‖x‖ ^ 2) + ⟪x, v⟫_ℝ ^ 2 / ‖x‖ ^ 2 := by
  have hne : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hx)
  rw [capBilinForm_apply]
  simp only [capAngularCoeff, capRadialCoeff, hx, ↓reduceIte, real_inner_self_eq_norm_sq]
  field_simp [hne]
  ring

private theorem sq_inner_div_norm_sq_le (x v : V) : ⟪x, v⟫_ℝ ^ 2 / ‖x‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [div_le_iff₀' (pow_pos (norm_pos_iff.2 hx) 2), ← mul_pow]
    exact sq_le_sq.2 ((abs_real_inner_le_norm x v).trans_eq
      (abs_of_nonneg (mul_nonneg (norm_nonneg x) (norm_nonneg v))).symm)

private theorem capBilinForm_self_le {f : ℝ → ℝ} (hf : IsStandardCapProfile f) (x v : V) :
    capBilinForm f x v v ≤ ‖v‖ ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [capBilinForm_apply, capAngularCoeff]
  · have hq : (f ‖x‖ / ‖x‖) ^ 2 ≤ 1 := by
      have h0 := (hf.div_self_pos (norm_ne_zero_iff.2 hx)).le
      have h1 := hf.div_self_le_one ‖x‖
      nlinarith
    have hcs : 0 ≤ ‖v‖ ^ 2 - ⟪x, v⟫_ℝ ^ 2 / ‖x‖ ^ 2 := sub_nonneg.2 (sq_inner_div_norm_sq_le x v)
    rw [capBilinForm_self_of_ne_zero f hx v]
    nlinarith

private theorem sq_div_self_mul_le_capBilinForm_self {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
    {x : V} (hx : x ≠ 0) (v : V) :
    (f ‖x‖ / ‖x‖) ^ 2 * ‖v‖ ^ 2 ≤ capBilinForm f x v v := by
  have hq : (f ‖x‖ / ‖x‖) ^ 2 ≤ 1 := by
    have h0 := (hf.div_self_pos (norm_ne_zero_iff.2 hx)).le
    have h1 := hf.div_self_le_one ‖x‖
    nlinarith
  have hrad : 0 ≤ ⟪x, v⟫_ℝ ^ 2 / ‖x‖ ^ 2 := by positivity
  rw [capBilinForm_self_of_ne_zero f hx v]
  nlinarith

private theorem isCoercive_capBilinForm {f : ℝ → ℝ} (hf : IsStandardCapProfile f) (x : V) :
    IsCoercive (capBilinForm f x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · refine ⟨1, one_pos, fun v ↦ ?_⟩
    simp [capBilinForm_apply, capAngularCoeff, sq]
  · refine ⟨(f ‖x‖ / ‖x‖) ^ 2, sq_pos_of_pos (hf.div_self_pos (norm_ne_zero_iff.2 hx)), fun v ↦ ?_⟩
    simpa only [sq, mul_assoc] using sq_div_self_mul_le_capBilinForm_self hf hx v

private theorem le_capBilinForm_self_of_norm_le {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
    {B : ℝ} {x : V} (hx : ‖x‖ ≤ B) (v : V) :
    (f B / B) ^ 2 * ‖v‖ ^ 2 ≤ capBilinForm f x v v := by
  have hB0 : 0 ≤ B := (norm_nonneg x).trans hx
  rcases eq_or_lt_of_le hB0 with rfl | hB
  · have hx0 : x = 0 := norm_le_zero_iff.1 hx
    subst hx0
    simp [capBilinForm_apply, capAngularCoeff]
  · rcases eq_or_ne x 0 with rfl | hx0
    · have hq : (f B / B) ^ 2 ≤ 1 := by
        have h0 := (hf.div_self_pos hB.ne').le
        have h1 := hf.div_self_le_one B
        nlinarith
      simp only [capBilinForm_apply, capAngularCoeff, ↓reduceIte, inner_zero_left, mul_zero,
        add_zero, real_inner_self_eq_norm_sq, one_mul]
      nlinarith [sq_nonneg ‖v‖]
    · have hpos := norm_pos_iff.2 hx0
      have hanti := hf.antitoneOn_div_self (mem_Ioi.2 hpos) (mem_Ioi.2 hB) hx
      have hsq : (f B / B) ^ 2 ≤ (f ‖x‖ / ‖x‖) ^ 2 :=
        pow_le_pow_left₀ (hf.div_self_pos hB.ne').le hanti 2
      exact (mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖v‖)).trans
        (sq_div_self_mul_le_capBilinForm_self hf hx0 v)

private theorem sq_inner_div_le_capBilinForm_self (f : ℝ → ℝ) (x v : V) :
    ⟪x, v⟫_ℝ ^ 2 / (1 + ‖x‖ ^ 2) ≤ capBilinForm f x v v := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [capBilinForm_apply, capAngularCoeff]
  · have hpos : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.2 hx) 2
    have hle : ⟪x, v⟫_ℝ ^ 2 / (1 + ‖x‖ ^ 2) ≤ ⟪x, v⟫_ℝ ^ 2 / ‖x‖ ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) hpos (by linarith)
    have hcs : 0 ≤ ‖v‖ ^ 2 - ⟪x, v⟫_ℝ ^ 2 / ‖x‖ ^ 2 := sub_nonneg.2 (sq_inner_div_norm_sq_le x v)
    rw [capBilinForm_self_of_ne_zero f hx v]
    exact hle.trans (le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) hcs))

end BilinForm

/-! ### The smooth standard cap metric on `V` -/

namespace IsStandardCapProfile

variable {f : ℝ → ℝ} (hf : IsStandardCapProfile f)

/-- The **standard cap metric** on a real inner product space `V` associated to a standard cap
profile `f`: it is Euclidean at `0` and equals `dr² + f(r)² g_(Sⁿ)` in polar coordinates `x = r • u`
away from `0`. -/
def metric (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    ContMDiffRiemannianMetric 𝓘(ℝ, V) ∞ V (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x) :=
  coerciveRiemannianMetric (capBilinForm f) (contDiff_capBilinForm hf) (capBilinForm_symm f)
    (isCoercive_capBilinForm hf)

section Basic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem metric_inner_eq_capBilinForm (x : V) (v w : TangentSpace 𝓘(ℝ, V) x) :
    (hf.metric V).inner x v w =
      capBilinForm f x (NormedSpace.fromTangentSpace x v) (NormedSpace.fromTangentSpace x w) :=
  coerciveRiemannianMetric_inner _ _ _ _ x v w

/-- At the tip `0 ∈ V`, the standard cap metric coincides with the Euclidean inner product of
`V`. -/
@[simp]
theorem metric_inner_zero (v w : TangentSpace 𝓘(ℝ, V) (0 : V)) :
    (hf.metric V).inner 0 v w =
      ⟪NormedSpace.fromTangentSpace (0 : V) v, NormedSpace.fromTangentSpace (0 : V) w⟫_ℝ := by
  rw [hf.metric_inner_eq_capBilinForm, capBilinForm_apply]
  simp [capAngularCoeff]

/-- Away from `0 ∈ V`, the standard cap metric splits into the angular factor `(f ‖x‖ / ‖x‖)²` and
the radial correction `((1 - (f ‖x‖ / ‖x‖)²) / ‖x‖²) ⟪x, ·⟫ ⟪x, ·⟫`. -/
theorem metric_inner_of_ne_zero {x : V} (hx : x ≠ 0) (v w : TangentSpace 𝓘(ℝ, V) x) :
    (hf.metric V).inner x v w =
      (f ‖x‖ / ‖x‖) ^ 2 * ⟪NormedSpace.fromTangentSpace x v, NormedSpace.fromTangentSpace x w⟫_ℝ +
        (1 - (f ‖x‖ / ‖x‖) ^ 2) / ‖x‖ ^ 2 *
          (⟪x, NormedSpace.fromTangentSpace x v⟫_ℝ * ⟪x, NormedSpace.fromTangentSpace x w⟫_ℝ) := by
  rw [hf.metric_inner_eq_capBilinForm, capBilinForm_apply]
  simp [capAngularCoeff, capRadialCoeff, hx]

/-- The standard cap metric is everywhere bounded above by the Euclidean norm squared. -/
theorem metric_inner_self_le (x : V) (v : TangentSpace 𝓘(ℝ, V) x) :
    (hf.metric V).inner x v v ≤ ‖NormedSpace.fromTangentSpace x v‖ ^ 2 := by
  rw [hf.metric_inner_eq_capBilinForm]
  exact capBilinForm_self_le hf x _

/-- On the Euclidean closed ball of radius `B`, the standard cap metric dominates `(f B / B)²`
times the Euclidean norm squared. -/
theorem le_metric_inner_self_of_norm_le {B : ℝ} {x : V} (hx : ‖x‖ ≤ B)
    (v : TangentSpace 𝓘(ℝ, V) x) :
    (f B / B) ^ 2 * ‖NormedSpace.fromTangentSpace x v‖ ^ 2 ≤ (hf.metric V).inner x v v := by
  rw [hf.metric_inner_eq_capBilinForm]
  exact le_capBilinForm_self_of_norm_le hf hx _

/-- The radial component `⟪x, v⟫² / (1 + ‖x‖²)` is globally bounded above by the standard cap
metric, preventing finite-length curves from escaping to infinity. -/
theorem sq_inner_div_le_metric_inner_self (x : V) (v : TangentSpace 𝓘(ℝ, V) x) :
    ⟪x, NormedSpace.fromTangentSpace x v⟫_ℝ ^ 2 / (1 + ‖x‖ ^ 2) ≤ (hf.metric V).inner x v v := by
  rw [hf.metric_inner_eq_capBilinForm]
  exact sq_inner_div_le_capBilinForm_self f x _

end Basic

end IsStandardCapProfile

/-! ### Polar diffeomorphism and Riemannian isometry away from the tip -/

section Polar

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (finrank ℝ V = n + 1)]

/-- **Polar coordinates** `(r, u) ↦ r • u` as a smooth diffeomorphism from
`standardCapRadialDomain × Sⁿ` onto the punctured space `V ∖ {0}`, with inverse
`x ↦ (‖x‖, ‖x‖⁻¹ • x)`. -/
def radialSphereDiffeomorph :
    (standardCapRadialDomain × sphere (0 : V) 1) ≃ₘ⟮𝓘(ℝ).prod (𝓡 n), 𝓘(ℝ, V)⟯ puncturedSpace V where
  toFun p := ⟨(p.1 : ℝ) • (p.2 : V),
    mem_puncturedSpace.2 (smul_ne_zero p.1.property.ne' (ne_zero_of_mem_unit_sphere p.2))⟩
  invFun x := (⟨‖(x : V)‖, norm_pos_iff.2 (mem_puncturedSpace.1 x.2)⟩,
    ⟨‖(x : V)‖⁻¹ • (x : V), by
      simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 (mem_puncturedSpace.1 x.2))]⟩)
  left_inv p := by
    rcases p with ⟨r, u⟩
    have hr : 0 < (r : ℝ) := r.property
    have hu : ‖(u : V)‖ = 1 := norm_eq_of_mem_sphere u
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simp [norm_smul, hu, abs_of_pos hr]
    · simp [norm_smul, hu, abs_of_pos hr, smul_smul, inv_mul_cancel₀ hr.ne']
  right_inv x := by
    have hx : ‖(x : V)‖ ≠ 0 := norm_ne_zero_iff.2 (mem_puncturedSpace.1 x.2)
    exact Subtype.ext (by simp [smul_smul, mul_inv_cancel₀ hx])
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff (puncturedSpace V) _).1 <|
      (contMDiff_subtype_val.comp contMDiff_fst).smul (contMDiff_coe_sphere.comp contMDiff_snd)
  contMDiff_invFun := by
    refine ContMDiff.prodMk ?_ ?_
    · refine (ContMDiff.subtypeVal_comp_iff standardCapRadialDomain _).1 fun x ↦ ?_
      have hx : (x : V) ≠ 0 := mem_puncturedSpace.1 x.2
      exact (contMDiffAt_subtype_iff (f := fun y : V ↦ ‖y‖)).2 (contDiffAt_norm ℝ hx).contMDiffAt
    · refine ContMDiff.codRestrict_sphere (f := fun x : puncturedSpace V ↦ ‖(x : V)‖⁻¹ • (x : V))
        (fun x ↦ (contMDiffAt_subtype_iff (f := fun y : V ↦ ‖y‖⁻¹ • y)).2 ?_) _
      have hx : (x : V) ≠ 0 := mem_puncturedSpace.1 x.2
      exact (((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.2 hx)).smul contDiffAt_id).contMDiffAt

variable {V}

@[simp]
theorem coe_radialSphereDiffeomorph_apply (p : standardCapRadialDomain × sphere (0 : V) 1) :
    (radialSphereDiffeomorph (n := n) V p : V) = (p.1 : ℝ) • (p.2 : V) :=
  (rfl)

@[simp]
theorem radialSphereDiffeomorph_symm_apply_fst (x : puncturedSpace V) :
    ((radialSphereDiffeomorph (n := n) V).symm x).1 =
      ⟨‖(x : V)‖, norm_pos_iff.2 (mem_puncturedSpace.1 x.2)⟩ :=
  (rfl)

@[simp]
theorem coe_radialSphereDiffeomorph_symm_apply_snd (x : puncturedSpace V) :
    (((radialSphereDiffeomorph (n := n) V).symm x).2 : V) = ‖(x : V)‖⁻¹ • (x : V) :=
  (rfl)

/-- The differential of `(r, u) ↦ r • u` on `(0, ∞) × Sⁿ` sends `(a, w)` at `(r, u)` to
`a • u + r • w`. -/
private theorem mvfderiv_radial_smul_coe_sphere_apply
    (p : standardCapRadialDomain × sphere (0 : V) 1)
    (v : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    mvfderiv (𝓘(ℝ).prod (𝓡 n))
        (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) p v =
      (tangentSpaceCastModel 𝓘(ℝ) p.1 (Manifold.tangentSpaceProdEquiv p v).1) • (p.2 : V) +
        (p.1 : ℝ) • mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) p.2
          (Manifold.tangentSpaceProdEquiv p v).2 := by
  have hd₁ : MDifferentiableAt (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ)
      (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ)) p :=
    (contMDiff_subtype_val.mdifferentiable one_ne_zero p.1).comp p mdifferentiableAt_fst
  have hd₂ : MDifferentiableAt (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
      (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.2 : V)) p :=
    ((contMDiff_coe_sphere (E := V) (n := n) (m := 1) p.2).mdifferentiableAt one_ne_zero).comp p
      mdifferentiableAt_snd
  have hsub : mvfderiv 𝓘(ℝ) Subtype.val p.1 (Manifold.tangentSpaceProdEquiv p v).1 =
      tangentSpaceCastModel 𝓘(ℝ) p.1 (Manifold.tangentSpaceProdEquiv p v).1 := by
    rw [Manifold.mvfderiv_subtype_val_apply]
    rfl
  have h₁ : mvfderiv (𝓘(ℝ).prod (𝓡 n))
      (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ)) p v =
      tangentSpaceCastModel 𝓘(ℝ) p.1 (Manifold.tangentSpaceProdEquiv p v).1 := by
    rw [← hsub, Manifold.tangentSpaceProdEquiv_apply]
    exact mvfderiv_comp_fst_apply Subtype.val p v
  have h₂ : mvfderiv (𝓘(ℝ).prod (𝓡 n))
      (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.2 : V)) p v =
      mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) p.2 (Manifold.tangentSpaceProdEquiv p v).2 := by
    rw [Manifold.tangentSpaceProdEquiv_apply]
    exact mvfderiv_comp_snd_apply _ p v
  rw [mvfderiv_fun_smul hd₁ hd₂]
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply, h₁, h₂]
  exact add_comm _ _

end Polar

namespace IsStandardCapProfile

section PolarIsometry

variable {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
  [Fact (finrank ℝ V = n + 1)]

private theorem puncturedMetric_inner_eq_metric_inner_polar
    (p : standardCapRadialDomain × sphere (0 : V) 1)
    (v w : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
    (hf.puncturedMetric (n := n) V).inner p v w =
      (hf.metric V).inner ((p.1 : ℝ) • (p.2 : V))
        (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
          (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) p v)
        (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
          (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) p w) := by
  have hr : 0 < (p.1 : ℝ) := p.1.property
  have hrne : (p.1 : ℝ) ≠ 0 := hr.ne'
  have hu : ‖(p.2 : V)‖ = 1 := norm_eq_of_mem_sphere p.2
  have hu2 : ⟪(p.2 : V), (p.2 : V)⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hx0 : (p.1 : ℝ) • (p.2 : V) ≠ 0 := smul_ne_zero hrne (ne_zero_of_mem_unit_sphere p.2)
  have hnorm : ‖(p.1 : ℝ) • (p.2 : V)‖ = (p.1 : ℝ) := by
    rw [norm_smul, hu, mul_one, Real.norm_of_nonneg hr.le]
  have hdv := mvfderiv_radial_smul_coe_sphere_apply (V := V) p v
  have hdw := mvfderiv_radial_smul_coe_sphere_apply (V := V) p w
  have horth_v := inner_coe_mvfderiv_subtypeVal_sphere p.2 (Manifold.tangentSpaceProdEquiv p v).2
  have horth_w := inner_coe_mvfderiv_subtypeVal_sphere p.2 (Manifold.tangentSpaceProdEquiv p w).2
  have horth_v' : ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) p.2
      (Manifold.tangentSpaceProdEquiv p v).2, (p.2 : V)⟫_ℝ = 0 := by rwa [real_inner_comm]
  have hfv : NormedSpace.fromTangentSpace ((p.1 : ℝ) • (p.2 : V))
      (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
        (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) p v) =
      mvfderiv (𝓘(ℝ).prod (𝓡 n))
        (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) p v := rfl
  have hfw : NormedSpace.fromTangentSpace ((p.1 : ℝ) • (p.2 : V))
      (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
        (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) p w) =
      mvfderiv (𝓘(ℝ).prod (𝓡 n))
        (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) p w := rfl
  rw [hf.puncturedMetric_inner, Manifold.inner_restrictOpenTangentSpace_real,
    ContMDiffRiemannianMetric.ofLE_inner, sphereRoundMetric_inner,
    hf.metric_inner_of_ne_zero hx0, hfv, hfw, hdv, hdw, hnorm]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    horth_v, horth_w, horth_v', hu2, mul_zero, zero_add, add_zero, mul_one]
  field_simp [hrne]
  ring

/-- The warped-product punctured metric `dr² + f(r)² g_(Sⁿ)` is the pullback along polar
coordinates `radialSphereDiffeomorph V` of the standard cap metric restricted to `V ∖ {0}`. -/
theorem puncturedMetric_eq_pullback :
    hf.puncturedMetric (n := n) V =
      ((hf.metric V).restrictOpenTangentSpace (puncturedSpace V)).pullback
        (radialSphereDiffeomorph (n := n) V)
        ((radialSphereDiffeomorph (n := n) V).contMDiff.of_le (by simp))
        (fun _ ↦
          ((radialSphereDiffeomorph (n := n) V).isInvertible_mfderiv (by simp)).injective) := by
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
  ext p v w
  have hdf (z : TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :
      Manifold.tangentSpaceOpenEquiv (radialSphereDiffeomorph (n := n) V p)
          (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V) (radialSphereDiffeomorph (n := n) V) p z) =
        mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
          (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ (q.1 : ℝ) • (q.2 : V)) p z := by
    change Manifold.tangentSpaceOpenEquiv (radialSphereDiffeomorph (n := n) V p)
        (mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V) (radialSphereDiffeomorph (n := n) V) p z) =
      mfderiv (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
        ((Subtype.val : puncturedSpace V → V) ∘ radialSphereDiffeomorph (n := n) V) p z
    rw [mfderiv_comp_apply p ((contMDiff_subtype_val (n := 1)).mdifferentiableAt one_ne_zero)
      ((radialSphereDiffeomorph (n := n) V).contMDiff.mdifferentiableAt (by simp)),
      Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe]
  rw [ContMDiffRiemannianMetric.pullback_inner,
    ContMDiffRiemannianMetric.restrictOpenTangentSpace_inner, hdf v, hdf w]
  exact hf.puncturedMetric_inner_eq_metric_inner_polar V p v w

/-- **Polar coordinates are a Riemannian isometry** from `hf.puncturedMetric V` on `(0, ∞) × Sⁿ`
onto the standard cap metric restricted to the punctured space `V ∖ {0}`. -/
def polarRiemannianIsometry :
    letI : RiemannianBundle
      (fun p : standardCapRadialDomain × sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :=
      ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : puncturedSpace V ↦ TangentSpace 𝓘(ℝ, V) x) :=
      ⟨((hf.metric V).restrictOpenTangentSpace (puncturedSpace V)).toRiemannianMetric⟩
    RiemannianIsometry (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
      (standardCapRadialDomain × sphere (0 : V) 1) (puncturedSpace V) :=
  letI : RiemannianBundle
    (fun p : standardCapRadialDomain × sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) p) :=
    ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
  letI : RiemannianBundle (fun x : puncturedSpace V ↦ TangentSpace 𝓘(ℝ, V) x) :=
    ⟨((hf.metric V).restrictOpenTangentSpace (puncturedSpace V)).toRiemannianMetric⟩
  { toDiffeomorph := radialSphereDiffeomorph (n := n) V
    inner_mfderiv' := fun p v w ↦ by
      have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
      change ((hf.metric V).restrictOpenTangentSpace (puncturedSpace V)).inner _ _ _ =
        (hf.puncturedMetric (n := n) V).inner p v w
      rw [hf.puncturedMetric_eq_pullback V, ContMDiffRiemannianMetric.pullback_inner] }

@[simp]
theorem coe_polarRiemannianIsometry (p : standardCapRadialDomain × sphere (0 : V) 1) :
    letI : RiemannianBundle
      (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : puncturedSpace V ↦ TangentSpace 𝓘(ℝ, V) x) :=
      ⟨((hf.metric V).restrictOpenTangentSpace (puncturedSpace V)).toRiemannianMetric⟩
    (hf.polarRiemannianIsometry (n := n) V p : V) = (p.1 : ℝ) • (p.2 : V) :=
  (rfl)

/-- Polar coordinates composed with `toWithMetric` form a local Riemannian isometry from
`hf.puncturedMetric V` directly into `WithMetric (hf.metric V)`. -/
private theorem isLocalRiemannianIsometry_toWithMetric_polar :
    letI : RiemannianBundle
      (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
      ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    letI : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
    IsLocalRiemannianIsometry (𝓘(ℝ).prod (𝓡 n)) 𝓘(ℝ, V)
      (fun p : standardCapRadialDomain × sphere (0 : V) 1 ↦
        WithMetric.toWithMetric (hf.metric V) ((p.1 : ℝ) • (p.2 : V))) := by
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
  let _ : RiemannianBundle
    (fun q : standardCapRadialDomain × sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) q) :=
    ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
  let _ : RiemannianBundle (fun x : puncturedSpace V ↦ TangentSpace 𝓘(ℝ, V) x) :=
    ⟨((hf.metric V).restrictOpenTangentSpace (puncturedSpace V)).toRiemannianMetric⟩
  let _ : RiemannianBundle (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x) :=
    ⟨(hf.metric V).toRiemannianMetric⟩
  have hto : IsLocalRiemannianIsometry 𝓘(ℝ, V) 𝓘(ℝ, V) (WithMetric.toWithMetric (hf.metric V)) :=
    { contMDiff := WithMetric.contMDiff_toWithMetric
      isInvertible_mfderiv := fun x ↦ by
        rw [WithMetric.mfderiv_toWithMetric]
        exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
      inner_mfderiv := fun x v w ↦ by
        rw [WithMetric.inner_def, WithMetric.ofWithMetric_toWithMetric,
          WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric,
          WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric]
        rfl }
  exact hto.comp (((hf.metric V).isLocalRiemannianIsometry_restrictOpenTangentSpace
    (puncturedSpace V)).comp (hf.polarRiemannianIsometry (n := n) V).isLocalRiemannianIsometry)

end PolarIsometry

/-! ### Metric and geodesic completeness of the standard cap -/

section Completeness

variable {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
include hf

/-- Because `g_x(v, v) ≤ ‖v‖²` everywhere, the Riemannian extended distance on
`WithMetric (hf.metric V)` is at most the Euclidean extended distance on `V`. -/
theorem riemannianEDist_toWithMetric_le (x y : V) :
    Manifold.riemannianEDist 𝓘(ℝ, V)
      (WithMetric.toWithMetric (hf.metric V) x)
      (WithMetric.toWithMetric (hf.metric V) y) ≤ edist x y := by
  rw [IsRiemannianManifold.out (I := 𝓘(ℝ, V)) x y,
    ← one_mul (Manifold.riemannianEDist 𝓘(ℝ, V) x y), ← ENNReal.coe_one]
  refine TauCeti.Manifold.riemannianEDist_le_mul (C := (1 : NNReal))
    WithMetric.contMDiff_toWithMetric one_ne_zero (fun z v ↦ ?_) x y
  rw [NNReal.coe_one, one_mul]
  have hsq : ‖mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) (WithMetric.toWithMetric (hf.metric V)) z v‖ ^ 2 ≤
      ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, WithMetric.inner_def, WithMetric.ofWithMetric_toWithMetric,
      WithMetric.mfderiv_ofWithMetric_mfderiv_toWithMetric, norm_tangentSpace_vectorSpace]
    exact hf.metric_inner_self_le z v
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

private theorem norm_mvfderiv_japaneseBracket_le (p : WithMetric (hf.metric V))
    (v : TangentSpace 𝓘(ℝ, V) p) :
    ‖mvfderiv 𝓘(ℝ, V)
        (fun q : WithMetric (hf.metric V) ↦ (1 + ‖q.ofWithMetric‖ ^ 2) ^ (1 / 2 : ℝ))
        p v‖ₑ ≤ (1 : ℝ≥0) * ‖v‖ₑ := by
  set ψ : V → ℝ := fun x ↦ (1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)
  have hderiv : ∀ x : V, HasFDerivAt ψ
      (((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)) • realInnerCLM V x) x := fun x ↦ by
    convert (((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_add 1).rpow_const
      (Or.inl (by positivity)) using 1
    ext w
    simp only [_root_.smul_apply, realInnerCLM_apply, innerSL_apply_apply, nsmul_eq_mul,
      Nat.cast_ofNat, smul_eq_mul]
    rw [show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num]
    ring
  rw [ENNReal.coe_one, one_mul, ← ofReal_norm, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  have hmv : mvfderiv 𝓘(ℝ, V) (ψ ∘ WithMetric.ofWithMetric) p v =
      (1 + ‖p.ofWithMetric‖ ^ 2) ^ (-1 / 2 : ℝ) *
        ⟪p.ofWithMetric, NormedSpace.fromTangentSpace p.ofWithMetric
          (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric p v)⟫_ℝ := by
    rw [WithMetric.mvfderiv_comp_ofWithMetric_apply, mvfderiv_eq_fderiv,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      (hderiv p.ofWithMetric).fderiv, _root_.smul_apply, realInnerCLM_apply, smul_eq_mul]
  rw [show (fun q : WithMetric (hf.metric V) ↦ (1 + ‖q.ofWithMetric‖ ^ 2) ^ (1 / 2 : ℝ)) =
    ψ ∘ WithMetric.ofWithMetric from rfl, hmv]
  have hsq : ((1 + ‖p.ofWithMetric‖ ^ 2) ^ (-1 / 2 : ℝ) *
      ⟪p.ofWithMetric, NormedSpace.fromTangentSpace p.ofWithMetric
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric p v)⟫_ℝ) ^ 2 ≤ ‖v‖ ^ 2 := by
    have hrpow : ((1 + ‖p.ofWithMetric‖ ^ 2) ^ (-1 / 2 : ℝ)) ^ 2 =
        (1 + ‖p.ofWithMetric‖ ^ 2)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
      exact Real.rpow_neg_one _
    have hv_sq : ‖v‖ ^ 2 = (hf.metric V).inner p.ofWithMetric
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric p v)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric p v) := by
      rw [← real_inner_self_eq_norm_sq, WithMetric.inner_def]
    rw [mul_pow, hrpow, inv_mul_eq_div, hv_sq]
    exact hf.sq_inner_div_le_metric_inner_self p.ofWithMetric _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (by simpa only [Real.norm_eq_abs, sq_abs] using hsq)

/-- Points at Riemannian extended distance at most `R` from the tip `0` have Euclidean norm at most
`R + 1`. -/
theorem norm_ofWithMetric_le_of_riemannianEDist_le {p : WithMetric (hf.metric V)} {R : ℝ}
    (hR : 0 ≤ R)
    (hp : Manifold.riemannianEDist 𝓘(ℝ, V) p (WithMetric.toWithMetric (hf.metric V) 0) ≤
      ENNReal.ofReal R) :
    ‖p.ofWithMetric‖ ≤ R + 1 := by
  let ψ : WithMetric (hf.metric V) → ℝ := fun q ↦ (1 + ‖q.ofWithMetric‖ ^ 2) ^ (1 / 2 : ℝ)
  have hψ : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, ℝ) 1 ψ :=
    ((contDiff_one_add_norm_sq_rpow (1 / 2 : ℝ)).contMDiff).comp WithMetric.contMDiff_ofWithMetric
  have hed := Manifold.edist_le_mul_riemannianEDist hψ one_ne_zero
    (hf.norm_mvfderiv_japaneseBracket_le) p (WithMetric.toWithMetric (hf.metric V) 0)
  rw [ENNReal.coe_one, one_mul, edist_dist] at hed
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hed.trans hp)
  rw [ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_ofReal hR] at hle
  have h0 : ψ (WithMetric.toWithMetric (hf.metric V) 0) = 1 := by simp [ψ]
  have hp_val : ψ p = √(1 + ‖p.ofWithMetric‖ ^ 2) := (Real.sqrt_eq_rpow _).symm
  rw [Real.dist_eq, h0, hp_val] at hle
  have hsqrt : √(1 + ‖p.ofWithMetric‖ ^ 2) ≤ R + 1 := by linarith [(le_abs_self _).trans hle]
  have hsq : ‖p.ofWithMetric‖ ^ 2 ≤ (R + 1) ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2
    rw [Real.sq_sqrt (by positivity)] at this
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

private theorem norm_mfderiv_ofWithMetric_le_of_norm_le {B : ℝ} (hB : 0 < B)
    {p : WithMetric (hf.metric V)} (hp : ‖p.ofWithMetric‖ ≤ B) (v : TangentSpace 𝓘(ℝ, V) p) :
    letI := normedAddCommGroupTangentSpaceVectorSpace p.ofWithMetric
    ‖mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric p v‖ₑ ≤
      ((B / f B).toNNReal : ℝ≥0∞) * ‖v‖ₑ := by
  let _ := normedAddCommGroupTangentSpaceVectorSpace p.ofWithMetric
  set c : NNReal := (B / f B).toNNReal
  have hc : (c : ℝ) = B / f B := Real.coe_toNNReal _ (div_pos hB (hf.apply_pos hB)).le
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul c.coe_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  have hb := hf.le_metric_inner_self_of_norm_le hp
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric p v)
  have hinv : (c : ℝ) ^ 2 * (f B / B) ^ 2 = 1 := by
    rw [hc]
    field_simp [(hf.apply_pos hB).ne', hB.ne']
  have hnorm_eq : ‖mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric p v‖ =
      ‖NormedSpace.fromTangentSpace p.ofWithMetric
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric p v)‖ := rfl
  have hsq : ‖mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric p v‖ ^ 2 ≤ ((c : ℝ) * ‖v‖) ^ 2 := by
    calc ‖mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric p v‖ ^ 2
        = (c : ℝ) ^ 2 * ((f B / B) ^ 2 *
            ‖NormedSpace.fromTangentSpace p.ofWithMetric
              (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) WithMetric.ofWithMetric p v)‖ ^ 2) := by
          rw [hnorm_eq, ← mul_assoc, hinv, one_mul]
      _ ≤ (c : ℝ) ^ 2 * (hf.metric V).inner p.ofWithMetric _ _ :=
          mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ = ((c : ℝ) * ‖v‖) ^ 2 := by
          rw [mul_pow, ← real_inner_self_eq_norm_sq, WithMetric.inner_def]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg c.coe_nonneg (norm_nonneg _))
    two_ne_zero).1 hsq

/-- Along a short path in `WithMetric (hf.metric V)` starting in `{d₁ · 0 ≤ R}`, the Euclidean
displacement is controlled by `((R + 3) / f (R + 3))` times the Riemannian distance. -/
private theorem edist_ofWithMetric_le_of_riemannianEDist_lt_one (R : NNReal)
    {x y : WithMetric (hf.metric V)}
    (hx : Manifold.riemannianEDist 𝓘(ℝ, V) x (WithMetric.toWithMetric (hf.metric V) 0) ≤ R)
    (hxy : Manifold.riemannianEDist 𝓘(ℝ, V) x y < 1) :
    edist x.ofWithMetric y.ofWithMetric ≤
      ((((R : ℝ) + 3) / f ((R : ℝ) + 3)).toNNReal : ℝ≥0∞) *
        Manifold.riemannianEDist 𝓘(ℝ, V) x y := by
  set B : ℝ := (R : ℝ) + 3
  have hB : 0 < B := by positivity
  set c : NNReal := (B / f B).toNNReal
  have hδ : ∀ δ : ℝ≥0∞, Manifold.riemannianEDist 𝓘(ℝ, V) x y < δ → δ ≤ 1 →
      edist x.ofWithMetric y.ofWithMetric ≤ (c : ℝ≥0∞) * δ := fun δ hyδ hδ1 ↦ by
    obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hyδ
    have hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ‖(γ t).ofWithMetric‖ ≤ B := fun t ht ↦ by
      have hxt : Manifold.riemannianEDist 𝓘(ℝ, V) (γ t) x ≤ 1 := by
        rw [Manifold.riemannianEDist_comm]
        have h1 : Manifold.riemannianEDist 𝓘(ℝ, V) x (γ t) ≤ Manifold.pathELength 𝓘(ℝ, V) γ 0 t :=
          Manifold.riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc_right ht.2)) hγ0 rfl ht.1
        have h2 : Manifold.pathELength 𝓘(ℝ, V) γ 0 t ≤ Manifold.pathELength 𝓘(ℝ, V) γ 0 1 :=
          Manifold.pathELength_mono le_rfl ht.2
        exact (h1.trans h2).trans (hlen.le.trans hδ1)
      have hd : Manifold.riemannianEDist 𝓘(ℝ, V) (γ t)
          (WithMetric.toWithMetric (hf.metric V) 0) ≤ ENNReal.ofReal ((R : ℝ) + 1) := by
        calc Manifold.riemannianEDist 𝓘(ℝ, V) (γ t) (WithMetric.toWithMetric (hf.metric V) 0)
            ≤ Manifold.riemannianEDist 𝓘(ℝ, V) (γ t) x +
                Manifold.riemannianEDist 𝓘(ℝ, V) x (WithMetric.toWithMetric (hf.metric V) 0) :=
              Manifold.riemannianEDist_triangle
          _ ≤ 1 + R := add_le_add hxt hx
          _ = ENNReal.ofReal ((R : ℝ) + 1) := by
              rw [ENNReal.ofReal_add R.coe_nonneg zero_le_one, ENNReal.ofReal_coe_nnreal,
                ENNReal.ofReal_one, add_comm]
      exact (hf.norm_ofWithMetric_le_of_riemannianEDist_le (by positivity) hd).trans (by linarith)
    have key := Manifold.enorm_sub_le_mul_pathELength (f := WithMetric.ofWithMetric) zero_le_one
      (hγ.mdifferentiableOn one_ne_zero) (WithMetric.contMDiff_ofWithMetric.comp_contMDiffOn hγ)
      (fun t _ ↦ WithMetric.contMDiff_ofWithMetric.mdifferentiableAt one_ne_zero) fun t ht ↦
        hf.norm_mfderiv_ofWithMetric_le_of_norm_le hB (hnorm t ht) _
    rw [hγ0, hγ1, ← eDist_eq_eNorm_sub, edist_comm] at key
    exact key.trans (by gcongr)
  have : (𝓝[>] (Manifold.riemannianEDist 𝓘(ℝ, V) x y)).NeBot :=
    nhdsGT_neBot_of_exists_gt ⟨1, hxy⟩
  have hlim : Tendsto (fun δ ↦ (c : ℝ≥0∞) * δ) (𝓝[>] (Manifold.riemannianEDist 𝓘(ℝ, V) x y))
      (𝓝 ((c : ℝ≥0∞) * Manifold.riemannianEDist 𝓘(ℝ, V) x y)) :=
    (ENNReal.Tendsto.const_mul tendsto_id (Or.inr ENNReal.coe_ne_top)).mono_left
      nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hxy] with δ hδmem using hδ δ hδmem.1 hδmem.2.le

/-- **Metric completeness of the standard cap (extended distance).** For a finite-dimensional real
inner product space `V`, `WithMetric (hf.metric V)` is a complete space for
`PseudoEMetricSpace.ofRiemannianMetric`. -/
theorem completeSpace_withMetric :
    letI : PseudoEMetricSpace (WithMetric (hf.metric V)) :=
      .ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
    CompleteSpace (WithMetric (hf.metric V)) := by
  let d₀ : PseudoEMetricSpace (WithMetric (hf.metric V)) :=
    PseudoEMetricSpace.induced (WithMetric.ofWithMetric : WithMetric (hf.metric V) → V)
      inferInstance
  let d₁ : PseudoEMetricSpace (WithMetric (hf.metric V)) :=
    .ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
  have hd₀_complete : @CompleteSpace (WithMetric (hf.metric V)) d₀.toUniformSpace := by
    let _ : UniformSpace (WithMetric (hf.metric V)) := d₀.toUniformSpace
    exact CompleteSpace.of_comp_eq_id (WithMetric.toWithMetric (hf.metric V))
      WithMetric.ofWithMetric rfl WithMetric.continuous_toWithMetric uniformContinuous_comap
  refine PseudoEMetricSpace.completeSpace_of_continuous_local_edist_bound_at_basepoint d₀ d₁
    (WithMetric.toWithMetric (hf.metric V) 0) hd₀_complete continuous_id
    (fun p ↦ ne_top_of_le_ne_top (edist_ne_top p.ofWithMetric 0)
      (hf.riemannianEDist_toWithMetric_le p.ofWithMetric 0)) fun R ↦ ?_
  set c : NNReal := (((R : ℝ) + 3) / f ((R : ℝ) + 3)).toNNReal
  refine ⟨max c (2 * (R + 1)), fun x y hx hy ↦ ?_⟩
  change Manifold.riemannianEDist 𝓘(ℝ, V) x (WithMetric.toWithMetric (hf.metric V) 0) ≤ R at hx
  change Manifold.riemannianEDist 𝓘(ℝ, V) y (WithMetric.toWithMetric (hf.metric V) 0) ≤ R at hy
  change edist x.ofWithMetric y.ofWithMetric ≤
    ((max c (2 * (R + 1)) : NNReal) : ℝ≥0∞) * Manifold.riemannianEDist 𝓘(ℝ, V) x y
  rcases lt_or_ge (Manifold.riemannianEDist 𝓘(ℝ, V) x y) 1 with hxy | hxy
  · exact (hf.edist_ofWithMetric_le_of_riemannianEDist_lt_one R hx hxy).trans
      (by gcongr; exact le_max_left _ _)
  · have hx_norm : ‖x.ofWithMetric‖ ≤ (R : ℝ) + 1 :=
      hf.norm_ofWithMetric_le_of_riemannianEDist_le R.coe_nonneg
        (by simpa [ENNReal.ofReal_coe_nnreal] using hx)
    have hy_norm : ‖y.ofWithMetric‖ ≤ (R : ℝ) + 1 :=
      hf.norm_ofWithMetric_le_of_riemannianEDist_le R.coe_nonneg
        (by simpa [ENNReal.ofReal_coe_nnreal] using hy)
    calc edist x.ofWithMetric y.ofWithMetric
        = ENNReal.ofReal ‖x.ofWithMetric - y.ofWithMetric‖ := by rw [edist_dist, dist_eq_norm]
      _ ≤ ENNReal.ofReal (2 * ((R : ℝ) + 1)) :=
          ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans (by linarith))
      _ = ((2 * (R + 1) : NNReal) : ℝ≥0∞) * 1 := by
          push_cast [ENNReal.ofReal_mul]
          simp [ENNReal.ofReal_add]
      _ ≤ ((max c (2 * (R + 1)) : NNReal) : ℝ≥0∞) * Manifold.riemannianEDist 𝓘(ℝ, V) x y := by
          gcongr
          exact le_max_right _ _

/-- **Metric completeness of the standard cap.** Equipped with its Riemannian `MetricSpace`
structure `MetricSpace.ofRiemannianMetric`, `WithMetric (hf.metric V)` is a complete metric
space. -/
theorem completeSpace_withMetric_metricSpace :
    letI : MetricSpace (WithMetric (hf.metric V)) :=
      MetricSpace.ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
    CompleteSpace (WithMetric (hf.metric V)) :=
  hf.completeSpace_withMetric

/-- **Geodesic completeness of the standard cap.** Every maximal geodesic of `hf.metric V` on a
finite-dimensional real inner product space `V` is defined on all of `ℝ`. -/
theorem isGeodesicallyCompleteAt_withMetric (p : WithMetric (hf.metric V)) :
    Manifold.IsGeodesicallyCompleteAt 𝓘(ℝ, V) (WithMetric (hf.metric V)) p := by
  let _ : MetricSpace (WithMetric (hf.metric V)) :=
    MetricSpace.ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V))
  have : CompleteSpace (WithMetric (hf.metric V)) := hf.completeSpace_withMetric_metricSpace
  exact Manifold.isGeodesicallyCompleteAt_of_completeSpace p

end Completeness

/-! ### Global sectional and scalar curvature of the standard cap -/

section Curvature

variable {f : ℝ → ℝ} (hf : IsStandardCapProfile f)
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
include hf

private theorem sectionalCurvature_withMetric_of_ne_zero {n : ℕ} [Fact (finrank ℝ V = n + 1)]
    {p : WithMetric (hf.metric V)} (hp : p.ofWithMetric ≠ 0)
    (X Y : TangentSpace 𝓘(ℝ, V) p) :
    letI : RiemannianBundle
      (fun z : standardCapRadialDomain × sphere (0 : V) 1 ↦
        TangentSpace (𝓘(ℝ).prod (𝓡 n)) z) :=
      ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
    ∃ (q : standardCapRadialDomain × sphere (0 : V) 1)
      (u v : TangentSpace (𝓘(ℝ).prod (𝓡 n)) q),
      (q.1 : ℝ) = ‖p.ofWithMetric‖ ∧
      (LinearIndependent ℝ ![u, v] ↔ LinearIndependent ℝ ![X, Y]) ∧
      (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) p X Y =
        (leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))
          (standardCapRadialDomain × sphere (0 : V) 1)).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection (𝓘(ℝ).prod (𝓡 n))) q u v := by
  let _ : RiemannianBundle
    (fun z : standardCapRadialDomain × sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) z) :=
    ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
  have hloc := hf.isLocalRiemannianIsometry_toWithMetric_polar (n := n) V
  set ψ : standardCapRadialDomain × sphere (0 : V) 1 → WithMetric (hf.metric V) :=
    fun z ↦ WithMetric.toWithMetric (hf.metric V) ((z.1 : ℝ) • (z.2 : V))
  obtain ⟨q, hq_norm, hψq⟩ :
      ∃ q : standardCapRadialDomain × sphere (0 : V) 1,
        (q.1 : ℝ) = ‖p.ofWithMetric‖ ∧ ψ q = p := by
    refine ⟨(radialSphereDiffeomorph (n := n) V).symm ⟨p.ofWithMetric, mem_puncturedSpace.2 hp⟩,
      by simp, ?_⟩
    have hcoe : (radialSphereDiffeomorph (n := n) V
        ((radialSphereDiffeomorph (n := n) V).symm ⟨p.ofWithMetric, mem_puncturedSpace.2 hp⟩) :
          V) = p.ofWithMetric :=
      congrArg Subtype.val ((radialSphereDiffeomorph (n := n) V).apply_symm_apply
        ⟨p.ofWithMetric, mem_puncturedSpace.2 hp⟩)
    rw [coe_radialSphereDiffeomorph_apply] at hcoe
    exact WithMetric.ext hcoe
  subst hψq
  obtain ⟨e, he⟩ := hloc.exists_linearIsometryEquiv_eq_mfderiv q
  obtain ⟨u, hu⟩ := (hloc.mfderiv_surjective q) X
  obtain ⟨v, hv⟩ := (hloc.mfderiv_surjective q) Y
  refine ⟨q, u, v, hq_norm, ?_, ?_⟩
  · have hcomp : ⇑e.toLinearEquiv.toLinearMap ∘ ![u, v] = ![X, Y] := by
      ext i; fin_cases i <;> simp [he, hu, hv]
    have hli := e.toLinearEquiv.toLinearMap.linearIndependent_iff (LinearEquiv.ker e.toLinearEquiv)
      (v := ![u, v])
    rw [hcomp] at hli
    exact hli.symm
  · have hsec := hloc.sectionalCurvature_mfderiv q u v
    rwa [hu, hv] at hsec

private theorem sectionalCurvature_withMetric_tip_limit
    {p₀ : WithMetric (hf.metric V)} (hp₀ : p₀.ofWithMetric = 0)
    {X Y : TangentSpace 𝓘(ℝ, V) p₀} (hXY : LinearIndependent ℝ ![X, Y])
    {s : Set (WithMetric (hf.metric V))} (hs : s ∈ 𝓝 p₀) {k : ℝ}
    (hk : ∀ q ∈ s, q.ofWithMetric ≠ 0 → ∀ u v : TangentSpace 𝓘(ℝ, V) q,
      LinearIndependent ℝ ![u, v] →
      (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) q u v = k) :
    (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) p₀ X Y = k := by
  have hcard : 2 ≤ finrank ℝ V := by
    have h := hXY.fintype_card_le_finrank
    rwa [Fintype.card_fin, (tangentSpaceCastModel 𝓘(ℝ, V) p₀).toLinearEquiv.finrank_eq] at h
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (M := V) (by omega)
  have : Nontrivial (WithMetric (hf.metric V)) :=
    (WithMetric.equiv (hf.metric V)).surjective.nontrivial
  obtain ⟨u, hu, hu₀⟩ := FiberBundle.exists_contMDiff_section_eq 𝓘(ℝ, V) V ∞ X
  obtain ⟨v, hv, hv₀⟩ := FiberBundle.exists_contMDiff_section_eq 𝓘(ℝ, V) V ∞ Y
  have hcont :=
    ((leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).contMDiffAt_sectionalCurvature
      (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) (n := (⊤ : ℕ∞)) (hu p₀) (hv p₀)
      (by rwa [hu₀, hv₀])).continuousAt
  have hdet_cont : Continuous fun q ↦
      inner ℝ (u q) (u q) * inner ℝ (v q) (v q) - inner ℝ (u q) (v q) ^ 2 :=
    ((hu.continuous.inner_bundle hu.continuous).mul
      (hv.continuous.inner_bundle hv.continuous)).sub
      ((hu.continuous.inner_bundle hv.continuous).pow 2)
  have hdet₀ :
      inner ℝ (u p₀) (u p₀) * inner ℝ (v p₀) (v p₀) - inner ℝ (u p₀) (v p₀) ^ 2 ≠ 0 := by
    rw [hu₀, hv₀, ← Matrix.real_det_gram_fin_two]
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hXY
  have hev : ∀ᶠ q in 𝓝[≠] p₀,
      (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
        (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) q (u q) (v q) = k := by
    filter_upwards [nhdsWithin_le_nhds (inter_mem hs (hdet_cont.continuousAt.eventually_ne hdet₀)),
      self_mem_nhdsWithin] with q ⟨hqs, hqdet⟩ hqne
    have hq0 : q.ofWithMetric ≠ 0 := fun h ↦ hqne (WithMetric.ext (h.trans hp₀.symm))
    refine hk q hqs hq0 (u q) (v q) (Matrix.det_gram_ne_zero_iff_linearIndependent.mp ?_)
    rwa [Matrix.real_det_gram_fin_two]
  have hneBot : (𝓝[≠] p₀).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [closure_compl_singleton]; trivial)
  have hlim₁ := (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' hev
  simpa [hu₀, hv₀] using tendsto_nhds_unique hlim₁ tendsto_const_nhds

/-- **Near the tip (including at `0`), the standard cap has constant sectional curvature
`1 / 4`.** -/
theorem exists_hasSectionalCurvatureAt_withMetric_round :
    ∃ r₀ > 0, ∀ p : WithMetric (hf.metric V), ‖p.ofWithMetric‖ < r₀ →
      (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).HasSectionalCurvatureAt
        (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) p (1 / 4) := by
  rcases Nat.eq_zero_or_pos (finrank ℝ V) with hd0 | hdpos
  · refine ⟨1, one_pos, fun p _ ↦
      (leviCivitaConnection 𝓘(ℝ, V)
        (WithMetric (hf.metric V))).hasSectionalCurvatureAt_of_finrank_le_one
        (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) p (1 / 4) ?_⟩
    rw [(tangentSpaceCastModel 𝓘(ℝ, V) p).toLinearEquiv.finrank_eq, hd0]
    exact Nat.zero_le 1
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hdpos.ne'
    let _ : Fact (finrank ℝ V = n + 1) := ⟨hn⟩
    obtain ⟨r₀, hr₀, hpunct⟩ :=
      hf.exists_hasSectionalCurvatureAt_puncturedMetric_round (n := n) (V := V)
    have haway : ∀ q : WithMetric (hf.metric V), ‖q.ofWithMetric‖ < r₀ → q.ofWithMetric ≠ 0 →
        ∀ X Y : TangentSpace 𝓘(ℝ, V) q, LinearIndependent ℝ ![X, Y] →
        (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) q X Y = 1 / 4 := by
      intro q hqr hq0 X Y hXY
      obtain ⟨z, u, v, hz, hli, hsec⟩ :=
        hf.sectionalCurvature_withMetric_of_ne_zero (n := n) hq0 X Y
      rw [hsec]
      let _ : RiemannianBundle
        (fun w : standardCapRadialDomain × sphere (0 : V) 1 ↦ TangentSpace (𝓘(ℝ).prod (𝓡 n)) w) :=
        ⟨(hf.puncturedMetric (n := n) V).toRiemannianMetric⟩
      exact (hpunct z (hz.trans_lt hqr)).sectionalCurvature_eq u v (hli.2 hXY)
    refine ⟨r₀, hr₀, fun p hp ↦ (hasSectionalCurvatureAt_iff _ _ _ _).2 fun X Y hXY ↦ ?_⟩
    rcases eq_or_ne p.ofWithMetric 0 with hp0 | hp0
    · refine hf.sectionalCurvature_withMetric_tip_limit hp0 hXY
        (s := WithMetric.ofWithMetric ⁻¹' Metric.ball (0 : V) r₀) ?_
        fun q hq hq0 u v huv ↦ haway q (by simpa using hq) hq0 u v huv
      exact (Metric.isOpen_ball.preimage WithMetric.continuous_ofWithMetric).mem_nhds
        (by simp [hp0, hr₀])
    · exact haway p hp hp0 X Y hXY

/-- **Every tangent two-plane of the standard cap (including at the tip) has nonnegative sectional
curvature.** -/
theorem sectionalCurvature_withMetric_nonneg (p : WithMetric (hf.metric V))
    (X Y : TangentSpace 𝓘(ℝ, V) p) :
    0 ≤ (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
      (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) p X Y := by
  by_cases hXY : LinearIndependent ℝ ![X, Y]
  · rcases eq_or_ne p.ofWithMetric 0 with hp0 | hp0
    · obtain ⟨r₀, hr₀, hround⟩ := hf.exists_hasSectionalCurvatureAt_withMetric_round (V := V)
      rw [(hround p (by simp [hp0, hr₀])).sectionalCurvature_eq X Y hXY]
      norm_num
    · have hdpos : 0 < finrank ℝ V := by
        have h := hXY.fintype_card_le_finrank
        rw [Fintype.card_fin, (tangentSpaceCastModel 𝓘(ℝ, V) p).toLinearEquiv.finrank_eq] at h
        omega
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hdpos.ne'
      let _ : Fact (finrank ℝ V = n + 1) := ⟨hn⟩
      obtain ⟨z, u, v, -, -, hsec⟩ := hf.sectionalCurvature_withMetric_of_ne_zero (n := n) hp0 X Y
      rw [hsec]
      exact hf.sectionalCurvature_puncturedMetric_nonneg (n := n) z u v
  · rw [sectionalCurvature_apply,
      not_not.mp (Matrix.det_gram_ne_zero_iff_linearIndependent.not.mpr hXY), div_zero]

private theorem scalarCurvature_metric_of_ne_zero {n : ℕ} [Fact (finrank ℝ V = n + 1)]
    {x : V} (hx : x ≠ 0) :
    (hf.metric V).scalarCurvature x =
      (hf.puncturedMetric (n := n) V).scalarCurvature
        ((radialSphereDiffeomorph (n := n) V).symm ⟨x, mem_puncturedSpace.2 hx⟩) := by
  rw [← (hf.metric V).scalarCurvature_restrictOpenTangentSpace (puncturedSpace V)
      ⟨x, mem_puncturedSpace.2 hx⟩,
    hf.puncturedMetric_eq_pullback (n := n) V,
    ContMDiffRiemannianMetric.scalarCurvature_pullback]
  simp

/-- **The standard cap metric has nonnegative scalar curvature everywhere on `V`**, in every
dimension. -/
theorem scalarCurvature_metric_nonneg (x : V) : 0 ≤ (hf.metric V).scalarCurvature x := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · let _ : RiemannianBundle (fun z : V ↦ TangentSpace 𝓘(ℝ, V) z) :=
      ⟨(hf.metric V).toRiemannianMetric⟩
    have : Subsingleton (TangentSpace 𝓘(ℝ, V) x) :=
      (tangentSpaceCastModel 𝓘(ℝ, V) x).injective.subsingleton
    rw [ContMDiffRiemannianMetric.scalarCurvature_def, CovariantDerivative.scalarCurvature_apply,
      Subsingleton.elim (CovariantDerivative.ricciTensor _ x) 0, map_zero]
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (finrank_pos (R := ℝ) (M := V)).ne'
    let _ : Fact (finrank ℝ V = n + 1) := ⟨hn⟩
    have hx : x ∈ closure ({0}ᶜ : Set V) := by rw [closure_compl_singleton]; trivial
    refine le_on_closure (fun y (hy : y ≠ 0) ↦ ?_) continuous_const.continuousOn
      (hf.metric V).continuous_scalarCurvature.continuousOn hx
    rw [hf.scalarCurvature_metric_of_ne_zero (n := n) hy]
    exact hf.scalarCurvature_puncturedMetric_nonneg (n := n) _

/-- **Near the tip (including at `0`), the standard cap metric on `V` has scalar curvature
`d (d - 1) / 4`** (`d = finrank ℝ V`), the scalar curvature of the round sphere of radius `2`. -/
theorem exists_scalarCurvature_metric_eq_round :
    ∃ r₀ > 0, ∀ x : V, ‖x‖ < r₀ →
      (hf.metric V).scalarCurvature x =
        (finrank ℝ V : ℝ) * ((finrank ℝ V : ℝ) - 1) / 4 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine ⟨1, one_pos, fun x _ ↦ ?_⟩
    let _ : RiemannianBundle (fun z : V ↦ TangentSpace 𝓘(ℝ, V) z) :=
      ⟨(hf.metric V).toRiemannianMetric⟩
    have : Subsingleton (TangentSpace 𝓘(ℝ, V) x) :=
      (tangentSpaceCastModel 𝓘(ℝ, V) x).injective.subsingleton
    rw [finrank_zero_of_subsingleton, ContMDiffRiemannianMetric.scalarCurvature_def,
      CovariantDerivative.scalarCurvature_apply,
      Subsingleton.elim (CovariantDerivative.ricciTensor _ x) 0, map_zero]
    norm_num
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (finrank_pos (R := ℝ) (M := V)).ne'
    let _ : Fact (finrank ℝ V = n + 1) := ⟨hn⟩
    obtain ⟨r₀, hr₀, hround⟩ :=
      hf.exists_scalarCurvature_puncturedMetric_eq_round (n := n) (V := V)
    have haway : ∀ y : V, y ≠ 0 → ‖y‖ < r₀ →
        (hf.metric V).scalarCurvature y = (finrank ℝ V : ℝ) * ((finrank ℝ V : ℝ) - 1) / 4 := by
      intro y hy hyr
      rw [hf.scalarCurvature_metric_of_ne_zero (n := n) hy, hround _ (by simpa using hyr), hn]
      push_cast
      ring
    refine ⟨r₀, hr₀, fun x hx ↦ ?_⟩
    rcases eq_or_ne x 0 with rfl | hx0
    · have hneBot : (𝓝[≠] (0 : V)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
        rw [closure_compl_singleton]; trivial)
      have hev : ∀ᶠ y in 𝓝[≠] (0 : V), (hf.metric V).scalarCurvature y =
          (finrank ℝ V : ℝ) * ((finrank ℝ V : ℝ) - 1) / 4 := by
        filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : V) hr₀),
          self_mem_nhdsWithin] with y hyr hy0
        exact haway y hy0 (by simpa using hyr)
      exact tendsto_nhds_unique
        (((hf.metric V).continuous_scalarCurvature.continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds).congr' hev)
        tendsto_const_nhds
    · exact haway x hx0 hx

/-- **On a sufficiently far cylindrical end (`R ≤ ‖x‖`), the standard cap metric on `V` has scalar
curvature `(d - 1) (d - 2) / 2`**, the scalar curvature of `ℝ × S^(d - 1)(√2)`. -/
theorem exists_scalarCurvature_metric_eq_cylinder :
    ∃ R > 0, ∀ x : V, R ≤ ‖x‖ →
      (hf.metric V).scalarCurvature x =
        ((finrank ℝ V : ℝ) - 1) * ((finrank ℝ V : ℝ) - 2) / 2 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine ⟨1, one_pos, fun x hx ↦ absurd hx ?_⟩
    rw [Subsingleton.elim x 0, norm_zero]
    exact not_le.2 one_pos
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (finrank_pos (R := ℝ) (M := V)).ne'
    let _ : Fact (finrank ℝ V = n + 1) := ⟨hn⟩
    obtain ⟨R, hR, hcyl⟩ := hf.exists_scalarCurvature_puncturedMetric_eq_cylinder (n := n) (V := V)
    refine ⟨R, hR, fun x hx ↦ ?_⟩
    have hx0 : x ≠ 0 := norm_pos_iff.1 (hR.trans_le hx)
    rw [hf.scalarCurvature_metric_of_ne_zero (n := n) hx0, hcyl _ (by simpa using hx), hn]
    push_cast
    ring

/-- In dimension three, the standard cap metric has scalar curvature `3 / 2` near the tip (including
at `0`). -/
theorem exists_scalarCurvature_metric_eq_three_halves (hd : finrank ℝ V = 3) :
    ∃ r₀ > 0, ∀ x : V, ‖x‖ < r₀ → (hf.metric V).scalarCurvature x = 3 / 2 := by
  obtain ⟨r₀, hr₀, h⟩ := hf.exists_scalarCurvature_metric_eq_round (V := V)
  refine ⟨r₀, hr₀, fun x hx ↦ ?_⟩
  rw [h x hx, hd]
  norm_num

/-- In dimension three, the standard cap metric has scalar curvature `1` on its cylindrical end. -/
theorem exists_scalarCurvature_metric_eq_one_of_finrank_eq_three (hd : finrank ℝ V = 3) :
    ∃ R > 0, ∀ x : V, R ≤ ‖x‖ → (hf.metric V).scalarCurvature x = 1 := by
  obtain ⟨R, hR, h⟩ := hf.exists_scalarCurvature_metric_eq_cylinder (V := V)
  refine ⟨R, hR, fun x hx ↦ ?_⟩
  rw [h x hx, hd]
  norm_num

end Curvature

end IsStandardCapProfile

/-- **Existence of a complete smooth three-dimensional standard cap metric.** On any
three-dimensional real inner product space `V` (in particular `EuclideanSpace ℝ (Fin 3)`), there
exists a standard cap profile `f` whose associated smooth Riemannian metric `hf.metric V` is
complete, has nonnegative sectional and scalar curvature everywhere, has constant sectional
curvature `1 / 4` near the tip `0`, and has scalar curvature `1` on a cylindrical end `R ≤ ‖x‖`. -/
theorem exists_standardCapMetric (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (hd : finrank ℝ V = 3) :
    ∃ (f : ℝ → ℝ) (hf : IsStandardCapProfile f),
      (letI : MetricSpace (WithMetric (hf.metric V)) :=
        MetricSpace.ofRiemannianMetric 𝓘(ℝ, V) (WithMetric (hf.metric V));
      CompleteSpace (WithMetric (hf.metric V))) ∧
      (∀ p : WithMetric (hf.metric V), ∀ X Y : TangentSpace 𝓘(ℝ, V) p,
        0 ≤ (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).sectionalCurvature
          (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) p X Y) ∧
      (∃ r₀ > 0, ∀ p : WithMetric (hf.metric V), ‖p.ofWithMetric‖ < r₀ →
        (leviCivitaConnection 𝓘(ℝ, V) (WithMetric (hf.metric V))).HasSectionalCurvatureAt
          (isMetricCompatible_leviCivitaConnection 𝓘(ℝ, V)) p (1 / 4)) ∧
      (∀ x : V, 0 ≤ (hf.metric V).scalarCurvature x) ∧
      (∃ R > 0, ∀ x : V, R ≤ ‖x‖ → (hf.metric V).scalarCurvature x = 1) := by
  obtain ⟨f, hf⟩ := exists_isStandardCapProfile
  exact ⟨f, hf, hf.completeSpace_withMetric_metricSpace,
    hf.sectionalCurvature_withMetric_nonneg,
    hf.exists_hasSectionalCurvatureAt_withMetric_round, hf.scalarCurvature_metric_nonneg,
    hf.exists_scalarCurvature_metric_eq_one_of_finrank_eq_three hd⟩

/-! ### Tip-obstruction theorem -/

section TipObstruction

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem continuous_inner_const_vector
    (g : ContinuousRiemannianMetric V (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x)) (w : V) :
    Continuous fun x : V ↦
      g.inner x ((NormedSpace.fromTangentSpace x).symm w)
        ((NormedSpace.fromTangentSpace x).symm w) := by
  let _ : RiemannianBundle (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle V (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x) :=
    Bundle.instIsContinuousRiemannianBundle g
  let σ : Π x : V, TangentSpace 𝓘(ℝ, V) x := fun x ↦ (NormedSpace.fromTangentSpace x).symm w
  have hσ : CMDiff ∞ (T% σ) :=
    (contMDiff_vectorSpace_iff_contDiff (n := ∞)).2 contDiff_const
  exact hσ.continuous.inner_bundle hσ.continuous

/-- **Tip-obstruction theorem (right-limit form).** Let `V` be a real inner product space of
dimension `n + 1` with `0 < n` (`dim V ≥ 2`), and let `g` be a continuous Riemannian metric on `V`.
If on concentric spheres `u ↦ r • u` of small positive radius `r`, `g` restricts to `f(r)² g_(Sⁿ)`,
then `|f(r)| → 0` as `r → 0⁺`. The hypothesis `0 < n` cannot be dropped: when `n = 0` (`V = ℝ`),
`S⁰` is discrete (`T_u S⁰ = 0`) and `f = 1` describes the flat metric `dx²` across `0`. -/
theorem tendsto_abs_of_spherical_pullback {n : ℕ} [Fact (finrank ℝ V = n + 1)] (hn : 0 < n)
    (g : ContinuousRiemannianMetric V (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x)) {f : ℝ → ℝ}
    (hpull : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ (u : sphere (0 : V) 1) (v : TangentSpace (𝓡 n) u),
      g.inner (r • (u : V))
        (mfderiv (𝓡 n) 𝓘(ℝ, V) (fun q : sphere (0 : V) 1 ↦ r • (q : V)) u v)
        (mfderiv (𝓡 n) 𝓘(ℝ, V) (fun q : sphere (0 : V) 1 ↦ r • (q : V)) u v) =
        f r ^ 2 * (sphereRoundMetric (E := V)).inner u v v) :
    Tendsto (fun r ↦ |f r|) (𝓝[>] 0) (𝓝 0) := by
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (M := V) (by
    rw [Fact.out (p := finrank ℝ V = n + 1)]; omega)
  obtain ⟨u⟩ : Nonempty (sphere (0 : V) 1) :=
    Set.Nonempty.to_subtype (NormedSpace.sphere_nonempty.2 zero_le_one)
  let v : TangentSpace (𝓡 n) u := EuclideanSpace.single ⟨0, hn⟩ 1
  have hv : v ≠ 0 := by
    change PiLp.single 2 (⟨0, hn⟩ : Fin n) (1 : ℝ) ≠ (0 : EuclideanSpace ℝ (Fin n))
    rw [ne_eq, PiLp.single_eq_zero_iff]
    exact one_ne_zero
  have hpos : 0 < (sphereRoundMetric (E := V)).inner u v v :=
    (sphereRoundMetric (E := V)).pos u v hv
  set w : V := mvfderiv (𝓡 n) ((↑) : sphere (0 : V) 1 → V) u v
  have heq : (fun r : ℝ ↦ f r ^ 2) =ᶠ[𝓝[>] (0 : ℝ)] fun r : ℝ ↦
      r ^ 2 * g.inner (r • (u : V)) ((NormedSpace.fromTangentSpace (r • (u : V))).symm w)
        ((NormedSpace.fromTangentSpace (r • (u : V))).symm w) /
        (sphereRoundMetric (E := V)).inner u v v := by
    filter_upwards [hpull] with r hr
    have hdf : mfderiv (𝓡 n) 𝓘(ℝ, V) (fun q : sphere (0 : V) 1 ↦ r • (q : V)) u v =
        r • (NormedSpace.fromTangentSpace (r • (u : V))).symm w := by
      apply (NormedSpace.fromTangentSpace (r • (u : V))).injective
      change mvfderiv (𝓡 n) (r • ((↑) : sphere (0 : V) 1 → V)) u v = _
      rw [mvfderiv_const_smul_field, _root_.smul_apply, map_smul,
        ContinuousLinearEquiv.apply_symm_apply]
    have hpull_r := hr u v
    rw [hdf, map_smul, map_smul, _root_.smul_apply, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, ← sq] at hpull_r
    exact (eq_div_iff hpos.ne').2 hpull_r.symm
  have hcont_g : Continuous fun r : ℝ ↦
      g.inner (r • (u : V)) ((NormedSpace.fromTangentSpace (r • (u : V))).symm w)
        ((NormedSpace.fromTangentSpace (r • (u : V))).symm w) :=
    (continuous_inner_const_vector g w).comp (continuous_id.smul continuous_const)
  have hsq : Tendsto (fun r : ℝ ↦ f r ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun r : ℝ ↦
        r ^ 2 * g.inner (r • (u : V)) ((NormedSpace.fromTangentSpace (r • (u : V))).symm w)
          ((NormedSpace.fromTangentSpace (r • (u : V))).symm w) /
          (sphereRoundMetric (E := V)).inner u v v) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((((continuous_pow 2).mul hcont_g).div_const _).continuousAt (x := 0)).tendsto
        |>.mono_left nhdsWithin_le_nhds
    exact hlim.congr' heq.symm
  have hsqrt : Tendsto (fun r : ℝ ↦ √(f r ^ 2)) (𝓝[>] 0) (𝓝 √0) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  rw [Real.sqrt_zero] at hsqrt
  exact hsqrt.congr fun r ↦ Real.sqrt_sq_eq_abs (f r)

/-- **Tip-obstruction theorem.** If `f : ℝ → ℝ` is right-continuous at `0` (in particular, if `f`
is continuous at `0`) and a continuous Riemannian metric `g` on `V` (`dim V = n + 1`, `0 < n`)
restricts on concentric spheres `u ↦ r • u` of small positive radius `r` to `f(r)² g_(Sⁿ)`, then
`f 0 = 0`; in particular `¬ 0 < f 0`. -/
theorem eq_zero_of_spherical_pullback {n : ℕ} [Fact (finrank ℝ V = n + 1)] (hn : 0 < n)
    (g : ContinuousRiemannianMetric V (fun x : V ↦ TangentSpace 𝓘(ℝ, V) x)) {f : ℝ → ℝ}
    (hf : ContinuousWithinAt f (Ici 0) 0)
    (hpull : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ (u : sphere (0 : V) 1) (v : TangentSpace (𝓡 n) u),
      g.inner (r • (u : V))
        (mfderiv (𝓡 n) 𝓘(ℝ, V) (fun q : sphere (0 : V) 1 ↦ r • (q : V)) u v)
        (mfderiv (𝓡 n) 𝓘(ℝ, V) (fun q : sphere (0 : V) 1 ↦ r • (q : V)) u v) =
        f r ^ 2 * (sphereRoundMetric (E := V)).inner u v v) :
    f 0 = 0 := by
  have hneBot : (𝓝[>] (0 : ℝ)).NeBot := nhdsGT_neBot (0 : ℝ)
  have h1 : Tendsto (fun r ↦ |f r|) (𝓝[>] 0) (𝓝 |f 0|) :=
    (continuous_abs.continuousAt.tendsto.comp hf).mono_left
      (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  exact abs_eq_zero.1 (tendsto_nhds_unique h1 (tendsto_abs_of_spherical_pullback hn g hpull))

end TipObstruction

end TauCeti
