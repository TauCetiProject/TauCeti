/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.ContinuityEquation.Endpoint
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.Convolution
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Hamilton–Jacobi subsolutions along the continuity equation

Let `t ↦ νₜ` be a curve of finite measures on a finite-dimensional real normed space `E`, narrowly
continuous on `[a, b]`, solving the continuity equation `∂ₜ νₜ + div (vₜ νₜ) = 0` on `(a, b)`, and
let `L : E → ℝ` be a Lagrangian. A function `u : ℝ × E → ℝ` is a *subsolution* of the
Hamilton–Jacobi equation `∂ₜ u + H (∇ₓ u) = 0`, with `H` the convex conjugate of `L`, when
`∂ₜ u (t, x) + ⟨∇ₓ u (t, x), w⟩ ≤ L w` for every velocity `w`. Testing the continuity equation
against a subsolution bounds its boundary terms by the action of the velocity field:

`∫ u (b, ·) dν_b - ∫ u (a, ·) dν_a ≤ ∫_a^b ∫ L (vₜ x) dνₜ(x) dt`.

The left side is a Kantorovich dual value when `u (a, ·)` and `u (b, ·)` are dual potentials for a
transport cost, and for `L w = ‖w‖ ^ p` the right side is the `p`-action of `v`. This is the
inequality behind the lower bound `W_p (ν_a, ν_b) ^ p ≤ ∫_a^b ∫ ‖vₜ‖ ^ p dνₜ dt` of the
Benamou–Brenier formula, whose subsolutions are Hopf–Lax functions.

For a `C¹` subsolution with bounded values and derivative, the inequality is the integrated
continuity equation `TauCeti.IsContinuityEquation.intervalIntegral_integral_fderiv_eq_sub`. Hopf–Lax
functions are not differentiable, and satisfy the subsolution inequality only in the difference
form `u (q + s • (1, w)) ≤ u q + s * L w` for `s > 0`. The inequality still holds for a bounded
measurable `u` satisfying this difference form on a strip `(a - r, b + r) × E`, provided `u` is
upper semicontinuous at almost every point of the initial slice `{a} × E` and lower
semicontinuous at almost every point of the final slice `{b} × E`. Its space-time mollifications
are bounded `C¹` subsolutions with bounded derivative
(`HasCompactSupport.fderiv_convolution_left_apply_le`). As the mollifier shrinks, they are
eventually almost below `u` on the initial slice and almost above `u` on the final slice
(`MeasureTheory.eventually_convolution_lsmul_lt_of_upperSemicontinuousAt` and
`MeasureTheory.eventually_lt_convolution_lsmul_of_lowerSemicontinuousAt`), which is the direction
the inequality needs. Hopf–Lax functions satisfy the difference form only at positive times, and
this is proved for the Lagrangian `‖·‖ ^ p` with `1 ≤ p` and a bounded-below initial datum
(`TauCeti.hopfLax_norm_rpow_add_add_smul_le`). They are upper semicontinuous at positive times when
the initial datum and the Lagrangian are bounded below and the Lagrangian is continuous
(`TauCeti.upperSemicontinuousOn_hopfLax`). So they must be shifted in time, to make the strip lie
in positive times, before this theorem applies to them. Lower semicontinuity on the final slice
needs more: in a finite-dimensional space a continuous bounded initial datum makes them continuous
at positive times (`TauCeti.continuousOn_hopfLax_norm_rpow`), which is how the lower bound of the
Benamou–Brenier formula is proved (`TauCeti.IsContinuityEquation.wassersteinEDist_rpow_le`).

The right side is the `ℝ≥0∞`-valued integral of the positive part of `L (vₜ x)`, so neither the
integrability of the action nor a sign condition on `L` is assumed.

## Main results

* `TauCeti.IsContinuityEquation.ofReal_integral_sub_integral_le_lintegral_of_fderiv_le`: the action
  bounds the boundary terms of a bounded `C¹` subsolution with bounded derivative.
* `TauCeti.IsContinuityEquation.ofReal_integral_sub_integral_le_lintegral_of_add_smul_le`: the same
  bound for a bounded measurable subsolution in difference form, upper semicontinuous almost
  everywhere on the initial slice and lower semicontinuous almost everywhere on the final one.

## References

* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, Birkhäuser, 2nd ed. 2008, §8.1.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 7.
-/

public section

open MeasureTheory Set Function Filter Topology ContinuousLinearMap
open scoped ENNReal Convolution

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {v : ℝ → E → E} {a b : ℝ} {u : ℝ × E → ℝ} {M M' : ℝ}
  {L : E → ℝ} {ν : ℝ → FiniteMeasure E} {m : Measure (ℝ × E)} [m.IsAddHaarMeasure]

namespace IsContinuityEquation

/-- **Smooth subsolutions.** Let `t ↦ νₜ` be a curve of finite measures, narrowly continuous on
`[a, b]`, solving the continuity equation with velocity `v` on `(a, b)`. For a bounded `C¹`
function `u` of time and space with bounded derivative such that
`∂ₜ u (t, x) + ⟨∇ₓ u (t, x), w⟩ ≤ L w` for every `t ∈ (a, b)`, every `x` and every velocity `w`,
the boundary terms are bounded by the action of `v`:
`∫ u (b, ·) dν_b - ∫ u (a, ·) dν_a ≤ ∫_a^b ∫ L (vₜ x) dνₜ(x) dt`, in the positive-part form. -/
theorem ofReal_integral_sub_integral_le_lintegral_of_fderiv_le
    (h : IsContinuityEquation (fun t ↦ (ν t : Measure E)) v a b) (hν : ContinuousOn ν (Icc a b))
    (hab : a ≤ b) (hu : ContDiff ℝ 1 u) (huM : ∀ q, ‖u q‖ ≤ M) (hDu : ∀ q, ‖fderiv ℝ u q‖ ≤ M')
    (hsub : ∀ t ∈ Ioo a b, ∀ x w, fderiv ℝ u (t, x) (1, w) ≤ L w) :
    ENNReal.ofReal (∫ x, u (b, x) ∂(ν b : Measure E) - ∫ x, u (a, x) ∂(ν a : Measure E)) ≤
      ∫⁻ t in Ioo a b, ∫⁻ x, ENNReal.ofReal (L (v t x)) ∂(ν t : Measure E) := by
  rw [← h.intervalIntegral_integral_fderiv_eq_sub hν hu huM hDu (left_mem_Icc.2 hab)
    (right_mem_Icc.2 hab), intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  refine MeasureTheory.ofReal_integral_le_lintegral_ofReal.trans
    (setLIntegral_mono' measurableSet_Ioo fun t ht ↦ ?_)
  exact MeasureTheory.ofReal_integral_le_lintegral_ofReal.trans
    (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (hsub t ht x (v t x)))

/-- One mollification step: if `u` is a bounded measurable subsolution in difference form on the
strip `(a - r, b + r) × E` and the bump `β` has radius `β.rOut < r`, then the mollification
`β ⋆ u` is a bounded `C¹` subsolution on `(a, b) × E` with bounded derivative, so the action
bounds its boundary terms. -/
private theorem ofReal_integral_convolution_sub_le_lintegral
    (h : IsContinuityEquation (fun t ↦ (ν t : Measure E)) v a b) (hν : ContinuousOn ν (Icc a b))
    (hab : a ≤ b) (hu : LocallyIntegrable u m) (huM : ∀ q, ‖u q‖ ≤ M) {r : ℝ}
    (hsub : ∀ w, ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ q : ℝ × E, q.1 ∈ Ioo (a - r) (b + r) →
      u (q + s • (1, w)) ≤ u q + s * L w)
    (β : ContDiffBump (0 : ℝ × E)) (hβ : β.rOut < r) :
    ENNReal.ofReal (∫ x, (β.normed m ⋆[lsmul ℝ ℝ, m] u) (b, x) ∂(ν b : Measure E) -
        ∫ x, (β.normed m ⋆[lsmul ℝ ℝ, m] u) (a, x) ∂(ν a : Measure E)) ≤
      ∫⁻ t in Ioo a b, ∫⁻ x, ENNReal.ofReal (L (v t x)) ∂(ν t : Measure E) := by
  refine h.ofReal_integral_sub_integral_le_lintegral_of_fderiv_le hν hab
    (β.hasCompactSupport_normed.contDiff_convolution_left _ β.contDiff_normed hu)
    (fun _ ↦ norm_convolution_lsmul_le_of_forall_norm_le β.support_normed_eq.subset
      β.nonneg_normed β.integral_normed hu.aestronglyMeasurable fun q _ ↦ huM q)
    (β.hasCompactSupport_normed.norm_fderiv_convolution_left_le β.contDiff_normed hu huM)
    fun t ht x w ↦ β.hasCompactSupport_normed.fderiv_convolution_left_apply_le β.contDiff_normed
      β.nonneg_normed β.integral_normed hu ?_
  -- The points `(t, x) - y` averaged by the mollifier stay in the strip.
  filter_upwards [hsub w] with s hs y hy
  refine hs _ ?_
  rw [β.support_normed_eq, Metric.mem_ball, dist_zero_right] at hy
  have hy1 : |y.1| < r := (norm_fst_le y).trans_lt (hy.trans hβ)
  rw [abs_lt] at hy1
  constructor <;> simp only [Prod.fst_sub] <;> linarith [ht.1, ht.2]

/-- **Subsolutions in difference form.** Let `t ↦ νₜ` be a curve of finite measures, narrowly
continuous on `[a, b]`, solving the continuity equation with velocity `v` on `(a, b)`. Let `u` be
a bounded measurable function of time and space, upper semicontinuous at almost every point of the
initial slice `{a} × E` and lower semicontinuous at almost every point of the final slice
`{b} × E`, such that for some `r > 0` and every velocity `w`, for all small `s > 0`,
`u (q + s • (1, w)) ≤ u q + s * L w` at every point `q` of the strip `(a - r, b + r) × E`.
Then the boundary terms are bounded by the action of `v`:
`∫ u (b, ·) dν_b - ∫ u (a, ·) dν_a ≤ ∫_a^b ∫ L (vₜ x) dνₜ(x) dt`, in the positive-part form. -/
theorem ofReal_integral_sub_integral_le_lintegral_of_add_smul_le
    (h : IsContinuityEquation (fun t ↦ (ν t : Measure E)) v a b) (hν : ContinuousOn ν (Icc a b))
    (hab : a ≤ b) (hu : Measurable u) (huM : ∀ q, ‖u q‖ ≤ M)
    (hua : ∀ᵐ x ∂(ν a : Measure E), UpperSemicontinuousAt u (a, x))
    (hub : ∀ᵐ x ∂(ν b : Measure E), LowerSemicontinuousAt u (b, x)) {r : ℝ} (hr : 0 < r)
    (hsub : ∀ w, ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ q : ℝ × E, q.1 ∈ Ioo (a - r) (b + r) →
      u (q + s • (1, w)) ≤ u q + s * L w) :
    ENNReal.ofReal (∫ x, u (b, x) ∂(ν b : Measure E) - ∫ x, u (a, x) ∂(ν a : Measure E)) ≤
      ∫⁻ t in Ioo a b, ∫⁻ x, ENNReal.ofReal (L (v t x)) ∂(ν t : Measure E) := by
  let m : Measure (ℝ × E) := Measure.addHaar
  have hloc : LocallyIntegrable u m :=
    (locallyIntegrable_const M).mono hu.aestronglyMeasurable
      (ae_of_all _ fun q ↦ (huM q).trans (le_abs_self M))
  -- Normalized bumps of radius `r / (n + 2) < r`, shrinking to `0`.
  let β (n : ℕ) : ContDiffBump (0 : ℝ × E) :=
    ⟨r / (n + 2) / 2, r / (n + 2), by positivity, half_lt_self (by positivity)⟩
  have hrOut : Tendsto (fun n ↦ (β n).rOut) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  let ψ (n : ℕ) : ℝ × E → ℝ := (β n).normed m ⋆[lsmul ℝ ℝ, m] u
  have hψM (n : ℕ) (q : ℝ × E) : |ψ n q| ≤ M := by
    simpa [Real.norm_eq_abs] using norm_convolution_lsmul_le_of_forall_norm_le
      (β n).support_normed_eq.subset (β n).nonneg_normed (β n).integral_normed
      hloc.aestronglyMeasurable fun q _ ↦ huM q
  have huM' (q : ℝ × E) : |u q| ≤ M := by simpa [Real.norm_eq_abs] using huM q
  have hψmeas (n : ℕ) (t : ℝ) : Measurable fun x : E ↦ ψ n (t, x) :=
    (((β n).hasCompactSupport_normed.continuous_convolution_left _ (β n).continuous_normed
      hloc).comp (Continuous.prodMk_right t)).measurable
  have hmeas (t : ℝ) : Measurable fun x : E ↦ u (t, x) := hu.comp measurable_prodMk_left
  -- The normalized bumps are mollifiers whose supports shrink to `0`.
  have hρ0 : ∀ᶠ n in atTop, ∀ y, 0 ≤ (β n).normed m y := .of_forall fun n ↦ (β n).nonneg_normed
  have hρ1 : ∀ᶠ n in atTop, ∫ y, (β n).normed m y ∂m = 1 :=
    .of_forall fun n ↦ (β n).integral_normed
  have hconv (q : ℝ × E) : ∀ᶠ n in atTop, ConvolutionExistsAt ((β n).normed m) u q (lsmul ℝ ℝ) m :=
    .of_forall fun n ↦
      (β n).hasCompactSupport_normed.convolutionExists_left _ (β n).continuous_normed hloc q
  have hρs := ContDiffBump.tendsto_support_normed_smallSets (μ := m) hrOut
  -- Integrate over the boundary slices, by dominated convergence.
  have hbM (n : ℕ) (x : E) : ‖min (ψ n (b, x)) (u (b, x))‖ ≤ M := by
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨le_min (abs_le.1 (hψM n _)).1 (abs_le.1 (huM' _)).1,
      (min_le_right _ _).trans (abs_le.1 (huM' _)).2⟩
  have haM (n : ℕ) (x : E) : ‖max (ψ n (a, x)) (u (a, x))‖ ≤ M := by
    rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨(abs_le.1 (huM' _)).1.trans (le_max_right _ _),
      max_le (abs_le.1 (hψM n _)).2 (abs_le.1 (huM' _)).2⟩
  have hlimb := tendsto_integral_of_dominated_convergence (μ := (ν b : Measure E)) (fun _ ↦ M)
    (fun n ↦ ((hψmeas n b).min (hmeas b)).aestronglyMeasurable) (integrable_const M)
    (fun n ↦ ae_of_all _ (hbM n))
    (hub.mono fun _ hx ↦
      tendsto_min_convolution_lsmul_of_lowerSemicontinuousAt hρ0 hρ1 hρs (hconv _) hx)
  have hlima := tendsto_integral_of_dominated_convergence (μ := (ν a : Measure E)) (fun _ ↦ M)
    (fun n ↦ ((hψmeas n a).max (hmeas a)).aestronglyMeasurable) (integrable_const M)
    (fun n ↦ ae_of_all _ (haM n))
    (hua.mono fun _ hx ↦
      tendsto_max_convolution_lsmul_of_upperSemicontinuousAt hρ0 hρ1 hρs (hconv _) hx)
  have hint {t : ℝ} {f : E → ℝ} (hf : Measurable f) (hfM : ∀ x, ‖f x‖ ≤ M) :
      Integrable f (ν t : Measure E) :=
    .of_bound hf.aestronglyMeasurable M (ae_of_all _ hfM)
  refine le_of_tendsto (ENNReal.tendsto_ofReal (hlimb.sub hlima)) (.of_forall fun n ↦ ?_)
  refine (ENNReal.ofReal_le_ofReal (sub_le_sub ?_ ?_)).trans
    (ofReal_integral_convolution_sub_le_lintegral h hν hab hloc huM hsub (β n)
      (div_lt_self hr (by linarith [n.cast_nonneg (α := ℝ)])))
  · exact integral_mono (hint ((hψmeas n b).min (hmeas b)) (hbM n))
      (hint (hψmeas n b) fun x ↦ by simpa [Real.norm_eq_abs] using hψM n _) fun x ↦ min_le_left _ _
  · exact integral_mono (hint (hψmeas n a) fun x ↦ by simpa [Real.norm_eq_abs] using hψM n _)
      (hint ((hψmeas n a).max (hmeas a)) (haM n)) fun x ↦ le_max_left _ _

end IsContinuityEquation

end TauCeti
