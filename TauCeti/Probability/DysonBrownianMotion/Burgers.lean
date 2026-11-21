/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.MeasureTheory.Measure.ResolventTransform.Basic
public import TauCeti.Probability.Distributions.Semicircle.LocationScale
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.EMetricSpace.Lipschitz
import TauCeti.MeasureTheory.Measure.ResolventTransform.Inversion
import TauCeti.Probability.Distributions.Semicircle.ResolventTransform

/-!
# The complex Burgers equation for resolvent transforms

The empirical eigenvalue measures of Dyson Brownian motion converge, as the number of particles
tends to infinity, to a family `(μ_t)_{t ≥ 0}` of probability measures on `ℝ` whose resolvent
transforms `m_t(z) = ∫ (x - z)⁻¹ dμ_t(x)` solve the complex Burgers equation
`∂_t m_t(z) = m_t(z) ∂_z m_t(z)` in the upper half-plane. Here `m_t` is Mathlib's
`MeasureTheory.resolventTransform`; the Stieltjes transform `G_t(z) = ∫ (z - x)⁻¹ dμ_t(x)` is
`-m_t(z)`, for which the equation reads `∂_t G = -G ∂_z G`.

`TauCeti.Probability.IsBurgersFlow μ` states the equation in the integrated form
`m_t(z) = m_0(z) + ∫₀ᵗ m_s(z) ∂_z m_s(z) ds` for every `z` in the upper half-plane, with an
integrable integrand. This file shows that the equation determines the family from its initial
measure. Along a solution the transforms are Lipschitz in time, so the equation holds in
differentiated form. Along each straight characteristic `s ↦ z - s m_0(z)`, Grönwall's inequality
then shows that `m_s` is constant, equal to `m_0(z)`, as long as the characteristic stays in the
upper half-plane. These characteristics are injective near `i ∞`, so the identity theorem and
Stieltjes inversion recover each `μ_t` from `μ_0`. The same argument gives the Pastur
(subordination) equation `m_t(w) = m_0(w + t m_t(w))` on the whole upper half-plane. The
semicircle laws of variance `t` centred at `a` form a Burgers flow: their transforms solve
`t m² + (z - a) m + 1 = 0`, and differentiating this quadratic in `t` and in `z` gives the
equation. So they are the unique flow started at the point mass at `a`.

## Main definitions

* `TauCeti.Probability.IsBurgersFlow`: the resolvent transforms of a family of measures solve the
  complex Burgers equation in integrated form.

## Main results

* `TauCeti.Probability.IsBurgersFlow.hasDerivWithinAt_resolventTransform`: the equation in
  differentiated form.
* `TauCeti.Probability.IsBurgersFlow.resolventTransform_sub_mul_resolventTransform`: the
  transforms are constant along characteristics, `m_t(z - t m_0(z)) = m_0(z)`.
* `TauCeti.Probability.IsBurgersFlow.resolventTransform_eq_resolventTransform_add_mul`: the
  Pastur equation `m_t(w) = m_0(w + t m_t(w))`.
* `TauCeti.Probability.IsBurgersFlow.eq`: uniqueness, a flow of probability measures is
  determined by its initial measure.
* `TauCeti.Probability.isBurgersFlow_semicircleReal` and
  `TauCeti.Probability.IsBurgersFlow.eq_semicircleReal`: the semicircle laws `semicircleReal a t`
  of variance `t` form a Burgers flow, and it is the only one started at the point mass at `a`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, §4.3.2.
* L. C. G. Rogers, Z. Shi, *Interacting Brownian particles and the Wigner law*, Probab. Theory
  Related Fields 95 (1993), 555–570.
* P. Biane, *On the free convolution with a semi-circular distribution*, Indiana Univ. Math. J.
  46 (1997), 705–718.
-/

public section

noncomputable section

open MeasureTheory Filter Set Complex
open scoped NNReal Topology

namespace TauCeti.Probability

/-- The resolvent transforms `m_t = resolventTransform (μ t)` of a family of measures on `ℝ` solve
the complex Burgers equation `∂_t m_t(z) = m_t(z) ∂_z m_t(z)` in integrated form: for every `z` in
the upper half-plane and every time `t`, the integrand `s ↦ m_s(z) ∂_z m_s(z)` is integrable on
`[0, t]` and `m_t(z) = m_0(z) + ∫₀ᵗ m_s(z) ∂_z m_s(z) ds`. -/
def IsBurgersFlow (μ : ℝ≥0 → Measure ℝ) : Prop :=
  ∀ z : ℂ, 0 < z.im → ∀ t : ℝ≥0,
    IntervalIntegrable (fun s : ℝ ↦ resolventTransform (μ s.toNNReal) z *
      deriv (resolventTransform (μ s.toNNReal)) z) volume 0 t ∧
    resolventTransform (μ t) z = resolventTransform (μ 0) z +
      ∫ s in (0 : ℝ)..t, resolventTransform (μ s.toNNReal) z *
        deriv (resolventTransform (μ s.toNNReal)) z

variable {μ ν : ℝ≥0 → Measure ℝ}

/-- Unfolding `IsBurgersFlow`: the integrability of `s ↦ m_s(z) ∂_z m_s(z)` on `[0, t]` and the
integrated equation, at every point of the upper half-plane and every time. -/
theorem isBurgersFlow_iff : IsBurgersFlow μ ↔ ∀ z : ℂ, 0 < z.im → ∀ t : ℝ≥0,
    IntervalIntegrable (fun s : ℝ ↦ resolventTransform (μ s.toNNReal) z *
      deriv (resolventTransform (μ s.toNNReal)) z) volume 0 t ∧
    resolventTransform (μ t) z = resolventTransform (μ 0) z +
      ∫ s in (0 : ℝ)..t, resolventTransform (μ s.toNNReal) z *
        deriv (resolventTransform (μ s.toNNReal)) z :=
  Iff.rfl

namespace IsBurgersFlow

/-- Along a Burgers flow the integrand `s ↦ m_s(z) ∂_z m_s(z)` is integrable on `[0, t]`. -/
theorem intervalIntegrable (hμ : IsBurgersFlow μ) {z : ℂ} (hz : 0 < z.im) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ ↦ resolventTransform (μ s.toNNReal) z *
      deriv (resolventTransform (μ s.toNNReal)) z) volume 0 t :=
  (hμ z hz t).1

/-- The integrated Burgers equation `m_t(z) = m_0(z) + ∫₀ᵗ m_s(z) ∂_z m_s(z) ds`. -/
theorem resolventTransform_eq (hμ : IsBurgersFlow μ) {z : ℂ} (hz : 0 < z.im) (t : ℝ≥0) :
    resolventTransform (μ t) z = resolventTransform (μ 0) z +
      ∫ s in (0 : ℝ)..t, resolventTransform (μ s.toNNReal) z *
        deriv (resolventTransform (μ s.toNNReal)) z :=
  (hμ z hz t).2

/-- **Burgers flows from the differentiated equation.** If, at every point `z` of the upper
half-plane, `t ↦ m_t(z)` is continuous, the integrand `s ↦ m_s(z) ∂_z m_s(z)` is integrable on
each `[0, t]`, and `s ↦ m_s(z)` has right derivative `m_t(z) ∂_z m_t(z)` at every time `t ≥ 0`,
then the family is a Burgers flow. -/
theorem of_hasDerivWithinAt
    (hc : ∀ z : ℂ, 0 < z.im → Continuous fun t : ℝ≥0 ↦ resolventTransform (μ t) z)
    (hi : ∀ z : ℂ, 0 < z.im → ∀ t : ℝ≥0,
      IntervalIntegrable (fun s : ℝ ↦ resolventTransform (μ s.toNNReal) z *
        deriv (resolventTransform (μ s.toNNReal)) z) volume 0 t)
    (hd : ∀ z : ℂ, 0 < z.im → ∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt (fun s : ℝ ↦ resolventTransform (μ s.toNNReal) z)
        (resolventTransform (μ t.toNNReal) z * deriv (resolventTransform (μ t.toNNReal)) z)
        (Ici t) t) :
    IsBurgersFlow μ := by
  refine fun z hz t ↦ ⟨hi z hz t, ?_⟩
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le t.coe_nonneg
    ((hc z hz).comp continuous_real_toNNReal).continuousOn
    (fun s hs ↦ (hd z hz s hs.1.le).mono Ioi_subset_Ici_self) (hi z hz t)
  simp only [Function.comp_apply, Real.toNNReal_coe, Real.toNNReal_zero] at hftc
  rw [hftc]
  ring

end IsBurgersFlow

/-- For a probability measure in the upper half-plane, the difference quotient of the transform
`m` at `z` is within `‖w - z‖ / ((Im z)² Im w)` of `m'(z)`. -/
private lemma norm_slope_sub_deriv_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) (hwz : w ≠ z) :
    ‖slope (resolventTransform ρ) z w - deriv (resolventTransform ρ) z‖ ≤
      ‖w - z‖ / (z.im ^ 2 * w.im) := by
  have h := norm_slope_resolventTransform_sub_deriv_le (μ := ρ) hz.ne' hw.ne' hwz
  rwa [probReal_univ, mul_one, abs_of_pos hz, abs_of_pos hw] at h

/-- Along the line `u ↦ z - u c` with `Im c ≥ 0` the imaginary part is antitone. -/
private lemma im_sub_mul_le_im_sub_mul {z c : ℂ} (hc : 0 ≤ c.im) {u t : ℝ} (hu : u ≤ t) :
    (z - t * c).im ≤ (z - u * c).im := by
  simp only [sub_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
  nlinarith

namespace IsBurgersFlow

variable [∀ t, IsProbabilityMeasure (μ t)]

/-- Along a Burgers flow of probability measures the transform at a point `z` of the upper
half-plane is Lipschitz in time: `‖m_t(z) - m_s(z)‖ ≤ (Im z)⁻³ |t - s|`. -/
theorem norm_resolventTransform_sub_le (hμ : IsBurgersFlow μ) {z : ℂ} (hz : 0 < z.im)
    (s t : ℝ≥0) :
    ‖resolventTransform (μ t) z - resolventTransform (μ s) z‖ ≤ (z.im ^ 3)⁻¹ * |(t : ℝ) - s| := by
  rw [hμ.resolventTransform_eq hz t, hμ.resolventTransform_eq hz s, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (hμ.intervalIntegrable hz t)
      (hμ.intervalIntegrable hz s)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun u _ ↦ ?_
  have h := norm_resolventTransform_mul_deriv_le (μ := μ u.toNNReal) hz.ne'
  rwa [probReal_univ, one_pow, mul_one, abs_of_pos hz, inv_pow] at h

/-- Along a Burgers flow of probability measures, `(t, z) ↦ m_t(z)` is jointly continuous on
time times the upper half-plane. -/
theorem continuousOn_resolventTransform (hμ : IsBurgersFlow μ) :
    ContinuousOn (fun p : ℝ≥0 × ℂ ↦ resolventTransform (μ p.1) p.2)
      (univ ×ˢ {w : ℂ | 0 < w.im}) := by
  rintro p ⟨-, hp⟩
  have hc : 0 < p.2.im / 2 := by simp only [mem_ofPred_eq] at hp; linarith
  -- On `{Im w > c}` the transform is Lipschitz in time uniformly in `w`.
  have hK : ContinuousOn (fun p : ℝ≥0 × ℂ ↦ resolventTransform (μ p.1) p.2)
      (univ ×ˢ {w : ℂ | p.2.im / 2 < w.im}) := by
    refine continuousOn_prod_of_continuousOn_lipschitzOnWith _
      (Real.toNNReal ((p.2.im / 2) ^ 3)⁻¹) (fun t _ w hw ↦ ?_) (fun w hw ↦ ?_)
    · exact (hasDerivAt_resolventTransform_of_im_ne_zero
        (hc.trans hw).ne').continuousAt.continuousWithinAt
    · refine LipschitzOnWith.of_dist_le_mul fun s _ t _ ↦ ?_
      rw [dist_eq_norm, NNReal.dist_eq, Real.coe_toNNReal _ (by positivity)]
      refine (hμ.norm_resolventTransform_sub_le (hc.trans hw) t s).trans ?_
      gcongr
      exact hw.le
  refine (hK p ⟨trivial, by simp only [mem_ofPred_eq] at hp ⊢; linarith⟩).mono_of_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds ((isOpen_univ.prod (isOpen_im_gt _)).mem_nhds ⟨trivial, ?_⟩))
  simp only [mem_ofPred_eq] at hp ⊢
  linarith

/-- Along a Burgers flow of probability measures, `t ↦ m_t(z)` is continuous for every `z` in the
upper half-plane. -/
theorem continuous_resolventTransform (hμ : IsBurgersFlow μ) {z : ℂ} (hz : 0 < z.im) :
    Continuous fun t : ℝ≥0 ↦ resolventTransform (μ t) z :=
  hμ.continuousOn_resolventTransform.comp_continuous (continuous_id.prodMk continuous_const)
    fun _ ↦ ⟨trivial, hz⟩

/-- Along a Burgers flow of probability measures, `t ↦ ∂_z m_t(z)` is continuous for every `z`
in the upper half-plane. -/
theorem continuous_deriv_resolventTransform (hμ : IsBurgersFlow μ) {z : ℂ} (hz : 0 < z.im) :
    Continuous fun t : ℝ≥0 ↦ deriv (resolventTransform (μ t)) z := by
  have hw {ε : ℝ} (hε : 0 < ε) : 0 < (z + ε * I).im := by simpa using add_pos hz hε
  refine TendstoUniformly.continuous (p := 𝓝[>] (0 : ℝ))
    (F := fun (ε : ℝ) (t : ℝ≥0) ↦ slope (resolventTransform (μ t)) z (z + ε * I)) ?_ ?_
  · rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    have hδ' : 0 < δ * z.im ^ 3 := by positivity
    filter_upwards [Ioo_mem_nhdsGT hδ'] with ε hε t
    have hne : z + ε * I ≠ z := by simpa using hε.1.ne'
    rw [dist_eq_norm, norm_sub_rev]
    calc _ ≤ ‖z + ε * I - z‖ / (z.im ^ 2 * (z + ε * I).im) :=
          norm_slope_sub_deriv_le _ hz (hw hε.1) hne
      _ = ε / (z.im ^ 2 * (z + ε * I).im) := by simp [abs_of_pos hε.1]
      _ ≤ ε / (z.im ^ 2 * z.im) := by
          have : z.im ≤ (z + ε * I).im := by simpa using hε.1.le
          gcongr
          exact hε.1.le
      _ < δ := by rw [div_lt_iff₀ (by positivity)]; linarith [hε.2]
  · refine (Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [slope_def_module, smul_eq_mul]
    exact continuous_const.mul ((hμ.continuous_resolventTransform (hw hε)).sub
      (hμ.continuous_resolventTransform hz))

/-- **The Burgers equation in differentiated form.** Along a Burgers flow of probability measures,
`s ↦ m_s(z)` has right derivative `m_t(z) ∂_z m_t(z)` at every time `t ≥ 0`, for every `z` in the
upper half-plane. -/
theorem hasDerivWithinAt_resolventTransform (hμ : IsBurgersFlow μ) {z : ℂ} (hz : 0 < z.im)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ ↦ resolventTransform (μ s.toNNReal) z)
      (resolventTransform (μ t.toNNReal) z * deriv (resolventTransform (μ t.toNNReal)) z)
      (Ici t) t := by
  have hg : Continuous fun s : ℝ ↦ resolventTransform (μ s.toNNReal) z *
      deriv (resolventTransform (μ s.toNNReal)) z :=
    ((hμ.continuous_resolventTransform hz).comp continuous_real_toNNReal).mul
      ((hμ.continuous_deriv_resolventTransform hz).comp continuous_real_toNNReal)
  refine ((hg.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add
    (resolventTransform (μ 0) z)).hasDerivWithinAt.congr_of_mem (fun u hu ↦ ?_) self_mem_Ici
  rw [hμ.resolventTransform_eq hz, Real.coe_toNNReal u (ht.trans hu)]

/-- Along a line `u ↦ z - u c` that stays in the upper half-plane up to time `t`, the increment
`u ↦ m_u(z - u c) - m_u(z - s c)` has right derivative `-c ∂_z m_s(z - s c)` at `s < t`, by the
second-order Taylor bound for `m_u` uniformly in `u`. -/
private lemma hasDerivWithinAt_resolventTransform_sub_mul_sub (hμ : IsBurgersFlow μ) {z c : ℂ}
    (hc : 0 ≤ c.im) {s t : ℝ} (hst : s < t) (ht : 0 < (z - t * c).im) :
    HasDerivWithinAt (fun u : ℝ ↦ resolventTransform (μ u.toNNReal) (z - u * c) -
      resolventTransform (μ u.toNNReal) (z - s * c))
      (-c * deriv (resolventTransform (μ s.toNNReal)) (z - s * c)) (Ici s) s := by
  rcases eq_or_ne c 0 with rfl | hc0
  · simpa using hasDerivWithinAt_const s (Ici s) (0 : ℂ)
  have hle {u : ℝ} (hu : u ≤ t) := im_sub_mul_le_im_sub_mul (z := z) hc hu
  set w := z - s * c with hw_def
  have hw : 0 < w.im := ht.trans_le (hle hst.le)
  refine HasDerivWithinAt.Ici_of_Ioi ((hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl s)).2 ?_)
  have hD : Tendsto (fun u : ℝ ↦ -c * deriv (resolventTransform (μ u.toNNReal)) w)
      (𝓝[>] s) (𝓝 (-c * deriv (resolventTransform (μ s.toNNReal)) w)) :=
    ((((hμ.continuous_deriv_resolventTransform hw).comp
      continuous_real_toNNReal).tendsto s).mono_left nhdsWithin_le_nhds).const_mul _
  -- The slope differs from `-c m_u'(w)` by at most `‖c‖² (u - s) / Im (z - t c)³`.
  have hE : Tendsto (fun u : ℝ ↦ slope (fun u : ℝ ↦ resolventTransform (μ u.toNNReal)
      (z - u * c) - resolventTransform (μ u.toNNReal) w) s u -
        -c * deriv (resolventTransform (μ u.toNNReal)) w) (𝓝[>] s) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun u ↦ ‖c‖ ^ 2 * (u - s) / (z - t * c).im ^ 3) ?_ ?_
    · filter_upwards [Ioc_mem_nhdsGT hst] with u hu
      have hu' : 0 < (z - u * c).im := ht.trans_le (hle hu.2)
      have hus : 0 < u - s := sub_pos.2 hu.1
      have hus' : ((u - s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hus.ne'
      have hdiff : z - u * c - w = -((u - s : ℝ) * c) := by rw [hw_def]; push_cast; ring
      have hne : z - u * c ≠ w := by
        rw [← sub_ne_zero, hdiff, neg_ne_zero]; exact mul_ne_zero hus' hc0
      -- The real slope is `-c` times the complex difference quotient of `m_u` at `w`.
      have hrw : slope (fun u : ℝ ↦ resolventTransform (μ u.toNNReal) (z - u * c) -
          resolventTransform (μ u.toNNReal) w) s u -
            -c * deriv (resolventTransform (μ u.toNNReal)) w =
          -c * (slope (resolventTransform (μ u.toNNReal)) w (z - u * c) -
            deriv (resolventTransform (μ u.toNNReal)) w) := by
        simp only [slope_def_module, ← hw_def, hdiff, sub_self, sub_zero, Complex.real_smul,
          Complex.ofReal_inv, smul_eq_mul]
        field_simp
        ring
      rw [hrw, norm_mul, norm_neg]
      calc ‖c‖ * ‖_‖ ≤ ‖c‖ * (‖z - u * c - w‖ / (w.im ^ 2 * (z - u * c).im)) := by
            gcongr; exact norm_slope_sub_deriv_le _ hw hu' hne
        _ = ‖c‖ ^ 2 * (u - s) / (w.im ^ 2 * (z - u * c).im) := by
            rw [hdiff, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hus.le]
            ring
        _ ≤ ‖c‖ ^ 2 * (u - s) / ((z - t * c).im ^ 2 * (z - t * c).im) := by
            gcongr
            · exact hle hst.le
            · exact hle hu.2
        _ = ‖c‖ ^ 2 * (u - s) / (z - t * c).im ^ 3 := by ring
    · have hcont : Continuous fun u : ℝ ↦ ‖c‖ ^ 2 * (u - s) / (z - t * c).im ^ 3 := by fun_prop
      have h0 : Tendsto (fun u : ℝ ↦ ‖c‖ ^ 2 * (u - s) / (z - t * c).im ^ 3) (𝓝 s) (𝓝 0) := by
        simpa using hcont.tendsto s
      exact h0.mono_left nhdsWithin_le_nhds
  simpa using hE.add hD

/-- The derivative of `m` along a straight line `u ↦ z - u c` that stays in the upper half-plane
up to time `t`: at a time `s ∈ [0, t)` it has right derivative
`(m_s(z - s c) - c) ∂_z m_s(z - s c)`. -/
private lemma hasDerivWithinAt_resolventTransform_sub_mul (hμ : IsBurgersFlow μ) {z c : ℂ}
    (hc : 0 ≤ c.im) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : 0 < (z - t * c).im) :
    HasDerivWithinAt (fun u : ℝ ↦ resolventTransform (μ u.toNNReal) (z - u * c))
      ((resolventTransform (μ s.toNNReal) (z - s * c) - c) *
        deriv (resolventTransform (μ s.toNNReal)) (z - s * c)) (Ici s) s := by
  have hw : 0 < (z - s * c).im := ht.trans_le (im_sub_mul_le_im_sub_mul hc hst.le)
  -- Split `m_u(z - u c) = (m_u(z - u c) - m_u(z - s c)) + m_u(z - s c)`; the second summand is
  -- the differentiated Burgers equation at the fixed point `z - s c`.
  convert (hasDerivWithinAt_resolventTransform_sub_mul_sub hμ hc hst ht).add
    (hμ.hasDerivWithinAt_resolventTransform hw hs) using 1
  · funext u
    simp only [Pi.add_apply, sub_add_cancel]
  · ring

/-- **Constancy along characteristics.** Along a Burgers flow of probability measures, the
transform is constant along the characteristic from `z` in the upper half-plane, as long as the
characteristic stays there: `m_t(z - t m_0(z)) = m_0(z)` whenever `Im (z - t m_0(z)) > 0`. -/
theorem resolventTransform_sub_mul_resolventTransform (hμ : IsBurgersFlow μ) {z : ℂ}
    (hz : 0 < z.im) {t : ℝ≥0}
    (ht : 0 < (z - t * resolventTransform (μ 0) z).im) :
    resolventTransform (μ t) (z - t * resolventTransform (μ 0) z) =
      resolventTransform (μ 0) z := by
  set c := resolventTransform (μ 0) z with hc_def
  have hc : 0 ≤ c.im := (im_resolventTransform_pos (IsProbabilityMeasure.ne_zero _) hz).le
  have hle {u : ℝ} (hu : u ≤ (t : ℝ)) := im_sub_mul_le_im_sub_mul (z := z) hc hu
  -- `F u = m_u(z - u c) - c` vanishes at `0` and satisfies `F' = F m_u'(z - u c)`.
  set F : ℝ → ℂ := fun u ↦ resolventTransform (μ u.toNNReal) (z - u * c) - c with hF_def
  have hF0 : F 0 = 0 := by simp [hF_def, hc_def]
  have hcont : ContinuousOn F (Icc 0 t) := by
    refine (hμ.continuousOn_resolventTransform.comp
      (continuous_real_toNNReal.prodMk (continuous_const.sub
        (continuous_ofReal.mul continuous_const))).continuousOn fun u hu ↦ ⟨trivial, ?_⟩).sub
      continuousOn_const
    exact ht.trans_le (hle hu.2)
  have hderiv : ∀ u ∈ Ico (0 : ℝ) t, HasDerivWithinAt F
      (F u * deriv (resolventTransform (μ u.toNNReal)) (z - u * c)) (Ici u) u :=
    fun u hu ↦ (hasDerivWithinAt_resolventTransform_sub_mul hμ hc hu.1 hu.2 ht).sub_const c
  have hbound : ∀ u ∈ Ico (0 : ℝ) t,
      ‖F u * deriv (resolventTransform (μ u.toNNReal)) (z - u * c)‖ ≤
        ((z - t * c).im ^ 2)⁻¹ * ‖F u‖ + 0 := by
    intro u hu
    have hu' : 0 < (z - u * c).im := ht.trans_le (hle hu.2.le)
    have hd := norm_deriv_resolventTransform_le (μ := μ u.toNNReal) hu'.ne'
    rw [probReal_univ, mul_one, abs_of_pos hu', inv_pow] at hd
    rw [add_zero, norm_mul, mul_comm]
    gcongr
    exact hd.trans (by gcongr; exact hle hu.2.le)
  have hFt := norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv
    (show ‖F 0‖ ≤ 0 by simp [hF0]) hbound
    t ⟨t.coe_nonneg, le_rfl⟩
  rw [gronwallBound_ε0_δ0, norm_le_zero_iff, hF_def] at hFt
  simpa [sub_eq_zero] using hFt

end IsBurgersFlow

/-- Let `m` be the transform of a probability measure and `t` real. If two functions analytic in
the upper half-plane agree at every point `z - t m(z)` of the upper half-plane with `z` in the upper
half-plane, then they agree on the whole upper half-plane, since near `i ∞` the map
`z ↦ z - t m(z)` is continuous and injective. -/
private lemma eqOn_of_eq_sub_mul_resolventTransform (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (t : ℝ) {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f {w : ℂ | 0 < w.im})
    (hg : AnalyticOnNhd ℂ g {w : ℂ | 0 < w.im})
    (hfg : ∀ z : ℂ, 0 < z.im → 0 < (z - t * resolventTransform ρ z).im →
      f (z - t * resolventTransform ρ z) = g (z - t * resolventTransform ρ z)) :
    EqOn f g {w : ℂ | 0 < w.im} := by
  set r := |t| * ρ.real univ + 1
  have hr : 0 < r := by positivity
  set z₀ : ℂ := ⟨0, 2 * r⟩
  have hz₀ : r < z₀.im := show r < 2 * r by linarith
  have hU : {z : ℂ | r < z.im} ∈ 𝓝 z₀ := (isOpen_im_gt _).mem_nhds hz₀
  have hcont : ContinuousAt (fun z : ℂ ↦ z - t * resolventTransform ρ z) z₀ :=
    continuousAt_id.sub (continuousAt_const.mul
      (hasDerivAt_resolventTransform_of_im_ne_zero (hr.trans hz₀).ne').continuousAt)
  -- The images of a punctured neighbourhood of `z₀` accumulate at the image of `z₀`.
  have htend : Tendsto (fun z : ℂ ↦ z - t * resolventTransform ρ z) (𝓝[≠] z₀)
      (𝓝[≠] (z₀ - t * resolventTransform ρ z₀)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hcont.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hU, self_mem_nhdsWithin] with z hz hne
    exact fun h ↦ hne (eq_of_sub_mul_resolventTransform_eq hz hz₀ h)
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, f (z - t * resolventTransform ρ z) =
      g (z - t * resolventTransform ρ z) := by
    refine Eventually.frequently ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hU] with z hz
    exact hfg z (hr.trans hz) (im_sub_mul_resolventTransform_pos hz)
  exact hf.eqOn_of_preconnected_of_frequently_eq hg (convex_halfSpace_im_gt 0).isPreconnected
    (im_sub_mul_resolventTransform_pos hz₀) (htend.frequently hfreq)

namespace IsBurgersFlow

variable [∀ t, IsProbabilityMeasure (μ t)]

/-- **The Pastur equation.** Along a Burgers flow of probability measures,
`m_t(w) = m_0(w + t m_t(w))` for every `w` in the upper half-plane. -/
theorem resolventTransform_eq_resolventTransform_add_mul (hμ : IsBurgersFlow μ) (t : ℝ≥0)
    {w : ℂ} (hw : 0 < w.im) :
    resolventTransform (μ t) w =
      resolventTransform (μ 0) (w + t * resolventTransform (μ t) w) := by
  have hmaps : MapsTo (fun w : ℂ ↦ w + ((t : ℝ) : ℂ) * resolventTransform (μ t) w)
      {w : ℂ | 0 < w.im} {w : ℂ | 0 < w.im} := by
    intro w hw
    have := im_resolventTransform_pos (IsProbabilityMeasure.ne_zero (μ t)) hw
    simp only [mem_ofPred_eq, add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero] at hw ⊢
    have : 0 ≤ (t : ℝ) * (resolventTransform (μ t) w).im := by positivity
    linarith
  refine eqOn_of_eq_sub_mul_resolventTransform (μ 0) t analyticOnNhd_resolventTransform_setOf_im_pos
    (analyticOnNhd_resolventTransform_setOf_im_pos.comp (analyticOnNhd_id.add
      (analyticOnNhd_const.mul analyticOnNhd_resolventTransform_setOf_im_pos)) hmaps)
    (fun z hz hzt ↦ ?_) hw
  simp only [Function.comp_apply, Pi.add_apply]
  rw [hμ.resolventTransform_sub_mul_resolventTransform hz hzt, sub_add_cancel]

/-- **Uniqueness.** Two Burgers flows of probability measures with the same initial measure
coincide. -/
theorem eq [∀ t, IsProbabilityMeasure (ν t)] (hμ : IsBurgersFlow μ) (hν : IsBurgersFlow ν)
    (h₀ : μ 0 = ν 0) : μ = ν := by
  funext t
  refine Measure.ext_of_resolventTransform fun w hw ↦
    eqOn_of_eq_sub_mul_resolventTransform (μ 0) t analyticOnNhd_resolventTransform_setOf_im_pos
      analyticOnNhd_resolventTransform_setOf_im_pos (fun z hz hzt ↦ ?_) hw
  rw [hμ.resolventTransform_sub_mul_resolventTransform hz hzt]
  rw [h₀] at hzt ⊢
  rw [hν.resolventTransform_sub_mul_resolventTransform hz hzt]

end IsBurgersFlow

/-! ### The semicircle flow -/

section Semicircle

variable {a : ℝ}

/-- **The semicircle flow.** The semicircle laws `semicircleReal a t` of variance `t` centred at
`a` form a Burgers flow. -/
theorem isBurgersFlow_semicircleReal (a : ℝ) : IsBurgersFlow fun t ↦ semicircleReal a t :=
  .of_hasDerivWithinAt (fun _ hz ↦ continuous_resolventTransform_semicircleReal hz)
    (fun _ hz _ ↦ (((continuous_resolventTransform_semicircleReal hz).mul
      (continuous_deriv_resolventTransform_semicircleReal hz)).comp
        continuous_real_toNNReal).intervalIntegrable _ _)
    fun _ hz _ ↦ hasDerivWithinAt_resolventTransform_semicircleReal hz

/-- **The Burgers flow from a point mass.** A Burgers flow of probability measures started at the
point mass at `a` is the semicircle flow `t ↦ semicircleReal a t`. -/
theorem IsBurgersFlow.eq_semicircleReal [∀ t, IsProbabilityMeasure (μ t)]
    (hμ : IsBurgersFlow μ) (h₀ : μ 0 = Measure.dirac a) : μ = fun t ↦ semicircleReal a t :=
  hμ.eq (isBurgersFlow_semicircleReal a) (by rw [h₀, semicircleReal_zero_var])

end Semicircle

end TauCeti.Probability
