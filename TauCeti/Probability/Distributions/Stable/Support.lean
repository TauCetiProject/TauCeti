/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.DensityConvolution
import Mathlib.MeasureTheory.Measure.Portmanteau
import TauCeti.Analysis.Convolution.Positivity
import TauCeti.Probability.Distributions.Stable.Approximation.Centering
import TauCeti.Probability.Distributions.Stable.Compensation
import TauCeti.Probability.Distributions.Stable.SmallJump.Limit

/-!
# Support and density positivity of stable laws

A positive-scale stable law has topological support all of `ℝ`, except in the fully skewed
cases of shape below one. Those are supported on a half-line ending at the `S₁` location
`d = stableS1Location α β s m`: on `[d, ∞)` at skewness `1`, and on `(-∞, d]` at skewness `-1`.
In particular, fully skewed laws of shape at least one have full support, even though all of
their jumps have the same sign.

For strict interior skewness, the large-jump compound-Poisson factor already has full support,
and convolution with the small-jump probability factor preserves this property.

At full skewness, the compound-Poisson approximations are supported on half-lines starting at
their negated sine compensators. Below shape one these compensators converge to the
negated `S₁` location, and weak convergence confines the limit law to `[d, ∞)`. Conversely, the
small-jump factors of the large-jump/small-jump decomposition concentrate at zero as their cutoff
shrinks. So they have support points near zero, while the large-jump half-lines eventually
contain any fixed neighbourhood of a point above `d`. At shape at least one, the compensators
diverge and these half-lines eventually contain any fixed neighbourhood of any point.

The continuous density is strictly positive exactly on the interior of the support. To see this,
split the law into two identically distributed stable factors with half the scale power and half
the `S₁` location. Their supports are intervals, so the convolution positivity theorem applies
even before either density is known to be positive in the interior of its support.

## Main results

* `TauCeti.Probability.support_stableMeasure_of_abs_lt_one` and
  `TauCeti.Probability.support_stableMeasure_of_one_le` give full topological support.
* `TauCeti.Probability.support_stableMeasure_one_of_lt_one` and
  `TauCeti.Probability.support_stableMeasure_neg_one_of_lt_one` give the half-line supports.
* `TauCeti.Probability.support_stableMeasure_eq_univ_iff` characterizes full support.
* `TauCeti.Probability.stablePDFReal_pos_of_abs_lt_one`,
  `TauCeti.Probability.stablePDFReal_pos_of_one_le`,
  `TauCeti.Probability.stablePDFReal_one_pos_iff_of_lt_one`, and
  `TauCeti.Probability.stablePDFReal_neg_one_pos_iff_of_lt_one` give strict density positivity
  on the support interior.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1 and section 3.2.
* K. Sato, *Lévy Processes and Infinitely Divisible Distributions*, Cambridge University Press,
  1999, section 24.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set ContinuousLinearMap
open scoped Convolution ENNReal NNReal Pointwise Topology

namespace TauCeti.Probability

variable {α β : ℝ} {s : ℝ≥0}

/-! ### Reduction to the standardized law -/

/-- A positive-scale non-Gaussian stable law is the affine image of the standardized law, so its
support is the affine image of the standardized support. -/
private theorem support_stableMeasure_eq_image (hs : 0 < s) (m : ℝ) :
    (stableMeasure α β s m).support =
      (fun x ↦ m + (s : ℝ) * x) '' (stableMeasure α β 1 0).support := by
  rw [← stableMeasure_one_zero_map_affine hs, support_map_affine (NNReal.coe_pos.2 hs).ne']

/-- Full support of the standardized non-Gaussian law gives full support at every positive
scale and location, and the Gaussian shape always has full support. -/
private theorem support_stableMeasure_eq_univ_of_standard (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1)
    (hs : 0 < s) (m : ℝ) (h : α ≠ 2 → (stableMeasure α β 1 0).support = univ) :
    (stableMeasure α β s m).support = univ := by
  rcases hα.2.eq_or_lt with htwo | htwo
  · subst α
    rw [stableMeasure_two hβ]
    apply eq_univ_of_univ_subset
    simpa only [Measure.support_eq_univ] using
      (gaussianReal_absolutelyContinuous' m (by positivity : 2 * s ^ 2 ≠ 0)).support_mono
  · rw [support_stableMeasure_eq_image hs, h htwo.ne, image_univ]
    exact range_eq_univ.mpr fun y ↦ ⟨(y - m) / s, by
      field_simp [(NNReal.coe_pos.2 hs).ne']
      ring⟩

/-! ### Strict interior skewness -/

private theorem support_standardStableMeasure_of_abs_lt_one (hα : α ∈ Ioo 0 2)
    (hβ : |β| < 1) : (stableMeasure α β 1 0).support = univ := by
  obtain ⟨μ, hμ, -⟩ := existsUnique_conv_stableCompensatedPoissonMeasure_eq hα hβ.le
    (by norm_num : (0 : ℝ) < 1)
  let _ := isProbabilityMeasure_stableCompensatedPoissonMeasure hα hβ.le zero_lt_one
  obtain ⟨a, ha⟩ := Measure.nonempty_support (IsProbabilityMeasure.ne_zero (μ : Measure ℝ))
  apply eq_univ_of_forall
  intro x
  rw [← hμ]
  have hy : x - a ∈ (stableCompensatedPoissonMeasure α β 1).support := by
    simp [support_stableCompensatedPoissonMeasure_of_abs_lt_one hα hβ zero_lt_one]
  convert Measure.add_mem_support_conv ha hy using 1
  ring

/-- A stable law of valid shape, positive scale and strict interior skewness has full
topological support. This includes shape one and the Gaussian shape two. -/
@[simp]
theorem support_stableMeasure_of_abs_lt_one (hα : α ∈ Ioc 0 2) (hβ : |β| < 1)
    (hs : 0 < s) (m : ℝ) : (stableMeasure α β s m).support = univ :=
  support_stableMeasure_eq_univ_of_standard hα hβ.le hs m fun htwo ↦
    support_standardStableMeasure_of_abs_lt_one ⟨hα.1, lt_of_le_of_ne hα.2 htwo⟩ hβ

/-! ### Full skewness -/

/-- A point lies in the standardized stable support whenever a fixed neighbourhood of it lies
in the support of the compensated large-jump approximations for all small cutoffs. The
small-jump factors concentrate at zero, so they supply support points near zero to add. -/
private theorem mem_support_standardStableMeasure_of_eventually (hα : α ∈ Ioo 0 2)
    (hβ : |β| ≤ 1) {y δ : ℝ} (hδ : 0 < δ)
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      Metric.ball y δ ⊆ (stableCompensatedPoissonMeasure α β r).support) :
    y ∈ (stableMeasure α β 1 0).support := by
  let r : ℕ → ℝ := fun n ↦ (2 : ℝ)⁻¹ ^ n
  have hr (n : ℕ) : 0 < r n := by positivity
  have hrlim : Tendsto r atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
      (by norm_num), .of_forall hr⟩
  choose ρ hρ using fun n ↦
    (existsUnique_conv_stableCompensatedPoissonMeasure_eq hα hβ (hr n)).exists
  -- The small-jump factors converge weakly to the point mass at zero.
  have hball := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (tendsto_smallJumpFactor_dirac hα hβ hr hrlim hρ) (Metric.isOpen_ball (x := 0) (ε := δ))
  have hpos : ∀ᶠ n in atTop, 0 < (ρ n : Measure ℝ) (Metric.ball 0 δ) := by
    refine eventually_lt_of_lt_liminf (lt_of_lt_of_le ?_ hball)
    simp [Metric.mem_ball, hδ]
  obtain ⟨n, hn, hsub⟩ := (hpos.and (hrlim.eventually h)).exists
  obtain ⟨a, ha, haS⟩ := Measure.nonempty_inter_support_of_pos hn
  have hya : y - a ∈ (stableCompensatedPoissonMeasure α β (r n)).support :=
    hsub (by simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using ha)
  let _ := isProbabilityMeasure_stableCompensatedPoissonMeasure hα hβ (hr n)
  have hmem := Measure.add_mem_support_conv haS hya
  rwa [hρ n, add_sub_cancel] at hmem

/-- Below shape one at full positive skewness, the standardized law gives no mass to the left
of its `S₁` location: the compound-Poisson approximations live to the right of their
compensators, which converge to that location. -/
private theorem support_standardStableMeasure_one_subset (hα : α ∈ Ioo 0 1) :
    (stableMeasure α 1 1 0).support ⊆ Ici (stableS1Location α 1 1 0) := by
  have hα2 : α ∈ Ioo 0 2 := ⟨hα.1, hα.2.trans one_lt_two⟩
  have hβ : |(1 : ℝ)| ≤ 1 := by simp
  intro x hx
  by_contra hxd
  rw [mem_Ici, not_le] at hxd
  set d := stableS1Location α 1 1 0
  set y := (x + d) / 2 with hy
  let ε : ℕ → ℝ := fun n ↦ (2 : ℝ)⁻¹ ^ n
  have hε (n : ℕ) : 0 < ε n := by positivity
  have hεlim : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
      (by norm_num), .of_forall hε⟩
  have hc := (tendsto_integral_sin_stableLevyMeasure_nhds hα hβ).comp hεlim
  rw [← neg_neg (∫ y, sin y ∂stableLevyMeasure α 1),
    neg_integral_sin_stableLevyMeasure_eq_stableS1Location hα hβ] at hc
  -- Eventually every approximation vanishes on the open half-line `(-∞, y)`.
  have hzero : ∀ᶠ n in atTop,
      stableCompensatedPoissonMeasure α 1 (ε n) (Iio y) = 0 := by
    filter_upwards [hc.eventually_lt_const (by linarith [hy] : -d < -y)] with n hn
    simp only [Function.comp_apply] at hn
    have hsub : Iio y ⊆ (stableCompensatedPoissonMeasure α 1 (ε n)).supportᶜ := by
      intro z hz hzS
      rw [support_stableCompensatedPoissonMeasure_one hα2 (hε n)] at hzS
      rw [mem_Iio] at hz
      rcases hzS with hzS | hzS
      · rw [mem_singleton_iff] at hzS
        linarith
      · rw [mem_Ici] at hzS
        linarith [hε n]
    exact measure_mono_null hsub Measure.measure_compl_support
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (tendsto_stableCompensatedPoissonMeasure_invTwoPow hα2 hβ) (isOpen_Iio (a := y))
  have hnull : stableMeasure α 1 1 0 (Iio y) = 0 :=
    le_antisymm (hlim.trans (liminf_le_of_frequently_le' (hzero.mono fun n hn ↦ hn.le).frequently))
      zero_le
  exact (Measure.notMem_support_iff_exists.2
    ⟨Iio y, Iio_mem_nhds (by linarith [hy]), hnull⟩) hx

/-- Below shape one at full positive skewness, the standardized support is the half-line to
the right of the `S₁` location. -/
private theorem support_standardStableMeasure_one_of_lt_one (hα : α ∈ Ioo 0 1) :
    (stableMeasure α 1 1 0).support = Ici (stableS1Location α 1 1 0) := by
  have hα2 : α ∈ Ioo 0 2 := ⟨hα.1, hα.2.trans one_lt_two⟩
  have hβ : |(1 : ℝ)| ≤ 1 := by simp
  refine (support_standardStableMeasure_one_subset hα).antisymm ?_
  rw [← closure_Ioi]
  refine closure_minimal (fun y hy ↦ ?_) Measure.isClosed_support
  set d := stableS1Location α 1 1 0
  rw [mem_Ioi] at hy
  have hδ : 0 < (y - d) / 3 := by linarith
  apply mem_support_standardStableMeasure_of_eventually hα2 hβ hδ
  have hc := tendsto_integral_sin_stableLevyMeasure_nhds hα hβ
  rw [← neg_neg (∫ y, sin y ∂stableLevyMeasure α 1),
    neg_integral_sin_stableLevyMeasure_eq_stableS1Location hα hβ] at hc
  -- For small cutoffs, the large-jump half-line starts below `y - (y - d) / 3`.
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds,
    hc.eventually_const_lt (by linarith : -d - (y - d) / 3 < -d)] with r hr hrδ hcr
  rw [support_stableCompensatedPoissonMeasure_one hα2 hr]
  intro z hz
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hz
  exact Or.inr (by rw [mem_Ici]; linarith)

/-- From shape one on, the fully skewed standardized laws have full support: their large-jump
half-lines eventually contain every fixed neighbourhood. -/
private theorem support_standardStableMeasure_of_one_le (hα : α ∈ Ico 1 2) (hβ : |β| = 1) :
    (stableMeasure α β 1 0).support = univ := by
  have hα2 : α ∈ Ioo 0 2 := ⟨by linarith [hα.1], hα.2⟩
  refine eq_univ_of_forall fun y ↦ mem_support_standardStableMeasure_of_eventually hα2 hβ.le
    one_pos ?_
  rcases (abs_eq zero_le_one).1 hβ with rfl | rfl
  · refine (eventually_Ici_subset_support_stableCompensatedPoissonMeasure_one hα (y - 1)).mono
      fun r hr z hz ↦ hr ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hz
    rw [mem_Ici]
    linarith
  · refine (eventually_Iic_subset_support_stableCompensatedPoissonMeasure_neg_one hα
      (y + 1)).mono fun r hr z hz ↦ hr ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hz
    rw [mem_Iic]
    linarith

/-- From shape one on, every positive-scale stable law has full topological support, including
both fully skewed laws and the Gaussian shape two. -/
@[simp]
theorem support_stableMeasure_of_one_le (hα : α ∈ Icc 1 2) (hβ : |β| ≤ 1) (hs : 0 < s)
    (m : ℝ) : (stableMeasure α β s m).support = univ := by
  have hα' : α ∈ Ioc 0 2 := ⟨by linarith [hα.1], hα.2⟩
  rcases hβ.lt_or_eq with hβ | hβ
  · exact support_stableMeasure_of_abs_lt_one hα' hβ hs m
  · exact support_stableMeasure_eq_univ_of_standard hα' hβ.le hs m fun htwo ↦
      support_standardStableMeasure_of_one_le ⟨hα.1, lt_of_le_of_ne hα.2 htwo⟩ hβ

/-- Below shape one, a positive-scale stable law of skewness `1` has topological support the
half-line `[d, ∞)` starting at its `S₁` location `d`. -/
@[simp]
theorem support_stableMeasure_one_of_lt_one (hα : α ∈ Ioo 0 1) (hs : 0 < s) (m : ℝ) :
    (stableMeasure α 1 s m).support = Ici (stableS1Location α 1 s m) := by
  rw [support_stableMeasure_eq_image hs, support_standardStableMeasure_one_of_lt_one hα,
    ← image_image (m + ·) ((s : ℝ) * ·), image_mul_left_Ici (NNReal.coe_pos.2 hs),
    image_const_add_Ici, stableS1Location_of_ne_one hα.2.ne, stableS1Location_of_ne_one hα.2.ne]
  congr 1
  push_cast
  ring

/-- Below shape one, a positive-scale stable law of skewness `-1` has topological support the
half-line `(-∞, d]` ending at its `S₁` location `d`. -/
@[simp]
theorem support_stableMeasure_neg_one_of_lt_one (hα : α ∈ Ioo 0 1) (hs : 0 < s) (m : ℝ) :
    (stableMeasure α (-1) s m).support = Iic (stableS1Location α (-1) s m) := by
  have hneg : (stableMeasure α 1 s (-m)).map (fun x ↦ 0 + -1 * x) =
      stableMeasure α (-1) s m := by
    simp
  rw [← hneg, support_map_affine (by norm_num), support_stableMeasure_one_of_lt_one hα hs]
  simp only [zero_add, neg_one_mul, image_neg_Ici, stableS1Location_of_ne_one hα.2.ne]
  congr 1
  ring

/-- A positive-scale stable law of valid shape has full topological support exactly when its
shape is at least one or its skewness is strictly interior. -/
theorem support_stableMeasure_eq_univ_iff (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1) (hs : 0 < s)
    (m : ℝ) : (stableMeasure α β s m).support = univ ↔ 1 ≤ α ∨ |β| < 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_contra hc
    push Not at hc
    have hα1 : α ∈ Ioo 0 1 := ⟨hα.1, hc.1⟩
    rcases (abs_eq zero_le_one).1 (le_antisymm hβ hc.2) with rfl | rfl
    · rw [support_stableMeasure_one_of_lt_one hα1 hs] at h
      have := h ▸ mem_univ (stableS1Location α 1 s m - 1)
      rw [mem_Ici] at this
      linarith
    · rw [support_stableMeasure_neg_one_of_lt_one hα1 hs] at h
      have := h ▸ mem_univ (stableS1Location α (-1) s m + 1)
      rw [mem_Iic] at this
      linarith
  · rintro (h | h)
    · exact support_stableMeasure_of_one_le ⟨h, hα.2⟩ hβ hs m
    · exact support_stableMeasure_of_abs_lt_one hα h hs m

/-! ### Density positivity -/

/-- Every positive-scale stable density is the self-convolution of the density of a stable law
with half the scale power and half the `S₁` location. -/
private theorem exists_stableDensity_convolution_self (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1)
    (hs : 0 < s) (m : ℝ) :
    ∃ (r : ℝ≥0) (c : ℝ), 0 < r ∧ stableS1Location α β r c = stableS1Location α β s m / 2 ∧
      stablePDFReal α β r c ⋆[mul ℝ ℝ] stablePDFReal α β r c = stablePDFReal α β s m := by
  let r : ℝ≥0 := (s ^ α / 2) ^ α⁻¹
  let c := stableS1Location α β s m / 2 - stableS1Location α β r 0
  have hr : 0 < r := NNReal.rpow_pos (div_pos (NNReal.rpow_pos hs) (by norm_num))
  have hpow : (r : ℝ) ^ α = (s : ℝ) ^ α / 2 := by
    simp [r, ← NNReal.coe_rpow, NNReal.rpow_inv_rpow hα.1.ne']
  have hloc : stableS1Location α β r c = stableS1Location α β s m / 2 := by
    rw [stableS1Location_eq_add α β r c]
    dsimp only [c]
    ring
  refine ⟨r, c, hr, hloc, stablePDFReal_convolution_stablePDFReal_of_eq hα hβ hβ hβ hr hr
    (by rw [hpow]; ring) (by rw [hpow]; ring) ?_⟩
  rw [hloc]
  ring

/-- If a stable density is the self-convolution of the density of a stable law with convex
support, then it is positive exactly on the interior of the sum of that support with itself. -/
private theorem stablePDFReal_pos_iff_mem_interior_add_support {m : ℝ} {r : ℝ≥0} {c : ℝ}
    (hr : 0 < r)
    (hconv : stablePDFReal α β r c ⋆[mul ℝ ℝ] stablePDFReal α β r c = stablePDFReal α β s m)
    (hconvex : Convex ℝ (stableMeasure α β r c).support) (x : ℝ) :
    0 < stablePDFReal α β s m x ↔
      x ∈ interior ((stableMeasure α β r c).support + (stableMeasure α β r c).support) := by
  have hf := continuous_stablePDFReal α β r c
  have hf0 := stablePDFReal_nonneg α β r c
  have hsupp : tsupport (stablePDFReal α β r c) = (stableMeasure α β r c).support := by
    rw [← Measure.support_withDensity_ofReal (μ := volume) hf hf0,
      ← funext (stablePDF_eq_ofReal α β r c), ← stableMeasure_eq_withDensity α β hr c]
  rw [← congrFun hconv x, ← hsupp]
  exact convolution_pos_iff_mem_interior_add_tsupport hf hf hf0 hf0
    (hsupp ▸ hconvex) (hsupp ▸ hconvex)
    (convolutionExists_stablePDFReal (integrable_stablePDFReal α β r c) α β r c x)

/-- A positive-scale stable density with full support is strictly positive everywhere. -/
private theorem stablePDFReal_pos_of_support_eq_univ (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1)
    (hs : 0 < s) (m x : ℝ)
    (hsupp : ∀ (r : ℝ≥0) (c : ℝ), 0 < r → (stableMeasure α β r c).support = univ) :
    0 < stablePDFReal α β s m x := by
  obtain ⟨r, c, hr, -, hconv⟩ := exists_stableDensity_convolution_self hα hβ hs m
  rw [stablePDFReal_pos_iff_mem_interior_add_support hr hconv
    (by rw [hsupp r c hr]; exact convex_univ), hsupp r c hr, univ_add_univ, interior_univ]
  exact mem_univ x

/-- The continuous density of a positive-scale stable law with strict interior skewness is
strictly positive at every real point, including at shapes one and two. -/
theorem stablePDFReal_pos_of_abs_lt_one (hα : α ∈ Ioc 0 2) (hβ : |β| < 1)
    (hs : 0 < s) (m x : ℝ) : 0 < stablePDFReal α β s m x :=
  stablePDFReal_pos_of_support_eq_univ hα hβ.le hs m x fun _ c hr ↦
    support_stableMeasure_of_abs_lt_one hα hβ hr c

/-- From shape one on, the continuous density of a positive-scale stable law is strictly
positive at every real point, including at full skewness. -/
theorem stablePDFReal_pos_of_one_le (hα : α ∈ Icc 1 2) (hβ : |β| ≤ 1)
    (hs : 0 < s) (m x : ℝ) : 0 < stablePDFReal α β s m x :=
  stablePDFReal_pos_of_support_eq_univ ⟨by linarith [hα.1], hα.2⟩ hβ hs m x fun _ c hr ↦
    support_stableMeasure_of_one_le hα hβ hr c

/-- Below shape one, the continuous density of a positive-scale stable law of skewness `1` is
strictly positive exactly to the right of its `S₁` location. -/
@[simp]
theorem stablePDFReal_one_pos_iff_of_lt_one (hα : α ∈ Ioo 0 1) (hs : 0 < s) (m x : ℝ) :
    0 < stablePDFReal α 1 s m x ↔ stableS1Location α 1 s m < x := by
  have hα' : α ∈ Ioc 0 2 := ⟨hα.1, (hα.2.trans one_lt_two).le⟩
  have hβ : |(1 : ℝ)| ≤ 1 := by simp
  obtain ⟨r, c, hr, hloc, hconv⟩ := exists_stableDensity_convolution_self hα' hβ hs m
  have hsupp := support_stableMeasure_one_of_lt_one hα hr c
  rw [stablePDFReal_pos_iff_mem_interior_add_support hr hconv
    (by rw [hsupp]; exact convex_Ici _), hsupp, hloc]
  set d := stableS1Location α 1 s m
  constructor
  · intro hx
    have hsub : Ici (d / 2) + Ici (d / 2) ⊆ Ici d := by
      simpa only [add_halves] using Ici_add_Ici_subset (d / 2) (d / 2)
    simpa only [interior_Ici, mem_Ioi] using interior_mono hsub hx
  · intro hx
    refine interior_maximal (fun z hz ↦ ?_) isOpen_Ioi hx
    rw [mem_Ioi] at hz
    exact ⟨d / 2, self_mem_Ici, z - d / 2, by rw [mem_Ici]; linarith, by ring⟩

/-- Below shape one, the continuous density of a positive-scale stable law of skewness `-1` is
strictly positive exactly to the left of its `S₁` location. -/
@[simp]
theorem stablePDFReal_neg_one_pos_iff_of_lt_one (hα : α ∈ Ioo 0 1) (hs : 0 < s) (m x : ℝ) :
    0 < stablePDFReal α (-1) s m x ↔ x < stableS1Location α (-1) s m := by
  have hα' : α ∈ Ioc 0 2 := ⟨hα.1, (hα.2.trans one_lt_two).le⟩
  have hβ : |(-1 : ℝ)| ≤ 1 := by simp
  obtain ⟨r, c, hr, hloc, hconv⟩ := exists_stableDensity_convolution_self hα' hβ hs m
  have hsupp := support_stableMeasure_neg_one_of_lt_one hα hr c
  rw [stablePDFReal_pos_iff_mem_interior_add_support hr hconv
    (by rw [hsupp]; exact convex_Iic _), hsupp, hloc]
  set d := stableS1Location α (-1) s m
  constructor
  · intro hx
    have hsub : Iic (d / 2) + Iic (d / 2) ⊆ Iic d := by
      simpa only [add_halves] using Iic_add_Iic_subset (d / 2) (d / 2)
    simpa only [interior_Iic, mem_Iio] using interior_mono hsub hx
  · intro hx
    refine interior_maximal (fun z hz ↦ ?_) isOpen_Iio hx
    rw [mem_Iio] at hz
    exact ⟨d / 2, self_mem_Iic, z - d / 2, by rw [mem_Iic]; linarith, by ring⟩

end TauCeti.Probability
