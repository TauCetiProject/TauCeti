/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Stable.Cdf
public import TauCeti.Probability.Distributions.Stable.Support
public import TauCeti.Probability.Quantile
import TauCeti.Probability.Distributions.Dirac

/-!
# Quantiles of stable laws

For a valid zero-scale stable law, every positive quantile level at most one gives its location,
and both one-sided endpoint limits remain at that location.

For a positive-scale stable law with strict interior skewness `|β| < 1`, the cdf is strictly
increasing on the whole real line. Every interior probability level therefore has a unique
real cdf root, given by `Measure.quantile`. The quantile is continuous and strictly increasing
on `(0, 1)`, tending to minus and plus infinity at the respective endpoints.

From shape one onward these conclusions also hold at full skewness, because the stable density
is then strictly positive on the whole real line.

Strict increase of the quantile itself only needs absence of atoms, so that result also covers
full skewness. Below shape one, the fully skewed laws have half-line support. Their interior
quantiles are the unique cdf roots in the open support interior, vary continuously, and tend to
the finite support endpoint on one side and infinity on the other.

The cdf strict-increase arguments use the exact stable support theorems; the remaining
statements specialize the general measure-level quantile API.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1 and section 3.2.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

variable {α β : ℝ} {s : ℝ≥0} {m u x : ℝ}

/-! ### Zero-scale boundary -/

/-- Every positive quantile level at most one of a valid zero-scale stable law is its location. -/
theorem quantile_stableMeasure_zero_scale (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1)
    (hu : u ∈ Ioc 0 1) : (stableMeasure α β 0 m).quantile u = m := by
  rw [stableMeasure_zero_scale hα hβ, Measure.quantile_dirac m hu.1 hu.2]

/-- Zero-scale stable quantiles tend to their location as the level decreases to zero. -/
theorem tendsto_quantile_stableMeasure_zero_scale_nhdsGT_zero (hα : α ∈ Ioc 0 2)
    (hβ : |β| ≤ 1) (m : ℝ) :
    Tendsto (fun u ↦ ((stableMeasure α β 0 m).quantile u : EReal))
      (nhdsWithin 0 (Ioi 0)) (nhds m) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  rw [quantile_stableMeasure_zero_scale hα hβ ⟨hu.1, hu.2.le⟩]

/-- Zero-scale stable quantiles tend to their location as the level increases to one. -/
theorem tendsto_quantile_stableMeasure_zero_scale_nhdsLT_one (hα : α ∈ Ioc 0 2)
    (hβ : |β| ≤ 1) (m : ℝ) :
    Tendsto (fun u ↦ ((stableMeasure α β 0 m).quantile u : EReal))
      (nhdsWithin 1 (Iio 1)) (nhds m) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  rw [quantile_stableMeasure_zero_scale hα hβ ⟨hu.1, hu.2.le⟩]

/-! ### Positive-scale laws -/

/-- A positive-scale stable cdf with strict interior skewness is strictly increasing on `ℝ`,
including at shapes one and two. -/
theorem strictMono_cdf_stableMeasure_of_abs_lt_one (hα : α ∈ Ioc 0 2) (hβ : |β| < 1)
    (hs : 0 < s) (m : ℝ) : StrictMono (cdf (stableMeasure α β s m)) := by
  let := isProbabilityMeasure_stableMeasure hα hβ.le s m
  have hmono := Measure.strictMonoOn_cdf_of_subset_support (stableMeasure α β s m)
    ordConnected_univ (by rw [support_stableMeasure_of_abs_lt_one hα hβ hs m])
  exact fun _ _ hxy ↦ hmono (mem_univ _) (mem_univ _) hxy

/-- For positive scale and strict interior skewness, the stable quantile is characterized as
the unique real root of its cdf equation at each interior probability level. -/
theorem quantile_stableMeasure_eq_iff_of_abs_lt_one (hα : α ∈ Ioc 0 2) (hβ : |β| < 1)
    (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    (stableMeasure α β s m).quantile u = x ↔ cdf (stableMeasure α β s m) x = u := by
  let := isProbabilityMeasure_stableMeasure hα hβ.le s m
  simpa using Measure.quantile_eq_iff_of_ae_mem_of_strictMonoOn _ ordConnected_univ
    (ae_of_all _ mem_univ) (continuous_cdf_stableMeasure hα hβ.le hs)
    ((strictMono_cdf_stableMeasure_of_abs_lt_one hα hβ hs m).strictMonoOn _) hu

/-- For every valid skewness, a positive-scale stable quantile is strictly increasing on
interior levels, even when the distribution is supported on a half-line. -/
theorem strictMonoOn_quantile_stableMeasure (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1)
    (hs : 0 < s) (m : ℝ) : StrictMonoOn (stableMeasure α β s m).quantile (Ioo 0 1) := by
  let := isProbabilityMeasure_stableMeasure hα hβ s m
  exact Measure.strictMonoOn_quantile _ (continuous_cdf_stableMeasure hα hβ hs)

/-- Two-sided positive-scale stable quantiles vary continuously with interior probability
levels. -/
theorem continuousOn_quantile_stableMeasure_of_abs_lt_one (hα : α ∈ Ioc 0 2)
    (hβ : |β| < 1) (hs : 0 < s) (m : ℝ) :
    ContinuousOn (stableMeasure α β s m).quantile (Ioo 0 1) := by
  let := isProbabilityMeasure_stableMeasure hα hβ.le s m
  exact Measure.continuousOn_quantile_of_strictMonoOn _ ordConnected_univ
    ((strictMono_cdf_stableMeasure_of_abs_lt_one hα hβ hs m).strictMonoOn _)
    (mapsTo_univ _ _)

/-- Two-sided positive-scale stable quantiles tend to minus infinity as the level decreases
to zero. This is a one-sided limit, not a value of the totalized quantile at zero. -/
theorem tendsto_quantile_stableMeasure_nhdsGT_zero_of_abs_lt_one (hα : α ∈ Ioc 0 2)
    (hβ : |β| < 1) (hs : 0 < s) (m : ℝ) :
    Tendsto (fun u ↦ ((stableMeasure α β s m).quantile u : EReal))
      (𝓝[>] 0) (𝓝 ⊥) := by
  let := isProbabilityMeasure_stableMeasure hα hβ.le s m
  exact Measure.tendsto_quantile_nhdsGT_zero_of_strictMono_cdf _
    (strictMono_cdf_stableMeasure_of_abs_lt_one hα hβ hs m)

/-- Two-sided positive-scale stable quantiles tend to plus infinity as the level increases
to one. This is a one-sided limit, not a value of the totalized quantile at one. -/
theorem tendsto_quantile_stableMeasure_nhdsLT_one_of_abs_lt_one (hα : α ∈ Ioc 0 2)
    (hβ : |β| < 1) (hs : 0 < s) (m : ℝ) :
    Tendsto (fun u ↦ ((stableMeasure α β s m).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) := by
  let := isProbabilityMeasure_stableMeasure hα hβ.le s m
  exact Measure.tendsto_quantile_nhdsLT_one_of_strictMono_cdf _
    (strictMono_cdf_stableMeasure_of_abs_lt_one hα hβ hs m)

/-! ### Shapes from one onward -/

/-- From shape one onward, a positive-scale stable quantile is characterized as the unique real
root of its cdf equation at each interior probability level, including at full skewness. -/
theorem quantile_stableMeasure_eq_iff_of_one_le (hα : α ∈ Icc 1 2) (hβ : |β| ≤ 1)
    (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    (stableMeasure α β s m).quantile u = x ↔ cdf (stableMeasure α β s m) x = u := by
  let := isProbabilityMeasure_stableMeasure ⟨by linarith [hα.1], hα.2⟩ hβ s m
  simpa using Measure.quantile_eq_iff_of_ae_mem_of_strictMonoOn _ ordConnected_univ
    (ae_of_all _ mem_univ) (continuous_cdf_stableMeasure ⟨by linarith [hα.1], hα.2⟩ hβ hs)
    ((strictMono_cdf_stableMeasure_of_one_le hα hβ hs m).strictMonoOn _) hu

/-- From shape one onward, positive-scale stable quantiles vary continuously with the interior
probability level, including at full skewness. -/
theorem continuousOn_quantile_stableMeasure_of_one_le (hα : α ∈ Icc 1 2)
    (hβ : |β| ≤ 1) (hs : 0 < s) (m : ℝ) :
    ContinuousOn (stableMeasure α β s m).quantile (Ioo 0 1) := by
  let := isProbabilityMeasure_stableMeasure ⟨by linarith [hα.1], hα.2⟩ hβ s m
  exact Measure.continuousOn_quantile_of_strictMonoOn _ ordConnected_univ
    ((strictMono_cdf_stableMeasure_of_one_le hα hβ hs m).strictMonoOn _)
    (mapsTo_univ _ _)

/-- From shape one onward, positive-scale stable quantiles tend to minus infinity as the level
decreases to zero, including at full skewness. -/
theorem tendsto_quantile_stableMeasure_nhdsGT_zero_of_one_le (hα : α ∈ Icc 1 2)
    (hβ : |β| ≤ 1) (hs : 0 < s) (m : ℝ) :
    Tendsto (fun u ↦ ((stableMeasure α β s m).quantile u : EReal))
      (𝓝[>] 0) (𝓝 ⊥) := by
  let := isProbabilityMeasure_stableMeasure ⟨by linarith [hα.1], hα.2⟩ hβ s m
  exact Measure.tendsto_quantile_nhdsGT_zero_of_strictMono_cdf _
    (strictMono_cdf_stableMeasure_of_one_le hα hβ hs m)

/-- From shape one onward, positive-scale stable quantiles tend to plus infinity as the level
increases to one, including at full skewness. -/
theorem tendsto_quantile_stableMeasure_nhdsLT_one_of_one_le (hα : α ∈ Icc 1 2)
    (hβ : |β| ≤ 1) (hs : 0 < s) (m : ℝ) :
    Tendsto (fun u ↦ ((stableMeasure α β s m).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) := by
  let := isProbabilityMeasure_stableMeasure ⟨by linarith [hα.1], hα.2⟩ hβ s m
  exact Measure.tendsto_quantile_nhdsLT_one_of_strictMono_cdf _
    (strictMono_cdf_stableMeasure_of_one_le hα hβ hs m)

/-! ### Full positive skewness below shape one -/

/-- Below shape one at full positive skewness, the stable quantile is the unique cdf root in
the open interior of its support. -/
theorem quantile_stableMeasure_one_eq_iff_of_lt_one (hα : α ∈ Ioo 0 1) (hs : 0 < s)
    (hu : u ∈ Ioo 0 1) :
    (stableMeasure α 1 s m).quantile u = x ↔
      stableS1Location α 1 s m < x ∧ cdf (stableMeasure α 1 s m) x = u := by
  let μ := stableMeasure α 1 s m
  let d := stableS1Location α 1 s m
  let := isProbabilityMeasure_stableMeasure
    ⟨hα.1, hα.2.le.trans (by norm_num)⟩
    (by norm_num : |(1 : ℝ)| ≤ 1) s m
  let _ : NullSingletonClass μ := ⟨stableMeasure_singleton hs⟩
  have hbound : ∀ᵐ y ∂μ, y ∈ Ici d := by
    filter_upwards [μ.support_mem_ae] with y hy
    simpa [μ, d, support_stableMeasure_one_of_lt_one hα hs] using hy
  have hstrict : ∀ᵐ y ∂μ, d < y := by
    filter_upwards [hbound, μ.ae_ne d] with y hy hyne
    exact lt_of_le_of_ne hy (Ne.symm hyne)
  have hzero : cdf μ d = 0 := Measure.cdf_eq_zero_of_ae_lt μ hstrict
  rw [Measure.quantile_eq_iff_of_ae_mem_of_strictMonoOn μ ordConnected_Ici hbound
    (continuous_cdf_stableMeasure
      ⟨hα.1, hα.2.le.trans (by norm_num)⟩
      (by norm_num : |(1 : ℝ)| ≤ 1) hs)
    (by simpa [μ, d] using strictMonoOn_cdf_stableMeasure_one_of_lt_one hα hs m) hu]
  constructor
  · rintro ⟨hx, hxu⟩
    refine ⟨lt_of_le_of_ne hx ?_, hxu⟩
    intro hdx
    subst x
    have hzero' : cdf (stableMeasure α 1 s m) (stableS1Location α 1 s m) = 0 := by
      simpa [μ, d] using hzero
    rw [hzero'] at hxu
    exact hu.1.ne hxu
  · rintro ⟨hx, hxu⟩
    exact ⟨hx.le, hxu⟩

/-- Below shape one at full positive skewness, stable quantiles vary continuously with the
interior probability level. -/
theorem continuousOn_quantile_stableMeasure_one_of_lt_one (hα : α ∈ Ioo 0 1)
    (hs : 0 < s) (m : ℝ) :
    ContinuousOn (stableMeasure α 1 s m).quantile (Ioo 0 1) := by
  let μ := stableMeasure α 1 s m
  let d := stableS1Location α 1 s m
  let := isProbabilityMeasure_stableMeasure
    ⟨hα.1, hα.2.le.trans (by norm_num)⟩
    (by norm_num : |(1 : ℝ)| ≤ 1) s m
  apply Measure.continuousOn_quantile_of_strictMonoOn μ ordConnected_Ici
    (by simpa [μ, d] using strictMonoOn_cdf_stableMeasure_one_of_lt_one hα hs m)
  intro u hu
  exact ((quantile_stableMeasure_one_eq_iff_of_lt_one hα hs hu).1 rfl).1.le

/-- Below shape one at full positive skewness, stable quantiles tend to the finite lower support
endpoint as the level decreases to zero. -/
theorem tendsto_quantile_stableMeasure_one_nhdsGT_zero_of_lt_one
    (hα : α ∈ Ioo 0 1) (hs : 0 < s) (m : ℝ) :
    Tendsto (fun u ↦ ((stableMeasure α 1 s m).quantile u : EReal)) (𝓝[>] 0)
      (𝓝 (stableS1Location α 1 s m : EReal)) := by
  let μ := stableMeasure α 1 s m
  let d := stableS1Location α 1 s m
  let := isProbabilityMeasure_stableMeasure
    ⟨hα.1, hα.2.le.trans (by norm_num)⟩
    (by norm_num : |(1 : ℝ)| ≤ 1) s m
  have hbound : ∀ᵐ y ∂μ, d ≤ y := by
    filter_upwards [μ.support_mem_ae] with y hy
    simpa [μ, d, support_stableMeasure_one_of_lt_one hα hs] using hy
  apply Measure.tendsto_quantile_nhdsGT_zero_of_ae_le_of_cdf_pos μ hbound
  intro x hdx
  apply Measure.cdf_pos_of_mem_support_of_lt μ (y := d) _ hdx
  simp [μ, d, support_stableMeasure_one_of_lt_one hα hs]

/-- Below shape one at full positive skewness, stable quantiles tend to plus infinity as the
level increases to one. -/
theorem tendsto_quantile_stableMeasure_one_nhdsLT_one_of_lt_one
    (hα : α ∈ Ioo 0 1) (hs : 0 < s) (m : ℝ) :
    Tendsto (fun u ↦ ((stableMeasure α 1 s m).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) := by
  let μ := stableMeasure α 1 s m
  let d := stableS1Location α 1 s m
  let := isProbabilityMeasure_stableMeasure
    ⟨hα.1, hα.2.le.trans (by norm_num)⟩
    (by norm_num : |(1 : ℝ)| ≤ 1) s m
  apply Measure.tendsto_quantile_nhdsLT_one_of_cdf_lt_one μ
  intro x
  exact Measure.cdf_lt_one_of_strictMonoOn_Ici μ
    (by simpa [μ, d] using strictMonoOn_cdf_stableMeasure_one_of_lt_one hα hs m) x

/-! ### Full negative skewness below shape one -/

/-- Below shape one at full negative skewness, the stable quantile is the unique cdf root in
the open interior of its support. -/
theorem quantile_stableMeasure_neg_one_eq_iff_of_lt_one (hα : α ∈ Ioo 0 1)
    (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    (stableMeasure α (-1) s m).quantile u = x ↔
      x < stableS1Location α (-1) s m ∧ cdf (stableMeasure α (-1) s m) x = u := by
  let μ := stableMeasure α (-1) s m
  let d := stableS1Location α (-1) s m
  let := isProbabilityMeasure_stableMeasure
    ⟨hα.1, hα.2.le.trans (by norm_num)⟩
    (by norm_num : |(-1 : ℝ)| ≤ 1) s m
  have hbound : ∀ᵐ y ∂μ, y ∈ Iic d := by
    filter_upwards [μ.support_mem_ae] with y hy
    simpa [μ, d, support_stableMeasure_neg_one_of_lt_one hα hs] using hy
  have hone : cdf μ d = 1 := Measure.cdf_eq_one_of_ae_le μ hbound
  rw [Measure.quantile_eq_iff_of_ae_mem_of_strictMonoOn μ ordConnected_Iic hbound
    (continuous_cdf_stableMeasure
      ⟨hα.1, hα.2.le.trans (by norm_num)⟩
      (by norm_num : |(-1 : ℝ)| ≤ 1) hs)
    (by simpa [μ, d] using strictMonoOn_cdf_stableMeasure_neg_one_of_lt_one hα hs m) hu]
  constructor
  · rintro ⟨hx, hxu⟩
    refine ⟨lt_of_le_of_ne hx ?_, hxu⟩
    intro hxd
    subst x
    have hone' : cdf (stableMeasure α (-1) s m)
        (stableS1Location α (-1) s m) = 1 := by
      simpa [μ, d] using hone
    rw [hone'] at hxu
    exact hu.2.ne' hxu
  · rintro ⟨hx, hxu⟩
    exact ⟨hx.le, hxu⟩

/-- Below shape one at full negative skewness, stable quantiles vary continuously with the
interior probability level. -/
theorem continuousOn_quantile_stableMeasure_neg_one_of_lt_one (hα : α ∈ Ioo 0 1)
    (hs : 0 < s) (m : ℝ) :
    ContinuousOn (stableMeasure α (-1) s m).quantile (Ioo 0 1) := by
  let μ := stableMeasure α (-1) s m
  let d := stableS1Location α (-1) s m
  let := isProbabilityMeasure_stableMeasure
    ⟨hα.1, hα.2.le.trans (by norm_num)⟩
    (by norm_num : |(-1 : ℝ)| ≤ 1) s m
  apply Measure.continuousOn_quantile_of_strictMonoOn μ ordConnected_Iic
    (by simpa [μ, d] using strictMonoOn_cdf_stableMeasure_neg_one_of_lt_one hα hs m)
  intro u hu
  exact ((quantile_stableMeasure_neg_one_eq_iff_of_lt_one hα hs hu).1 rfl).1.le

/-- Below shape one at full negative skewness, stable quantiles tend to minus infinity as the
level decreases to zero. -/
theorem tendsto_quantile_stableMeasure_neg_one_nhdsGT_zero_of_lt_one
    (hα : α ∈ Ioo 0 1) (hs : 0 < s) (m : ℝ) :
    Tendsto (fun u ↦ ((stableMeasure α (-1) s m).quantile u : EReal))
      (𝓝[>] 0) (𝓝 ⊥) := by
  let μ := stableMeasure α (-1) s m
  let d := stableS1Location α (-1) s m
  let := isProbabilityMeasure_stableMeasure
    ⟨hα.1, hα.2.le.trans (by norm_num)⟩
    (by norm_num : |(-1 : ℝ)| ≤ 1) s m
  apply Measure.tendsto_quantile_nhdsGT_zero_of_cdf_pos μ
  intro x
  let y := min d x - 1
  apply Measure.cdf_pos_of_mem_support_of_lt μ (y := y)
  · dsimp only [μ]
    rw [support_stableMeasure_neg_one_of_lt_one hα hs]
    exact mem_Iic.2 (by dsimp [y]; linarith [min_le_left d x])
  · dsimp [y]
    linarith [min_le_right d x]

/-- Below shape one at full negative skewness, stable quantiles tend to the finite upper support
endpoint as the level increases to one. -/
theorem tendsto_quantile_stableMeasure_neg_one_nhdsLT_one_of_lt_one
    (hα : α ∈ Ioo 0 1) (hs : 0 < s) (m : ℝ) :
    Tendsto (fun u ↦ ((stableMeasure α (-1) s m).quantile u : EReal)) (𝓝[<] 1)
      (𝓝 (stableS1Location α (-1) s m : EReal)) := by
  let μ := stableMeasure α (-1) s m
  let d := stableS1Location α (-1) s m
  let := isProbabilityMeasure_stableMeasure
    ⟨hα.1, hα.2.le.trans (by norm_num)⟩
    (by norm_num : |(-1 : ℝ)| ≤ 1) s m
  have hbound : ∀ᵐ y ∂μ, y ≤ d := by
    filter_upwards [μ.support_mem_ae] with y hy
    simpa [μ, d, support_stableMeasure_neg_one_of_lt_one hα hs] using hy
  apply Measure.tendsto_quantile_nhdsLT_one_of_ae_le_of_cdf_lt_one μ hbound
  intro x hxd
  apply Measure.cdf_lt_one_of_mem_support_of_lt μ (y := d) _ hxd
  simp [μ, d, support_stableMeasure_neg_one_of_lt_one hα hs]

end TauCeti.Probability
