/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.NoncentralBeta.Cdf
public import TauCeti.Probability.Quantile
import TauCeti.Probability.Distributions.Dirac

/-!
# Quantiles of noncentral Beta laws

Every interior quantile of a valid noncentral Beta law lies in `[0, 1)`. At positive first shape
it is the unique root in `(0, 1)` of the Poisson-series cdf. At first shape zero the quantile is
zero through the atom of mass `exp (-l / 2)` at zero, and above that mass it is again the unique
cdf root in `(0, 1)`. The quantile is continuous on all interior levels, even across this
transition, and strictly increasing on its positive range.

As the level tends to zero the quantile tends to zero. As the level tends to one it tends to one,
except for the Dirac law at `a = l = 0`, whose quantiles are constantly zero.

## Main results

* `TauCeti.Probability.quantile_noncentralBetaMeasure_eq_zero_iff` — the quantile vanishes
  exactly through the atom at zero.
* `TauCeti.Probability.quantile_noncentralBetaMeasure_eq_iff` — above the atom, the quantile is
  the unique cdf root in `(0, 1)`.
* `TauCeti.Probability.strictMonoOn_quantile_noncentralBetaMeasure` and
  `TauCeti.Probability.continuousOn_quantile_noncentralBetaMeasure` — monotonicity and
  continuity in the level.
* `TauCeti.Probability.tendsto_quantile_noncentralBetaMeasure_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_noncentralBetaMeasure_nhdsLT_one` — the endpoint limits.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 30.
* The structure follows `TauCeti.Probability.Distributions.NoncentralChiSquared.Quantile`, the
  quantile theory of the noncentral chi-squared law, which has the same kind of atom at zero.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology
open scoped NNReal

namespace TauCeti.Probability

variable {a b u x : ℝ} {l : ℝ≥0}

/-- Every interior quantile lies in the closed unit interval. -/
theorem quantile_noncentralBetaMeasure_mem_Icc (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0)
    (hu : u ∈ Ioo 0 1) : (noncentralBetaMeasure a b l).quantile u ∈ Icc 0 1 := by
  have := isProbabilityMeasure_noncentralBetaMeasure ha hb l
  exact ordConnected_Icc.quantile_mem (ae_mem_Icc_noncentralBetaMeasure a b l) hu.1 hu.2

/-- Every interior quantile is strictly less than one, since one carries no atom. -/
theorem quantile_noncentralBetaMeasure_lt_one (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0)
    (hu : u ∈ Ioo 0 1) : (noncentralBetaMeasure a b l).quantile u < 1 := by
  have := isProbabilityMeasure_noncentralBetaMeasure ha hb l
  refine (quantile_noncentralBetaMeasure_mem_Icc ha hb l hu).2.lt_of_ne fun h ↦ ?_
  have hle := Measure.measureReal_Iio_quantile_le (noncentralBetaMeasure a b l) hu.1 hu.2
  rw [h, measureReal_congr (Iio_ae_eq_Iic'
      (noncentralBetaMeasure_singleton_of_ne_zero one_ne_zero a b l)), ← cdf_eq_real,
    cdf_noncentralBetaMeasure_of_one_le ha hb l le_rfl] at hle
  exact hle.not_gt hu.2

/-- An interior quantile is zero exactly through the mass of the atom at zero. At positive first
shape that mass is zero, so every interior quantile is positive. -/
@[simp]
theorem quantile_noncentralBetaMeasure_eq_zero_iff (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0)
    (hu : u ∈ Ioo 0 1) :
    (noncentralBetaMeasure a b l).quantile u = 0 ↔
      u ≤ if a = 0 then exp (-(l : ℝ) / 2) else 0 := by
  have hq := (quantile_noncentralBetaMeasure_mem_Icc ha hb l hu).1
  rw [← cdf_noncentralBetaMeasure_zero ha hb, ← Measure.quantile_le_iff _ hu.1 hu.2]
  exact ⟨fun h ↦ h.le, fun h ↦ le_antisymm h hq⟩

/-- Every interior quantile above the mass of the atom at zero is positive. -/
theorem quantile_noncentralBetaMeasure_pos (ha : 0 ≤ a) (hb : 0 < b) (hu : u ∈ Ioo 0 1)
    (hcut : (if a = 0 then exp (-(l : ℝ) / 2) else 0) < u) :
    0 < (noncentralBetaMeasure a b l).quantile u := by
  rwa [Measure.lt_quantile_iff _ hu.1 hu.2, cdf_noncentralBetaMeasure_zero ha hb]

/-- A quantile above the atom solves the cdf equation exactly. -/
theorem cdf_quantile_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b) (hu : u ∈ Ioo 0 1)
    (hcut : (if a = 0 then exp (-(l : ℝ) / 2) else 0) < u) :
    cdf (noncentralBetaMeasure a b l) ((noncentralBetaMeasure a b l).quantile u) = u := by
  have := isProbabilityMeasure_noncentralBetaMeasure ha hb l
  have hpos := quantile_noncentralBetaMeasure_pos ha hb hu hcut
  exact Measure.cdf_quantile' _ hu.1 hu.2
    (noncentralBetaMeasure_singleton_of_ne_zero hpos.ne' a b l)

/-- Above the atom, the quantile is the unique root of the cdf in the open unit interval.
Together with `cdf_noncentralBetaMeasure_eq` and `cdf_noncentralBetaMeasure_zero_shape`, this
characterizes it by the explicit Poisson series of incomplete Beta functions. -/
theorem quantile_noncentralBetaMeasure_eq_iff (ha : 0 ≤ a) (hb : 0 < b) (hu : u ∈ Ioo 0 1)
    (hcut : (if a = 0 then exp (-(l : ℝ) / 2) else 0) < u) :
    (noncentralBetaMeasure a b l).quantile u = x ↔
      x ∈ Ioo 0 1 ∧ cdf (noncentralBetaMeasure a b l) x = u := by
  have hpos := quantile_noncentralBetaMeasure_pos ha hb hu hcut
  have hlt := quantile_noncentralBetaMeasure_lt_one ha hb l hu
  have hroot := cdf_quantile_noncentralBetaMeasure ha hb hu hcut
  constructor
  · rintro rfl
    exact ⟨⟨hpos, hlt⟩, hroot⟩
  · rintro ⟨hx, heq⟩
    have hne : a ≠ 0 ∨ l ≠ 0 := by
      by_contra hn
      simp only [not_or, not_not] at hn
      rcases hn with ⟨rfl, rfl⟩
      simp at hcut
      linarith [hu.2]
    exact (strictMonoOn_cdf_noncentralBetaMeasure ha hb hne).injOn ⟨hpos.le, hlt.le⟩
      ⟨hx.1.le, hx.2.le⟩ (hroot.trans heq.symm)

/-- On the levels above its atom, the quantile is strictly increasing. -/
theorem strictMonoOn_quantile_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) :
    StrictMonoOn (noncentralBetaMeasure a b l).quantile
      (Ioo (if a = 0 then exp (-(l : ℝ) / 2) else 0) 1) := by
  have hnonneg : 0 ≤ if a = 0 then exp (-(l : ℝ) / 2) else 0 := by split_ifs <;> positivity
  intro s hs t ht hst
  rw [Measure.lt_quantile_iff _ (hnonneg.trans_lt ht.1) ht.2,
    cdf_quantile_noncentralBetaMeasure ha hb ⟨hnonneg.trans_lt hs.1, hs.2⟩ hs.1]
  exact hst

/-- The quantile is continuous on all interior levels, including the transition out of the atom
at first shape zero. -/
theorem continuousOn_quantile_noncentralBetaMeasure (ha : 0 ≤ a) (hb : 0 < b) (l : ℝ≥0) :
    ContinuousOn (noncentralBetaMeasure a b l).quantile (Ioo 0 1) := by
  by_cases h : a = 0 ∧ l = 0
  · rcases h with ⟨rfl, rfl⟩
    exact continuousOn_const.congr fun u hu ↦ by
      rw [noncentralBetaMeasure_zero_noncentrality 0 hb, noncentralBetaComponent_zero,
        Measure.quantile_dirac 0 hu.1 hu.2.le]
  exact Measure.continuousOn_quantile_of_strictMonoOn _ ordConnected_Icc
    (strictMonoOn_cdf_noncentralBetaMeasure ha hb (not_and_or.mp h))
    (fun _ hu ↦ quantile_noncentralBetaMeasure_mem_Icc ha hb l hu)

/-- At the lower endpoint, every valid noncentral Beta quantile tends to zero. -/
theorem tendsto_quantile_noncentralBetaMeasure_nhdsGT_zero (ha : 0 ≤ a) (hb : 0 < b)
    (l : ℝ≥0) :
    Tendsto (fun u ↦ ((noncentralBetaMeasure a b l).quantile u : EReal)) (𝓝[>] 0) (𝓝 0) := by
  have := isProbabilityMeasure_noncentralBetaMeasure ha hb l
  exact Measure.tendsto_quantile_nhdsGT_zero_of_ae_le_of_cdf_pos _
    ((ae_mem_Icc_noncentralBetaMeasure a b l).mono fun _ hx ↦ hx.1)
    (fun _ hx ↦ cdf_noncentralBetaMeasure_pos ha hb l hx)

/-- At the upper endpoint, the quantile tends to one, except for the Dirac law at `a = l = 0`,
whose quantiles are constantly zero. -/
theorem tendsto_quantile_noncentralBetaMeasure_nhdsLT_one (ha : 0 ≤ a) (hb : 0 < b)
    (l : ℝ≥0) :
    Tendsto (fun u ↦ ((noncentralBetaMeasure a b l).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (if a = 0 ∧ l = 0 then 0 else 1)) := by
  have := isProbabilityMeasure_noncentralBetaMeasure ha hb l
  by_cases h : a = 0 ∧ l = 0
  · rw [ite_eq_left h]
    rcases h with ⟨rfl, rfl⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    rw [noncentralBetaMeasure_zero_noncentrality 0 hb, noncentralBetaComponent_zero,
      Measure.quantile_dirac 0 hu.1 hu.2.le]
    norm_num
  · rw [ite_eq_right h]
    exact Measure.tendsto_quantile_nhdsLT_one_of_ae_le_of_cdf_lt_one _
      ((ae_mem_Icc_noncentralBetaMeasure a b l).mono fun _ hx ↦ hx.2)
      (fun _ hx ↦ cdf_noncentralBetaMeasure_lt_one ha hb (not_and_or.mp h) hx)

end TauCeti.Probability
