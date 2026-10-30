/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.NoncentralChi.Basic
public import TauCeti.Probability.Distributions.NoncentralChiSquared.Quantile
import TauCeti.Probability.Quantile.Map

/-!
# Quantiles of noncentral chi laws

Interior noncentral chi quantiles are scaled square roots of noncentral chi-squared quantiles.
They are zero through the degree-zero atom `exp (-δ ^ 2 / 2)` and otherwise the unique positive
roots of the noncentral chi cdf. The quantile function is strictly increasing and continuous
above the atom; its endpoint limits are zero and positive infinity, except for the Dirac law at
zero degree and noncentrality, whose quantiles vanish.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 29.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology
open scoped NNReal

namespace TauCeti.Probability

variable {k s u x : ℝ} {δ : ℝ≥0}

/-- The noncentral chi quantile is the scaled square root of the noncentral chi-squared quantile
of noncentrality `δ ^ 2`, including the degree-zero boundary. -/
theorem quantile_noncentralChiMeasure (hk : 0 ≤ k) (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    (noncentralChiMeasure k δ s).quantile u =
      s * √((noncentralChiSquaredMeasure k (δ ^ 2)).quantile u) := by
  have := isProbabilityMeasure_noncentralChiSquaredMeasure hk (δ ^ 2)
  rw [noncentralChiMeasure_of_scale_pos hs, Measure.quantile_map_of_monotone
    (fun x y hxy ↦ mul_le_mul_of_nonneg_left (sqrt_le_sqrt hxy) hs.le) (by fun_prop) hu.1 hu.2]

/-- Interior quantiles vanish exactly through the atom at zero, which is present only at degree
zero. -/
theorem quantile_noncentralChiMeasure_eq_zero_iff (hk : 0 ≤ k) (hs : 0 < s)
    (hu : u ∈ Ioo 0 1) :
    (noncentralChiMeasure k δ s).quantile u = 0 ↔
      u ≤ if k = 0 then exp (-(δ : ℝ) ^ 2 / 2) else 0 := by
  rw [quantile_noncentralChiMeasure hk hs hu, mul_eq_zero, or_iff_right hs.ne',
    sqrt_eq_zero (quantile_noncentralChiSquaredMeasure_nonneg hk _ hu),
    quantile_noncentralChiSquaredMeasure_eq_zero_iff hk _ hu, NNReal.coe_pow]

/-- Above the atom, the quantile is the unique positive root of the cdf. -/
theorem quantile_noncentralChiMeasure_eq_iff (hk : 0 ≤ k) (hs : 0 < s) (hu : u ∈ Ioo 0 1)
    (hcut : (if k = 0 then exp (-(δ : ℝ) ^ 2 / 2) else 0) < u) :
    (noncentralChiMeasure k δ s).quantile u = x ↔
      0 < x ∧ cdf (noncentralChiMeasure k δ s) x = u := by
  have hcut' : (if k = 0 then exp (-(((δ ^ 2 : ℝ≥0)) : ℝ) / 2) else 0) < u := by
    rwa [NNReal.coe_pow]
  have hpos := quantile_noncentralChiSquaredMeasure_pos hk hu hcut'
  rw [quantile_noncentralChiMeasure hk hs hu]
  constructor
  · rintro rfl
    refine ⟨mul_pos hs (sqrt_pos.2 hpos), ?_⟩
    rw [cdf_noncentralChiMeasure_eq hk hs, ite_eq_right (not_lt.mpr (by positivity)),
      mul_div_cancel_left₀ _ hs.ne', sq_sqrt hpos.le,
      cdf_quantile_noncentralChiSquaredMeasure hk hu hcut']
  · rintro ⟨hx, hcdf⟩
    rw [cdf_noncentralChiMeasure_eq hk hs, ite_eq_right (not_lt.mpr hx.le)] at hcdf
    rw [((quantile_noncentralChiSquaredMeasure_eq_iff hk hu hcut').2
      ⟨by positivity, hcdf⟩), sqrt_sq (div_pos hx hs).le, mul_div_cancel₀ _ hs.ne']

/-- Above the atom, the quantile function is strictly increasing. -/
theorem strictMonoOn_quantile_noncentralChiMeasure (hk : 0 ≤ k) (hs : 0 < s) :
    StrictMonoOn (noncentralChiMeasure k δ s).quantile
      (Ioo (if k = 0 then exp (-(δ : ℝ) ^ 2 / 2) else 0) 1) := by
  have hnonneg : 0 ≤ if k = 0 then exp (-(δ : ℝ) ^ 2 / 2) else 0 := by
    split_ifs <;> positivity
  have hmono := strictMonoOn_quantile_noncentralChiSquaredMeasure hk (δ ^ 2)
  rw [NNReal.coe_pow] at hmono
  intro a ha b hb hab
  have ha' : a ∈ Ioo 0 1 := ⟨hnonneg.trans_lt ha.1, ha.2⟩
  have hb' : b ∈ Ioo 0 1 := ⟨hnonneg.trans_lt hb.1, hb.2⟩
  rw [quantile_noncentralChiMeasure hk hs ha', quantile_noncentralChiMeasure hk hs hb']
  exact mul_lt_mul_of_pos_left (sqrt_lt_sqrt
    (quantile_noncentralChiSquaredMeasure_nonneg hk _ ha') (hmono ha hb hab)) hs

/-- The quantile function is continuous on the open unit interval. -/
theorem continuousOn_quantile_noncentralChiMeasure (hk : 0 ≤ k) (hs : 0 < s) :
    ContinuousOn (noncentralChiMeasure k δ s).quantile (Ioo 0 1) := by
  refine (by fun_prop : Continuous fun x : ℝ ↦ s * √x).comp_continuousOn
    (continuousOn_quantile_noncentralChiSquaredMeasure hk (δ ^ 2)) |>.congr fun u hu ↦ ?_
  exact quantile_noncentralChiMeasure hk hs hu

/-- Noncentral chi quantiles tend to zero along every filter on the open unit interval along
which the noncentral chi-squared quantiles do. -/
private theorem tendsto_quantile_noncentralChiMeasure_zero {l : Filter ℝ}
    (hl : l ≤ 𝓟 (Ioo 0 1)) (hk : 0 ≤ k) (hs : 0 < s)
    (h : Tendsto (fun u ↦ ((noncentralChiSquaredMeasure k (δ ^ 2)).quantile u : EReal)) l
      (𝓝 0)) :
    Tendsto (fun u ↦ ((noncentralChiMeasure k δ s).quantile u : EReal)) l (𝓝 0) := by
  have hlim := ((by fun_prop : Continuous fun x : ℝ ↦ s * √x).tendsto 0).comp
    (EReal.tendsto_coe.1 h)
  simp only [sqrt_zero, mul_zero] at hlim
  apply (EReal.tendsto_coe.2 hlim).congr'
  filter_upwards [le_principal_iff.1 hl] with u hu
  exact congrArg (fun x : ℝ ↦ (x : EReal)) (quantile_noncentralChiMeasure hk hs hu).symm

/-- Every valid noncentral chi law has lower quantile endpoint zero. -/
theorem tendsto_quantile_noncentralChiMeasure_nhdsGT_zero (hk : 0 ≤ k) (hs : 0 < s) :
    Tendsto (fun u ↦ ((noncentralChiMeasure k δ s).quantile u : EReal)) (𝓝[>] 0) (𝓝 0) :=
  tendsto_quantile_noncentralChiMeasure_zero (le_principal_iff.2 (Ioo_mem_nhdsGT zero_lt_one))
    hk hs (tendsto_quantile_noncentralChiSquaredMeasure_nhdsGT_zero hk (δ ^ 2))

/-- Away from the double-zero Dirac law, quantiles tend to infinity as the level tends to one;
for the Dirac law they remain zero. -/
theorem tendsto_quantile_noncentralChiMeasure_nhdsLT_one (hk : 0 ≤ k) (hs : 0 < s) :
    Tendsto (fun u ↦ ((noncentralChiMeasure k δ s).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (if k = 0 ∧ δ = 0 then 0 else ⊤)) := by
  have hlim := tendsto_quantile_noncentralChiSquaredMeasure_nhdsLT_one hk (δ ^ 2)
  simp only [pow_eq_zero_iff two_ne_zero] at hlim
  by_cases h : k = 0 ∧ δ = 0
  · rw [ite_eq_left h] at hlim ⊢
    exact tendsto_quantile_noncentralChiMeasure_zero
      (le_principal_iff.2 (Ioo_mem_nhdsLT zero_lt_one)) hk hs hlim
  · rw [ite_eq_right h] at hlim ⊢
    rw [EReal.tendsto_coe_nhds_top_iff] at hlim ⊢
    apply ((tendsto_sqrt_atTop.comp hlim).const_mul_atTop hs).congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    exact (quantile_noncentralChiMeasure hk hs hu).symm

end TauCeti.Probability
