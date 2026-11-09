/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Triangular.Basic
public import TauCeti.Probability.Quantile

/-!
# Quantiles of the triangular distribution

For endpoints `a < b` and mode `a ≤ c ≤ b`, the triangular cdf is the quadratic
`(x - a) ^ 2 / ((b - a) * (c - a))` on `[a, c]` and `1 - (b - x) ^ 2 / ((b - a) * (b - c))` on
`[c, b]`. It reaches the level `(c - a) / (b - a)` at the mode, and each quadratic inverts by a
square root. So at an interior level `u` the lower quantile is

* `a + √(u * (b - a) * (c - a))` when `u ≤ (c - a) / (b - a)`;
* `b - √((1 - u) * (b - a) * (b - c))` otherwise.

When the mode is an endpoint only one branch occurs: for `c = a` every interior level uses the
second formula, and for `c = b` the first. The quantiles tend to the endpoints `a` and `b` of the
support as the level tends to `0` and `1`.

## Main results

* `TauCeti.Probability.quantile_triangularMeasure` — the closed-form quantile;
* `TauCeti.Probability.tendsto_quantile_triangularMeasure_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_triangularMeasure_nhdsLT_one` — the endpoint limits.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley, 1995, Chapter 26, Section 9.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {a b c u x : ℝ}

/-- At a level `0 < u ≤ (c - a) / (b - a)`, the quantile lies on the rising branch. -/
private theorem quantile_triangularMeasure_of_le (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b)
    (hu : u ∈ Ioo 0 1) (huc : u ≤ (c - a) / (b - a)) :
    (triangularMeasure a b c).quantile u = a + √(u * (b - a) * (c - a)) := by
  have hba : 0 < b - a := sub_pos.2 hab
  have huc' : u * (b - a) ≤ c - a := (le_div_iff₀ hba).1 huc
  have hca : 0 < c - a := (mul_pos hu.1 hba).trans_le huc'
  have hpos : 0 < u * (b - a) * (c - a) := by have := hu.1; positivity
  -- The candidate lies in `(a, c]`.
  have hqa : a < a + √(u * (b - a) * (c - a)) := lt_add_of_pos_right a (sqrt_pos.2 hpos)
  have hqc : a + √(u * (b - a) * (c - a)) ≤ c := by
    rw [← le_sub_iff_add_le', sqrt_le_left (sub_nonneg.2 hac)]
    nlinarith
  refine eq_of_forall_ge_iff fun x ↦ ?_
  rw [Measure.quantile_le_iff _ hu.1 hu.2]
  rcases le_or_gt x a with hxa | hax
  · rw [cdf_triangularMeasure_of_le_left hab hac hcb hxa]
    exact iff_of_false (not_le.2 hu.1) (not_le.2 (hxa.trans_lt hqa))
  rcases le_total x c with hxc | hcx
  · rw [cdf_triangularMeasure_of_mem_Icc_left hab hcb ⟨hax.le, hxc⟩,
      le_div_iff₀ (mul_pos hba hca), ← le_sub_iff_add_le', sqrt_le_left (sub_nonneg.2 hax.le),
      mul_assoc]
  · refine iff_of_true ?_ (hqc.trans hcx)
    calc u ≤ (c - a) / (b - a) := huc
      _ = cdf (triangularMeasure a b c) c := (cdf_triangularMeasure_mode hab hac hcb).symm
      _ ≤ cdf (triangularMeasure a b c) x := monotone_cdf _ hcx

/-- At a level `(c - a) / (b - a) < u < 1`, the quantile lies on the falling branch. -/
private theorem quantile_triangularMeasure_of_lt (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b)
    (hu : u ∈ Ioo 0 1) (huc : (c - a) / (b - a) < u) :
    (triangularMeasure a b c).quantile u = b - √((1 - u) * (b - a) * (b - c)) := by
  have hba : 0 < b - a := sub_pos.2 hab
  have huc' : c - a < u * (b - a) := (div_lt_iff₀ hba).1 huc
  have hbc : 0 < b - c := by nlinarith [hu.2]
  have hnn : 0 ≤ (1 - u) * (b - a) * (b - c) := by
    have := sub_pos.2 hu.2
    positivity
  -- The candidate lies in `(c, b]`.
  have hcq : c < b - √((1 - u) * (b - a) * (b - c)) := by
    rw [lt_sub_iff_add_lt', ← lt_sub_iff_add_lt, sqrt_lt' hbc]
    nlinarith
  have hqb : b - √((1 - u) * (b - a) * (b - c)) ≤ b := sub_le_self _ (sqrt_nonneg _)
  refine eq_of_forall_ge_iff fun x ↦ ?_
  rw [Measure.quantile_le_iff _ hu.1 hu.2]
  rcases le_or_gt b x with hbx | hxb
  · rw [cdf_triangularMeasure_of_le_right hab hac hcb hbx]
    exact iff_of_true hu.2.le (hqb.trans hbx)
  rcases le_total x c with hxc | hcx
  · refine iff_of_false (not_le.2 ?_) (not_le.2 (hxc.trans_lt hcq))
    calc cdf (triangularMeasure a b c) x ≤ cdf (triangularMeasure a b c) c := monotone_cdf _ hxc
      _ = (c - a) / (b - a) := cdf_triangularMeasure_mode hab hac hcb
      _ < u := huc
  · rw [cdf_triangularMeasure_of_mem_Icc_right hab hac ⟨hcx, hxb.le⟩, le_sub_comm,
      div_le_iff₀ (mul_pos hba hbc), sub_le_comm, le_sqrt (sub_nonneg.2 hxb.le) hnn, mul_assoc]

/-- **Quantile.** At an interior level `u`, the lower quantile of the triangular law with
endpoints `a < b` and mode `a ≤ c ≤ b` is `a + √(u * (b - a) * (c - a))` up to the level
`(c - a) / (b - a)` of the mode, and `b - √((1 - u) * (b - a) * (b - c))` above it. -/
theorem quantile_triangularMeasure (hab : a < b) (hac : a ≤ c) (hcb : c ≤ b) (hu : u ∈ Ioo 0 1) :
    (triangularMeasure a b c).quantile u =
      if u ≤ (c - a) / (b - a) then a + √(u * (b - a) * (c - a))
      else b - √((1 - u) * (b - a) * (b - c)) := by
  split_ifs with huc
  · exact quantile_triangularMeasure_of_le hab hac hcb hu huc
  · exact quantile_triangularMeasure_of_lt hab hac hcb hu (not_le.1 huc)

/-- Triangular quantiles tend to the lower endpoint `a` as the level tends to zero from above. -/
theorem tendsto_quantile_triangularMeasure_nhdsGT_zero (hab : a < b) (hac : a ≤ c)
    (hcb : c ≤ b) : Tendsto (triangularMeasure a b c).quantile (𝓝[>] 0) (𝓝 a) := by
  have := isProbabilityMeasure_triangularMeasure hab hac hcb
  apply EReal.tendsto_coe.1
  exact Measure.tendsto_quantile_nhdsGT_zero_of_ae_le_of_cdf_pos _
    ((ae_mem_Icc_triangularMeasure a b c).mono fun _ hx ↦ hx.1)
    fun _ hx ↦ cdf_triangularMeasure_pos hab hac hcb hx

/-- Triangular quantiles tend to the upper endpoint `b` as the level tends to one from below. -/
theorem tendsto_quantile_triangularMeasure_nhdsLT_one (hab : a < b) (hac : a ≤ c)
    (hcb : c ≤ b) : Tendsto (triangularMeasure a b c).quantile (𝓝[<] 1) (𝓝 b) := by
  have := isProbabilityMeasure_triangularMeasure hab hac hcb
  apply EReal.tendsto_coe.1
  exact Measure.tendsto_quantile_nhdsLT_one_of_ae_le_of_cdf_lt_one _
    ((ae_mem_Icc_triangularMeasure a b c).mono fun _ hx ↦ hx.2)
    fun _ hx ↦ cdf_triangularMeasure_lt_one hab hac hcb hx

end TauCeti.Probability
