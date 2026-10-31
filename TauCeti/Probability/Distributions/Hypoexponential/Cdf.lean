/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hypoexponential.PDF
public import TauCeti.Probability.Cdf
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma
import TauCeti.Probability.Distributions.Gamma.Cdf
import TauCeti.Probability.Distributions.Poisson.Tail

/-!
# The cdf of hypoexponential laws

For a nonempty family of positive rates, the hypoexponential cdf is continuous, vanishes on
`(-∞, 0]`, increases strictly on `[0, ∞)`, and stays below one at every finite point. These
properties follow from absolute continuity and the exact support `[0, ∞)`, so they hold for
arbitrary repeated rates. They make the quantile the unique positive root of the cdf.

The cdf also has a closed form. Integrating the density of
`TauCeti.Probability.hypoexponentialPDFReal_eq_sum_gammaPDFReal` term by term writes it as the
combination `∑ ρ, ∑ k, A ρ k / ρ ^ k * P(k, ρ * x)` of Erlang cdfs, where `ρ` runs over the
distinct rates, `1 ≤ k` is at most the multiplicity of `ρ`, and `A ρ k` are the partial-fraction
coefficients `TauCeti.Probability.hypoexponentialCoeff r ρ k`. For integer shape `k`,
`P(k, y) = 1 - exp (-y) * ∑ j < k, y ^ j / j!`, and the weights `A ρ k / ρ ^ k` sum to one, so
for `x ≥ 0`

`F x = 1 - ∑ ρ, ∑ k, A ρ k / ρ ^ k * exp (-(ρ * x)) * ∑ j < k, (ρ * x) ^ j / j!`.

## Main results

* `TauCeti.Probability.strictMonoOn_cdf_hypoexponentialMeasure`: the cdf increases strictly on
  `[0, ∞)`.
* `TauCeti.Probability.cdf_hypoexponentialMeasure_eq_sum_regularizedGamma`: the cdf as a
  combination of Erlang cdfs.
* `TauCeti.Probability.cdf_hypoexponentialMeasure_eq`: the closed-form cdf.
* `TauCeti.Probability.cdf_hypoexponentialMeasure_of_injective`: the closed form for pairwise
  distinct rates, `1 - ∑ i, exp (-(r i * x)) * ∏ j ≠ i, r j / (r j - r i)`.

## References

* S. M. Ross, *Introduction to Probability Models*, 12th ed., Academic Press (2019), Chapter 5.
-/

public section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [Nonempty ι] {r : ι → ℝ} {x : ℝ}

/-- A nonempty hypoexponential cdf with positive rates is continuous. -/
theorem continuous_cdf_hypoexponentialMeasure (hr : ∀ i, 0 < r i) :
    Continuous (cdf (hypoexponentialMeasure r)) := by
  let _ := isProbabilityMeasure_hypoexponentialMeasure hr
  exact Measure.continuous_cdf_of_noAtoms _

/-- A nonempty hypoexponential cdf with positive rates increases strictly on `[0, ∞)`. -/
theorem strictMonoOn_cdf_hypoexponentialMeasure (hr : ∀ i, 0 < r i) :
    StrictMonoOn (cdf (hypoexponentialMeasure r)) (Ici 0) := by
  let _ := isProbabilityMeasure_hypoexponentialMeasure hr
  exact Measure.strictMonoOn_cdf_of_subset_support _ ordConnected_Ici
    (support_hypoexponentialMeasure hr).symm.subset

/-- A nonempty hypoexponential cdf vanishes at and below zero. -/
@[simp]
theorem cdf_hypoexponentialMeasure_of_nonpos (hr : ∀ i, 0 < r i) (hx : x ≤ 0) :
    cdf (hypoexponentialMeasure r) x = 0 := by
  let _ := isProbabilityMeasure_hypoexponentialMeasure hr
  rw [cdf_eq_real, measureReal_def, measure_mono_null
    (fun y hy ↦ not_lt.2 ((mem_Iic.1 hy).trans hx)) (ae_iff.1 (ae_pos_hypoexponentialMeasure r)),
    ENNReal.toReal_zero]

/-- A nonempty hypoexponential cdf with positive rates is positive exactly above zero. -/
@[simp]
theorem cdf_hypoexponentialMeasure_pos_iff (hr : ∀ i, 0 < r i) :
    0 < cdf (hypoexponentialMeasure r) x ↔ 0 < x := by
  refine ⟨fun h ↦ not_le.1 fun hx ↦ ?_, fun hx ↦ ?_⟩
  · simp [cdf_hypoexponentialMeasure_of_nonpos hr hx] at h
  · rw [← cdf_hypoexponentialMeasure_of_nonpos hr le_rfl]
    exact strictMonoOn_cdf_hypoexponentialMeasure hr self_mem_Ici hx.le hx

/-- A nonempty hypoexponential cdf with positive rates is below one at every finite point. -/
theorem cdf_hypoexponentialMeasure_lt_one (hr : ∀ i, 0 < r i) (x : ℝ) :
    cdf (hypoexponentialMeasure r) x < 1 :=
  Measure.cdf_lt_one_of_strictMonoOn_Ici _ (strictMonoOn_cdf_hypoexponentialMeasure hr) x

/-! ### The closed form -/

section ClosedForm

open scoped Finset Nat

/-- **The hypoexponential cdf as an Erlang mixture.** For positive rates, the hypoexponential
cdf is the combination of the Erlang cdfs `P(k, ρ * x)` with the partial-fraction weights
`A ρ k / ρ ^ k` of `TauCeti.Probability.hypoexponentialPDFReal_eq_sum_gammaPDFReal`. No sign
hypothesis on `x` is needed, since both sides vanish on `(-∞, 0]`. -/
theorem cdf_hypoexponentialMeasure_eq_sum_regularizedGamma (hr : ∀ i, 0 < r i) (x : ℝ) :
    cdf (hypoexponentialMeasure r) x = ∑ ρ ∈ Finset.univ.image r, ∑ k ∈ Finset.Icc 1 #{i | r i = ρ},
      hypoexponentialCoeff r ρ k / ρ ^ k * regularizedGamma k (ρ * x) := by
  let _ := isProbabilityMeasure_hypoexponentialMeasure hr
  have hρ : ∀ ρ ∈ Finset.univ.image r, 0 < ρ := fun ρ hρ ↦ by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hρ
    exact hr i
  have hk : ∀ ρ, ∀ k ∈ Finset.Icc 1 #{i | r i = ρ}, (0 : ℝ) < k := fun _ k hk ↦
    Nat.cast_pos.2 (Nat.zero_lt_one.trans_le (Finset.mem_Icc.1 hk).1)
  have hae : hypoexponentialPDFReal r =ᵐ[volume.restrict (Iic x)] fun t ↦
      ∑ ρ ∈ Finset.univ.image r, ∑ k ∈ Finset.Icc 1 #{i | r i = ρ},
        hypoexponentialCoeff r ρ k / ρ ^ k * gammaPDFReal k ρ t := by
    filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton (0 : ℝ)))]
      with t ht
    rcases (show t ≠ 0 from ht).lt_or_gt with ht | ht
    · simp [hypoexponentialPDFReal_of_nonpos r ht.le, gammaPDFReal, ht.not_ge]
    · exact hypoexponentialPDFReal_eq_sum_gammaPDFReal hr ht
  rw [cdf_eq_real, hypoexponentialMeasure_eq_withDensity hr, measureReal_def,
    withDensity_apply _ measurableSet_Iic]
  simp only [hypoexponentialPDF_eq_ofReal]
  rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hypoexponentialPDFReal_nonneg r))
      (by fun_prop), integral_congr_ae hae, integral_finsetSum _ fun ρ hρ' ↦
      integrable_finsetSum _ fun k hk' ↦
        ((integrable_gammaPDFReal (hk ρ k hk') (hρ ρ hρ')).const_mul _).integrableOn]
  refine Finset.sum_congr rfl fun ρ hρ' ↦ ?_
  rw [integral_finsetSum _ fun k hk' ↦
    ((integrable_gammaPDFReal (hk ρ k hk') (hρ ρ hρ')).const_mul _).integrableOn]
  refine Finset.sum_congr rfl fun k hk' ↦ ?_
  rw [integral_const_mul, ← cdf_gammaMeasure_eq_integral (hk ρ k hk') (hρ ρ hρ'),
    cdf_gammaMeasure_eq (hk ρ k hk') (hρ ρ hρ')]

/-- **The closed-form hypoexponential cdf.** For a nonempty family of positive rates and
`x ≥ 0`,

`F x = 1 - ∑ ρ, ∑ k ∈ [1, m ρ], A ρ k / ρ ^ k * exp (-(ρ * x)) * ∑ j < k, (ρ * x) ^ j / j!`,

where `ρ` runs over the distinct rates, `m ρ` is the multiplicity of `ρ` and
`A ρ k = hypoexponentialCoeff r ρ k`. Below zero the cdf vanishes by
`TauCeti.Probability.cdf_hypoexponentialMeasure_of_nonpos`. -/
theorem cdf_hypoexponentialMeasure_eq (hr : ∀ i, 0 < r i) (hx : 0 ≤ x) :
    cdf (hypoexponentialMeasure r) x =
      1 - ∑ ρ ∈ Finset.univ.image r, ∑ k ∈ Finset.Icc 1 #{i | r i = ρ},
        hypoexponentialCoeff r ρ k / ρ ^ k * exp (-(ρ * x)) *
          ∑ j ∈ Finset.range k, (ρ * x) ^ j / j ! := by
  rw [cdf_hypoexponentialMeasure_eq_sum_regularizedGamma hr, eq_sub_iff_add_eq,
    ← Finset.sum_add_distrib, ← sum_hypoexponentialCoeff_div_pow fun i ↦ (hr i).ne']
  refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hρ
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [regularizedGamma_natCast (Nat.one_le_iff_ne_zero.1 (Finset.mem_Icc.1 hk).1)
    (mul_nonneg (hr i).le hx)]
  ring

/-- **Distinct rates.** For pairwise distinct positive rates and `x ≥ 0`, the cdf is
`1 - ∑ i, exp (-(r i * x)) * ∏ j ≠ i, r j / (r j - r i)`. -/
theorem cdf_hypoexponentialMeasure_of_injective [DecidableEq ι]
    (hr : ∀ i, 0 < r i) (hinj : Function.Injective r) (hx : 0 ≤ x) :
    cdf (hypoexponentialMeasure r) x =
      1 - ∑ i, exp (-(r i * x)) * ∏ j ∈ Finset.univ.erase i, r j / (r j - r i) := by
  rw [cdf_hypoexponentialMeasure_eq hr hx, Finset.sum_image fun i _ j _ h ↦ hinj h]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hfilter : ({j | r j = r i} : Finset ι) = {i} := by
    ext j
    simp [hinj.eq_iff]
  have hne : ({j | r j ≠ r i} : Finset ι) = Finset.univ.erase i := by
    ext j
    simp [hinj.ne_iff]
  have hA := hypoexponentialCoeff_card r (r i)
  rw [hfilter, Finset.card_singleton, hne] at hA
  rw [hfilter, Finset.card_singleton, Finset.Icc_self, Finset.sum_singleton, hA,
    ← Finset.mul_prod_erase Finset.univ r (Finset.mem_univ i), Finset.prod_div_distrib]
  field_simp [(hr i).ne']
  simp

end ClosedForm

end TauCeti.Probability
