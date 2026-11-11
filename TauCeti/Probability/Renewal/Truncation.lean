/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Convolution.Tail
public import TauCeti.Probability.Renewal.LocalBound
public import TauCeti.Probability.Renewal.Equation
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Uniform truncation of monotone renewal forcing

For nonnegative, nonincreasing, integrable forcing on the half-line, the part of the renewal
convolution where the age is at least `N` tends to zero uniformly in time. This permits
compact-support truncation before approximating the forcing by step functions. The estimate
uses the local renewal bound and the integral test, not a renewal limit theorem.

For a forcing function `h : ℝ≥0 → ℝ`, Lebesgue integrability on the half-line is expressed as
`IntegrableOn (fun x : ℝ => h x.toNNReal) (Ioi 0)`. Its value at zero is retained: the renewal
measure includes the artificial arrival at zero and may also have genuine zero-gap clusters.
No finite-mean or nonlattice assumption is needed.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition (1971), Chapter XI, the monotone-forcing approximation in renewal theory.
-/

public section

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

variable (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]

/-- Integrable nonnegative monotone forcing has uniformly negligible distant tails against
the renewal measure. Thus truncation is uniform over all finite observation times. -/
theorem tendsto_iSup_lintegral_renewalMeasure_tail (hμ : μ {0} < 1)
    {h : ℝ≥0 → ℝ} (hh : Antitone h) (h₀ : ∀ x, 0 ≤ h x)
    (hint : IntegrableOn (fun x : ℝ => h x.toNNReal) (Ioi 0)) :
    Tendsto (fun N : ℕ => ⨆ t : ℝ≥0,
      ∫⁻ s in Iic t ∩ {s | (N : ℝ≥0) ≤ t - s}, ENNReal.ofReal (h (t - s))
        ∂μ.renewalMeasure) atTop (𝓝 0) := by
  have hanti : AntitoneOn (fun x : ℝ => h x.toNNReal) (Ici 0) :=
    fun _ _ _ _ hab => hh (Real.toNNReal_mono hab)
  have hsum : Summable (fun n : ℕ => h n) := by
    simpa using hanti.summable_of_integrableOn_Ioi_zero hint (fun x _ => h₀ x.toNNReal)
  have hsum' : (∑' n : ℕ, ENNReal.ofReal (h n)) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n : ℕ => h₀ n) hsum]
    exact ENNReal.ofReal_ne_top
  exact μ.renewalMeasure.tendsto_iSup_lintegral_antitone_sub_tail
    (fun a => μ.renewalMeasure_Icc_add_le a 1) (μ.renewalMeasure_Iic_lt_top hμ 1).ne
    (fun _ _ hab => ENNReal.ofReal_le_ofReal (hh hab)) hsum'

open TauCeti.Probability

/-- Removing the initial segment of a nonnegative integrable monotone forcing function
makes its renewal convolution tend uniformly to zero. This is the uniform error estimate
for compact-support truncation of the forcing. -/
theorem tendstoUniformly_renewalConv_indicator_Ici (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (hμ : μ {0} < 1) {h : ℝ≥0 → ℝ} (hh : Antitone h) (h₀ : ∀ x, 0 ≤ h x)
    (hint : IntegrableOn (fun x : ℝ => h x.toNNReal) (Ioi 0)) :
    TendstoUniformly (fun N : ℕ => renewalConv ((Ici (N : ℝ≥0)).indicator h) μ.renewalMeasure)
      0 atTop := by
  have hlim := μ.tendsto_iSup_lintegral_renewalMeasure_tail hμ hh h₀ hint
  refine EMetric.tendstoUniformly_iff.2 fun ε hε => ?_
  filter_upwards [hlim.eventually_lt_const hε] with N hN t
  have hset : MeasurableSet {s : ℝ≥0 | (N : ℝ≥0) ≤ t - s} := by measurability
  have hid : (fun s => (Ici (N : ℝ≥0)).indicator h (t - s)) =
      {s : ℝ≥0 | (N : ℝ≥0) ≤ t - s}.indicator (fun s => h (t - s)) := by
    ext s
    simp [indicator_apply]
  calc
    edist (0 : ℝ) (renewalConv ((Ici (N : ℝ≥0)).indicator h) μ.renewalMeasure t) =
        ‖∫ s in Iic t ∩ {s | (N : ℝ≥0) ≤ t - s}, h (t - s) ∂μ.renewalMeasure‖ₑ := by
      rw [renewalConv_def, hid, setIntegral_indicator hset]
      simp [edist_eq_enorm_sub]
    _ ≤ ∫⁻ s in Iic t ∩ {s | (N : ℝ≥0) ≤ t - s}, ENNReal.ofReal (h (t - s))
        ∂μ.renewalMeasure := by
      simpa only [Real.enorm_of_nonneg (h₀ _)] using
        (enorm_integral_le_lintegral_enorm (fun s => h (t - s)))
    _ ≤ ⨆ u : ℝ≥0, ∫⁻ s in Iic u ∩ {s | (N : ℝ≥0) ≤ u - s},
        ENNReal.ofReal (h (u - s)) ∂μ.renewalMeasure := le_iSup (fun u =>
          ∫⁻ s in Iic u ∩ {s | (N : ℝ≥0) ≤ u - s},
            ENNReal.ofReal (h (u - s)) ∂μ.renewalMeasure) t
    _ < ε := hN

end MeasureTheory.Measure
