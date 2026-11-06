/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.Approximation.Support
import TauCeti.Analysis.SpecialFunctions.Integrals.PowerSin

/-!
# Divergent centering of skewed stable approximations

At shapes `1 ≤ α < 2`, the sine compensator of a stable Lévy measure tends to positive
infinity for positive skewness and negative infinity for negative skewness as the jump
cutoff tends to zero. At full positive, respectively negative, skewness, every fixed right,
respectively left, half-line eventually lies in the support of the corresponding compensated
compound-Poisson approximations, although every retained jump has the same sign.

These facts account for the unbounded compensating translations in support arguments for
fully skewed stable laws. They concern the finite-cutoff components; passing support to a
limiting law also requires control of the independent small-jump remainder.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology

namespace TauCeti.Probability

private lemma integral_sin_cutoff {α β ε : ℝ} (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    (hε : 0 < ε) :
    (∫ x in {x : ℝ | ε < |x|}, sin x ∂stableLevyMeasure α β) =
      (2 * β * (Gamma (1 + α) * sin (π * α / 2) / π)) *
        ∫ x in Ioi ε, x ^ (-(α + 1)) * sin x := by
  have hs : MeasurableSet {x : ℝ | ε < |x|} := by measurability
  let _ := isFiniteMeasure_stableLevyMeasure_restrict_abs_gt (α := α) (β := β) hε
  have hi : IntegrableOn sin {x : ℝ | ε < |x|} (stableLevyMeasure α β) :=
    Integrable.of_bound (by fun_prop) 1
      (ae_of_all _ fun x ↦ by simpa using abs_sin_le_one x)
  rw [← integral_indicator hs,
    integral_stableLevyMeasure_eq hα hβ ((integrable_indicator_iff hs).mpr hi)]
  have hneg (x : ℝ) : {x : ℝ | ε < |x|}.indicator sin (-x) =
      -{x : ℝ | ε < |x|}.indicator sin x := by
    by_cases hx : ε < |x| <;> simp [indicator, abs_neg, hx]
  simp_rw [smul_eq_mul, hneg, mul_neg, integral_neg]
  have heq : (∫ x in Ioi (0 : ℝ), x ^ (-(α + 1)) *
      {x : ℝ | ε < |x|}.indicator sin x) =
      ∫ x in Ioi ε, x ^ (-(α + 1)) * sin x := by
    calc
      _ = ∫ x in Ioi (0 : ℝ), (Ioi ε).indicator
          (fun x ↦ x ^ (-(α + 1)) * sin x) x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        simp [indicator, abs_of_pos hx]
      _ = _ := by
        rw [setIntegral_indicator measurableSet_Ioi,
          inter_eq_right.mpr (Ioi_subset_Ioi hε.le)]
  rw [heq]
  ring

/-- For shape at least one and positive skewness, the cutoff sine compensator diverges
to positive infinity, including at shape one. -/
theorem tendsto_integral_sin_stableLevyMeasure_atTop {α β : ℝ} (hα : α ∈ Ico 1 2)
    (hβ : 0 < β) (hβ1 : β ≤ 1) :
    Tendsto (fun ε : ℝ ↦ ∫ x in {x : ℝ | ε < |x|}, sin x ∂stableLevyMeasure α β)
      (𝓝[>] 0) atTop := by
  have ha : α ∈ Ioo 0 2 := ⟨by linarith [hα.1], hα.2⟩
  have ht := Tendsto.const_mul_atTop
    (mul_pos (mul_pos zero_lt_two hβ) (stableLevyDensity_coefficient_pos ha))
    (TauCeti.tendsto_integral_rpow_mul_sin_Ioi_nhdsGT_zero
      (a := -(α + 1)) (by linarith [hα.1]))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_sin_cutoff ha (abs_le.mpr ⟨by linarith, hβ1⟩) hε).symm

/-- For shape at least one and negative skewness, the cutoff sine compensator diverges
to negative infinity. -/
theorem tendsto_integral_sin_stableLevyMeasure_atBot {α β : ℝ} (hα : α ∈ Ico 1 2)
    (hβ : β < 0) (hβ1 : -1 ≤ β) :
    Tendsto (fun ε : ℝ ↦ ∫ x in {x : ℝ | ε < |x|}, sin x ∂stableLevyMeasure α β)
      (𝓝[>] 0) atBot := by
  have ha : α ∈ Ioo 0 2 := ⟨by linarith [hα.1], hα.2⟩
  have ht := Tendsto.const_mul_atTop_of_neg
    (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg zero_lt_two hβ)
      (stableLevyDensity_coefficient_pos ha))
    (TauCeti.tendsto_integral_rpow_mul_sin_Ioi_nhdsGT_zero
      (a := -(α + 1)) (by linarith [hα.1]))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_sin_cutoff ha (abs_le.mpr ⟨hβ1, by linarith⟩) hε).symm

/-- Every fixed right half-line eventually lies in the support of the fully positively
skewed compensated approximations when the shape is at least one. -/
theorem eventually_Ici_subset_support_stableCompensatedPoissonMeasure_one {α : ℝ}
    (hα : α ∈ Ico 1 2) (x : ℝ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, Ici x ⊆ (stableCompensatedPoissonMeasure α 1 ε).support := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds,
    (tendsto_integral_sin_stableLevyMeasure_atTop hα zero_lt_one le_rfl).eventually_ge_atTop
      (1 - x)]
      with ε hε hε1 hc
  rw [support_stableCompensatedPoissonMeasure_one ⟨by linarith [hα.1], hα.2⟩ hε]
  intro y hy
  simp only [mem_Ici] at hy
  exact Or.inr (by simp only [mem_Ici]; linarith)

/-- Every fixed left half-line eventually lies in the support of the fully negatively
skewed compensated approximations when the shape is at least one. -/
theorem eventually_Iic_subset_support_stableCompensatedPoissonMeasure_neg_one {α : ℝ}
    (hα : α ∈ Ico 1 2) (x : ℝ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, Iic x ⊆ (stableCompensatedPoissonMeasure α (-1) ε).support := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds,
    (tendsto_integral_sin_stableLevyMeasure_atBot hα neg_one_lt_zero le_rfl).eventually_le_atBot
      (-1 - x)]
      with ε hε hε1 hc
  rw [support_stableCompensatedPoissonMeasure_neg_one ⟨by linarith [hα.1], hα.2⟩ hε]
  intro y hy
  simp only [mem_Iic] at hy
  exact Or.inr (by simp only [mem_Iic]; linarith)

end TauCeti.Probability
