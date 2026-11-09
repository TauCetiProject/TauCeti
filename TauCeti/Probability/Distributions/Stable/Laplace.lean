/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.IntegrableExpMul
import TauCeti.MeasureTheory.Measure.FiniteMeasure.UniformIntegrable
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Distributions.Stable.CompensatedIntegral
import TauCeti.Probability.Distributions.Stable.Operations

/-!
# Passage to the limiting Laplace transform of stable laws

For totally skewed non-Gaussian stable laws, the moment-generating functions of the compensated
compound-Poisson approximations converge to that of the standardized stable law on the allowed
half-line. A uniform bound at twice the transform parameter controls the tails of the
exponential integrand. Thus weak convergence suffices to pass these unbounded integrands to the
limit, including at shape one.

The resulting moment-generating function is the exponential of the absolutely convergent real
compensated Lévy integral. Affine transport evaluates this integral at the scaled parameter and
adds the location term to the cumulant-generating function. These identities separate passage
to the limiting transform from evaluation of the integral in closed form.

## References

* K. Sato, *Lévy Processes and Infinitely Divisible Distributions*, Cambridge University Press,
  1999, section 25.
* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer, 2020,
  chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {α β t : ℝ}

/-- On the allowed half-line, the transforms of the dyadic compensated approximations converge
to the transform of the standardized totally skewed stable law. -/
theorem tendsto_mgf_stableCompensatedPoissonMeasure_invTwoPow
    (hα : α ∈ Ioo 0 2) (hβ : |β| = 1) (ht : β * t ≤ 0) :
    Tendsto (fun n : ℕ ↦ mgf id
      (stableCompensatedPoissonMeasure α β ((2 : ℝ)⁻¹ ^ n)) t) atTop
      (𝓝 (mgf id (stableMeasure α β 1 0) t)) := by
  let g : ℝ → ℝ≥0 := fun x ↦ (exp (t * x)).toNNReal
  let C : ℝ≥0 := (exp (∫ x, |exp ((2 * t) * x) - 1 - (2 * t) * sin x|
    ∂stableLevyMeasure α β)).toNNReal
  have ht2 : β * (2 * t) ≤ 0 := by nlinarith
  have hae := ae_mul_nonpos_stableLevyMeasure (α := α) hβ ht2
  have hlim := tendsto_stableCompensatedPoissonMeasure_invTwoPow hα hβ.le
  -- The bound at twice the parameter controls the square of the exponential integrand.
  have hsq : ∀ᶠ n : ℕ in atTop,
      ∫⁻ x, (g x : ℝ≥0∞) ^ 2
        ∂stableCompensatedPoissonMeasure α β ((2 : ℝ)⁻¹ ^ n) ≤ C := by
    apply Eventually.of_forall
    intro n
    have heq (x : ℝ) : (g x : ℝ≥0∞) ^ 2 = ENNReal.ofReal (exp ((2 * t) * x)) := by
      rw [← ENNReal.coe_pow, ENNReal.coe_nnreal_eq, NNReal.coe_pow]
      simp only [g, Real.coe_toNNReal _ (exp_pos _).le, ← exp_nat_mul]
      congr 2
      ring
    simp_rw [heq]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_exp_mul_stableCompensatedPoissonMeasure hae)
      (ae_of_all _ fun x ↦ (exp_pos _).le)]
    simpa only [C, ENNReal.ofReal, mgf, id_eq] using ENNReal.ofReal_le_ofReal
      (mgf_stableCompensatedPoissonMeasure_le (ε := (2 : ℝ)⁻¹ ^ n)
        hα hβ.le (by positivity) hae)
  have hlin := tendsto_lintegral_of_sq_bound (g := g) (by fun_prop)
    ((ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds atTop).1 hlim) hsq
  -- Transfer the extended integrals first, then use finiteness to pass to real transforms.
  have hfinite : ∫⁻ x, (g x : ℝ≥0∞) ∂stableMeasure α β 1 0 ≠ ∞ := by
    simpa only [ENNReal.coe_nnreal_eq, g, Real.coe_toNNReal _ (exp_pos _).le] using
      ((hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x ↦ (exp_pos (t * x)).le)).1
        (integrable_exp_mul_stableMeasure (α := α) hβ 1 0 ht).hasFiniteIntegral).ne
  have hreal := (ENNReal.continuousAt_toReal hfinite).tendsto.comp hlin
  have heq (μ : Measure ℝ) :
      (∫⁻ x, (g x : ℝ≥0∞) ∂μ).toReal = mgf id μ t := by
    rw [← integral_toReal (by fun_prop) (ae_of_all _ fun _ ↦ ENNReal.coe_lt_top)]
    simp only [ENNReal.coe_toReal, g, Real.coe_toNNReal _ (exp_pos _).le, mgf, id_eq]
  simp only [Function.comp_def, heq] at hreal
  convert hreal using 1
  funext n
  congr 1

/-- The transform of the standardized totally skewed non-Gaussian stable law is the exponential
of its real compensated Lévy integral on the allowed half-line. -/
private theorem mgf_id_stableMeasure_one_zero_eq_exp_integral
    (hα : α ∈ Ioo 0 2) (hβ : |β| = 1) (ht : β * t ≤ 0) :
    mgf id (stableMeasure α β 1 0) t =
      exp (∫ x, exp (t * x) - 1 - t * sin x ∂stableLevyMeasure α β) := by
  have hcut : Tendsto (fun n : ℕ ↦ (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim := (continuous_exp.tendsto _).comp
    ((tendsto_integral_exp_mul_sub_one_sub_mul_sin_stableLevyMeasure
      (ae_mul_nonpos_stableLevyMeasure (α := α) hβ ht)).comp hcut)
  have hmgf : Tendsto (fun n : ℕ ↦ mgf id
      (stableCompensatedPoissonMeasure α β ((2 : ℝ)⁻¹ ^ n)) t) atTop
      (𝓝 (exp (∫ x, exp (t * x) - 1 - t * sin x ∂stableLevyMeasure α β))) := by
    convert hlim using 1
    funext n
    exact mgf_stableCompensatedPoissonMeasure hα hβ.le (by positivity)
      (ae_mul_nonpos_stableLevyMeasure hβ ht)
  exact tendsto_nhds_unique
    (tendsto_mgf_stableCompensatedPoissonMeasure_invTwoPow hα hβ ht) hmgf

/-- At arbitrary scale and location, the transform on the allowed half-line is obtained from
the compensated Lévy integral at the scaled parameter. This includes the zero-scale Dirac law. -/
theorem mgf_id_stableMeasure_eq_exp_integral
    (hα : α ∈ Ioo 0 2) (hβ : |β| = 1) (s : ℝ≥0) (m : ℝ) (ht : β * t ≤ 0) :
    mgf id (stableMeasure α β s m) t =
      exp (m * t + ∫ x, exp ((s * t) * x) - 1 - (s * t) * sin x
        ∂stableLevyMeasure α β) := by
  rcases eq_zero_or_pos s with rfl | hs
  · rw [stableMeasure_zero_scale ⟨hα.1, hα.2.le⟩ hβ.le, mgf_dirac']
    simp [mul_comm]
  have hst : β * (s * t) ≤ 0 := by
    rw [mul_left_comm]
    exact mul_nonpos_of_nonneg_of_nonpos s.2 ht
  rw [← stableMeasure_one_zero_map_affine hs, mgf_id_map_affine,
    mgf_id_stableMeasure_one_zero_eq_exp_integral hα hβ hst,
    ← exp_add]

/-- The cumulant-generating function on the allowed half-line is the real compensated Lévy
integral plus the location term, including at shape one and at zero scale. -/
theorem cgf_id_stableMeasure_eq_integral
    (hα : α ∈ Ioo 0 2) (hβ : |β| = 1) (s : ℝ≥0) (m : ℝ) (ht : β * t ≤ 0) :
    cgf id (stableMeasure α β s m) t =
      m * t + ∫ x, exp ((s * t) * x) - 1 - (s * t) * sin x
        ∂stableLevyMeasure α β := by
  rw [cgf, mgf_id_stableMeasure_eq_exp_integral hα hβ s m ht, log_exp]

end TauCeti.Probability
