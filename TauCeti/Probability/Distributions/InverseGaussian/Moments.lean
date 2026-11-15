/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.InverseGaussian.Transforms
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Moments of inverse Gaussian laws

The inverse Gaussian law with positive mean parameter `μ` and shape `lam` has mean `μ`
and variance `μ ^ 3 / lam`. The identity belongs to every finite `Lᵖ`, including for the
zero measure at invalid parameters. These results also apply to random variables with
the specified law.

The moment calculations use the cumulant-generating function from
`InverseGaussian.Transforms` and Mathlib's `deriv_cgf_zero` and
`iteratedDeriv_two_cgf_eq_integral`, following the cumulant argument in
`NoncentralChiSquared.Moments`.

## References

* R. S. Chhikara, J. L. Folks, *The Inverse Gaussian Distribution: Theory, Methodology, and
  Applications*, Marcel Dekker (1989).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped Topology NNReal

namespace TauCeti.Probability

variable {μ lam : ℝ}

private theorem zero_mem_interior_integrableExpSet (hμ : 0 < μ) (hlam : 0 < lam) :
    0 ∈ interior (integrableExpSet id (inverseGaussianMeasure μ lam)) := by
  rw [integrableExpSet_id_inverseGaussianMeasure hμ hlam, interior_Iic]
  exact div_pos hlam (by positivity)

/-- The identity belongs to every finite `Lᵖ` under every inverse Gaussian law, including
the zero measure at invalid parameters. -/
theorem memLp_id_inverseGaussianMeasure (μ lam : ℝ) (p : ℝ≥0) :
    MemLp id p (inverseGaussianMeasure μ lam) := by
  by_cases h : 0 < μ ∧ 0 < lam
  · exact memLp_of_mem_interior_integrableExpSet
      (zero_mem_interior_integrableExpSet h.1 h.2) p
  · simp [inverseGaussianMeasure_of_not_pos h]

private theorem hasDerivAt_cgf_inverseGaussianMeasure (hμ : 0 < μ) (hlam : 0 < lam)
    {t : ℝ} (ht : t < lam / (2 * μ ^ 2)) :
    HasDerivAt (cgf id (inverseGaussianMeasure μ lam))
      (μ / √(1 - 2 * μ ^ 2 * t / lam)) t := by
  have hpos : 0 < 1 - 2 * μ ^ 2 * t / lam := by
    have := (lt_div_iff₀ (by positivity : 0 < 2 * μ ^ 2)).mp ht
    apply sub_pos.mpr
    exact (div_lt_one hlam).mpr (by linarith)
  have hd : HasDerivAt (fun u : ℝ ↦ 1 - 2 * μ ^ 2 * u / lam)
      (-(2 * μ ^ 2 / lam)) t := by
    simpa using (((hasDerivAt_id t).const_mul (2 * μ ^ 2)).div_const lam).const_sub 1
  have hformula : HasDerivAt (fun u : ℝ ↦
      lam / μ * (1 - √(1 - 2 * μ ^ 2 * u / lam)))
      (μ / √(1 - 2 * μ ^ 2 * t / lam)) t := by
    convert ((hd.sqrt hpos.ne').const_sub 1).const_mul (lam / μ) using 1
    field_simp
  apply hformula.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds ht] with u hu
  exact cgf_id_inverseGaussianMeasure hμ hlam hu.le

/-- The mean of an inverse Gaussian law is its mean parameter. -/
@[simp]
theorem integral_id_inverseGaussianMeasure (hμ : 0 < μ) (hlam : 0 < lam) :
    ∫ x, x ∂inverseGaussianMeasure μ lam = μ := by
  let := isProbabilityMeasure_inverseGaussianMeasure hμ hlam
  have h := deriv_cgf_zero (zero_mem_interior_integrableExpSet hμ hlam)
  have hderiv := hasDerivAt_cgf_inverseGaussianMeasure hμ hlam
    (by positivity : (0 : ℝ) < lam / (2 * μ ^ 2))
  simpa only [hderiv.deriv, mul_zero, zero_div, sub_zero, sqrt_one, div_one,
    id_eq, probReal_univ] using h.symm

/-- The variance of an inverse Gaussian law is `μ ^ 3 / lam`. -/
@[simp]
theorem variance_id_inverseGaussianMeasure (hμ : 0 < μ) (hlam : 0 < lam) :
    variance id (inverseGaussianMeasure μ lam) = μ ^ 3 / lam := by
  let := isProbabilityMeasure_inverseGaussianMeasure hμ hlam
  have hzero := zero_mem_interior_integrableExpSet hμ hlam
  have hfirst : deriv (cgf id (inverseGaussianMeasure μ lam)) =ᶠ[𝓝 0]
      fun t ↦ μ / √(1 - 2 * μ ^ 2 * t / lam) := by
    filter_upwards [Iio_mem_nhds (by positivity : (0 : ℝ) < lam / (2 * μ ^ 2))]
      with t ht
    exact (hasDerivAt_cgf_inverseGaussianMeasure hμ hlam ht).deriv
  have hd : HasDerivAt (fun t : ℝ ↦ 1 - 2 * μ ^ 2 * t / lam)
      (-(2 * μ ^ 2 / lam)) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_mul (2 * μ ^ 2)).div_const lam).const_sub 1
  have hsecond : HasDerivAt (fun t : ℝ ↦ μ / √(1 - 2 * μ ^ 2 * t / lam))
      (μ ^ 3 / lam) 0 := by
    convert (hasDerivAt_const (0 : ℝ) μ).div (hd.sqrt (by norm_num)) (by norm_num) using 1
    norm_num
    ring
  calc
    variance id (inverseGaussianMeasure μ lam) =
        iteratedDeriv 2 (cgf id (inverseGaussianMeasure μ lam)) 0 := by
      rw [iteratedDeriv_two_cgf_eq_integral hzero, deriv_cgf_zero hzero,
        variance_eq_integral (by fun_prop)]
      simp
    _ = μ ^ 3 / lam := by
      rw [iteratedDeriv_succ, iteratedDeriv_one, hfirst.deriv_eq, hsecond.deriv]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with a valid inverse Gaussian law has mean `μ`. -/
theorem integral_of_hasLaw_inverseGaussianMeasure (hμ : 0 < μ) (hlam : 0 < lam)
    (hX : HasLaw X (inverseGaussianMeasure μ lam) P) :
    ∫ ω, X ω ∂P = μ := by
  rw [hX.integral_eq, integral_id_inverseGaussianMeasure hμ hlam]

/-- A random variable with a valid inverse Gaussian law has variance `μ ^ 3 / lam`. -/
theorem variance_of_hasLaw_inverseGaussianMeasure (hμ : 0 < μ) (hlam : 0 < lam)
    (hX : HasLaw X (inverseGaussianMeasure μ lam) P) :
    variance X P = μ ^ 3 / lam := by
  rw [hX.variance_eq, variance_id_inverseGaussianMeasure hμ hlam]

end TauCeti.Probability
