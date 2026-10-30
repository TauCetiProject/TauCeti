/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralChiSquared.Transforms

/-!
# Moments of noncentral chi-squared laws

A noncentral chi-squared law with nonnegative degree `k` and noncentrality `l` has mean
`k + l` and variance `2 * (k + 2 * l)`. Every natural moment is integrable, including at the
degree-zero mixed boundary and the double-zero point mass.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 29.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped Topology NNReal

namespace TauCeti.Probability

variable {k : ℝ}

private theorem zero_mem_interior_integrableExpSet (hk : 0 ≤ k) (l : ℝ≥0) :
    0 ∈ interior (integrableExpSet id (noncentralChiSquaredMeasure k l)) := by
  rw [integrableExpSet_id_noncentralChiSquaredMeasure hk]
  split_ifs <;> norm_num

/-- All natural moments are integrable, also for the zero measure at negative degree. -/
theorem integrable_pow_noncentralChiSquaredMeasure (k : ℝ) (l : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (noncentralChiSquaredMeasure k l) := by
  by_cases hk : 0 ≤ k
  · exact integrable_pow_of_mem_interior_integrableExpSet
      (zero_mem_interior_integrableExpSet hk l) n
  · simp [noncentralChiSquaredMeasure_of_neg (lt_of_not_ge hk)]

/-- The identity is integrable for every degree and noncentrality. -/
theorem integrable_id_noncentralChiSquaredMeasure (k : ℝ) (l : ℝ≥0) :
    Integrable id (noncentralChiSquaredMeasure k l) := by
  simpa only [pow_one, Function.id_def] using integrable_pow_noncentralChiSquaredMeasure k l 1

private theorem hasDerivAt_cgf_noncentralChiSquaredMeasure (hk : 0 ≤ k)
    (l : ℝ≥0) {t : ℝ} (ht : t < 2⁻¹) :
    HasDerivAt (cgf id (noncentralChiSquaredMeasure k l))
      (k / (1 - 2 * t) + l / (1 - 2 * t) ^ 2) t := by
  have hb : 1 - 2 * t ≠ 0 := ne_of_gt (by linarith)
  have hd : HasDerivAt (fun u : ℝ ↦ 1 - 2 * u) (-2) t := by
    simpa using ((hasDerivAt_id t).const_mul 2).const_sub 1
  have hformula : HasDerivAt
      (fun u : ℝ ↦ -(k / 2) * log (1 - 2 * u) + l * u / (1 - 2 * u))
      (k / (1 - 2 * t) + l / (1 - 2 * t) ^ 2) t := by
    convert ((hd.log hb).const_mul (-(k / 2))).add
      (((hasDerivAt_id t).const_mul (l : ℝ)).div hd hb) using 1
    · ext u
      simp
    · simp only [id_eq]
      field_simp
      ring
  apply hformula.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds ht] with u hu
  exact cgf_id_noncentralChiSquaredMeasure hk l hu

private theorem hasDerivAt_cgf_deriv_formula (k : ℝ) (l : ℝ≥0) {t : ℝ}
    (ht : 1 - 2 * t ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ k / (1 - 2 * u) + l / (1 - 2 * u) ^ 2)
      (2 * k / (1 - 2 * t) ^ 2 + 4 * l / (1 - 2 * t) ^ 3) t := by
  have hd : HasDerivAt (fun u : ℝ ↦ 1 - 2 * u) (-2) t := by
    simpa using ((hasDerivAt_id t).const_mul 2).const_sub 1
  convert ((hasDerivAt_const t k).div hd ht).add
    ((hasDerivAt_const t (l : ℝ)).div (hd.pow 2) (pow_ne_zero 2 ht)) using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- The mean is the sum of degree and noncentrality, including degree zero. -/
@[simp]
theorem integral_id_noncentralChiSquaredMeasure (hk : 0 ≤ k) (l : ℝ≥0) :
    ∫ x, x ∂noncentralChiSquaredMeasure k l = k + l := by
  let := isProbabilityMeasure_noncentralChiSquaredMeasure hk l
  have h := deriv_cgf_zero (zero_mem_interior_integrableExpSet hk l)
  simpa only [(hasDerivAt_cgf_noncentralChiSquaredMeasure hk l (by norm_num :
    (0 : ℝ) < 2⁻¹)).deriv, mul_zero, sub_zero, div_one, one_pow,
    id_eq, probReal_univ] using h.symm

/-- The variance is twice the degree plus four times the noncentrality, including the
mixed degree-zero law and the double-zero Dirac law. -/
@[simp]
theorem variance_id_noncentralChiSquaredMeasure (hk : 0 ≤ k) (l : ℝ≥0) :
    variance id (noncentralChiSquaredMeasure k l) = 2 * (k + 2 * l) := by
  let := isProbabilityMeasure_noncentralChiSquaredMeasure hk l
  have hzero := zero_mem_interior_integrableExpSet hk l
  have hfirst : deriv (cgf id (noncentralChiSquaredMeasure k l)) =ᶠ[𝓝 0]
      fun t ↦ k / (1 - 2 * t) + l / (1 - 2 * t) ^ 2 := by
    filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 2⁻¹)] with t ht
    exact (hasDerivAt_cgf_noncentralChiSquaredMeasure hk l ht).deriv
  calc
    variance id (noncentralChiSquaredMeasure k l) =
        iteratedDeriv 2 (cgf id (noncentralChiSquaredMeasure k l)) 0 := by
      rw [iteratedDeriv_two_cgf_eq_integral hzero, deriv_cgf_zero hzero,
        variance_eq_integral (by fun_prop)]
      simp
    _ = 2 * (k + 2 * l) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one, hfirst.deriv_eq,
        (hasDerivAt_cgf_deriv_formula k l (by norm_num : 1 - 2 * (0 : ℝ) ≠ 0)).deriv]
      norm_num
      ring

/-- A random variable with noncentral chi-squared law has mean `k + l`. -/
theorem integral_of_hasLaw_noncentralChiSquaredMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {l : ℝ≥0} (hk : 0 ≤ k)
    (hX : HasLaw X (noncentralChiSquaredMeasure k l) P) :
    ∫ ω, X ω ∂P = k + l := by
  rw [hX.integral_eq, integral_id_noncentralChiSquaredMeasure hk]

/-- A random variable with noncentral chi-squared law has variance `2 * (k + 2 * l)`. -/
theorem variance_of_hasLaw_noncentralChiSquaredMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {l : ℝ≥0} (hk : 0 ≤ k)
    (hX : HasLaw X (noncentralChiSquaredMeasure k l) P) :
    variance X P = 2 * (k + 2 * l) := by
  rw [hX.variance_eq, variance_id_noncentralChiSquaredMeasure hk]

end TauCeti.Probability
