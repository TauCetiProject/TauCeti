/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedPareto.Basic
import TauCeti.Probability.Distributions.Affine

/-!
# Moments of the generalized Pareto distribution

For positive scale `s`, the generalized Pareto law of shape `ξ` has a finite absolute moment
of any nonnegative real order `p` exactly when `p * ξ < 1`. In particular, every finite moment
exists at nonpositive shape, whereas positive shape gives a sharp upper threshold.

Its mean is `s / (1 - ξ)` for `ξ < 1`, its second raw moment is
`2 * s ^ 2 / ((1 - ξ) * (1 - 2 * ξ))` for `2 * ξ < 1`, and its variance is
`s ^ 2 / ((1 - ξ) ^ 2 * (1 - 2 * ξ))` on the same second-moment domain.
The integrability equivalences include divergence at the boundary; the real-valued formulas
are asserted only where the corresponding moments exist.

These results use the defining exponential transformation, including the separate zero-shape
exponential law, and need no density representation.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace TauCeti.Probability

variable {s ξ : ℝ}

private lemma generalizedParetoMeasure_eq_map_affine (hs : 0 < s) (hξ : ξ ≠ 0) :
    generalizedParetoMeasure s ξ =
      ((expMeasure 1).map fun e => exp (ξ * e)).map
        (fun y => -(s / ξ) + (s / ξ) * y) := by
  rw [generalizedParetoMeasure_of_shape_ne_zero hs hξ,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext e
  simp only [Function.comp_apply]
  ring

/-- The identity belongs to finite `Lᵖ` under a positive-scale generalized Pareto law exactly
when `p * ξ < 1`. This includes order zero and every nonpositive shape. -/
@[simp]
theorem memLp_id_generalizedParetoMeasure_iff (hs : 0 < s) (p : ℝ≥0) :
    MemLp id p (generalizedParetoMeasure s ξ) ↔ (p : ℝ) * ξ < 1 := by
  let _ : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  by_cases hξ : ξ = 0
  · subst ξ
    simp only [mul_zero, zero_lt_one, iff_true]
    rw [generalizedParetoMeasure_zero hs]
    apply memLp_of_mem_interior_integrableExpSet
    rw [integrableExpSet_id_expMeasure (inv_pos.mpr hs), isOpen_Iio.interior_eq]
    exact inv_pos.mpr hs
  rw [generalizedParetoMeasure_eq_map_affine hs hξ,
    memLp_id_map_affine_iff (div_ne_zero hs.ne' hξ),
    memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)]
  by_cases hp : p = 0
  · subst p
    simp only [ENNReal.coe_zero, NNReal.coe_zero, zero_mul, zero_lt_one, iff_true,
      memLp_zero_iff_aestronglyMeasurable]
    fun_prop
  rw [← integrable_norm_rpow_iff (by fun_prop) (by exact_mod_cast hp) (by simp)]
  simp only [Function.comp_apply, id_eq, Real.norm_eq_abs, abs_of_pos (exp_pos _),
    ENNReal.coe_toReal, ← exp_mul]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    integrable_exp_mul_expMeasure_iff (r := 1) (t := (p : ℝ) * ξ) one_pos

/-- The mean integrand of a positive-scale generalized Pareto law is integrable exactly for
shape less than one. -/
@[simp]
theorem integrable_id_generalizedParetoMeasure_iff (hs : 0 < s) :
    Integrable id (generalizedParetoMeasure s ξ) ↔ ξ < 1 := by
  simpa only [ENNReal.coe_one, NNReal.coe_one, one_mul, memLp_one_iff_integrable] using
    memLp_id_generalizedParetoMeasure_iff (ξ := ξ) hs 1

/-- A natural raw moment of a positive-scale generalized Pareto law exists exactly when its
order times the shape is less than one. The zeroth moment is always integrable. -/
@[simp]
theorem integrable_pow_generalizedParetoMeasure_iff (hs : 0 < s) (n : ℕ) :
    Integrable (fun x => x ^ n) (generalizedParetoMeasure s ξ) ↔ (n : ℝ) * ξ < 1 := by
  let _ := isProbabilityMeasure_generalizedParetoMeasure hs ξ
  by_cases hn : n = 0
  · subst n
    simp
  have hmem : Integrable (fun x => x ^ n) (generalizedParetoMeasure s ξ) ↔
      MemLp id (n : ℝ≥0∞) (generalizedParetoMeasure s ξ) := by
    rw [← integrable_norm_iff (by fun_prop)]
    simpa only [id_eq, ENNReal.toReal_natCast, Real.rpow_natCast, norm_pow] using
      integrable_norm_rpow_iff (f := id) (p := (n : ℝ≥0∞))
        (μ := generalizedParetoMeasure s ξ) aestronglyMeasurable_id (by simpa) (by simp)
  rw [hmem]
  simpa using memLp_id_generalizedParetoMeasure_iff (ξ := ξ) hs (n : ℝ≥0)

/-- The mean of the generalized Pareto law on its exact first-moment domain. -/
@[simp]
theorem integral_id_generalizedParetoMeasure (hs : 0 < s) (hξ : ξ < 1) :
    ∫ x, x ∂generalizedParetoMeasure s ξ = s / (1 - ξ) := by
  let _ : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  by_cases hξ0 : ξ = 0
  · subst ξ
    simp [generalizedParetoMeasure_zero hs, integral_id_expMeasure (inv_pos.mpr hs)]
  rw [generalizedParetoMeasure_of_shape_ne_zero hs hξ0,
    integral_map (by fun_prop) (by fun_prop), integral_div, integral_const_mul,
    integral_sub ((integrable_exp_mul_expMeasure_iff one_pos).2 hξ) (integrable_const 1)]
  have hm : (∫ e, exp (ξ * e) ∂expMeasure 1) = 1 / (1 - ξ) := by
    simpa only [mgf, id_eq] using mgf_id_expMeasure one_pos hξ
  rw [hm]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  field_simp
  ring

/-- The second raw moment of the generalized Pareto law on its exact second-moment domain. -/
@[simp]
theorem integral_sq_generalizedParetoMeasure (hs : 0 < s) (hξ : 2 * ξ < 1) :
    ∫ x, x ^ 2 ∂generalizedParetoMeasure s ξ =
      2 * s ^ 2 / ((1 - ξ) * (1 - 2 * ξ)) := by
  let _ : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hξ1 : ξ < 1 := by linarith
  by_cases hξ0 : ξ = 0
  · subst ξ
    rw [generalizedParetoMeasure_zero hs, integral_sq_expMeasure (inv_pos.mpr hs)]
    simp
  have he : Integrable (fun e => exp (ξ * e)) (expMeasure 1) :=
    (integrable_exp_mul_expMeasure_iff one_pos).2 hξ1
  have he2 : Integrable (fun e => exp ((2 * ξ) * e)) (expMeasure 1) :=
    (integrable_exp_mul_expMeasure_iff one_pos).2 hξ
  have hpow (e : ℝ) : (s * (exp (ξ * e) - 1) / ξ) ^ 2 =
      (s / ξ) ^ 2 * (exp ((2 * ξ) * e) - 2 * exp (ξ * e) + 1) := by
    have hexp : (2 * ξ) * e = ξ * e + ξ * e := by ring
    rw [hexp, exp_add]
    ring
  rw [generalizedParetoMeasure_of_shape_ne_zero hs hξ0,
    integral_map (by fun_prop) (by fun_prop)]
  simp_rw [hpow]
  rw [integral_const_mul, integral_add (f := fun e => exp ((2 * ξ) * e) - 2 * exp (ξ * e))
      (he2.sub (he.const_mul 2)) (integrable_const 1),
    integral_sub he2 (he.const_mul 2), integral_const_mul]
  have hm1 : (∫ e, exp (ξ * e) ∂expMeasure 1) = 1 / (1 - ξ) := by
    simpa only [mgf, id_eq] using mgf_id_expMeasure one_pos hξ1
  have hm2 : (∫ e, exp ((2 * ξ) * e) ∂expMeasure 1) = 1 / (1 - 2 * ξ) := by
    simpa only [mgf, id_eq] using mgf_id_expMeasure one_pos hξ
  rw [hm1, hm2]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  field_simp (disch := grind)
  ring

/-- The variance of the generalized Pareto law when its second moment exists. -/
@[simp]
theorem variance_id_generalizedParetoMeasure (hs : 0 < s) (hξ : 2 * ξ < 1) :
    Var[id; generalizedParetoMeasure s ξ] =
      s ^ 2 / ((1 - ξ) ^ 2 * (1 - 2 * ξ)) := by
  let _ := isProbabilityMeasure_generalizedParetoMeasure hs ξ
  have hLp : MemLp id 2 (generalizedParetoMeasure s ξ) :=
    (memLp_id_generalizedParetoMeasure_iff hs 2).2 (by simpa using hξ)
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply, id_eq, integral_sq_generalizedParetoMeasure hs hξ,
    integral_id_generalizedParetoMeasure hs (by linarith : ξ < 1)]
  field_simp
  ring

end TauCeti.Probability
