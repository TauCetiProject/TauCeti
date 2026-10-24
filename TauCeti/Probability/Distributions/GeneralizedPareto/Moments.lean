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

Its `n`-th raw moment is `s ^ n * n! / ∏ j ∈ Finset.range n, (1 - (j + 1) * ξ)`
for `n * ξ < 1`. Its mean is `s / (1 - ξ)` for `ξ < 1`, its second raw moment is
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

open MeasureTheory ProbabilityTheory Real Set
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

private lemma integral_pow_generalizedParetoMeasure_succ (hs : 0 < s)
    (hξ0 : ξ ≠ 0) (n : ℕ) (hξ : (n + 1 : ℝ) * ξ < 1) :
    (1 - (n + 1 : ℝ) * ξ) * (∫ x, x ^ (n + 1) ∂generalizedParetoMeasure s ξ) =
      (n + 1 : ℝ) * s * (∫ x, x ^ n ∂generalizedParetoMeasure s ξ) := by
  let y : ℝ → ℝ := fun e => s * (exp (ξ * e) - 1) / ξ
  have hi (k : ℕ) (hk : (k : ℝ) * ξ < 1) :
      IntegrableOn (fun e => exp (-e) * y e ^ k) (Ioi 0) := by
    have hi := (integrable_pow_generalizedParetoMeasure_iff hs k).2 hk
    rw [generalizedParetoMeasure_of_shape_ne_zero hs hξ0,
      integrable_map_measure (by fun_prop) (by fun_prop)] at hi
    simpa only [Function.comp_def, one_mul, smul_eq_mul] using
      (integrable_expMeasure_iff_integrableOn_Ioi one_pos _).1 hi
  have hin := hi n (by by_cases h : 0 ≤ ξ <;> nlinarith)
  have hin1 := hi (n + 1) (by exact_mod_cast hξ)
  have hd (e : ℝ) : HasDerivAt y (s + ξ * y e) e := by
    convert ((((hasDerivAt_id e).const_mul ξ).exp.sub_const 1).const_mul s).div_const ξ
      using 1 <;> dsimp [y]
    field_simp
    ring
  -- Integrate the derivative of the density-weighted power; integrability gives its zero limit.
  have hderiv (e : ℝ) : HasDerivAt (fun e => exp (-e) * y e ^ (n + 1))
      ((n + 1 : ℝ) * s * (exp (-e) * y e ^ n) -
        (1 - (n + 1 : ℝ) * ξ) * (exp (-e) * y e ^ (n + 1))) e := by
    convert ((hasDerivAt_id e).neg.exp).mul ((hd e).pow (n + 1)) using 1
    · rfl
    · simp only [Pi.pow_apply, Pi.neg_apply, id_eq, Nat.cast_add, Nat.cast_one,
        Nat.add_sub_cancel, pow_succ]
      ring
  have hint := (hin.const_mul ((n + 1 : ℝ) * s)).sub
    (hin1.const_mul (1 - (n + 1 : ℝ) * ξ))
  have ht := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (fun e _ => hderiv e) hint hin1
  have heq := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun e _ => hderiv e) hint ht
  simp only [y, mul_zero, exp_zero, sub_self, mul_zero, zero_div, zero_pow
    (Nat.succ_ne_zero n)] at heq
  rw [integral_sub (hin.const_mul _) (hin1.const_mul _), integral_const_mul,
    integral_const_mul] at heq
  have hmoment (k : ℕ) : (∫ x, x ^ k ∂generalizedParetoMeasure s ξ) =
      ∫ e in Ioi 0, exp (-e) * y e ^ k := by
    rw [generalizedParetoMeasure_of_shape_ne_zero hs hξ0,
      integral_map (by fun_prop) (by fun_prop), integral_expMeasure_eq_integral_Ioi one_pos]
    simp only [one_mul, smul_eq_mul, y]
  rw [hmoment, hmoment]
  linarith

/-- A natural raw moment of the generalized Pareto law on its exact integrability domain,
including the zeroth moment and the zero-shape exponential case. -/
@[simp]
theorem integral_pow_generalizedParetoMeasure (hs : 0 < s) (n : ℕ)
    (hξ : (n : ℝ) * ξ < 1) :
    ∫ x, x ^ n ∂generalizedParetoMeasure s ξ =
      s ^ n * (n.factorial : ℝ) / ∏ j ∈ Finset.range n, (1 - (j + 1 : ℝ) * ξ) := by
  let _ := isProbabilityMeasure_generalizedParetoMeasure hs ξ
  by_cases hξ0 : ξ = 0
  · subst ξ
    simp [generalizedParetoMeasure_zero hs, integral_pow_expMeasure (inv_pos.mpr hs),
      div_eq_mul_inv, mul_comm]
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast at hξ
    have hn : (n : ℝ) * ξ < 1 := by
      by_cases h : 0 ≤ ξ <;> nlinarith
    have hd : 1 - (n + 1 : ℝ) * ξ ≠ 0 := ne_of_gt (sub_pos.mpr hξ)
    have hrec := integral_pow_generalizedParetoMeasure_succ hs hξ0 n hξ
    rw [mul_comm, ← eq_div_iff hd] at hrec
    rw [hrec, ih hn, Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    simp only [div_eq_mul_inv, mul_inv_rev, pow_succ]
    ring

/-- The mean of the generalized Pareto law on its exact first-moment domain. -/
@[simp]
theorem integral_id_generalizedParetoMeasure (hs : 0 < s) (hξ : ξ < 1) :
    ∫ x, x ∂generalizedParetoMeasure s ξ = s / (1 - ξ) := by
  simpa using integral_pow_generalizedParetoMeasure hs 1 (by simpa using hξ)

/-- The second raw moment of the generalized Pareto law on its exact second-moment domain. -/
@[simp high]
theorem integral_sq_generalizedParetoMeasure (hs : 0 < s) (hξ : 2 * ξ < 1) :
    ∫ x, x ^ 2 ∂generalizedParetoMeasure s ξ =
      2 * s ^ 2 / ((1 - ξ) * (1 - 2 * ξ)) := by
  simpa [Finset.prod_range_succ, one_add_one_eq_two, mul_comm] using
    integral_pow_generalizedParetoMeasure hs 2 (by simpa using hξ)

/-- The variance of the generalized Pareto law when its second moment exists. -/
@[simp]
theorem variance_id_generalizedParetoMeasure (hs : 0 < s) (hξ : 2 * ξ < 1) :
    Var[id; generalizedParetoMeasure s ξ] =
      s ^ 2 / ((1 - ξ) ^ 2 * (1 - 2 * ξ)) := by
  let _ : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hξ1 : ξ < 1 := by linarith
  by_cases hξ0 : ξ = 0
  · subst ξ
    simp [generalizedParetoMeasure_zero hs, variance_id_expMeasure (inv_pos.mpr hs)]
  have he2 : Integrable (fun e => exp ((2 * ξ) * e)) (expMeasure 1) :=
    (integrable_exp_mul_expMeasure_iff one_pos).2 hξ
  have hLp : MemLp (fun e => exp (ξ * e)) 2 (expMeasure 1) := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    simpa only [← exp_nat_mul, Nat.cast_ofNat, ← mul_assoc] using he2
  rw [generalizedParetoMeasure_eq_map_affine hs hξ0, variance_id_map_affine,
    variance_id_map (by fun_prop), variance_eq_sub hLp]
  simp only [Pi.pow_apply, ← exp_nat_mul, Nat.cast_ofNat, ← mul_assoc]
  have hm1 : (∫ e, exp (ξ * e) ∂expMeasure 1) = 1 / (1 - ξ) := by
    simpa only [mgf, id_eq] using mgf_id_expMeasure one_pos hξ1
  have hm2 : (∫ e, exp ((2 * ξ) * e) ∂expMeasure 1) = 1 / (1 - 2 * ξ) := by
    simpa only [mgf, id_eq] using mgf_id_expMeasure one_pos hξ
  rw [hm1, hm2]
  field_simp (disch := grind)
  ring

end TauCeti.Probability
