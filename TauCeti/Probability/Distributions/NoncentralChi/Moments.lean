/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralChi.Basic
import TauCeti.Probability.Distributions.Chi.Moments
import TauCeti.Probability.Distributions.NoncentralChiSquared.Moments

/-!
# Moments of noncentral chi laws

Every natural moment of a noncentral chi law is finite and is a convergent Poisson average
of central chi moments. The formulas include degree zero, whose zero-count component is
a point mass at zero: it contributes one at order zero and zero at positive orders.
The second moment is `s ^ 2 * (k + δ ^ 2)`, so the mean series also determines the variance.
Every real exponential moment is finite, without a closed-form mgf assertion.

The moment series uses `noncentralChiMeasure_eq_sum` and the central chi Gamma-function
formula. Exponential integrability follows from that of the noncentral chi-squared law.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 29.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

namespace TauCeti.Probability

variable {k s : ℝ} {δ : ℝ≥0}

/-- Every exponential moment is integrable, including the degree-zero mixed boundary,
the double-zero Dirac law, and the invalid zero-measure regimes. -/
theorem integrable_exp_mul_id_noncentralChiMeasure (k : ℝ) (δ : ℝ≥0) (s t : ℝ) :
    Integrable (fun x : ℝ ↦ exp (t * x)) (noncentralChiMeasure k δ s) := by
  by_cases hs : 0 < s
  swap
  · simp [noncentralChiMeasure_of_scale_nonpos (le_of_not_gt hs)]
  by_cases hk : 0 ≤ k
  swap
  · simp [noncentralChiMeasure_of_neg (lt_of_not_ge hk)]
  rw [noncentralChiMeasure_of_scale_pos hs,
    integrable_map_measure (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def]
  have hdom := (integrable_exp_mul_noncentralChiSquaredMeasure hk (δ ^ 2)
    (t := 1 / 4) (by norm_num)).const_mul (exp ((t * s) ^ 2))
  apply hdom.mono' (by fun_prop)
  filter_upwards [ae_nonneg_noncentralChiSquaredMeasure k (δ ^ 2)] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), ← exp_add]
  apply exp_le_exp.2
  have hsq := sq_nonneg (t * s - √x / 2)
  have hsqrt := sq_sqrt hx
  nlinarith

/-- The exact exponential-integrability domain of every noncentral chi law is all of `ℝ`. -/
@[simp]
theorem integrableExpSet_id_noncentralChiMeasure (k : ℝ) (δ : ℝ≥0) (s : ℝ) :
    integrableExpSet id (noncentralChiMeasure k δ s) = univ := by
  ext t
  simp only [integrableExpSet, id_eq, mem_ofPred_eq, mem_univ, iff_true]
  exact integrable_exp_mul_id_noncentralChiMeasure k δ s t

/-- All natural powers are integrable for the entire totalized noncentral chi family. -/
theorem integrable_pow_noncentralChiMeasure (k : ℝ) (δ : ℝ≥0) (s : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (noncentralChiMeasure k δ s) := by
  apply integrable_pow_of_mem_interior_integrableExpSet (X := id) _ n
  simp

/-- The natural-moment series converges to the corresponding moment. The order-zero term
is one before weighting, including for the degree-zero component; at positive orders the
Gamma ratio is zero at that component because `Real.Gamma 0 = 0`. -/
theorem hasSum_integral_pow_noncentralChiMeasure (hk : 0 ≤ k) (hs : 0 < s) (n : ℕ) :
    HasSum (fun j : ℕ ↦
      (exp (-(δ : ℝ) ^ 2 / 2) * ((δ : ℝ) ^ 2 / 2) ^ j / j.factorial) *
        (if n = 0 then 1 else
          s ^ n * (2 : ℝ) ^ ((n : ℝ) / 2) * Real.Gamma ((k + 2 * j + n) / 2) /
            Real.Gamma ((k + 2 * j) / 2)))
      (∫ x, x ^ n ∂noncentralChiMeasure k δ s) := by
  have h := integrable_pow_noncentralChiMeasure k δ s n
  rw [noncentralChiMeasure_eq_sum hk] at h ⊢
  convert hasSum_integral_measure h using 1
  funext j
  rw [integral_smul_measure, smul_eq_mul, ← measureReal_def,
    poissonMeasure_real_singleton]
  simp only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat, neg_div]
  congr 1
  by_cases hn : n = 0
  · subst n
    let _ := isProbabilityMeasure_chiMeasure (by positivity : 0 ≤ k + 2 * (j : ℝ)) hs
    simp
  · rw [ite_eq_right hn]
    rcases (show 0 ≤ k + 2 * (j : ℝ) by positivity).eq_or_lt' with hj | hj
    · rw [hj, chiMeasure_zero hs]
      simp [hn]
    · exact (integral_pow_chiMeasure hj hs n).symm

/-- Every natural moment is the convergent Poisson mixture of the central chi moments. -/
theorem integral_pow_noncentralChiMeasure (hk : 0 ≤ k) (hs : 0 < s) (n : ℕ) :
    ∫ x, x ^ n ∂noncentralChiMeasure k δ s = ∑' j : ℕ,
      (exp (-(δ : ℝ) ^ 2 / 2) * ((δ : ℝ) ^ 2 / 2) ^ j / j.factorial) *
        (if n = 0 then 1 else
          s ^ n * (2 : ℝ) ^ ((n : ℝ) / 2) * Real.Gamma ((k + 2 * j + n) / 2) /
            Real.Gamma ((k + 2 * j) / 2)) :=
  (hasSum_integral_pow_noncentralChiMeasure hk hs n).tsum_eq.symm

/-- The noncentral chi mean is a convergent Poisson average of central chi means. -/
theorem integral_id_noncentralChiMeasure (hk : 0 ≤ k) (hs : 0 < s) :
    ∫ x, x ∂noncentralChiMeasure k δ s = ∑' j : ℕ,
      (exp (-(δ : ℝ) ^ 2 / 2) * ((δ : ℝ) ^ 2 / 2) ^ j / j.factorial) *
        (s * √2 * Real.Gamma ((k + 2 * j + 1) / 2) /
          Real.Gamma ((k + 2 * j) / 2)) := by
  simpa only [pow_one, Nat.cast_one, one_ne_zero, ite_false, ← sqrt_eq_rpow] using
    integral_pow_noncentralChiMeasure (δ := δ) hk hs 1

/-- The second noncentral chi moment is the squared scale times degree plus noncentrality
squared, also at degree zero. -/
@[simp]
theorem integral_sq_noncentralChiMeasure (hk : 0 ≤ k) (hs : 0 < s) :
    ∫ x, x ^ 2 ∂noncentralChiMeasure k δ s = s ^ 2 * (k + (δ : ℝ) ^ 2) := by
  have h := congrArg (fun μ : Measure ℝ ↦ ∫ x, x ∂μ)
    (noncentralChiMeasure_map_sq (k := k) (δ := δ) hs)
  rw [integral_map (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) (by fun_prop), integral_const_mul,
    integral_id_noncentralChiSquaredMeasure hk] at h
  exact h

/-- The variance is the explicit second moment minus the square of the convergent mean series.
This includes the mixed degree-zero laws and the double-zero Dirac law. -/
theorem variance_id_noncentralChiMeasure (hk : 0 ≤ k) (hs : 0 < s) :
    variance id (noncentralChiMeasure k δ s) = s ^ 2 * (k + (δ : ℝ) ^ 2) -
      (∑' j : ℕ,
        (exp (-(δ : ℝ) ^ 2 / 2) * ((δ : ℝ) ^ 2 / 2) ^ j / j.factorial) *
          (s * √2 * Real.Gamma ((k + 2 * j + 1) / 2) /
            Real.Gamma ((k + 2 * j) / 2))) ^ 2 := by
  let _ := isProbabilityMeasure_noncentralChiMeasure (δ := δ) hk hs
  have hLp : MemLp id 2 (noncentralChiMeasure k δ s) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (integrable_pow_noncentralChiMeasure k δ s 2)
  rw [variance_eq_sub hLp]
  simp only [Pi.pow_apply, id_eq, integral_sq_noncentralChiMeasure hk hs,
    integral_id_noncentralChiMeasure hk hs]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A variable with noncentral chi law has every natural moment integrable. -/
theorem integrable_pow_of_hasLaw_noncentralChiMeasure
    (hX : HasLaw X (noncentralChiMeasure k δ s) P) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n) P :=
  hX.integrable_fun_comp (integrable_pow_noncentralChiMeasure k δ s n)

/-- The natural moments of a variable with noncentral chi law are the convergent
Poisson averages of central chi moments. -/
theorem integral_pow_of_hasLaw_noncentralChiMeasure (hk : 0 ≤ k) (hs : 0 < s)
    (hX : HasLaw X (noncentralChiMeasure k δ s) P) (n : ℕ) :
    ∫ ω, X ω ^ n ∂P = ∑' j : ℕ,
      (exp (-(δ : ℝ) ^ 2 / 2) * ((δ : ℝ) ^ 2 / 2) ^ j / j.factorial) *
        (if n = 0 then 1 else
          s ^ n * (2 : ℝ) ^ ((n : ℝ) / 2) * Real.Gamma ((k + 2 * j + n) / 2) /
            Real.Gamma ((k + 2 * j) / 2)) := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ x ^ n), hX.integral_comp (by fun_prop),
    integral_pow_noncentralChiMeasure hk hs]

/-- A variable with noncentral chi law has the explicit second moment
`s ^ 2 * (k + δ ^ 2)`. -/
theorem integral_sq_of_hasLaw_noncentralChiMeasure (hk : 0 ≤ k) (hs : 0 < s)
    (hX : HasLaw X (noncentralChiMeasure k δ s) P) :
    ∫ ω, X ω ^ 2 ∂P = s ^ 2 * (k + (δ : ℝ) ^ 2) := by
  rw [← Function.comp_def (f := fun x : ℝ ↦ x ^ 2), hX.integral_comp (by fun_prop),
    integral_sq_noncentralChiMeasure hk hs]

/-- The mean of a variable with noncentral chi law is the Poisson average of central chi means. -/
theorem integral_of_hasLaw_noncentralChiMeasure (hk : 0 ≤ k) (hs : 0 < s)
    (hX : HasLaw X (noncentralChiMeasure k δ s) P) :
    ∫ ω, X ω ∂P = ∑' j : ℕ,
      (exp (-(δ : ℝ) ^ 2 / 2) * ((δ : ℝ) ^ 2 / 2) ^ j / j.factorial) *
        (s * √2 * Real.Gamma ((k + 2 * j + 1) / 2) /
          Real.Gamma ((k + 2 * j) / 2)) := by
  rw [hX.integral_eq, integral_id_noncentralChiMeasure hk hs]

/-- The noncentral chi variance formula for a random variable with that law. -/
theorem variance_of_hasLaw_noncentralChiMeasure (hk : 0 ≤ k) (hs : 0 < s)
    (hX : HasLaw X (noncentralChiMeasure k δ s) P) :
    variance X P = s ^ 2 * (k + (δ : ℝ) ^ 2) -
      (∑' j : ℕ,
        (exp (-(δ : ℝ) ^ 2 / 2) * ((δ : ℝ) ^ 2 / 2) ^ j / j.factorial) *
          (s * √2 * Real.Gamma ((k + 2 * j + 1) / 2) /
            Real.Gamma ((k + 2 * j) / 2))) ^ 2 := by
  rw [hX.variance_eq, variance_id_noncentralChiMeasure hk hs]

/-- Every real exponential moment of a variable with noncentral chi law is integrable. -/
theorem integrable_exp_mul_of_hasLaw_noncentralChiMeasure
    (hX : HasLaw X (noncentralChiMeasure k δ s) P) (t : ℝ) :
    Integrable (fun ω ↦ exp (t * X ω)) P :=
  hX.integrable_fun_comp (integrable_exp_mul_id_noncentralChiMeasure k δ s t)

end TauCeti.Probability
