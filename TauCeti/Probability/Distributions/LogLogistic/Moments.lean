/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.LogLogistic.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Probability.Moments.Variance
import TauCeti.Probability.Distributions.Logistic.Transforms
import TauCeti.Probability.Moments.IntegrableExpMul

/-!
# Moments of the log-logistic distribution

The log-logistic law with scale `a > 0` and shape `b > 0` has a finite real-power moment of order
`q` exactly when `|q| < b`, and then

`E[X ^ q] = a ^ q * Γ(1 + q / b) * Γ(1 - q / b)`.

Both thresholds are sharp: the density behaves like `x ^ (b - 1)` at zero and like `x ^ (-b - 1)`
at infinity. This file proves that criterion, the moment formula, its natural-power forms, the
mean (for `b > 1`) and the variance (for `b > 2`), and the exact exponential-integrability domain
`Set.Iic 0`: the polynomial tail rules out every positive exponential moment.

## Implementation

Since a log-logistic variable is `exp Y` for a logistic `Y` with location `log a` and scale `b⁻¹`,
its real power `X ^ q` is `exp (q * Y)`. The moment criterion and formula are therefore the exact
domain and the value of the logistic moment-generating function, from
`TauCeti.Probability.integrable_exp_mul_id_logisticMeasure_iff` and
`TauCeti.Probability.mgf_id_logisticMeasure`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 23.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {a b q : ℝ}

/-! ### Real-power moments -/

/-- **The sharp real-power moment criterion.** A real power `X ^ q` of a log-logistic variable is
integrable exactly when `|q| < b`. -/
@[simp]
theorem integrable_rpow_logLogisticMeasure_iff (ha : 0 < a) (hb : 0 < b) (q : ℝ) :
    Integrable (fun x : ℝ => x ^ q) (logLogisticMeasure a b) ↔ |q| < b := by
  -- Pulled back along `exp`, the real power `x ^ q` is the exponential `exp (q * y)`.
  have hcomp : (fun x : ℝ => x ^ q) ∘ Real.exp = fun y => Real.exp (q * y) := by
    funext y
    rw [Function.comp_apply, ← Real.exp_mul, mul_comm]
  rw [logLogisticMeasure_of_pos ha hb,
    integrable_map_measure (by fun_prop) Real.measurable_exp.aemeasurable, hcomp,
    integrable_exp_mul_id_logisticMeasure_iff (inv_pos.mpr hb), div_inv_eq_mul, neg_one_mul,
    one_div, inv_inv, abs_lt]

/-- **The real-power moments of the log-logistic law.** For `|q| < b`,
`E[X ^ q] = a ^ q * Γ(1 + q / b) * Γ(1 - q / b)`. -/
theorem integral_rpow_logLogisticMeasure (ha : 0 < a) (hb : 0 < b) (hq : |q| < b) :
    ∫ x, x ^ q ∂logLogisticMeasure a b =
      a ^ q * Real.Gamma (1 + q / b) * Real.Gamma (1 - q / b) := by
  have hq' := abs_lt.mp hq
  have hmem : q ∈ Ioo (-1 / b⁻¹) (1 / b⁻¹) := by
    rw [div_inv_eq_mul, neg_one_mul, one_div, inv_inv]
    exact hq'
  -- Pulled back along `exp`, the moment is the logistic moment-generating function at `q`.
  have hmgf : ∫ y, Real.exp y ^ q ∂logisticMeasure (Real.log a) b⁻¹ =
      mgf id (logisticMeasure (Real.log a) b⁻¹) q := by
    simp only [mgf, id_eq, ← Real.exp_mul, mul_comm q]
  rw [logLogisticMeasure_of_pos ha hb,
    integral_map Real.measurable_exp.aemeasurable (by fun_prop), hmgf,
    mgf_id_logisticMeasure (inv_pos.mpr hb) hmem, Real.rpow_def_of_pos ha, inv_mul_eq_div]
  ring_nf

/-- A natural power `X ^ n` of a log-logistic variable is integrable exactly when `n < b`. -/
@[simp]
theorem integrable_pow_logLogisticMeasure_iff (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (logLogisticMeasure a b) ↔ (n : ℝ) < b := by
  simpa only [Real.rpow_natCast, Nat.abs_cast] using
    integrable_rpow_logLogisticMeasure_iff ha hb (n : ℝ)

/-- The natural raw moments of the log-logistic law: for `n < b`,
`E[X ^ n] = a ^ n * Γ(1 + n / b) * Γ(1 - n / b)`. -/
theorem integral_pow_logLogisticMeasure (ha : 0 < a) (hb : 0 < b) {n : ℕ} (hn : (n : ℝ) < b) :
    ∫ x, x ^ n ∂logLogisticMeasure a b =
      a ^ n * Real.Gamma (1 + n / b) * Real.Gamma (1 - n / b) := by
  simpa only [Real.rpow_natCast] using
    integral_rpow_logLogisticMeasure ha hb (q := n) (by rwa [Nat.abs_cast])

/-! ### Mean and variance -/

/-- A log-logistic variable is integrable exactly when its shape exceeds `1`. -/
@[simp]
theorem integrable_id_logLogisticMeasure_iff (ha : 0 < a) (hb : 0 < b) :
    Integrable id (logLogisticMeasure a b) ↔ 1 < b := by
  have h := integrable_pow_logLogisticMeasure_iff ha hb 1
  simp only [pow_one, Nat.cast_one] at h
  exact h

/-- **The mean of the log-logistic law** is `a * Γ(1 + 1 / b) * Γ(1 - 1 / b)` for `b > 1`. -/
theorem integral_id_logLogisticMeasure (ha : 0 < a) (hb : 1 < b) :
    ∫ x, x ∂logLogisticMeasure a b = a * Real.Gamma (1 + 1 / b) * Real.Gamma (1 - 1 / b) := by
  simpa using integral_pow_logLogisticMeasure ha (zero_lt_one.trans hb) (n := 1) (by simpa)

/-- The second raw moment of the log-logistic law is `a ^ 2 * Γ(1 + 2 / b) * Γ(1 - 2 / b)` for
`b > 2`. -/
theorem integral_sq_logLogisticMeasure (ha : 0 < a) (hb : 2 < b) :
    ∫ x, x ^ 2 ∂logLogisticMeasure a b =
      a ^ 2 * Real.Gamma (1 + 2 / b) * Real.Gamma (1 - 2 / b) := by
  simpa using integral_pow_logLogisticMeasure ha (zero_lt_two.trans hb) (n := 2) (by simpa)

/-- **The variance of the log-logistic law** for `b > 2` is
`a ^ 2 * (Γ(1 + 2 / b) * Γ(1 - 2 / b) - (Γ(1 + 1 / b) * Γ(1 - 1 / b)) ^ 2)`. -/
theorem variance_id_logLogisticMeasure (ha : 0 < a) (hb : 2 < b) :
    Var[id; logLogisticMeasure a b] =
      a ^ 2 * (Real.Gamma (1 + 2 / b) * Real.Gamma (1 - 2 / b) -
        (Real.Gamma (1 + 1 / b) * Real.Gamma (1 - 1 / b)) ^ 2) := by
  have hb0 : 0 < b := zero_lt_two.trans hb
  have := isProbabilityMeasure_logLogisticMeasure ha hb0
  have hLp : MemLp id 2 (logLogisticMeasure a b) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      ((integrable_pow_logLogisticMeasure_iff ha hb0 2).2 (by simpa))
  rw [variance_eq_sub hLp]
  have h₂ : (logLogisticMeasure a b)[(id : ℝ → ℝ) ^ 2] =
      a ^ 2 * Real.Gamma (1 + 2 / b) * Real.Gamma (1 - 2 / b) := by
    simpa using integral_sq_logLogisticMeasure ha hb
  have h₁ : (logLogisticMeasure a b)[(id : ℝ → ℝ)] =
      a * Real.Gamma (1 + 1 / b) * Real.Gamma (1 - 1 / b) := by
    simpa using integral_id_logLogisticMeasure ha (one_lt_two.trans hb)
  rw [h₂, h₁]
  ring

/-! ### Exponential moments -/

/-- **The exponential moments of a log-logistic law exist exactly at nonpositive rates.**
`exp (t * X)` is integrable if and only if `t ≤ 0`. -/
@[simp]
theorem integrable_exp_mul_id_logLogisticMeasure_iff (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (logLogisticMeasure a b) ↔ t ≤ 0 := by
  have := isProbabilityMeasure_logLogisticMeasure ha hb
  have hnonneg : ∀ᵐ x ∂logLogisticMeasure a b, (0 : ℝ) ≤ id x :=
    (ae_mem_Ioi_logLogisticMeasure a b).mono fun _ hx => le_of_lt hx
  refine ⟨fun h => le_of_not_gt fun ht => ?_, fun ht =>
    TauCeti.integrable_exp_mul_of_ge t 0 ht measurable_id.aemeasurable hnonneg⟩
  have hmom : ¬ Integrable (fun x : ℝ => id x ^ b) (logLogisticMeasure a b) := by
    simp [integrable_rpow_logLogisticMeasure_iff ha hb, abs_of_pos hb]
  exact TauCeti.not_integrable_exp_mul_of_not_integrable_rpow b measurable_id.aemeasurable
    hnonneg hb.le hmom ht h

/-- The exact exponential-integrability domain of a log-logistic law is the nonpositive
half-line. -/
@[simp]
theorem integrableExpSet_id_logLogisticMeasure (ha : 0 < a) (hb : 0 < b) :
    integrableExpSet id (logLogisticMeasure a b) = Iic 0 := by
  ext t
  simpa [integrableExpSet, id_eq] using integrable_exp_mul_id_logLogisticMeasure_iff ha hb t

end TauCeti.Probability
