/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Poisson.Basic
public import TauCeti.Probability.Distributions.Poisson.Quantile
public import TauCeti.Probability.Distributions.ZeroTruncation

/-!
# The zero-truncated Poisson distribution

The zero-truncated Poisson law of rate `r` is `Po(r)[|{0}ᶜ]`, the Poisson law conditioned on a
positive count. This file specializes the generic zero-truncation formulas of
`TauCeti.Probability.Distributions.ZeroTruncation` using the Poisson mass `exp (-r)` at zero:

* the masses `r ^ k / (k! (exp r - 1))` for `k ≠ 0`;
* the mean `r / (1 - exp (-r))` and the variance;
* the exponential-integrability domain, all of `ℝ`;
* the cdf `(1 - P(⌊x⌋₊ + 1, r) - exp (-r)) / (1 - exp (-r))` through the regularized incomplete
  Gamma function `P`, and the quantile as the least index whose upper tail `P(n + 1, r)` is at most
  `(1 - u) (1 - exp (-r))`.

At rate zero the Poisson law is the point mass at zero and truncation removes all mass. The mass,
mean and variance formulas cover this boundary too, with the convention `1 / 0 = 0`.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, section 4.10.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal Nat

namespace TauCeti.Probability

variable {r : ℝ≥0}

private theorem poissonMeasure_singleton_zero_ne_one (hr : r ≠ 0) : Po(r) {0} ≠ 1 :=
  poissonMeasure_singleton_zero_eq_one_iff.not.2 hr

private theorem one_sub_exp_neg_pos (hr : r ≠ 0) : 0 < 1 - exp (-(r : ℝ)) := by
  rw [sub_pos, exp_lt_one_iff, neg_lt_zero, NNReal.coe_pos]
  exact pos_iff_ne_zero.2 hr

/-- Zero truncation removes all mass from a Poisson law exactly at rate zero. -/
theorem poissonMeasure_cond_compl_zero_eq_zero_iff : Po(r)[|{0}ᶜ] = 0 ↔ r = 0 := by
  refine ⟨fun h => by_contra fun hr => poissonMeasure_singleton_zero_ne_one hr
    (cond_compl_singleton_eq_zero_iff.1 h), fun hr => ?_⟩
  simp [hr]

/-- The zero-truncated Poisson law of positive rate is a probability law. -/
theorem isProbabilityMeasure_poissonMeasure_cond_compl_zero (hr : r ≠ 0) :
    IsProbabilityMeasure Po(r)[|{0}ᶜ] :=
  isProbabilityMeasure_cond_compl_singleton (poissonMeasure_singleton_zero_ne_one hr)

/-- The masses of the zero-truncated Poisson law away from zero are `r ^ k / (k! (exp r - 1))`. -/
theorem poissonMeasure_cond_compl_zero_real_singleton {k : ℕ} (hk : k ≠ 0) :
    (Po(r)[|{0}ᶜ]).real {k} = (r : ℝ) ^ k / (k ! * (exp r - 1)) := by
  rw [cond_compl_singleton_real_singleton hk, poissonMeasure_real_singleton,
    poissonMeasure_real_singleton_zero]
  rcases eq_or_ne r 0 with rfl | hr
  · simp [hk]
  have hexp := (one_sub_exp_neg_pos hr).ne'
  rw [exp_neg] at hexp ⊢
  field_simp

/-- The real cast of the zero-truncated Poisson law has every exponential moment. -/
theorem integrableExpSet_id_map_cast_poissonMeasure_cond_compl_zero :
    integrableExpSet id ((Po(r)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)) = univ := by
  rw [Measure.integrableExpSet_id_map_natCast_cond_compl_zero]
  exact integrableExpSet_id_map_cast_poissonMeasure r

/-- The mean of the zero-truncated Poisson law is `r / (1 - exp (-r))`. -/
@[simp]
theorem integral_id_map_cast_poissonMeasure_cond_compl_zero :
    ∫ x, x ∂(Po(r)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ) = r / (1 - exp (-(r : ℝ))) := by
  rw [Measure.integral_id_map_natCast_cond_compl_zero, integral_id_map_cast_poissonMeasure,
    poissonMeasure_real_singleton_zero]

/-- The variance of the zero-truncated Poisson law, `r (1 + r) / (1 - exp (-r))` minus the square
of the mean. -/
theorem variance_id_map_cast_poissonMeasure_cond_compl_zero :
    variance id ((Po(r)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)) =
      r * (1 + r) / (1 - exp (-(r : ℝ))) - ((r : ℝ) / (1 - exp (-(r : ℝ)))) ^ 2 := by
  have hsq : Integrable (fun x : ℝ => x ^ 2) Po(ℝ, r) :=
    integrable_pow_of_integrable_exp_mul (by norm_num : (1 : ℝ) ≠ 0)
      (integrable_exp_mul_id_map_cast_poissonMeasure r 1)
      (integrable_exp_mul_id_map_cast_poissonMeasure r (-1)) 2
  rw [Measure.variance_id_map_natCast_cond_compl_zero _ hsq, integral_sq_map_cast_poissonMeasure,
    integral_id_map_cast_poissonMeasure, poissonMeasure_real_singleton_zero]
  ring

/-- At a nonnegative point, the cdf of the zero-truncated Poisson law of positive rate is the
Poisson cdf `1 - P(⌊x⌋₊ + 1, r)` with the mass `exp (-r)` at zero removed and the rest
rescaled. -/
theorem cdf_map_cast_poissonMeasure_cond_compl_zero (hr : r ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    cdf ((Po(r)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)) x =
      (1 - regularizedGamma (⌊x⌋₊ + 1) (r : ℝ) - exp (-(r : ℝ))) / (1 - exp (-(r : ℝ))) := by
  rw [Measure.cdf_map_natCast_cond_compl_zero _ (poissonMeasure_singleton_zero_ne_one hr) hx,
    cdf_map_cast_poissonMeasure r hx, poissonMeasure_real_singleton_zero]

/-- Below one, the cdf of the zero-truncated Poisson law of positive rate vanishes. -/
theorem cdf_map_cast_poissonMeasure_cond_compl_zero_of_lt_one (hr : r ≠ 0) {x : ℝ}
    (hx : x < 1) : cdf ((Po(r)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)) x = 0 :=
  Measure.cdf_map_natCast_cond_compl_zero_of_lt_one _ (poissonMeasure_singleton_zero_ne_one hr) hx

/-- At an interior level `u`, the quantile of the zero-truncated Poisson law of positive rate is
the Poisson quantile at the rescaled level `exp (-r) + u (1 - exp (-r))`. -/
theorem quantile_map_cast_poissonMeasure_cond_compl_zero (hr : r ≠ 0) {u : ℝ}
    (hu : u ∈ Ioo 0 1) :
    ((Po(r)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)).quantile u =
      Po(ℝ, r).quantile (exp (-(r : ℝ)) + u * (1 - exp (-(r : ℝ)))) := by
  rw [Measure.quantile_map_natCast_cond_compl_zero _ (poissonMeasure_singleton_zero_ne_one hr) hu,
    poissonMeasure_real_singleton_zero]

/-- A natural number is the quantile of the zero-truncated Poisson law of positive rate at an
interior level `u` exactly when it is the least index whose Poisson upper tail
`P(n + 1, r)` is at most `(1 - u) (1 - exp (-r))`. -/
theorem quantile_map_cast_poissonMeasure_cond_compl_zero_eq_iff (hr : r ≠ 0) {u : ℝ}
    (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((Po(r)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {n : ℕ | regularizedGamma (n + 1) (r : ℝ) ≤ (1 - u) * (1 - exp (-(r : ℝ)))} k := by
  have hexp := one_sub_exp_neg_pos hr
  have hv : exp (-(r : ℝ)) + u * (1 - exp (-(r : ℝ))) ∈ Ioo 0 1 :=
    ⟨by nlinarith [exp_pos (-(r : ℝ)), hu.1], by nlinarith [hu.2]⟩
  rw [quantile_map_cast_poissonMeasure_cond_compl_zero hr hu,
    quantile_map_cast_poissonMeasure_eq_iff_regularizedGamma r hv,
    show 1 - (exp (-(r : ℝ)) + u * (1 - exp (-(r : ℝ)))) = (1 - u) * (1 - exp (-(r : ℝ))) by ring]

end TauCeti.Probability
