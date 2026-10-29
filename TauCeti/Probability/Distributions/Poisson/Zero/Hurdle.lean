/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Poisson.Zero.Truncated
public import TauCeti.Probability.Distributions.Zero.Hurdle

/-!
# The Poisson hurdle distribution

The Poisson hurdle law of rate `r` and zero weight `w ∈ [0, 1]` is
`(Po(r)[|{0}ᶜ]).atomMixture 0 w = w δ₀ + (1 - w) Po(r)[|{0}ᶜ]`: a count is zero with probability
`w`, and otherwise it is drawn from the zero-truncated Poisson law. This file specializes the
generic hurdle formulas of `TauCeti.Probability.Distributions.Zero.Hurdle` using the Poisson mass
`exp (-r)` at zero:

* the masses `w` at zero, by the generic
  `MeasureTheory.Measure.cond_compl_zero_atomMixture_zero_real_singleton_zero`, and
  `(1 - w) r ^ k / (k! (exp r - 1))` for `k ≠ 0`;
* the mean `(1 - w) r / (1 - exp (-r))` and the variance;
* the exponential-integrability domain, all of `ℝ`;
* the cdf `w + (1 - w) (1 - P(⌊x⌋₊ + 1, r) - exp (-r)) / (1 - exp (-r))` through the regularized
  incomplete Gamma function `P`, and the quantile as the least index whose weighted Poisson upper
  tail `(1 - w) P(n + 1, r)` is at most `(1 - u) (1 - exp (-r))`, or equivalently as zero up to
  the level `w` and the Poisson quantile at the level `exp (-r) + (u - w) / (1 - w) (1 - exp (-r))`
  above it.

At rate zero the truncated law vanishes, so the hurdle law is a probability law only at `w = 1`,
where it is the point mass at zero; the variance, cdf and quantile formulas assume `r ≠ 0`.

## References

* J. Mullahy, *Specification and testing of some modified count data models*, Journal of
  Econometrics 33 (1986), 341–365.
* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, section 8.2.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal Nat unitInterval

namespace TauCeti.Probability

variable {r : ℝ≥0} (w : unitInterval)

/-- Away from zero, the Poisson hurdle law has masses `(1 - w) r ^ k / (k! (exp r - 1))`. -/
theorem poissonMeasure_cond_compl_zero_atomMixture_zero_real_singleton {k : ℕ} (hk : k ≠ 0) :
    ((Po(r)[|{0}ᶜ]).atomMixture 0 w).real {k} =
      (1 - (w : ℝ)) * ((r : ℝ) ^ k / (k ! * (exp r - 1))) := by
  rw [Measure.atomMixture_real_singleton_of_ne _ hk.symm,
    poissonMeasure_cond_compl_zero_real_singleton hk]

/-- The real cast of the Poisson hurdle law has every exponential moment. -/
@[simp]
theorem integrableExpSet_id_map_cast_poissonMeasure_cond_compl_zero_atomMixture_zero :
    integrableExpSet id (((Po(r)[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) = univ := by
  have h : integrableExpSet id Po(ℝ, r) = univ := integrableExpSet_id_map_cast_poissonMeasure r
  rw [Measure.integrableExpSet_id_map_natCast_cond_compl_zero_atomMixture_zero, h, ite_self]

/-- The mean of the Poisson hurdle law is `(1 - w) r / (1 - exp (-r))`. -/
@[simp]
theorem integral_id_map_cast_poissonMeasure_cond_compl_zero_atomMixture_zero :
    ∫ x, x ∂((Po(r)[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ) =
      (1 - (w : ℝ)) * r / (1 - exp (-(r : ℝ))) := by
  rw [Measure.integral_id_map_natCast_cond_compl_zero_atomMixture_zero _ _
      ((memLp_id_map_cast_poissonMeasure r 1).integrable le_rfl),
    integral_id_map_cast_poissonMeasure, poissonMeasure_real_singleton_zero]

/-- The variance of the Poisson hurdle law of positive rate, `(1 - w) r (1 + r) / (1 - exp (-r))`
minus the square of the mean. -/
theorem variance_id_map_cast_poissonMeasure_cond_compl_zero_atomMixture_zero (hr : r ≠ 0) :
    variance id (((Po(r)[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) =
      (1 - (w : ℝ)) * (r * (1 + r)) / (1 - exp (-(r : ℝ))) -
        ((1 - (w : ℝ)) * r / (1 - exp (-(r : ℝ)))) ^ 2 := by
  rw [Measure.variance_id_map_natCast_cond_compl_zero_atomMixture_zero _ _
      (poissonMeasure_singleton_zero_eq_one_iff.not.2 hr)
      (memLp_id_map_cast_poissonMeasure r 2).integrable_sq,
    integral_sq_map_cast_poissonMeasure, integral_id_map_cast_poissonMeasure,
    poissonMeasure_real_singleton_zero]
  ring

/-- At a nonnegative point, the cdf of the Poisson hurdle law of positive rate is
`w + (1 - w) (1 - P(⌊x⌋₊ + 1, r) - exp (-r)) / (1 - exp (-r))`. -/
theorem cdf_map_cast_poissonMeasure_cond_compl_zero_atomMixture_zero (hr : r ≠ 0) {x : ℝ}
    (hx : 0 ≤ x) :
    cdf (((Po(r)[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) x =
      (w : ℝ) + (1 - (w : ℝ)) * (1 - regularizedGamma (⌊x⌋₊ + 1) (r : ℝ) - exp (-(r : ℝ))) /
        (1 - exp (-(r : ℝ))) := by
  rw [Measure.cdf_map_natCast_cond_compl_zero_atomMixture_zero _ _
      (poissonMeasure_singleton_zero_eq_one_iff.not.2 hr) hx,
    cdf_map_cast_poissonMeasure r hx, poissonMeasure_real_singleton_zero]

/-- Below the origin, the cdf of the Poisson hurdle law of positive rate vanishes. -/
theorem cdf_map_cast_poissonMeasure_cond_compl_zero_atomMixture_zero_of_neg (hr : r ≠ 0) {x : ℝ}
    (hx : x < 0) : cdf (((Po(r)[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) x = 0 := by
  have := isProbabilityMeasure_poissonMeasure_cond_compl_zero hr
  exact Measure.cdf_map_natCast_of_neg _ hx

/-- A natural number is the quantile of the Poisson hurdle law of positive rate at an interior
level `u` exactly when it is the least index whose weighted Poisson upper tail
`(1 - w) P(n + 1, r)` is at most `(1 - u) (1 - exp (-r))`. -/
theorem quantile_map_cast_poissonMeasure_cond_compl_zero_atomMixture_zero_eq_iff (hr : r ≠ 0)
    {u : ℝ} (hu : u ∈ Ioo 0 1) (k : ℕ) :
    (((Po(r)[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {n : ℕ | (1 - (w : ℝ)) * regularizedGamma (n + 1) (r : ℝ) ≤
        (1 - u) * (1 - exp (-(r : ℝ)))} k := by
  have hexp : 0 < 1 - exp (-(r : ℝ)) :=
    sub_pos.2 (exp_lt_one_iff.2 (neg_lt_zero.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hr))))
  have key (a : ℝ) : u ≤ (w : ℝ) + (1 - (w : ℝ)) * (1 - a - exp (-(r : ℝ))) /
      (1 - exp (-(r : ℝ))) ↔ (1 - (w : ℝ)) * a ≤ (1 - u) * (1 - exp (-(r : ℝ))) := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hexp]
    constructor <;> intro h <;> linarith
  simp_rw [Measure.quantile_map_natCast_cond_compl_zero_atomMixture_zero_eq_iff _ _
      (poissonMeasure_singleton_zero_eq_one_iff.not.2 hr) hu, poissonMeasure_real_Iic,
    poissonMeasure_real_singleton_zero, key]

/-- The quantile of the Poisson hurdle law of positive rate at an interior level `u` is zero up to
`w`, and above `w` it is the Poisson quantile at the rescaled level
`exp (-r) + (u - w) / (1 - w) * (1 - exp (-r))`. -/
theorem quantile_map_cast_poissonMeasure_cond_compl_zero_atomMixture_zero (hr : r ≠ 0) {u : ℝ}
    (hu : u ∈ Ioo 0 1) :
    (((Po(r)[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u =
      if u ≤ w then 0
      else Po(ℝ, r).quantile
        (exp (-(r : ℝ)) + (u - (w : ℝ)) / (1 - (w : ℝ)) * (1 - exp (-(r : ℝ)))) := by
  rw [Measure.quantile_map_natCast_cond_compl_zero_atomMixture_zero _ _
      (poissonMeasure_singleton_zero_eq_one_iff.not.2 hr) hu, poissonMeasure_real_singleton_zero]

end TauCeti.Probability
