/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.NegativeBinomial.Quantile
public import TauCeti.Probability.Distributions.NegativeBinomial.Transforms
public import TauCeti.Probability.Distributions.Zero.Truncation

/-!
# The zero-truncated negative-binomial distribution

The zero-truncated negative-binomial law with shape `r` and success probability `p` is
`(negativeBinomialMeasure r p)[|{0}ᶜ]`, the negative-binomial law conditioned on a positive count.
This file specializes the generic zero-truncation formulas of
`TauCeti.Probability.Distributions.Zero.Truncation` using the negative-binomial mass `p ^ r` at
zero:

* the masses `negativeBinomialWeightReal r p k / (1 - p ^ r)` for `k ≠ 0`;
* the mean `r (1 - p) / (p (1 - p ^ r))` and the variance;
* the exponential-integrability domain `{t | (1 - p) exp t < 1}`, unchanged by truncation;
* the cdf `(I_p(r, ⌊x⌋₊ + 1) - p ^ r) / (1 - p ^ r)` through the regularized incomplete Beta
  function, and the quantile as the least index whose untruncated cumulative mass reaches the
  rescaled level `p ^ r + u (1 - p ^ r)`.

At the boundaries `r = 0` and `p = 1` the negative-binomial law is the point mass at zero and
truncation removes all mass. The mass, mean and variance formulas cover these boundaries too, with
the convention `1 / 0 = 0`.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, section 5.11.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {r p : ℝ}

/-- A negative-binomial law of positive shape and success probability below one is not the point
mass at zero. -/
theorem negativeBinomialMeasure_singleton_zero_ne_one (hr : 0 < r) (hp : 0 < p)
    (hp1 : p < 1) : negativeBinomialMeasure r p {0} ≠ 1 := by
  rw [Ne, negativeBinomialMeasure_singleton_zero_eq_one_iff hr.le hp hp1.le]
  exact fun h => h.elim hr.ne' hp1.ne

private theorem one_sub_rpow_pos (hr : 0 < r) (hp : 0 < p) (hp1 : p < 1) : 0 < 1 - p ^ r :=
  sub_pos.2 (rpow_lt_one hp.le hp1 hr)

/-- Zero truncation removes all mass from a valid negative-binomial law exactly at the Dirac
boundaries `r = 0` and `p = 1`. -/
theorem negativeBinomialMeasure_cond_compl_zero_eq_zero_iff (hr : 0 ≤ r) (hp : 0 < p)
    (hp1 : p ≤ 1) : (negativeBinomialMeasure r p)[|{0}ᶜ] = 0 ↔ r = 0 ∨ p = 1 := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr hp hp1
  rw [cond_compl_singleton_eq_zero_iff,
    negativeBinomialMeasure_singleton_zero_eq_one_iff hr hp hp1]

/-- The zero-truncated negative-binomial law of positive shape and success probability below one
is a probability law. -/
theorem isProbabilityMeasure_negativeBinomialMeasure_cond_compl_zero (hr : 0 < r) (hp : 0 < p)
    (hp1 : p < 1) : IsProbabilityMeasure (negativeBinomialMeasure r p)[|{0}ᶜ] := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1.le
  exact isProbabilityMeasure_cond_compl_singleton
    (negativeBinomialMeasure_singleton_zero_ne_one hr hp hp1)

/-- The masses of the zero-truncated negative-binomial law away from zero are the
negative-binomial masses divided by `1 - p ^ r`. -/
theorem negativeBinomialMeasure_cond_compl_zero_real_singleton (hr : 0 ≤ r) (hp : 0 < p)
    (hp1 : p ≤ 1) {k : ℕ} (hk : k ≠ 0) :
    ((negativeBinomialMeasure r p)[|{0}ᶜ]).real {k} =
      negativeBinomialWeightReal r p k / (1 - p ^ r) := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr hp hp1
  rw [cond_compl_singleton_real_singleton hk, negativeBinomialMeasure_real_singleton hr hp hp1,
    negativeBinomialMeasure_real_singleton_zero hr hp hp1]

/-- Zero truncation leaves the exponential-integrability domain `{t | (1 - p) exp t < 1}` of a
positive-shape negative-binomial law unchanged. -/
theorem integrableExpSet_id_map_cast_negativeBinomialMeasure_cond_compl_zero (hr : 0 < r)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    integrableExpSet id (((negativeBinomialMeasure r p)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)) =
      {t | (1 - p) * exp t < 1} := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1
  rw [Measure.integrableExpSet_id_map_natCast_cond_compl_zero,
    integrableExpSet_id_map_cast_negativeBinomialMeasure hr hp hp1]

/-- The mean of the zero-truncated negative-binomial law is `r (1 - p) / p / (1 - p ^ r)`. -/
theorem integral_id_map_cast_negativeBinomialMeasure_cond_compl_zero (hr : 0 ≤ r) (hp : 0 < p)
    (hp1 : p ≤ 1) :
    ∫ x, x ∂((negativeBinomialMeasure r p)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ) =
      r * (1 - p) / p / (1 - p ^ r) := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr hp hp1
  rw [Measure.integral_id_map_natCast_cond_compl_zero,
    integral_id_map_cast_negativeBinomialMeasure hr hp hp1,
    negativeBinomialMeasure_real_singleton_zero hr hp hp1]

/-- The variance of the zero-truncated negative-binomial law: the untruncated second moment
`r (1 - p) (1 + r (1 - p)) / p ^ 2` divided by `1 - p ^ r`, minus the square of the mean. -/
theorem variance_id_map_cast_negativeBinomialMeasure_cond_compl_zero (hr : 0 ≤ r) (hp : 0 < p)
    (hp1 : p ≤ 1) :
    variance id (((negativeBinomialMeasure r p)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)) =
      r * (1 - p) * (1 + r * (1 - p)) / p ^ 2 / (1 - p ^ r) -
        (r * (1 - p) / p / (1 - p ^ r)) ^ 2 := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [(negativeBinomialMeasure_cond_compl_zero_eq_zero_iff le_rfl hp hp1).2 (Or.inl rfl)]
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1
  rw [Measure.variance_id_map_natCast_cond_compl_zero _
      (integrable_pow_of_mem_interior_integrableExpSet
        (zero_mem_interior_integrableExpSet_id_map_cast_negativeBinomialMeasure hr hp hp1) 2),
    integral_sq_map_cast_negativeBinomialMeasure hr.le hp hp1,
    integral_id_map_cast_negativeBinomialMeasure hr.le hp hp1,
    negativeBinomialMeasure_real_singleton_zero hr.le hp hp1]

/-- At a nonnegative point, the cdf of the zero-truncated negative-binomial law is the
negative-binomial cdf `I_p(r, ⌊x⌋₊ + 1)` with the mass `p ^ r` at zero removed and the rest
rescaled. -/
theorem cdf_map_cast_negativeBinomialMeasure_cond_compl_zero (hr : 0 < r) (hp : 0 < p)
    (hp1 : p < 1) {x : ℝ} (hx : 0 ≤ x) :
    cdf (((negativeBinomialMeasure r p)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)) x =
      (regularizedIncompleteBeta r (⌊x⌋₊ + 1) p - p ^ r) / (1 - p ^ r) := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1.le
  rw [Measure.cdf_map_natCast_cond_compl_zero _
      (negativeBinomialMeasure_singleton_zero_ne_one hr hp hp1) hx,
    cdf_map_cast_negativeBinomialMeasure hr hp hp1.le hx,
    negativeBinomialMeasure_real_singleton_zero hr.le hp hp1.le]

/-- Below one, the cdf of the zero-truncated negative-binomial law of positive shape and success
probability below one vanishes. -/
theorem cdf_map_cast_negativeBinomialMeasure_cond_compl_zero_of_lt_one (hr : 0 < r) (hp : 0 < p)
    (hp1 : p < 1) {x : ℝ} (hx : x < 1) :
    cdf (((negativeBinomialMeasure r p)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)) x = 0 := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1.le
  exact Measure.cdf_map_natCast_cond_compl_zero_of_lt_one _
    (negativeBinomialMeasure_singleton_zero_ne_one hr hp hp1) hx

/-- At an interior level `u`, the quantile of the zero-truncated negative-binomial law is the
negative-binomial quantile at the rescaled level `p ^ r + u (1 - p ^ r)`. -/
theorem quantile_map_cast_negativeBinomialMeasure_cond_compl_zero (hr : 0 < r) (hp : 0 < p)
    (hp1 : p < 1) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    (((negativeBinomialMeasure r p)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)).quantile u =
      ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)).quantile
        (p ^ r + u * (1 - p ^ r)) := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1.le
  rw [Measure.quantile_map_natCast_cond_compl_zero _
      (negativeBinomialMeasure_singleton_zero_ne_one hr hp hp1) hu,
    negativeBinomialMeasure_real_singleton_zero hr.le hp hp1.le]

/-- A natural number is the quantile of the zero-truncated negative-binomial law at an interior
level `u` exactly when it is the least index whose negative-binomial cumulative mass
`I_p(r, j + 1)` reaches `p ^ r + u (1 - p ^ r)`. -/
theorem quantile_map_cast_negativeBinomialMeasure_cond_compl_zero_eq_iff (hr : 0 < r)
    (hp : 0 < p) (hp1 : p < 1) {u : ℝ} (hu : u ∈ Ioo 0 1) (k : ℕ) :
    (((negativeBinomialMeasure r p)[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {j : ℕ | p ^ r + u * (1 - p ^ r) ≤ regularizedIncompleteBeta r (j + 1) p} k := by
  have hpos := one_sub_rpow_pos hr hp hp1
  have hv : p ^ r + u * (1 - p ^ r) ∈ Ioo 0 1 :=
    ⟨by nlinarith [rpow_pos_of_pos hp r, hu.1], by nlinarith [hu.2]⟩
  rw [quantile_map_cast_negativeBinomialMeasure_cond_compl_zero hr hp hp1 hu,
    quantile_map_cast_negativeBinomialMeasure_eq_iff hr hp hp1.le hv]

end TauCeti.Probability
