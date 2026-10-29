/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.NegativeBinomial.Zero.Truncated
public import TauCeti.Probability.Distributions.Zero.Hurdle

/-!
# The negative-binomial hurdle distribution

The negative-binomial hurdle law with shape `r`, success probability `p` and zero weight
`w ∈ [0, 1]` is `((negativeBinomialMeasure r p)[|{0}ᶜ]).atomMixture 0 w`: a count is zero with
probability `w`, and otherwise it is drawn from the zero-truncated negative-binomial law. This
file specializes the generic hurdle formulas of `TauCeti.Probability.Distributions.Zero.Hurdle`
using the negative-binomial mass `p ^ r` at zero:

* the masses `w` at zero, by the generic
  `MeasureTheory.Measure.cond_compl_zero_atomMixture_zero_real_singleton_zero`, and
  `(1 - w) negativeBinomialWeightReal r p k / (1 - p ^ r)` for `k ≠ 0`;
* the mean `(1 - w) r (1 - p) / p / (1 - p ^ r)` and the variance;
* the exponential-integrability domain: all of `ℝ` at `w = 1`, and otherwise the negative-binomial
  domain `{t | (1 - p) exp t < 1}`;
* the cdf `w + (1 - w) (I_p(r, ⌊x⌋₊ + 1) - p ^ r) / (1 - p ^ r)` through the regularized incomplete
  Beta function, and the quantile as the least index whose hurdle cumulative mass
  `w + (1 - w) (I_p(r, j + 1) - p ^ r) / (1 - p ^ r)` reaches the level, or equivalently as zero
  up to the level `w` and the negative-binomial quantile at the level
  `p ^ r + (u - w) / (1 - w) (1 - p ^ r)` above it.

At the Dirac boundaries `r = 0` and `p = 1` the truncated law vanishes, so the hurdle law is a
probability law only at `w = 1`, where it is the point mass at zero; the variance, cdf and quantile
formulas assume `0 < r` and `p < 1`.

## References

* J. Mullahy, *Specification and testing of some modified count data models*, Journal of
  Econometrics 33 (1986), 341–365.
* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, section 8.2.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped unitInterval

namespace TauCeti.Probability

variable {r p : ℝ} (w : unitInterval)

/-- Away from zero, the negative-binomial hurdle law has the negative-binomial masses rescaled by
`(1 - w) / (1 - p ^ r)`. -/
theorem negativeBinomialMeasure_cond_compl_zero_atomMixture_zero_real_singleton (hr : 0 ≤ r)
    (hp : 0 < p) (hp1 : p ≤ 1) {k : ℕ} (hk : k ≠ 0) :
    (((negativeBinomialMeasure r p)[|{0}ᶜ]).atomMixture 0 w).real {k} =
      (1 - (w : ℝ)) * (negativeBinomialWeightReal r p k / (1 - p ^ r)) := by
  rw [Measure.atomMixture_real_singleton_of_ne _ hk.symm,
    negativeBinomialMeasure_cond_compl_zero_real_singleton hr hp hp1 hk]

/-- The exact exponential-integrability domain of the negative-binomial hurdle law of positive
shape: all of `ℝ` for the point mass at `w = 1`, and otherwise the negative-binomial domain
`{t | (1 - p) exp t < 1}`. -/
theorem integrableExpSet_id_map_cast_negativeBinomialMeasure_cond_compl_zero_atomMixture_zero
    (hr : 0 < r) (hp : 0 < p) (hp1 : p ≤ 1) :
    integrableExpSet id
        ((((negativeBinomialMeasure r p)[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) =
      if w = 1 then univ else {t | (1 - p) * exp t < 1} := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1
  rw [Measure.integrableExpSet_id_map_natCast_cond_compl_zero_atomMixture_zero,
    integrableExpSet_id_map_cast_negativeBinomialMeasure hr hp hp1]

/-- The mean of the negative-binomial hurdle law is `(1 - w) r (1 - p) / p / (1 - p ^ r)`. -/
theorem integral_id_map_cast_negativeBinomialMeasure_cond_compl_zero_atomMixture_zero
    (hr : 0 ≤ r) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∫ x, x ∂(((negativeBinomialMeasure r p)[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ) =
      (1 - (w : ℝ)) * (r * (1 - p) / p) / (1 - p ^ r) := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr hp hp1
  rw [Measure.integral_id_map_natCast_cond_compl_zero_atomMixture_zero _ _
      ((memLp_id_map_cast_negativeBinomialMeasure hr hp hp1 1).integrable le_rfl),
    integral_id_map_cast_negativeBinomialMeasure hr hp hp1,
    negativeBinomialMeasure_real_singleton_zero hr hp hp1]

/-- The variance of the negative-binomial hurdle law of positive shape and success probability
below one: the rescaled second moment `(1 - w) r (1 - p) (1 + r (1 - p)) / p ^ 2 / (1 - p ^ r)`
minus the square of the mean. -/
theorem variance_id_map_cast_negativeBinomialMeasure_cond_compl_zero_atomMixture_zero
    (hr : 0 < r) (hp : 0 < p) (hp1 : p < 1) :
    variance id
        ((((negativeBinomialMeasure r p)[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) =
      (1 - (w : ℝ)) * (r * (1 - p) * (1 + r * (1 - p)) / p ^ 2) / (1 - p ^ r) -
        ((1 - (w : ℝ)) * (r * (1 - p) / p) / (1 - p ^ r)) ^ 2 := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1.le
  rw [Measure.variance_id_map_natCast_cond_compl_zero_atomMixture_zero _ _
      (negativeBinomialMeasure_singleton_zero_ne_one hr hp hp1)
      (memLp_id_map_cast_negativeBinomialMeasure hr.le hp hp1.le 2).integrable_sq,
    integral_sq_map_cast_negativeBinomialMeasure hr.le hp hp1.le,
    integral_id_map_cast_negativeBinomialMeasure hr.le hp hp1.le,
    negativeBinomialMeasure_real_singleton_zero hr.le hp hp1.le]

/-- At a nonnegative point, the cdf of the negative-binomial hurdle law of positive shape and
success probability below one is `w + (1 - w) (I_p(r, ⌊x⌋₊ + 1) - p ^ r) / (1 - p ^ r)`. -/
theorem cdf_map_cast_negativeBinomialMeasure_cond_compl_zero_atomMixture_zero (hr : 0 < r)
    (hp : 0 < p) (hp1 : p < 1) {x : ℝ} (hx : 0 ≤ x) :
    cdf ((((negativeBinomialMeasure r p)[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) x =
      (w : ℝ) + (1 - (w : ℝ)) * (regularizedIncompleteBeta r (⌊x⌋₊ + 1) p - p ^ r) /
        (1 - p ^ r) := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1.le
  rw [Measure.cdf_map_natCast_cond_compl_zero_atomMixture_zero _ _
      (negativeBinomialMeasure_singleton_zero_ne_one hr hp hp1) hx,
    cdf_map_cast_negativeBinomialMeasure hr hp hp1.le hx,
    negativeBinomialMeasure_real_singleton_zero hr.le hp hp1.le]

/-- Below the origin, the cdf of the negative-binomial hurdle law of positive shape and success
probability below one vanishes. -/
theorem cdf_map_cast_negativeBinomialMeasure_cond_compl_zero_atomMixture_zero_of_neg (hr : 0 < r)
    (hp : 0 < p) (hp1 : p < 1) {x : ℝ} (hx : x < 0) :
    cdf ((((negativeBinomialMeasure r p)[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) x =
      0 := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure_cond_compl_zero hr hp hp1
  exact Measure.cdf_map_natCast_of_neg _ hx

/-- A natural number is the quantile of the negative-binomial hurdle law of positive shape and
success probability below one at an interior level `u` exactly when it is the least index whose
hurdle cumulative mass `w + (1 - w) (I_p(r, j + 1) - p ^ r) / (1 - p ^ r)` reaches `u`. -/
theorem quantile_map_cast_negativeBinomialMeasure_cond_compl_zero_atomMixture_zero_eq_iff
    (hr : 0 < r) (hp : 0 < p) (hp1 : p < 1) {u : ℝ} (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((((negativeBinomialMeasure r p)[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile
        u = k ↔
      IsLeast {j : ℕ | u ≤ (w : ℝ) + (1 - (w : ℝ)) *
        (regularizedIncompleteBeta r (j + 1) p - p ^ r) / (1 - p ^ r)} k := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1.le
  simp_rw [Measure.quantile_map_natCast_cond_compl_zero_atomMixture_zero_eq_iff _ _
      (negativeBinomialMeasure_singleton_zero_ne_one hr hp hp1) hu,
    negativeBinomialMeasure_real_Iic hr hp hp1.le,
    negativeBinomialMeasure_real_singleton_zero hr.le hp hp1.le]

/-- The quantile of the negative-binomial hurdle law of positive shape and success probability
below one at an interior level `u` is zero up to `w`, and above `w` it is the negative-binomial
quantile at the rescaled level `p ^ r + (u - w) / (1 - w) * (1 - p ^ r)`. -/
theorem quantile_map_cast_negativeBinomialMeasure_cond_compl_zero_atomMixture_zero (hr : 0 < r)
    (hp : 0 < p) (hp1 : p < 1) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((((negativeBinomialMeasure r p)[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile
        u =
      if u ≤ w then 0
      else ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)).quantile
        (p ^ r + (u - (w : ℝ)) / (1 - (w : ℝ)) * (1 - p ^ r)) := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1.le
  rw [Measure.quantile_map_natCast_cond_compl_zero_atomMixture_zero _ _
      (negativeBinomialMeasure_singleton_zero_ne_one hr hp hp1) hu,
    negativeBinomialMeasure_real_singleton_zero hr.le hp hp1.le]

end TauCeti.Probability
