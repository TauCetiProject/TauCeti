/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.NegativeBinomial.Quantile
public import TauCeti.Probability.Distributions.NegativeBinomial.Transforms
public import TauCeti.Probability.Distributions.Zero.Inflation

/-!
# The zero-inflated negative-binomial distribution

The zero-inflated negative-binomial law with shape `r`, success probability `p` and inflation
weight `w ∈ [0, 1]` is `(negativeBinomialMeasure r p).atomMixture 0 w`, the mixture
`w δ₀ + (1 - w) NB(r, p)`. This file specializes the generic zero-inflation formulas of
`TauCeti.Probability.Distributions.Zero.Inflation` using the negative-binomial mass `p ^ r` at
zero:

* the masses `w + (1 - w) p ^ r` at zero and `(1 - w) negativeBinomialWeightReal r p k` for
  `k ≠ 0`;
* the mean `(1 - w) r (1 - p) / p` and the variance `(1 - w) r (1 - p) (1 + w r (1 - p)) / p ^ 2`;
* the exponential-integrability domain: all of `ℝ` at `w = 1`, and otherwise the negative-binomial
  domain `{t | (1 - p) exp t < 1}`;
* the cdf `w + (1 - w) I_p(r, ⌊x⌋₊ + 1)` through the regularized incomplete Beta function, and the
  quantile as the least index whose zero-inflated cumulative mass `w + (1 - w) I_p(r, j + 1)`
  reaches the level, or equivalently as zero up to the mass at zero and the negative-binomial
  quantile at the rescaled level `(u - w) / (1 - w)` above it.

The mass, mean, variance and quantile formulas also cover the Dirac boundaries `r = 0` and `p = 1`.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, chapter 8.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped unitInterval

namespace TauCeti.Probability

variable {r p : ℝ} (w : unitInterval)

/-- The zero-inflated negative-binomial law has mass `w + (1 - w) p ^ r` at zero. -/
theorem negativeBinomialMeasure_atomMixture_zero_real_singleton_zero (hr : 0 ≤ r) (hp : 0 < p)
    (hp1 : p ≤ 1) :
    ((negativeBinomialMeasure r p).atomMixture 0 w).real {0} =
      (w : ℝ) + (1 - (w : ℝ)) * p ^ r := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr hp hp1
  rw [Measure.atomMixture_real_singleton, negativeBinomialMeasure_real_singleton_zero hr hp hp1]

/-- Away from zero, the zero-inflated negative-binomial law rescales the negative-binomial masses
by `1 - w`. -/
theorem negativeBinomialMeasure_atomMixture_zero_real_singleton (hr : 0 ≤ r) (hp : 0 < p)
    (hp1 : p ≤ 1) {k : ℕ} (hk : k ≠ 0) :
    ((negativeBinomialMeasure r p).atomMixture 0 w).real {k} =
      (1 - (w : ℝ)) * negativeBinomialWeightReal r p k := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr hp hp1
  rw [Measure.atomMixture_real_singleton_of_ne _ hk.symm,
    negativeBinomialMeasure_real_singleton hr hp hp1]

/-- The exact exponential-integrability domain of the zero-inflated negative-binomial law of
positive shape: all of `ℝ` for the point mass at `w = 1`, and otherwise the negative-binomial
domain `{t | (1 - p) exp t < 1}`. -/
theorem integrableExpSet_id_map_cast_negativeBinomialMeasure_atomMixture_zero (hr : 0 < r)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    integrableExpSet id (((negativeBinomialMeasure r p).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) =
      if w = 1 then univ else {t | (1 - p) * exp t < 1} := by
  rw [Measure.map_natCast_atomMixture_zero, Measure.integrableExpSet_id_atomMixture,
    integrableExpSet_id_map_cast_negativeBinomialMeasure hr hp hp1]

/-- The mean of the zero-inflated negative-binomial law is `(1 - w) r (1 - p) / p`. -/
theorem integral_id_map_cast_negativeBinomialMeasure_atomMixture_zero (hr : 0 ≤ r) (hp : 0 < p)
    (hp1 : p ≤ 1) :
    ∫ x, x ∂((negativeBinomialMeasure r p).atomMixture 0 w).map (Nat.cast : ℕ → ℝ) =
      (1 - (w : ℝ)) * (r * (1 - p) / p) := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr hp hp1
  rw [Measure.map_natCast_atomMixture_zero, Measure.integral_id_atomMixture _ _ _
      ((memLp_id_map_cast_negativeBinomialMeasure hr hp hp1 1).integrable le_rfl),
    integral_id_map_cast_negativeBinomialMeasure hr hp hp1]
  ring

/-- The variance of the zero-inflated negative-binomial law is
`(1 - w) r (1 - p) (1 + w r (1 - p)) / p ^ 2`. -/
theorem variance_id_map_cast_negativeBinomialMeasure_atomMixture_zero (hr : 0 ≤ r) (hp : 0 < p)
    (hp1 : p ≤ 1) :
    variance id (((negativeBinomialMeasure r p).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) =
      (1 - (w : ℝ)) * r * (1 - p) * (1 + (w : ℝ) * r * (1 - p)) / p ^ 2 := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr hp hp1
  rw [Measure.map_natCast_atomMixture_zero, Measure.variance_id_atomMixture _ _ _
      (memLp_id_map_cast_negativeBinomialMeasure hr hp hp1 2),
    variance_id_map_cast_negativeBinomialMeasure hr hp hp1,
    integral_id_map_cast_negativeBinomialMeasure hr hp hp1]
  field_simp
  ring

/-- At a nonnegative point, the cdf of the zero-inflated negative-binomial law of positive shape
is `w + (1 - w) I_p(r, ⌊x⌋₊ + 1)`. -/
theorem cdf_map_cast_negativeBinomialMeasure_atomMixture_zero (hr : 0 < r) (hp : 0 < p)
    (hp1 : p ≤ 1) {x : ℝ} (hx : 0 ≤ x) :
    cdf (((negativeBinomialMeasure r p).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) x =
      (w : ℝ) + (1 - (w : ℝ)) * regularizedIncompleteBeta r (⌊x⌋₊ + 1) p := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1
  rw [Measure.cdf_map_natCast _ hx, Measure.atomMixture_zero_real_Iic,
    negativeBinomialMeasure_real_Iic hr hp hp1]

/-- Below the origin, the cdf of the zero-inflated negative-binomial law vanishes. -/
theorem cdf_map_cast_negativeBinomialMeasure_atomMixture_zero_of_neg (hr : 0 ≤ r) (hp : 0 < p)
    (hp1 : p ≤ 1) {x : ℝ} (hx : x < 0) :
    cdf (((negativeBinomialMeasure r p).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) x = 0 := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr hp hp1
  exact Measure.cdf_map_natCast_of_neg _ hx

/-- A natural number is the quantile of the zero-inflated negative-binomial law of positive shape
at an interior level `u` exactly when it is the least index whose zero-inflated cumulative mass
`w + (1 - w) I_p(r, j + 1)` reaches `u`. -/
theorem quantile_map_cast_negativeBinomialMeasure_atomMixture_zero_eq_iff (hr : 0 < r)
    (hp : 0 < p) (hp1 : p ≤ 1) {u : ℝ} (hu : u ∈ Ioo 0 1) (k : ℕ) :
    (((negativeBinomialMeasure r p).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {j : ℕ | u ≤ (w : ℝ) + (1 - (w : ℝ)) * regularizedIncompleteBeta r (j + 1) p} k := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1
  simp_rw [Measure.quantile_map_natCast_atomMixture_zero_eq_iff _ _ hu,
    negativeBinomialMeasure_real_Iic hr hp hp1]

/-- At an interior level, the quantile of the zero-inflated negative-binomial law is zero exactly
up to the mass `w + (1 - w) p ^ r` at zero. -/
theorem quantile_map_cast_negativeBinomialMeasure_atomMixture_zero_eq_zero_iff (hr : 0 ≤ r)
    (hp : 0 < p) (hp1 : p ≤ 1) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    (((negativeBinomialMeasure r p).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u = 0 ↔
      u ≤ (w : ℝ) + (1 - (w : ℝ)) * p ^ r := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr hp hp1
  rw [Measure.quantile_map_natCast_atomMixture_zero_eq_zero_iff _ _ hu,
    negativeBinomialMeasure_real_singleton_zero hr hp hp1]

/-- The quantile of the zero-inflated negative-binomial law is zero up to the mass at zero, and
above it is the negative-binomial quantile at the rescaled level `(u - w) / (1 - w)`. -/
theorem quantile_map_cast_negativeBinomialMeasure_atomMixture_zero (hr : 0 ≤ r) (hp : 0 < p)
    (hp1 : p ≤ 1) {u : ℝ} (hu : u ∈ Ioc 0 1) :
    (((negativeBinomialMeasure r p).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u =
      if u ≤ (w : ℝ) + (1 - (w : ℝ)) * p ^ r then 0
      else ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)).quantile
        ((u - (w : ℝ)) / (1 - (w : ℝ))) := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr hp hp1
  rw [Measure.quantile_map_natCast_atomMixture_zero _ _ hu,
    negativeBinomialMeasure_real_singleton_zero hr hp hp1]

end TauCeti.Probability
