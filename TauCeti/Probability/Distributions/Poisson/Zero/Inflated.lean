/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Poisson.Basic
public import TauCeti.Probability.Distributions.Poisson.Quantile
public import TauCeti.Probability.Distributions.Zero.Inflation

/-!
# The zero-inflated Poisson distribution

The zero-inflated Poisson law of rate `r` and inflation weight `w ∈ [0, 1]` is
`Po(r).atomMixture 0 w = w δ₀ + (1 - w) Po(r)`. This file specializes the generic zero-inflation
formulas of `TauCeti.Probability.Distributions.Zero.Inflation` using the Poisson masses
`exp (-r) r ^ k / k!`:

* the masses `w + (1 - w) exp (-r)` at zero and `(1 - w) exp (-r) r ^ k / k!` for `k ≠ 0`;
* the mean `(1 - w) r` and the variance `(1 - w) r (1 + w r)`;
* the exponential-integrability domain, all of `ℝ`;
* the cdf `w + (1 - w) (1 - P(⌊x⌋₊ + 1, r))` through the regularized incomplete Gamma function
  `P`, and the quantile as the least index whose weighted upper tail `(1 - w) P(n + 1, r)` is at
  most `1 - u`, or equivalently as zero up to the mass at zero and the Poisson quantile at the
  rescaled level `(u - w) / (1 - w)` above it.

The boundary cases `r = 0` and `w = 1`, where the law is the point mass at zero, are included.

## References

* D. Lambert, *Zero-inflated Poisson regression, with an application to defects in
  manufacturing*, Technometrics 34 (1992), 1–14.
* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, chapter 8.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal Nat unitInterval

namespace TauCeti.Probability

variable (r : ℝ≥0) (w : unitInterval)

/-- The zero-inflated Poisson law has mass `w + (1 - w) exp (-r)` at zero. -/
theorem poissonMeasure_atomMixture_zero_real_singleton_zero :
    (Po(r).atomMixture 0 w).real {0} = (w : ℝ) + (1 - (w : ℝ)) * exp (-(r : ℝ)) := by
  rw [Measure.atomMixture_real_singleton, poissonMeasure_real_singleton_zero]

/-- Away from zero, the zero-inflated Poisson law has masses `(1 - w) exp (-r) r ^ k / k!`. -/
theorem poissonMeasure_atomMixture_zero_real_singleton {k : ℕ} (hk : k ≠ 0) :
    (Po(r).atomMixture 0 w).real {k} =
      (1 - (w : ℝ)) * (exp (-(r : ℝ)) * (r : ℝ) ^ k / k !) := by
  rw [Measure.atomMixture_real_singleton_of_ne _ hk.symm, poissonMeasure_real_singleton]

/-- The real cast of the zero-inflated Poisson law has every exponential moment. -/
@[simp]
theorem integrableExpSet_id_map_cast_poissonMeasure_atomMixture_zero :
    integrableExpSet id ((Po(r).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) = univ := by
  have h : integrableExpSet id Po(ℝ, r) = univ := integrableExpSet_id_map_cast_poissonMeasure r
  rw [Measure.map_natCast_atomMixture_zero, Measure.integrableExpSet_id_atomMixture, h, ite_self]

/-- The mean of the zero-inflated Poisson law is `(1 - w) r`. -/
@[simp]
theorem integral_id_map_cast_poissonMeasure_atomMixture_zero :
    ∫ x, x ∂(Po(r).atomMixture 0 w).map (Nat.cast : ℕ → ℝ) = (1 - (w : ℝ)) * r := by
  rw [Measure.map_natCast_atomMixture_zero, Measure.integral_id_atomMixture _ _ _
      ((memLp_id_map_cast_poissonMeasure r 1).integrable le_rfl),
    integral_id_map_cast_poissonMeasure]
  ring

/-- The variance of the zero-inflated Poisson law is `(1 - w) r (1 + w r)`. -/
@[simp]
theorem variance_id_map_cast_poissonMeasure_atomMixture_zero :
    variance id ((Po(r).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) =
      (1 - (w : ℝ)) * r * (1 + (w : ℝ) * r) := by
  rw [Measure.map_natCast_atomMixture_zero,
    Measure.variance_id_atomMixture _ _ _ (memLp_id_map_cast_poissonMeasure r 2),
    variance_id_map_cast_poissonMeasure, integral_id_map_cast_poissonMeasure]
  ring

/-- At a nonnegative point, the cdf of the zero-inflated Poisson law is
`w + (1 - w) (1 - P(⌊x⌋₊ + 1, r))`. -/
theorem cdf_map_cast_poissonMeasure_atomMixture_zero {x : ℝ} (hx : 0 ≤ x) :
    cdf ((Po(r).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) x =
      (w : ℝ) + (1 - (w : ℝ)) * (1 - regularizedGamma (⌊x⌋₊ + 1) (r : ℝ)) := by
  rw [Measure.cdf_map_natCast _ hx, Measure.atomMixture_zero_real_Iic, poissonMeasure_real_Iic]

/-- Below the origin, the cdf of the zero-inflated Poisson law vanishes. -/
theorem cdf_map_cast_poissonMeasure_atomMixture_zero_of_neg {x : ℝ} (hx : x < 0) :
    cdf ((Po(r).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) x = 0 :=
  Measure.cdf_map_natCast_of_neg _ hx

/-- A natural number is the quantile of the zero-inflated Poisson law at an interior level `u`
exactly when it is the least index whose weighted Poisson upper tail `(1 - w) P(n + 1, r)` is at
most `1 - u`. -/
theorem quantile_map_cast_poissonMeasure_atomMixture_zero_eq_iff {u : ℝ} (hu : u ∈ Ioo 0 1)
    (k : ℕ) :
    ((Po(r).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {n : ℕ | (1 - (w : ℝ)) * regularizedGamma (n + 1) (r : ℝ) ≤ 1 - u} k := by
  have key (a : ℝ) : u ≤ (w : ℝ) + (1 - (w : ℝ)) * (1 - a) ↔ (1 - (w : ℝ)) * a ≤ 1 - u := by
    constructor <;> intro h <;> linarith
  simp_rw [Measure.quantile_map_natCast_atomMixture_zero_eq_iff _ _ hu, poissonMeasure_real_Iic,
    key]

/-- At an interior level, the quantile of the zero-inflated Poisson law is zero exactly up to the
mass `w + (1 - w) exp (-r)` at zero. -/
@[simp]
theorem quantile_map_cast_poissonMeasure_atomMixture_zero_eq_zero_iff {u : ℝ}
    (hu : u ∈ Ioo 0 1) :
    ((Po(r).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u = 0 ↔
      u ≤ (w : ℝ) + (1 - (w : ℝ)) * exp (-(r : ℝ)) := by
  rw [Measure.quantile_map_natCast_atomMixture_zero_eq_zero_iff _ _ hu,
    poissonMeasure_real_singleton_zero]

/-- The quantile of the zero-inflated Poisson law is zero up to the mass at zero, and above it is
the Poisson quantile at the rescaled level `(u - w) / (1 - w)`. -/
theorem quantile_map_cast_poissonMeasure_atomMixture_zero {u : ℝ} (hu : u ∈ Ioc 0 1) :
    ((Po(r).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u =
      if u ≤ (w : ℝ) + (1 - (w : ℝ)) * exp (-(r : ℝ)) then 0
      else Po(ℝ, r).quantile ((u - (w : ℝ)) / (1 - (w : ℝ))) := by
  rw [Measure.quantile_map_natCast_atomMixture_zero _ _ hu, poissonMeasure_real_singleton_zero]

end TauCeti.Probability
