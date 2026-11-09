/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Zero.Inflation
public import TauCeti.Probability.Distributions.Zero.Truncation

/-!
# Hurdle laws on the natural numbers

The hurdle version of a probability law `ν` on `ℕ` with zero weight `w ∈ [0, 1]` is
`(ν[|{0}ᶜ]).atomMixture 0 w = w δ₀ + (1 - w) ν[|{0}ᶜ]`: a count is zero with probability `w`, and
otherwise it is drawn from the zero-truncated law of `ν`. Unlike zero inflation, the weight `w` is
the whole mass at zero, whatever mass `ν` itself puts there.

Write `p₀ = ν.real {0}`. This file combines the zero-inflation formulas of
`TauCeti.Probability.Distributions.Zero.Inflation` with the zero-truncation formulas of
`TauCeti.Probability.Distributions.Zero.Truncation`:

* the law is a probability law exactly when `ν` is not the point mass at zero or `w = 1`;
* the masses `w` at zero and `(1 - w) ν.real {k} / (1 - p₀)` for `k ≠ 0`, and the cumulative
  masses `w + (1 - w) (ν.real (Iic k) - p₀) / (1 - p₀)`;
* the nonzero natural moments `(1 - w) E[X ^ n] / (1 - p₀)` of the real cast, its mean and
  variance, and its exponential-integrability domain, which is all of `ℝ` at `w = 1` and otherwise
  that of `ν`;
* the cdf of the real cast and its quantile: zero up to the level `w`, and above it the quantile of
  `ν` at the level `p₀ + (u - w) / (1 - w) * (1 - p₀)`.

At `w = 1` the hurdle law is the point mass at zero by `MeasureTheory.Measure.atomMixture_one`,
even when `ν` is the point mass at zero and the truncated law vanishes. In that zero-base case
with `w < 1` the hurdle law is not a probability law. The variance formula covers this boundary,
while the cdf and quantile formulas assume that `ν` is not the point mass at zero.

## References

* J. Mullahy, *Specification and testing of some modified count data models*, Journal of
  Econometrics 33 (1986), 341–365.
* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, section 8.2.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped unitInterval

namespace MeasureTheory.Measure

variable (ν : Measure ℕ) (w : unitInterval)

/-- The hurdle law has mass `w` at zero. -/
theorem cond_compl_zero_atomMixture_zero_real_singleton_zero :
    ((ν[|{0}ᶜ]).atomMixture 0 w).real {0} = w := by
  simp [measureReal_def, unitInterval.nonneg w]

variable [IsProbabilityMeasure ν]

/-- The hurdle law of a probability law `ν` on `ℕ` is a probability law exactly when `ν` is not
the point mass at zero, or when all the weight is on the atom at zero. -/
theorem isProbabilityMeasure_cond_compl_zero_atomMixture_zero_iff :
    IsProbabilityMeasure ((ν[|{0}ᶜ]).atomMixture 0 w) ↔ ν {0} ≠ 1 ∨ w = 1 := by
  refine ⟨fun h => or_iff_not_imp_left.2 fun h0 => ?_, ?_⟩
  · have huniv := h.measure_univ
    rw [cond_compl_singleton_eq_zero_iff.2 (not_not.1 h0),
      atomMixture_apply _ _ _ MeasurableSet.univ] at huniv
    simpa using huniv
  · rintro (h0 | rfl)
    · have := isProbabilityMeasure_cond_compl_singleton h0
      infer_instance
    · rw [atomMixture_one]
      infer_instance

/-- Away from zero, the hurdle law has the masses of `ν` rescaled by
`(1 - w) / (1 - ν.real {0})`. -/
theorem cond_compl_zero_atomMixture_zero_real_singleton {k : ℕ} (hk : k ≠ 0) :
    ((ν[|{0}ᶜ]).atomMixture 0 w).real {k} = (1 - (w : ℝ)) * ν.real {k} / (1 - ν.real {0}) := by
  rw [atomMixture_real_singleton_of_ne _ hk.symm, cond_compl_singleton_real_singleton hk,
    mul_div_assoc]

/-- The cumulative masses of the hurdle law are `w + (1 - w) (ν.real (Iic k) - ν.real {0}) /
(1 - ν.real {0})`. -/
theorem cond_compl_zero_atomMixture_zero_real_Iic (k : ℕ) :
    ((ν[|{0}ᶜ]).atomMixture 0 w).real (Iic k) =
      (w : ℝ) + (1 - (w : ℝ)) * (ν.real (Iic k) - ν.real {0}) / (1 - ν.real {0}) := by
  rw [atomMixture_zero_real_Iic, cond_compl_zero_real_Iic, mul_div_assoc]

/-! ### The real cast -/

/-- The exact exponential-integrability domain of the real cast of the hurdle law: all of `ℝ` for
the point mass at `w = 1`, and otherwise the domain of the real cast of `ν`. -/
theorem integrableExpSet_id_map_natCast_cond_compl_zero_atomMixture_zero :
    integrableExpSet id (((ν[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) =
      if w = 1 then univ else integrableExpSet id (ν.map (Nat.cast : ℕ → ℝ)) := by
  rw [map_natCast_atomMixture_zero, integrableExpSet_id_atomMixture,
    integrableExpSet_id_map_natCast_cond_compl_zero]

/-- Every nonzero natural moment of the real cast of the hurdle law is the corresponding moment of
`ν` rescaled by `(1 - w) / (1 - ν.real {0})`. -/
theorem integral_pow_map_natCast_cond_compl_zero_atomMixture_zero {n : ℕ} (hn : n ≠ 0)
    (hν : Integrable (fun x : ℝ => x ^ n) (ν.map (Nat.cast : ℕ → ℝ))) :
    ∫ x, x ^ n ∂((ν[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ) =
      (1 - (w : ℝ)) * (∫ x, x ^ n ∂ν.map (Nat.cast : ℕ → ℝ)) / (1 - ν.real {0}) := by
  rw [map_natCast_atomMixture_zero,
    integral_atomMixture _ _ _ _ (integrable_map_natCast_cond_compl_zero_iff ν |>.2 hν),
    integral_pow_map_natCast_cond_compl_zero ν hn, smul_eq_mul, smul_eq_mul, zero_pow hn,
    mul_zero, zero_add, mul_div_assoc]

/-- The mean of the real cast of the hurdle law is the mean of `ν` rescaled by
`(1 - w) / (1 - ν.real {0})`. -/
theorem integral_id_map_natCast_cond_compl_zero_atomMixture_zero
    (hν : Integrable id (ν.map (Nat.cast : ℕ → ℝ))) :
    ∫ x, x ∂((ν[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ) =
      (1 - (w : ℝ)) * (∫ x, x ∂ν.map (Nat.cast : ℕ → ℝ)) / (1 - ν.real {0}) := by
  rw [map_natCast_atomMixture_zero,
    integral_id_atomMixture _ _ _ (integrable_map_natCast_cond_compl_zero_iff ν |>.2 hν),
    integral_id_map_natCast_cond_compl_zero, mul_zero, zero_add, mul_div_assoc]

/-- The variance of the real cast of the hurdle law, in terms of the first two moments of `ν`. -/
theorem variance_id_map_natCast_cond_compl_zero_atomMixture_zero
    (hν : Integrable (fun x : ℝ => x ^ 2) (ν.map (Nat.cast : ℕ → ℝ))) :
    variance id (((ν[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) =
      (1 - (w : ℝ)) * (∫ x, x ^ 2 ∂ν.map (Nat.cast : ℕ → ℝ)) / (1 - ν.real {0}) -
        ((1 - (w : ℝ)) * (∫ x, x ∂ν.map (Nat.cast : ℕ → ℝ)) / (1 - ν.real {0})) ^ 2 := by
  by_cases h0 : ν {0} = 1
  · have hreal : ν.real {0} = 1 := by simp [measureReal_def, h0]
    rw [cond_compl_singleton_eq_zero_iff.2 h0, map_natCast_atomMixture_zero,
      Measure.map_zero, Measure.atomMixture_def, smul_zero, add_zero, hreal]
    rw [variance_eq_integral (by fun_prop)]
    simp
  have := isProbabilityMeasure_cond_compl_singleton h0
  have hmem : MemLp id 2 (ν.map (Nat.cast : ℕ → ℝ)) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hν
  have hmem' : MemLp id 2 (((ν[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) := by
    refine (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 ?_
    rw [map_natCast_atomMixture_zero]
    exact Integrable.atomMixture (integrable_map_natCast_cond_compl_zero_iff ν |>.2 hν) _ _
  rw [variance_eq_sub hmem']
  simp only [Pi.pow_apply, id_eq]
  rw [integral_pow_map_natCast_cond_compl_zero_atomMixture_zero ν w two_ne_zero hν,
    integral_id_map_natCast_cond_compl_zero_atomMixture_zero ν w (hmem.integrable one_le_two)]

/-- At a nonnegative point, the cdf of the real cast of the hurdle law is `w` plus the cdf of the
real cast of `ν` with its atom at zero removed and the rest rescaled by `1 - w`. -/
theorem cdf_map_natCast_cond_compl_zero_atomMixture_zero (h : ν {0} ≠ 1) {x : ℝ} (hx : 0 ≤ x) :
    cdf (((ν[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)) x =
      (w : ℝ) + (1 - (w : ℝ)) * (cdf (ν.map (Nat.cast : ℕ → ℝ)) x - ν.real {0}) /
        (1 - ν.real {0}) := by
  have := isProbabilityMeasure_cond_compl_singleton h
  rw [cdf_map_natCast _ hx, cdf_map_natCast _ hx, cond_compl_zero_atomMixture_zero_real_Iic]

/-- A natural number is the quantile of the real cast of the hurdle law at an interior level
exactly when it is the least index whose hurdle cumulative mass reaches the level. -/
theorem quantile_map_natCast_cond_compl_zero_atomMixture_zero_eq_iff (h : ν {0} ≠ 1) {u : ℝ}
    (hu : u ∈ Ioo 0 1) (k : ℕ) :
    (((ν[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {j : ℕ | u ≤ (w : ℝ) + (1 - (w : ℝ)) * (ν.real (Iic j) - ν.real {0}) /
        (1 - ν.real {0})} k := by
  have := isProbabilityMeasure_cond_compl_singleton h
  simp_rw [quantile_map_natCast_eq_iff _ hu, cond_compl_zero_atomMixture_zero_real_Iic]

/-- At an interior level, the quantile of the real cast of the hurdle law is zero exactly up to
the level `w`. -/
@[simp]
theorem quantile_map_natCast_cond_compl_zero_atomMixture_zero_eq_zero_iff (h : ν {0} ≠ 1)
    {u : ℝ} (hu : u ∈ Ioo 0 1) :
    (((ν[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u = 0 ↔ u ≤ w := by
  have := isProbabilityMeasure_cond_compl_singleton h
  rw [quantile_map_natCast_atomMixture_zero_eq_zero_iff _ _ hu]
  simp [measureReal_def]

/-- The quantile of the real cast of the hurdle law at an interior level `u` is zero up to `w`,
and above `w` it is the quantile of the real cast of `ν` at the rescaled level
`ν.real {0} + (u - w) / (1 - w) * (1 - ν.real {0})`. -/
theorem quantile_map_natCast_cond_compl_zero_atomMixture_zero (h : ν {0} ≠ 1) {u : ℝ}
    (hu : u ∈ Ioo 0 1) :
    (((ν[|{0}ᶜ]).atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u =
      if u ≤ w then 0
      else (ν.map (Nat.cast : ℕ → ℝ)).quantile
        (ν.real {0} + (u - (w : ℝ)) / (1 - (w : ℝ)) * (1 - ν.real {0})) := by
  have := isProbabilityMeasure_cond_compl_singleton h
  have hzero : (ν[|{0}ᶜ]).real {0} = 0 := by simp [measureReal_def]
  rw [quantile_map_natCast_atomMixture_zero _ _ ⟨hu.1, hu.2.le⟩, hzero, mul_zero, add_zero]
  split_ifs with hle
  · rfl
  have hden : 0 < 1 - (w : ℝ) := by linarith [lt_of_not_ge hle, hu.2]
  exact quantile_map_natCast_cond_compl_zero ν h ⟨div_pos (by linarith [lt_of_not_ge hle]) hden,
    (div_lt_one hden).2 (by linarith [hu.2])⟩

end MeasureTheory.Measure
