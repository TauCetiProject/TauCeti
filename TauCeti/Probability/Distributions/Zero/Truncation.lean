/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Variance
public import TauCeti.Probability.Cdf
public import TauCeti.Probability.ConditionalProbability
public import TauCeti.Probability.Distributions.Truncation

/-!
# Zero truncation of laws on the natural numbers

The zero-truncated version of a probability law `ν` on `ℕ` is the conditional law `ν[|{0}ᶜ]`:
the atom at zero is removed and the remaining masses are rescaled by `1 / (1 - ν {0})`. This is
the law of a count observed only when it is positive, and it is the positive part of a hurdle
model.

Write `p₀ = ν.real {0}`. The singleton masses `ν.real {k} / (1 - p₀)` for `k ≠ 0`, integrability,
and integrals against the truncated law are instances of the general results for conditioning
away from one point, such as `ProbabilityTheory.cond_compl_singleton_real_singleton` and
`ProbabilityTheory.integral_cond_compl_singleton`. This file adds the formulas that use the order
of `ℕ` and the real cast:

* the cumulative masses `(ν.real (Iic k) - p₀) / (1 - p₀)`;
* the natural moments `E[X ^ n] / (1 - p₀)` for `n ≠ 0` of the real cast, and its variance;
* the exponential-integrability domain of the real cast, which truncation leaves unchanged;
* the cdf of the real cast, and its quantile at level `u`, which is the quantile of `ν` at the
  rescaled level `p₀ + u * (1 - p₀)`.

When `ν` is the point mass at zero, truncation removes all mass and the truncated law is zero, as
`ProbabilityTheory.cond_compl_singleton_eq_zero_iff` records. The cumulative-mass, moment and
variance formulas hold in that boundary case as well, with the convention `1 / 0 = 0`.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, sections 4.10.1 and 5.11.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace MeasureTheory.Measure

variable (ν : Measure ℕ)

/-- Casting a zero-truncated law to the reals gives the real cast conditioned on the positive
half-line. -/
theorem map_natCast_cond_compl_zero :
    (ν[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ) = (ν.map (Nat.cast : ℕ → ℝ))[|Ioi 0] := by
  have hpre : (Nat.cast : ℕ → ℝ) ⁻¹' Ioi 0 = {0}ᶜ := by
    ext k
    simp [Nat.pos_iff_ne_zero]
  rw [← hpre]
  exact map_cond_preimage (by fun_prop) one_ne_zero ENNReal.one_ne_top
    (fun A hA => by rw [map_apply (by fun_prop) hA, one_mul]) measurableSet_Ioi

variable [IsProbabilityMeasure ν]

/-- The cumulative masses of a zero-truncated law are the cumulative masses of `ν` beyond zero,
rescaled by `1 / (1 - ν.real {0})`. -/
theorem cond_compl_zero_real_Iic (k : ℕ) :
    (ν[|{0}ᶜ]).real (Iic k) = (ν.real (Iic k) - ν.real {0}) / (1 - ν.real {0}) := by
  rw [cond_compl_singleton_real, measureReal_sdiff (singleton_subset_iff.2 (Nat.zero_le k))
    (measurableSet_singleton 0)]

/-! ### The real cast -/

/-- The exponential-integrability domain of the real cast is unchanged by zero truncation. -/
@[simp]
theorem integrableExpSet_id_map_natCast_cond_compl_zero :
    integrableExpSet id ((ν[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)) =
      integrableExpSet id (ν.map (Nat.cast : ℕ → ℝ)) := by
  ext t
  simp only [integrableExpSet, mem_ofPred_eq, id_eq,
    (MeasurableEmbedding.natCast (α := ℝ)).integrable_map_iff]
  exact integrable_cond_compl_singleton_iff

/-- Every nonzero natural moment of the real cast of a zero-truncated law is the corresponding
moment of the original law rescaled by `1 / (1 - ν.real {0})`. -/
theorem integral_pow_map_natCast_cond_compl_zero {n : ℕ} (hn : n ≠ 0) :
    ∫ x, x ^ n ∂(ν[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ) =
      (∫ x, x ^ n ∂ν.map (Nat.cast : ℕ → ℝ)) / (1 - ν.real {0}) := by
  rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop),
    integral_cond_compl_singleton_of_eq_zero (f := fun k : ℕ => (k : ℝ) ^ n) (by simp [hn]),
    smul_eq_mul, inv_mul_eq_div]

/-- The mean of the real cast of a zero-truncated law is the mean of the original law rescaled by
`1 / (1 - ν.real {0})`. -/
theorem integral_id_map_natCast_cond_compl_zero :
    ∫ x, x ∂(ν[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ) =
      (∫ x, x ∂ν.map (Nat.cast : ℕ → ℝ)) / (1 - ν.real {0}) := by
  simpa using integral_pow_map_natCast_cond_compl_zero ν one_ne_zero

/-- The variance of the real cast of a zero-truncated law, in terms of the first two moments of
the original law. -/
theorem variance_id_map_natCast_cond_compl_zero
    (hν : Integrable (fun x : ℝ => x ^ 2) (ν.map (Nat.cast : ℕ → ℝ))) :
    variance id ((ν[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)) =
      (∫ x, x ^ 2 ∂ν.map (Nat.cast : ℕ → ℝ)) / (1 - ν.real {0}) -
        ((∫ x, x ∂ν.map (Nat.cast : ℕ → ℝ)) / (1 - ν.real {0})) ^ 2 := by
  by_cases h0 : ν {0} = 1
  · have hreal : ν.real {0} = 1 := by simp [measureReal_def, h0]
    simp [cond_compl_singleton_eq_zero_iff.2 h0, hreal]
  have := isProbabilityMeasure_cond_compl_singleton h0
  have hsq : Integrable (fun x : ℝ => x ^ 2) ((ν[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)) := by
    rw [(MeasurableEmbedding.natCast (α := ℝ)).integrable_map_iff] at hν ⊢
    exact integrable_cond_compl_singleton_iff.2 hν
  have hmem : MemLp id 2 ((ν[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hsq
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_pow_map_natCast_cond_compl_zero ν two_ne_zero,
    integral_id_map_natCast_cond_compl_zero]

/-- At a nonnegative point, the cdf of the real cast of a zero-truncated law is the cdf of the
original law with the atom at zero removed and the rest rescaled. -/
theorem cdf_map_natCast_cond_compl_zero (h : ν {0} ≠ 1) {x : ℝ} (hx : 0 ≤ x) :
    cdf ((ν[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)) x =
      (cdf (ν.map (Nat.cast : ℕ → ℝ)) x - ν.real {0}) / (1 - ν.real {0}) := by
  have := isProbabilityMeasure_cond_compl_singleton h
  rw [cdf_map_natCast _ hx, cdf_map_natCast _ hx, cond_compl_zero_real_Iic]

/-- Below one, the cdf of the real cast of a zero-truncated law vanishes. -/
theorem cdf_map_natCast_cond_compl_zero_of_lt_one (h : ν {0} ≠ 1) {x : ℝ} (hx : x < 1) :
    cdf ((ν[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)) x = 0 := by
  have := isProbabilityMeasure_cond_compl_singleton h
  rcases lt_or_ge x 0 with hneg | hnonneg
  · exact cdf_map_natCast_of_neg _ hneg
  · rw [cdf_map_natCast _ hnonneg, Nat.floor_eq_zero.2 hx, cond_compl_zero_real_Iic,
      ← Nat.bot_eq_zero, Iic_bot, sub_self, zero_div]

/-- At an interior level `u`, the quantile of the real cast of a zero-truncated law is the
quantile of the original law at the rescaled level `ν.real {0} + u * (1 - ν.real {0})`. -/
theorem quantile_map_natCast_cond_compl_zero (h : ν {0} ≠ 1) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    ((ν[|{0}ᶜ]).map (Nat.cast : ℕ → ℝ)).quantile u =
      (ν.map (Nat.cast : ℕ → ℝ)).quantile (ν.real {0} + u * (1 - ν.real {0})) := by
  have hIic : (ν.map (Nat.cast : ℕ → ℝ)).real (Iic 0) = ν.real {0} := by
    rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext k
    simp
  have hlt : ν.real {0} < 1 :=
    lt_of_le_of_ne measureReal_le_one fun h' => h (by
      rwa [measureReal_def, ENNReal.toReal_eq_one_iff] at h')
  have hset : (univ : Set ℝ) \ Iic 0 = Ioi 0 := by
    rw [← compl_eq_univ_sdiff, compl_Iic]
  have hq := (ν.map (Nat.cast : ℕ → ℝ)).quantile_cond_sdiff (IsLowerSet.Iic 0) isLowerSet_univ
    measurableSet_Iic MeasurableSet.univ (by simpa [hIic] using hlt) hu
  rwa [hset, hIic, probReal_univ, ← map_natCast_cond_compl_zero] at hq

end MeasureTheory.Measure
