/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.AtomMixture
public import TauCeti.Probability.Quantile.Discrete

/-!
# Zero inflation of laws on the natural numbers

The zero-inflated version of a probability law `ν` on `ℕ` with inflation weight `w ∈ [0, 1]` is
the atom mixture `ν.atomMixture 0 w = w δ₀ + (1 - w) ν`: with probability `w` the count is a
structural zero, and otherwise it is drawn from `ν`. Its masses are `w + (1 - w) ν {0}` at zero
and `(1 - w) ν {k}` for `k ≠ 0`; these are instances of
`MeasureTheory.Measure.atomMixture_real_singleton` and
`MeasureTheory.Measure.atomMixture_real_singleton_of_ne`.

Casting to the reals commutes with adding the atom, so the mean, variance, exponential-integrability
domain and cdf of the real cast are those of `MeasureTheory.Measure.atomMixture` from
`TauCeti.Probability.Distributions.AtomMixture`. This file adds the formulas that use the order of
`ℕ`:

* the cumulative masses `w + (1 - w) ν (Iic k)`;
* the quantile of the real cast as the least natural number whose cumulative mass reaches the
  level, which is zero exactly up to the mass `w + (1 - w) ν {0}` at zero;
* the quantile above that mass as the quantile of `ν` at the rescaled level `(u - w) / (1 - w)`.

At `w = 1` the zero-inflated law is the point mass at zero, and the formulas cover this boundary.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, chapter 8.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped unitInterval

namespace MeasureTheory.Measure

variable (ν : Measure ℕ) (w : unitInterval)

/-- Casting a zero-inflated law to the reals adds the same atom at zero to the real cast. -/
theorem map_natCast_atomMixture_zero :
    (ν.atomMixture 0 w).map (Nat.cast : ℕ → ℝ) = (ν.map (Nat.cast : ℕ → ℝ)).atomMixture 0 w := by
  rw [map_atomMixture _ _ _ (by fun_prop), Nat.cast_zero]

/-- The cumulative masses of a zero-inflated law are `w + (1 - w) ν (Iic k)`. -/
theorem atomMixture_zero_real_Iic [IsFiniteMeasure ν] (k : ℕ) :
    (ν.atomMixture 0 w).real (Iic k) = (w : ℝ) + (1 - (w : ℝ)) * ν.real (Iic k) := by
  simp [atomMixture_real_apply _ _ _ measurableSet_Iic]

variable [IsProbabilityMeasure ν]

/-- A natural number is the quantile of the real cast of a zero-inflated law at an interior level
exactly when it is the least index whose zero-inflated cumulative mass reaches the level. -/
theorem quantile_map_natCast_atomMixture_zero_eq_iff {u : ℝ} (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((ν.atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {j : ℕ | u ≤ (w : ℝ) + (1 - (w : ℝ)) * ν.real (Iic j)} k := by
  simp_rw [quantile_map_natCast_eq_iff _ hu, atomMixture_zero_real_Iic]

/-- At an interior level, the quantile of the real cast of a zero-inflated law is zero exactly up
to the mass `w + (1 - w) ν {0}` at zero. -/
theorem quantile_map_natCast_atomMixture_zero_eq_zero_iff {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((ν.atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u = 0 ↔
      u ≤ (w : ℝ) + (1 - (w : ℝ)) * ν.real {0} := by
  have hIic : (Iic 0 : Set ℕ) = {0} := Iic_bot
  simpa [IsLeast, lowerBounds, hIic] using quantile_map_natCast_atomMixture_zero_eq_iff ν w hu 0

/-- The quantile of the real cast of a zero-inflated law: it is zero through the mass at zero,
and above it is the quantile of the real cast of `ν` at the rescaled level `(u - w) / (1 - w)`. -/
theorem quantile_map_natCast_atomMixture_zero {u : ℝ} (hu : u ∈ Ioc 0 1) :
    ((ν.atomMixture 0 w).map (Nat.cast : ℕ → ℝ)).quantile u =
      if u ≤ (w : ℝ) + (1 - (w : ℝ)) * ν.real {0} then 0
      else (ν.map (Nat.cast : ℕ → ℝ)).quantile ((u - (w : ℝ)) / (1 - (w : ℝ))) := by
  have hIio : (ν.map (Nat.cast : ℕ → ℝ)) (Iio 0) = 0 := by
    rw [map_apply (by fun_prop) measurableSet_Iio]
    simp
  have hzero : (ν.map (Nat.cast : ℕ → ℝ)).real {0} = ν.real {0} := by
    rw [map_measureReal_apply (by fun_prop) (measurableSet_singleton 0)]
    congr 1
    ext k
    simp
  rw [map_natCast_atomMixture_zero, quantile_atomMixture hIio w hu, hzero]

end MeasureTheory.Measure
