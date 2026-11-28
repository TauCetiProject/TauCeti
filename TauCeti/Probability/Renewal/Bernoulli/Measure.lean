/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Bernoulli.Basic
import TauCeti.MeasureTheory.Constructions.BorelSpace.Order
import TauCeti.Probability.Distributions.Bernoulli.Basic

/-!
# Atomic renewal measure for two-point increments

For increments equal to `a > 0` with probability `q > 0` and zero otherwise, the renewal
measure assigns mass `1 / q` to every nonnegative multiple of `a`. The mass at zero includes
the artificial arrival as well as the cluster of genuine zero-time arrivals.

This is the measure form of the two-point renewal computation in Vincent Tassion,
*Applied Stochastic Processes*, §5.3, and uses `renewalMeasure_bernoulliMeasure_real_Iic`.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {a : ℝ≥0} {q : unitInterval}

/-- For a two-point increment law with positive success probability `q`, the renewal measure
is a sum of masses `1 / q` at the multiples `n * a` for `n : ℕ`. If `a = 0`, all the
terms are at the origin and their sum has infinite mass there. -/
theorem renewalMeasure_bernoulliMeasure (hq : 0 < (q : ℝ)) :
    (bernoulliMeasure a 0 q).renewalMeasure =
      (ENNReal.ofReal (q : ℝ))⁻¹ • Measure.sum (fun n : ℕ ↦ Measure.dirac ((n : ℝ≥0) * a)) := by
  classical
  rcases eq_zero_or_pos a with rfl | ha
  · simp only [bernoulliMeasure_self_eq_dirac, Measure.renewalMeasure_def, mul_zero]
    ext s hs
    simp only [smul_apply, smul_eq_mul, Measure.sum_apply _ hs, Measure.convolutionPower_dirac_zero]
    by_cases hz : (0 : ℝ≥0) ∈ s
    · simp [Measure.dirac_apply' _ hs, hz, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero,
        ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top]
    · simp [Measure.dirac_apply' _ hs, hz]
  have hfinite (t : ℝ≥0) : (bernoulliMeasure a 0 q).renewalMeasure (Iic t) ≠ ∞ :=
    (Measure.renewalMeasure_Iic_lt_top _ (bernoulliMeasure_singleton_zero_lt_one ha.ne' hq) t).ne
  refine Measure.ext_of_Iic' _ _ hfinite fun t ↦ ?_
  have hle (n : ℕ) : (n : ℝ≥0) * a ∈ Iic t ↔ n ≤ ⌊t / a⌋₊ := by
    rw [mem_Iic, ← le_div_iff₀ ha, Nat.le_floor_iff (by positivity)]
  have hsum : (∑' n : ℕ, Measure.dirac ((n : ℝ≥0) * a) (Iic t)) =
      (↑(⌊t / a⌋₊ + 1) : ℝ≥0∞) := by
    simp only [Measure.dirac_apply' _ measurableSet_Iic, indicator_apply, Pi.one_apply, hle]
    rw [tsum_eq_sum (s := Finset.Iic ⌊t / a⌋₊) (fun n hn ↦ ite_eq_right (by simpa using hn))]
    calc
      _ = ∑ _n ∈ Finset.Iic ⌊t / a⌋₊, (1 : ℝ≥0∞) :=
        Finset.sum_congr rfl fun n hn ↦ ite_eq_left (by simpa using hn)
      _ = _ := by simp [Nat.card_Iic]
  rw [smul_apply, smul_eq_mul, Measure.sum_apply _ measurableSet_Iic, hsum,
    ← ENNReal.ofReal_toReal (hfinite t), ← measureReal_def,
    renewalMeasure_bernoulliMeasure_real_Iic ha hq, ENNReal.ofReal_div_of_pos hq,
    ← Nat.cast_succ, ENNReal.ofReal_natCast, div_eq_mul_inv, mul_comm]

/-- Each lattice point, including the origin, has renewal mass `1 / q`. -/
@[simp]
theorem renewalMeasure_bernoulliMeasure_apply_singleton_natCast_mul
    (ha : 0 < a) (hq : 0 < (q : ℝ)) (n : ℕ) :
    (bernoulliMeasure a 0 q).renewalMeasure {(n : ℝ≥0) * a} = (ENNReal.ofReal (q : ℝ))⁻¹ := by
  rw [renewalMeasure_bernoulliMeasure hq, smul_apply,
    Measure.sum_apply _ (measurableSet_singleton _), tsum_eq_single n]
  · simp
  · intro m hmn
    have hne : (m : ℝ≥0) * a ≠ (n : ℝ≥0) * a := fun h ↦
      hmn (Nat.cast_injective (mul_right_cancel₀ ha.ne' h))
    simp [hne]

end TauCeti.Probability
