/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hypergeometric.Basic

/-!
# Complementing hypergeometric counts

If a sample of size `n` contains `X` marked objects, it contains `n - X` unmarked objects.
Thus complementing a hypergeometric count replaces the marked population size `K` by `N - K`.
This file proves the native natural-valued pushforward identity, its real-cast reflection,
and the corresponding random-variable laws. Natural subtraction agrees with real subtraction
because the count is at most the sample size almost surely.

The identities include empty and full samples and deterministic marked populations. They also
hold when `n > N`, when both totalized laws are zero; the marked count must satisfy `K ≤ N`.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- Complementing the count in a sample exchanges marked and unmarked population objects.
This includes the zero law when the sample size exceeds the population size. -/
@[simp]
theorem map_sub_hypergeometricMeasure {N K n : ℕ} (hK : K ≤ N) :
    (hypergeometricMeasure N K n).map (fun k ↦ n - k) =
      hypergeometricMeasure N (N - K) n := by
  by_cases hn : n ≤ N
  · rw [hypergeometricMeasure_eq_sum_dirac hK hn,
      hypergeometricMeasure_eq_sum_dirac (Nat.sub_le N K) hn,
      Measure.map_finset_sum Measurable.of_discrete.aemeasurable]
    simp_rw [Measure.map_smul _ Measurable.of_discrete.aemeasurable,
      Measure.map_dirac' Measurable.of_discrete]
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hkn : k ≤ n := Finset.mem_range_succ_iff.mp hk
    simp only [Nat.add_sub_cancel, Nat.sub_sub_self hkn,
      hypergeometricWeight_of_le (Nat.sub_le n k), hypergeometricWeight_of_le hkn,
      Nat.sub_sub_self hK, mul_comm]
  · rw [hypergeometricMeasure_eq_zero_of_invalid (by omega), Measure.map_zero,
      hypergeometricMeasure_eq_zero_of_invalid (by omega)]

/-- Reflection about half the sample size sends the real cast of a hypergeometric law to the
real cast of the complementary marked-population law. -/
@[simp]
theorem map_sub_map_cast_hypergeometricMeasure {N K n : ℕ} (hK : K ≤ N) :
    ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)).map
        (fun x ↦ (n : ℝ) - x) =
      (hypergeometricMeasure N (N - K) n).map (Nat.cast : ℕ → ℝ) := by
  by_cases hn : n ≤ N
  · rw [← map_sub_hypergeometricMeasure hK,
      Measure.map_map (by fun_prop) Measurable.of_discrete,
      Measure.map_map Measurable.of_discrete (by fun_prop)]
    apply Measure.map_congr
    apply ae_iff_of_countable.mpr
    intro k hk
    have hsupp := (hypergeometricWeight_ne_zero_iff N K n k).mp
      (by simpa only [hypergeometricMeasure_singleton hK hn] using hk)
    exact (Nat.cast_sub hsupp.2.1).symm
  · rw [hypergeometricMeasure_eq_zero_of_invalid (by omega), Measure.map_zero,
      Measure.map_zero, hypergeometricMeasure_eq_zero_of_invalid (by omega), Measure.map_zero]

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- Counting the unmarked objects in a hypergeometric sample replaces `K` by `N - K`.
Subtraction here is on the native natural-number carrier. -/
theorem hypergeometric_compl {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℕ} {N K n : ℕ} (hX : HasLaw X (hypergeometricMeasure N K n) P)
    (hK : K ≤ N) :
    HasLaw (fun ω ↦ n - X ω) (hypergeometricMeasure N (N - K) n) P := by
  exact (⟨Measurable.of_discrete.aemeasurable, map_sub_hypergeometricMeasure hK⟩ :
    HasLaw (fun k ↦ n - k) (hypergeometricMeasure N (N - K) n)
      (hypergeometricMeasure N K n)).comp hX

/-- A real-valued variable with the cast hypergeometric law is reflected by `x ↦ n - x`
to the cast law with complementary marked population. -/
theorem hypergeometric_compl_real {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {N K n : ℕ}
    (hX : HasLaw X ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)) P)
    (hK : K ≤ N) :
    HasLaw (fun ω ↦ (n : ℝ) - X ω)
      ((hypergeometricMeasure N (N - K) n).map (Nat.cast : ℕ → ℝ)) P := by
  exact (⟨by fun_prop, map_sub_map_cast_hypergeometricMeasure hK⟩ :
    HasLaw (fun x : ℝ ↦ (n : ℝ) - x)
      ((hypergeometricMeasure N (N - K) n).map (Nat.cast : ℕ → ℝ))
      ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ))).comp hX

end ProbabilityTheory.HasLaw
