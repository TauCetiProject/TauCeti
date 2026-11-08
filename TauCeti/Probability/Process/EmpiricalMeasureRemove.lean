/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.EmpiricalMeasure

/-!
# Removing one point from an empirical measure

Deleting one point from a finite population of size `n + 2` changes the average of a
bounded continuous test function by at most `2 * ‖f‖ / (n + 2)`. The deleted point is
arbitrary, and repeated values are counted with multiplicity. In particular, the bound
applies to the removal of one eigenvalue from an empirical spectral measure.
-/

public section

open MeasureTheory
open scoped BoundedContinuousFunction

namespace TauCeti.Probability

/-- Inserting one value changes a bounded average by at most twice the bound, divided by
the new population size. -/
private theorem abs_average_insert_sub {α : Type*} [TopologicalSpace α]
    (m : ℕ) (a : α) (x : Fin (m + 1) → α) (f : α →ᵇ ℝ) :
    |(f a + ∑ i, f (x i)) / (m + 2 : ℝ) -
        (∑ i, f (x i)) / (m + 1 : ℝ)| ≤ 2 * ‖f‖ / (m + 2 : ℝ) := by
  have h1 : 0 < (m + 1 : ℝ) := by positivity
  have h2 : 0 < (m + 2 : ℝ) := by positivity
  have hf : |f a| ≤ ‖f‖ := by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm a
  have hsum : |∑ i, f (x i)| ≤ (m + 1 : ℝ) * ‖f‖ := by
    calc
      _ ≤ ∑ i, |f (x i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (m + 1), ‖f‖ := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [Real.norm_eq_abs] using f.norm_coe_le_norm (x i)
      _ = _ := by simp
  have havg : |(∑ i, f (x i)) / (m + 1 : ℝ)| ≤ ‖f‖ := by
    rw [abs_div, abs_of_pos h1, div_le_iff₀ h1]
    simpa [mul_comm] using hsum
  have heq : (f a + ∑ i, f (x i)) / (m + 2 : ℝ) -
      (∑ i, f (x i)) / (m + 1 : ℝ) =
        (f a - (∑ i, f (x i)) / (m + 1 : ℝ)) / (m + 2 : ℝ) := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos h2]
  apply div_le_div_of_nonneg_right _ h2.le
  have hsum' := add_le_add hf havg
  have htriangle := abs_sub_le (f a) 0 ((∑ i, f (x i)) / (m + 1 : ℝ))
  simp only [sub_zero, zero_sub, abs_neg] at htriangle
  linarith

/-- Removing any one value changes a bounded continuous test integral by at most
`2 * ‖f‖ / (n + 2)`. -/
theorem abs_integral_empiricalMeasureOfFintype_sub_succAbove_le
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    (n : ℕ) (x : Fin (n + 2) → α) (i : Fin (n + 2)) (f : α →ᵇ ℝ) :
    |(∫ y, f y ∂(empiricalMeasureOfFintype x : Measure α)) -
      (∫ y, f y ∂(empiricalMeasureOfFintype (x ∘ i.succAbove) : Measure α))| ≤
      2 * ‖f‖ / (n + 2 : ℝ) := by
  rw [integral_empiricalMeasureOfFintype f.continuous.stronglyMeasurable,
    integral_empiricalMeasureOfFintype f.continuous.stronglyMeasurable]
  simp only [Fintype.card_fin, smul_eq_mul, Function.comp_apply]
  rw [Fin.sum_univ_succAbove _ i]
  simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, div_eq_mul_inv, mul_comm,
    Function.comp_def] using
    abs_average_insert_sub n (x i) (x ∘ i.succAbove) f

end TauCeti.Probability
