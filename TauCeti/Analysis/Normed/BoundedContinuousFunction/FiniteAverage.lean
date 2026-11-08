/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Averages of bounded continuous functions

Inserting one point changes a finite average by at most twice the uniform bound divided
by the new number of points.
-/

public section

open scoped BoundedContinuousFunction

namespace BoundedContinuousFunction

/-- Inserting a value changes a bounded average by at most twice the bound divided by
the new population size. -/
theorem abs_average_insert_sub {α : Type*} [TopologicalSpace α]
    (m : ℕ) (a : α) (x : Fin (m + 1) → α) (f : α →ᵇ ℝ) :
    |(f a + ∑ i, f (x i)) / (m + 2 : ℝ) -
        (∑ i, f (x i)) / (m + 1 : ℝ)| ≤ 2 * ‖f‖ / (m + 2 : ℝ) := by
  have h1 : 0 < (m + 1 : ℝ) := by positivity
  have h2 : 0 < (m + 2 : ℝ) := by positivity
  have hf : |f a| ≤ ‖f‖ := by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm a
  have hsum : |∑ i, f (x i)| ≤ (m + 1 : ℝ) * ‖f‖ := by
    simpa [Real.norm_eq_abs] using
      (norm_sum_le_of_le Finset.univ (fun i _ ↦ f.norm_coe_le_norm (x i)))
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

end BoundedContinuousFunction
