/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.LocalPrimeSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Loss from partner weights in local prime sums

A local prime sum clips each term `y / p ^ e - w(p ^ e)` at zero, where the weight can
vary with the prime power. Its deficit from the uncut reciprocal sum is the local sum of
`min (y / p ^ e) (w(p ^ e))`. The reciprocal coefficient is the sum of `p ^ (-e)` over the
contributing exponents, with the same ramified half weight as in the capped sum. Summing
this identity over the places isolates the term to be bounded by sparsity of the large weights.

The normalization and place-summed identity follow `New.Data.mul_sum_weight_sub_localPrimeSumTotal`
in `New/Derivatives/Sharpness/NearPairs.lean` of lsernau/grh-lean at `72fead1`.
-/

public section

namespace TauCeti.OneSidedBound

open Filter

/-- Subtracting a local sum of positive parts from the uncut reciprocal contribution
leaves the local sum of the minima. All three terms use the same exponent set and
ramified half weight. -/
theorem mul_localPrimeSum_inv_sub_eq_localPrimeSum_min {d p : ℕ} [Fact d.Prime]
    (y : ℝ) (w : ℕ → ℝ) (hw : ∀ᶠ e : ℕ in atTop, 0 ≤ w (p ^ e)) :
    y * localPrimeSum d p (fun n ↦ (n : ℝ)⁻¹) -
        localPrimeSum d p (fun n ↦ max (y / n - w n) 0) =
      localPrimeSum d p (fun n ↦ min (y / n) (w n)) := by
  rcases le_or_gt p 1 with hp | hp
  · obtain rfl | rfl : p = 0 ∨ p = 1 := by omega
    · simp [localPrimeSum_def, (Fact.out : d.Prime).ne_zero.symm]
    · simp
  simp only [localPrimeSum_def]
  let A (e : ℕ) : Prop := 0 < e ∧ (p = d ∨ legendreSym d p = -1 ∧ Odd e)
  let u (e : ℕ) : ℝ := if A e then y / (↑(p ^ e) : ℝ) else 0
  let v (e : ℕ) : ℝ := if A e then min (y / (↑(p ^ e) : ℝ)) (w (p ^ e)) else 0
  have hg : Summable (fun e : ℕ ↦ |y| * ((p : ℝ)⁻¹) ^ e) :=
    (summable_geometric_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp))).mul_left _
  have hspec (e : ℕ) : ‖y / (↑(p ^ e) : ℝ)‖ = |y| * ((p : ℝ)⁻¹) ^ e := by
    have hpe : 0 ≤ (↑(p ^ e) : ℝ) := Nat.cast_nonneg _
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hpe, div_eq_mul_inv, Nat.cast_pow, inv_pow]
  have hu : Summable u := hg.of_norm_bounded fun e ↦ by
    by_cases he : A e
    · simp only [u, ite_eq_left he, hspec, le_refl]
    · simp [u, he, mul_nonneg]
  have hv : Summable v := hg.of_norm_bounded_eventually_nat <| by
    filter_upwards [hw] with e hwe
    by_cases he : A e
    · simp only [v, ite_eq_left he, ← hspec]
      obtain h | h := le_total (y / (↑(p ^ e) : ℝ)) (w (p ^ e))
      · rw [min_eq_left h]
      · rw [min_eq_right h, Real.norm_eq_abs, abs_of_nonneg hwe]
        exact h.trans (le_abs_self _)
    · simp [v, he, mul_nonneg]
  have hlinear : (fun e : ℕ ↦ y * (if A e then (↑(p ^ e) : ℝ)⁻¹ else 0)) = u := by
    funext e
    by_cases he : A e <;> simp [u, he, div_eq_mul_inv]
  have hramp : (fun e : ℕ ↦ if A e then max (y / (↑(p ^ e) : ℝ) - w (p ^ e)) 0 else 0) =
      fun e ↦ u e - v e := by
    funext e
    by_cases he : A e
    · simp only [u, v, ite_eq_left he]
      obtain h | h := le_total (y / (↑(p ^ e) : ℝ)) (w (p ^ e))
      · rw [max_eq_right (sub_nonpos.mpr h), min_eq_left h, sub_self]
      · rw [max_eq_left (sub_nonneg.mpr h), min_eq_right h]
    · simp [u, v, he]
  -- Move the scalar inside the reciprocal series, then subtract the ramp termwise.
  rw [mul_left_comm y, ← mul_sub, ← tsum_mul_left, hlinear, hramp, hu.tsum_sub hv, sub_sub_cancel]

/-- The deficit of the total local prime sum from the reciprocal coefficient times
the sum of the weights is the sum of the partner losses. -/
theorem mul_sum_weight_sub_localPrimeSum_total {ι : Type*} {d p : ℕ} [Fact d.Prime]
    (s : Finset ι) (κ : ι → ℝ) (w : ℕ → ι → ℝ)
    (hw : ∀ i ∈ s, ∀ᶠ e : ℕ in atTop, 0 ≤ w (p ^ e) i) :
    localPrimeSum d p (fun n ↦ (n : ℝ)⁻¹) * (∑ i ∈ s, κ i) -
        (∑ i ∈ s, localPrimeSum d p (fun n ↦ max (κ i / n - w n i) 0)) =
      ∑ i ∈ s, localPrimeSum d p (fun n ↦ min (κ i / n) (w n i)) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [mul_comm]
  exact mul_localPrimeSum_inv_sub_eq_localPrimeSum_min (κ i) (fun n ↦ w n i) (hw i hi)

end TauCeti.OneSidedBound
