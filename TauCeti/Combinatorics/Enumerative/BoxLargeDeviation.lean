/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Few lattice points of a box lie far below its centre

For positive integers `r i`, `i : ι`, the box `∏ i, {0, …, r i}` has `∏ i, (r i + 1)` points
`d`, and the normalized coordinate sum `∑ i, d i / r i` has mean `n / 2`, where `n = #ι`. This
file proves that the points with `∑ i, d i / r i ≤ (n / 2) (1 - ε)` make up at most the fraction
`exp (-ε² n / 2)` of the box.

This is the counting estimate behind the auxiliary polynomial in Roth's theorem. There the
unknowns are the coefficients of a polynomial in `n` variables of partial degrees at most `r i`,
and vanishing to weighted index `(n / 2) (1 - ε)` at a diagonal point imposes one linear
condition for each `d` in the small set counted here. Once `n` is large, the conditions are far
fewer than the unknowns, so Siegel's lemma gives a solution with small coefficients.

## Main results

* `TauCeti.card_piFinset_range`, `TauCeti.card_piFinset_range_le_two_pow`: the box has
  `∏ i, (r i + 1) ≤ 2 ^ (∑ i, r i)` points.
* `TauCeti.sum_range_exp_mul_div_sub_half_le`: Hoeffding's lemma on the grid
  `{0, 1 / r, …, 1}`, `∑ k ≤ r, exp (t (k / r - 1 / 2)) ≤ (r + 1) exp (t² / 8)`.
* `TauCeti.card_filter_sum_div_le_mul_one_sub_le`: the count
  `#{d : ∑ i, d i / r i ≤ (n / 2) (1 - ε)} ≤ (∏ i, (r i + 1)) exp (-ε² n / 2)` for `ε ≥ 0`.

## Implementation notes

The proof is the Chernoff bound written as a count. Each point of the small set contributes at
least `1` to `exp (2 ε ((n / 2) (1 - ε) - ∑ i, d i / r i))`, and the sum of this exponential over
the whole box factors over the coordinates. In each coordinate, pairing `k` with `r - k` turns
the exponential sum into a sum of hyperbolic cosines, which `Real.cosh_le_exp_half_sq` bounds.

Mathlib's measure-theoretic Hoeffding inequality `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun`
gives the same estimate, but applying it here would first require identifying the normalized
counting measure on the box with a product of uniform measures on the coordinates, which is
longer than the direct argument.

Pottmeyer states the bound with `exp (-ε² n / 4)` and assumes `ε < 1`. The direct argument gives
the exponent `ε² n / 2` and needs only `0 ≤ ε`; for negative `ε` the estimate fails, since the
whole box can satisfy the condition.

## References

* L. Pottmeyer, *Diophantine Approximation* (2022), Lemma 2.6.4.
* W. Hoeffding, *Probability inequalities for sums of bounded random variables*, J. Amer.
  Statist. Assoc. 58 (1963), 13–30.
-/

public section

open Finset Real

namespace TauCeti

/-- The box `∏ i, {0, …, r i}` has `∏ i, (r i + 1)` points. -/
theorem card_piFinset_range {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ℕ) :
    #(Fintype.piFinset fun i ↦ range (r i + 1)) = ∏ i, (r i + 1) := by
  simp [Fintype.card_piFinset]

/-- The box `∏ i, {0, …, r i}` has at most `2 ^ (∑ i, r i)` points. -/
theorem card_piFinset_range_le_two_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ℕ) :
    #(Fintype.piFinset fun i ↦ range (r i + 1)) ≤ 2 ^ ∑ i, r i := by
  rw [card_piFinset_range, ← prod_pow_eq_pow_sum]
  gcongr with i
  exact Nat.lt_two_pow_self

/-- **Hoeffding's lemma on the grid `{0, 1 / r, …, 1}`.** For `r ≠ 0` and every real `t`, the
exponential moment of the uniformly distributed centred point `k / r - 1 / 2` satisfies
`∑ k ∈ range (r + 1), exp (t (k / r - 1 / 2)) ≤ (r + 1) exp (t² / 8)`. -/
theorem sum_range_exp_mul_div_sub_half_le {r : ℕ} (hr : r ≠ 0) (t : ℝ) :
    ∑ k ∈ range (r + 1), exp (t * ((k : ℝ) / r - 1 / 2)) ≤ (r + 1) * exp (t ^ 2 / 8) := by
  set f : ℕ → ℝ := fun k ↦ t * ((k : ℝ) / r - 1 / 2) with hf
  -- The reflection `k ↦ r - k` of `range (r + 1)` negates `f`.
  have hrefl : ∑ k ∈ range (r + 1), exp (-f k) = ∑ k ∈ range (r + 1), exp (f k) := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun k hk ↦ ?_
    have hk : k ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [add_tsub_cancel_right, hf]
    push_cast [hk]
    congr 1
    field_simp
    ring
  have hsq : ∀ k ∈ range (r + 1), f k ^ 2 / 2 ≤ t ^ 2 / 8 := by
    intro k hk
    have hk : (k : ℝ) ≤ r := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
    have h0 : 0 ≤ (k : ℝ) / r := by positivity
    have h1 : (k : ℝ) / r ≤ 1 := div_le_one_of_le₀ hk (Nat.cast_nonneg r)
    have hc : ((k : ℝ) / r - 1 / 2) ^ 2 ≤ 1 / 4 := by nlinarith
    have := mul_le_mul_of_nonneg_left hc (sq_nonneg t)
    rw [hf]
    linarith [mul_pow t ((k : ℝ) / r - 1 / 2) 2]
  calc ∑ k ∈ range (r + 1), exp (f k)
      = ∑ k ∈ range (r + 1), cosh (f k) := by
        simp_rw [cosh_eq]
        rw [← Finset.sum_div, sum_add_distrib, hrefl]
        ring
    _ ≤ ∑ _k ∈ range (r + 1), exp (t ^ 2 / 8) :=
        sum_le_sum fun k hk ↦ (cosh_le_exp_half_sq _).trans (exp_le_exp.mpr (hsq k hk))
    _ = (r + 1) * exp (t ^ 2 / 8) := by simp

/-- **Few points of a box lie far below its centre** (Pottmeyer, Lemma 2.6.4). Let `r i ≠ 0` for
`i : ι` and `n = #ι`. Among the `∏ i, (r i + 1)` points `d` of the box `∏ i, {0, …, r i}`, at
most `(∏ i, (r i + 1)) exp (-ε² n / 2)` satisfy `∑ i, d i / r i ≤ (n / 2) (1 - ε)`, for every
`ε ≥ 0`. -/
theorem card_filter_sum_div_le_mul_one_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ι → ℕ} (hr : ∀ i, r i ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) :
    (#{d ∈ Fintype.piFinset fun i ↦ range (r i + 1) |
        ∑ i, (d i : ℝ) / r i ≤ Fintype.card ι / 2 * (1 - ε)} : ℝ) ≤
      (∏ i, ((r i : ℝ) + 1)) * exp (-(ε ^ 2 * Fintype.card ι / 2)) := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  set E : (ι → ℕ) → ℝ := fun d ↦ exp (2 * ε * (n / 2 * (1 - ε) - ∑ i, (d i : ℝ) / r i))
    with hE
  -- The Chernoff weight `E d` factors over the coordinates.
  have hfactor : ∀ d : ι → ℕ,
      E d = exp (-(ε ^ 2 * n)) * ∏ i, exp (-2 * ε * ((d i : ℝ) / r i - 1 / 2)) := by
    intro d
    rw [hE, ← exp_sum, ← exp_add, ← mul_sum, sum_sub_distrib]
    simp only [sum_const, card_univ, nsmul_eq_mul, ← hn]
    congr 1
    ring
  calc (#{d ∈ Fintype.piFinset fun i ↦ range (r i + 1) |
          ∑ i, (d i : ℝ) / r i ≤ n / 2 * (1 - ε)} : ℝ)
      = ∑ d ∈ Fintype.piFinset fun i ↦ range (r i + 1) with
          ∑ i, (d i : ℝ) / r i ≤ n / 2 * (1 - ε), (1 : ℝ) := by simp
    _ ≤ ∑ d ∈ Fintype.piFinset fun i ↦ range (r i + 1) with
          ∑ i, (d i : ℝ) / r i ≤ n / 2 * (1 - ε), E d :=
        sum_le_sum fun d hd ↦ one_le_exp (mul_nonneg (by positivity)
          (sub_nonneg.mpr (mem_filter.mp hd).2))
    _ ≤ ∑ d ∈ Fintype.piFinset fun i ↦ range (r i + 1), E d :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ (exp_pos _).le
    _ = exp (-(ε ^ 2 * n)) *
          ∏ i, ∑ k ∈ range (r i + 1), exp (-2 * ε * ((k : ℝ) / r i - 1 / 2)) := by
        simp_rw [hfactor, ← mul_sum, prod_univ_sum]
    _ ≤ exp (-(ε ^ 2 * n)) * ∏ i, (((r i : ℝ) + 1) * exp ((-2 * ε) ^ 2 / 8)) := by
        gcongr with i
        exact sum_range_exp_mul_div_sub_half_le (hr i) _
    _ = (∏ i, ((r i : ℝ) + 1)) * exp (-(ε ^ 2 * n / 2)) := by
        rw [prod_mul_distrib, prod_const, card_univ, ← exp_nat_mul, ← hn, mul_left_comm,
          ← exp_add]
        congr 2
        ring

end TauCeti
