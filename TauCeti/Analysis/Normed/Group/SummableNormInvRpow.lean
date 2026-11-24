/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Counting points of a family with summable inverse powers

Let `a : ι → E` be a family in a normed group and `0 ≤ τ` with `∑' i, ‖a i‖⁻¹ ^ τ < ∞`, as for
the zeros of an entire function of finite order below `τ`. Then only finitely many nonzero
`a i` lie in each ball `‖a i‖ ≤ R`, and any finite set of them numbers at most
`R ^ τ * ∑' i, ‖a i‖⁻¹ ^ τ`.

## Main results

* `Summable.finite_setOf_ne_zero_norm_le`: `{i | a i ≠ 0 ∧ ‖a i‖ ≤ R}` is finite.
* `Summable.card_le_rpow_mul_tsum`: for `0 ≤ R`, a finite set of indices with `a i ≠ 0` and
  `‖a i‖ ≤ R` has at most `R ^ τ * ∑' i, ‖a i‖⁻¹ ^ τ` elements.
-/

public section

open Filter

namespace Summable

variable {ι E : Type*} [NormedAddCommGroup E] {τ : ℝ} {a : ι → E}

/-- If `∑' i, ‖a i‖⁻¹ ^ τ` converges with `0 ≤ τ`, only finitely many nonzero `a i` have norm at
most `R`. -/
theorem finite_setOf_ne_zero_norm_le (ha : Summable fun i ↦ ‖a i‖⁻¹ ^ τ) (hτ : 0 ≤ τ) (R : ℝ) :
    {i | a i ≠ 0 ∧ ‖a i‖ ≤ R}.Finite := by
  rcases le_or_gt R 0 with hR | hR
  · exact Set.finite_empty.subset fun i hi ↦ (norm_pos_iff.mpr hi.1).not_ge (hi.2.trans hR)
  have hε : 0 < R⁻¹ ^ τ := Real.rpow_pos_of_pos (inv_pos.mpr hR) τ
  refine (eventually_cofinite.mp (ha.tendsto_cofinite_zero.eventually (gt_mem_nhds hε))).subset
    fun i hi ↦ not_lt.mpr ?_
  exact Real.rpow_le_rpow (inv_nonneg.mpr hR.le) (inv_anti₀ (norm_pos_iff.mpr hi.1) hi.2) hτ

/-- If `∑' i, ‖a i‖⁻¹ ^ τ` converges with `0 ≤ τ`, a finite set of indices with `a i ≠ 0` and
`‖a i‖ ≤ R`, `0 ≤ R`, has at most `R ^ τ * ∑' i, ‖a i‖⁻¹ ^ τ` elements. -/
theorem card_le_rpow_mul_tsum (ha : Summable fun i ↦ ‖a i‖⁻¹ ^ τ) (hτ : 0 ≤ τ) {R : ℝ}
    (hR : 0 ≤ R) {s : Finset ι} (hs : ∀ i ∈ s, a i ≠ 0 ∧ ‖a i‖ ≤ R) :
    (s.card : ℝ) ≤ R ^ τ * ∑' i, ‖a i‖⁻¹ ^ τ := by
  calc
    (s.card : ℝ) = ∑ i ∈ s, 1 := by simp
    _ ≤ ∑ i ∈ s, R ^ τ * ‖a i‖⁻¹ ^ τ := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      have hpos : 0 < ‖a i‖ := norm_pos_iff.mpr (hs i hi).1
      rw [← Real.mul_rpow hR (by positivity), ← div_eq_mul_inv]
      exact Real.one_le_rpow ((one_le_div hpos).mpr (hs i hi).2) hτ
    _ ≤ R ^ τ * ∑' i, ‖a i‖⁻¹ ^ τ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (ha.sum_le_tsum s fun i _ ↦ by positivity)
        (Real.rpow_nonneg hR τ)

end Summable
