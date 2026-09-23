/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Comparing weighted sums through their partial sums

If every initial partial sum of `f` is at most the corresponding partial sum of `g`, then the
same comparison holds after weighting both sequences by a nonnegative, antitone weight `w`:
`∑_{i < N} w i * f i ≤ ∑_{i < N} w i * g i`. This is Abel's inequality in its comparison form.
Summation by parts (`Finset.sum_range_by_parts`) writes the difference of the two weighted sums
as the last weight times the last partial-sum difference plus the successive decrements of `w`
times the earlier partial-sum differences, and every one of these products is nonnegative.

No sign condition on `f` or `g` is needed. The typical use takes `g` constant: a bound
`∑_{i < k} f i ≤ C k` on all partial sums then gives `∑ w i * f i ≤ C ∑ w i` for every
nonnegative antitone weight.

## Main results

* `TauCeti.sum_range_mul_le_sum_range_mul`: the weighted comparison.
-/

public section

namespace TauCeti

open Finset

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]

/-- **Abel's inequality, comparison form.** If the partial sums of `f` are dominated by those of
`g` up to `N`, and `w` is nonnegative and antitone on the first `N` indices, then
`∑_{i < N} w i * f i ≤ ∑_{i < N} w i * g i`. -/
theorem sum_range_mul_le_sum_range_mul {f g w : ℕ → R} {N : ℕ}
    (hfg : ∀ k ≤ N, ∑ i ∈ range k, f i ≤ ∑ i ∈ range k, g i)
    (hw : ∀ i, i + 1 < N → w (i + 1) ≤ w i) (hw0 : 0 ≤ w (N - 1)) :
    ∑ i ∈ range N, w i * f i ≤ ∑ i ∈ range N, w i * g i := by
  set d : ℕ → R := fun i ↦ g i - f i with hd
  have hD : ∀ k ≤ N, 0 ≤ ∑ i ∈ range k, d i := fun k hk ↦ by
    simpa [hd, sum_sub_distrib] using hfg k hk
  suffices 0 ≤ ∑ i ∈ range N, w i * d i by
    simpa [hd, mul_sub, sum_sub_distrib] using this
  have hparts := sum_range_by_parts w d N
  simp only [smul_eq_mul] at hparts
  rw [hparts, sub_nonneg]
  calc ∑ i ∈ range (N - 1), (w (i + 1) - w i) * ∑ j ∈ range (i + 1), d j
      ≤ ∑ i ∈ range (N - 1), (0 : R) := by
        refine sum_le_sum fun i hi ↦ ?_
        rw [mem_range] at hi
        exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (hw i (by omega)))
          (hD (i + 1) (by omega))
    _ = 0 := sum_const_zero
    _ ≤ w (N - 1) * ∑ j ∈ range N, d j := mul_nonneg hw0 (hD N le_rfl)

end TauCeti
