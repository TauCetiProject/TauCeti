/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Comparing weighted sums through their partial sums

If every initial partial sum of `f` is at most the corresponding partial sum of `g`, then the
same comparison holds after weighting both sequences by a nonnegative, antitone weight `w`:
`∑_{i < N} w i • f i ≤ ∑_{i < N} w i • g i`. This is Abel's inequality in its comparison form.
The sequences `f` and `g` take values in an ordered module over the ordered ring of weights;
for real or ring-valued sequences the scalar action is multiplication.
Summation by parts (`Finset.sum_range_by_parts`) writes the difference of the two weighted sums
as the last weight times the last partial-sum difference plus the successive decrements of `w`
times the earlier partial-sum differences, and every one of these products is nonnegative.

No sign condition on `f` or `g` is needed. The typical use takes `g` constant: a bound
`∑_{i < k} f i ≤ k • C` on all partial sums then gives `∑ w i • f i ≤ (∑ w i) • C` for every
nonnegative antitone weight.

The second result is the case where `g` is the indicator of the first `k` indices. Weights
`c i ∈ [0, 1]` of total mass at most `k`, placed against a nonnegative antitone sequence `w`,
give a weighted sum at most the sum of the `k` largest values of `w`: the mass is best spent on
the first `k` indices. Only `c i ≤ 1` for `i < k` and `0 ≤ c i` for `k ≤ i < N` are used. When
the mass is exactly `k`, no sign condition on `w` is needed. This is the step that turns
Bessel-type weight bounds into Ky Fan inequalities for singular values and eigenvalues.

## Main results

* `TauCeti.sum_range_smul_le_sum_range_smul`: the weighted comparison.
* `TauCeti.sum_range_mul_le_sum_range_of_sum_le`: unit-bounded weights of total mass at most `k`
  against a nonnegative antitone sequence give at most the sum of its first `k` terms.
* `TauCeti.sum_range_mul_le_sum_range_of_sum_eq`: the same for weights of total mass exactly `k`,
  against an antitone sequence of any sign.
-/

public section

namespace TauCeti

open Finset

variable {R M : Type*} [Ring R] [Preorder R] [IsOrderedAddMonoid R]

/-- **Abel's inequality, comparison form.** If the partial sums of `f` are dominated by those of
`g` up to `N`, and `w` is nonnegative and antitone on the first `N` indices, then
`∑_{i < N} w i • f i ≤ ∑_{i < N} w i • g i`. Only the last weight is required
to be nonnegative explicitly; the other signs follow from the successive comparisons
when `N > 0`. -/
theorem sum_range_smul_le_sum_range_smul [AddCommGroup M] [Preorder M] [IsOrderedAddMonoid M]
    [Module R M] [PosSMulMono R M] {f g : ℕ → M} {w : ℕ → R} {N : ℕ}
    (hfg : ∀ k ≤ N, ∑ i ∈ range k, f i ≤ ∑ i ∈ range k, g i)
    (hw : ∀ i, i + 1 < N → w (i + 1) ≤ w i) (hw0 : 0 ≤ w (N - 1)) :
    ∑ i ∈ range N, w i • f i ≤ ∑ i ∈ range N, w i • g i := by
  have hD (k : ℕ) (hk : k ≤ N) : 0 ≤ ∑ i ∈ range k, (g i - f i) := by
    simpa [sum_sub_distrib] using hfg k hk
  rw [← sub_nonneg, ← sum_sub_distrib]
  simp only [← smul_sub]
  rw [sum_range_by_parts, sub_nonneg]
  refine (sum_nonpos fun i hi ↦ ?_).trans (smul_nonneg hw0 (hD N le_rfl))
  rw [← neg_sub, neg_smul, neg_nonpos]
  exact smul_nonneg (sub_nonneg.2 (hw i (by grind))) (hD (i + 1) (by grind))

variable [PosMulMono R]

/-- Weights `c i` with total mass at most `k ≤ N`, at most `1` on the first `k` indices and
nonnegative on the remaining indices below `N`, placed against a sequence `w` that is antitone and
nonnegative on the first `N` indices, give at most the sum of the first `k` terms of `w`:
`∑_{i < N} w i * c i ≤ ∑_{i < k} w i`. In particular this applies to weights `c i ∈ [0, 1]`. -/
theorem sum_range_mul_le_sum_range_of_sum_le {w c : ℕ → R} {N k : ℕ} (hk : k ≤ N)
    (hc0 : ∀ i, k ≤ i → i < N → 0 ≤ c i) (hc1 : ∀ i < k, c i ≤ 1)
    (hck : ∑ i ∈ range N, c i ≤ k) (hw : ∀ i, i + 1 < N → w (i + 1) ≤ w i)
    (hw0 : 0 ≤ w (N - 1)) :
    ∑ i ∈ range N, w i * c i ≤ ∑ i ∈ range k, w i := by
  have hf (m : ℕ) : {i ∈ range m | i < k} = range (min m k) := by ext; simp
  have hg : ∑ i ∈ range N, w i * (if i < k then 1 else 0) = ∑ i ∈ range k, w i := by
    simp only [mul_ite, mul_one, mul_zero, ← sum_filter, hf, min_eq_right hk]
  rw [← hg]
  simp_rw [← smul_eq_mul]
  refine sum_range_smul_le_sum_range_smul (fun m hm ↦ ?_) hw hw0
  rw [← sum_filter, hf, sum_const, card_range, nsmul_one]
  rcases le_total m k with hmk | hkm
  · rw [min_eq_left hmk]
    exact (sum_le_card_nsmul _ _ 1 fun i hi ↦ hc1 i (by grind)).trans (by simp)
  · rw [min_eq_right hkm]
    refine (sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hm) fun i hi hni ↦ ?_).trans hck
    exact hc0 i (by grind) (by grind)

/-- Weights `c i` with total mass exactly `k ≤ N`, at most `1` on the first `k` indices and
nonnegative on the remaining indices below `N`, placed against a sequence `w` that is antitone on
the first `N` indices, give at most the sum of the first `k` terms of `w`:
`∑_{i < N} w i * c i ≤ ∑_{i < k} w i`. Unlike `TauCeti.sum_range_mul_le_sum_range_of_sum_le`,
no sign condition on `w` is needed. -/
theorem sum_range_mul_le_sum_range_of_sum_eq {w c : ℕ → R} {N k : ℕ} (hk : k ≤ N)
    (hc0 : ∀ i, k ≤ i → i < N → 0 ≤ c i) (hc1 : ∀ i < k, c i ≤ 1)
    (hck : ∑ i ∈ range N, c i = k)
    (hw : ∀ i, i + 1 < N → w (i + 1) ≤ w i) :
    ∑ i ∈ range N, w i * c i ≤ ∑ i ∈ range k, w i := by
  -- Shift `w` by its last value, which makes it nonnegative without changing the comparison.
  have h := sum_range_mul_le_sum_range_of_sum_le (w := fun i ↦ w i - w (N - 1)) hk hc0 hc1
    hck.le (fun i hi ↦ sub_le_sub_right (hw i hi) _) (by simp)
  simpa [sub_mul, sum_sub_distrib, ← mul_sum, hck, Nat.cast_comm] using h

end TauCeti
