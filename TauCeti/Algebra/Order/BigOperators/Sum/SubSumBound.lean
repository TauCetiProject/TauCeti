/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic

/-!
# Summing the errors of a sequence of increments

If the increments `G (k + 1) - G k` of a sequence `G` are each within `D` of a prescribed value
`g k` for `k < n`, then `G n - G 0` is within `n • D` of the sum `∑ k < n, g k`. The increments
telescope, and the errors add up by the triangle inequality.

Likewise, if a subadditive function `q` is small on each step `F (r + 1) - F r` of a sequence,
relative to weights `w r` whose partial sums are at most `1`, then it is small on the total
displacement `F (N + 1) - F 0`. This is how per-stage perturbation estimates, with weights such as
`2⁻⁽ʳ⁺¹⁾`, are combined into an estimate for the limit of the stages.

## Main results

* `TauCeti.abs_sub_sub_sum_range_le_of_forall_lt`: the bound on `G n - G 0 - ∑ k < n, g k` from
  the bounds on the increments.
* `TauCeti.lt_of_forall_sub_lt_mul`: the telescoping bound for a subadditive function and weights
  with partial sums at most `1`.
-/

public section

namespace TauCeti

/-- If the increments `G (k + 1) - G k` of a sequence are within `D` of `g k` for `k < n`, then
`G n - G 0` is within `n • D` of `∑ k ∈ range n, g k`. -/
theorem abs_sub_sub_sum_range_le_of_forall_lt {α : Type*} [AddCommGroup α] [LinearOrder α]
    [IsOrderedAddMonoid α] {G g : ℕ → α} {D : α} {n : ℕ}
    (hstep : ∀ k < n, |G (k + 1) - G k - g k| ≤ D) :
    |G n - G 0 - ∑ k ∈ Finset.range n, g k| ≤ n • D := by
  have hbound := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk =>
    hstep k (Finset.mem_range.1 hk))
  rwa [Finset.sum_sub_distrib, Finset.sum_range_sub G, Finset.sum_const, Finset.card_range]
    at hbound

/-- A telescoping bound. If a subadditive function `q` is small on each step `F (r + 1) - F r` of a
sequence, relative to weights `w r` summing to at most `1`, then it is small on the total
displacement `F (N + 1) - F 0`. -/
theorem lt_of_forall_sub_lt_mul {G : Type*} [AddCommGroup G] (q : G → ℝ) (hq0 : q 0 ≤ 0)
    (hadd : ∀ a b, q (a + b) ≤ q a + q b) {t : ℝ} (ht : 0 < t) {w : ℕ → ℝ}
    (hw : ∀ N, ∑ r ∈ Finset.range N, w r ≤ 1) (F : ℕ → G) (N : ℕ)
    (h : ∀ r ≤ N, q (F (r + 1) - F r) < t * w r) : q (F (N + 1) - F 0) < t :=
  calc q (F (N + 1) - F 0) = q (∑ r ∈ Finset.range (N + 1), (F (r + 1) - F r)) := by
        rw [Finset.sum_range_sub]
    _ ≤ ∑ r ∈ Finset.range (N + 1), q (F (r + 1) - F r) :=
        Finset.le_sum_of_subadditive _ hq0 hadd _ _
    _ < ∑ r ∈ Finset.range (N + 1), t * w r :=
        Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩ fun r hr ↦
          h r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
    _ ≤ t := by
        rw [← Finset.mul_sum]
        exact mul_le_of_le_one_right ht.le (hw _)

end TauCeti
