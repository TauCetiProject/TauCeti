/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic

/-!
# A telescoping bound for subadditive functions

If a subadditive function `q` is small on each step `F (r + 1) - F r` of a sequence, relative to
weights `w r` whose partial sums are at most `1`, then it is small on the total displacement
`F (N + 1) - F 0`. This is how per-stage perturbation estimates, with weights such as `2⁻⁽ʳ⁺¹⁾`,
are combined into an estimate for the limit of the stages.

## Main results

* `TauCeti.lt_of_forall_sub_lt_mul`: the telescoping bound.
-/

public section

namespace TauCeti

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
