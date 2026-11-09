/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Fintype.BigOperators

/-!
# Sums of differences of natural-valued functions

If `c ≤ d` pointwise and `c ≠ d` (that is, `c < d` in the pointwise order) for functions from a
finite type to the natural numbers, then the differences `d i - c i`, computed in a linearly
ordered additive group with one, sum to at least `1`.

## Main results

* `TauCeti.one_le_sum_sub_of_lt`: `1 ≤ ∑ i, ((d i : R) - c i)` for `c < d`.
-/

public section

namespace TauCeti

open Finset

/-- If `c ≤ d` pointwise and `c ≠ d` (that is, `c < d` in the pointwise order) on a finite index
type, the differences `d i - c i` sum to at least `1`. -/
theorem one_le_sum_sub_of_lt {R β : Type*} [AddCommGroupWithOne R] [LinearOrder R]
    [IsOrderedAddMonoid R] [ZeroLEOneClass R] [NeZero (1 : R)] [Fintype β] {c d : β → ℕ}
    (h : c < d) : 1 ≤ ∑ i, ((d i : R) - c i) := by
  obtain ⟨i₀, hi₀⟩ := Pi.lt_def.mp h |>.2
  have hnn (i : β) : 0 ≤ (d i : R) - c i := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (h.le i)
    rw [hk, Nat.cast_add, add_sub_cancel_left]
    exact Nat.cast_nonneg' k
  calc (1 : R) ≤ (d i₀ : R) - c i₀ := by
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hi₀
        rw [hk, Nat.cast_add, Nat.cast_add, Nat.cast_one, add_assoc, add_sub_cancel_left]
        exact le_add_of_nonneg_left (Nat.cast_nonneg' k)
    _ ≤ ∑ i, ((d i : R) - c i) :=
        single_le_sum (f := fun i => (d i : R) - c i) (fun i _ => hnn i) (mem_univ i₀)

end TauCeti
