/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Fintype.BigOperators

/-!
# Sums of differences of natural-valued functions

If `c < d` as functions from a finite type to the natural numbers, then the real differences
`d i - c i` sum to at least `1`.

## Main results

* `Finset.one_le_sum_sub_of_lt`: `1 ≤ ∑ i, ((d i : ℝ) - c i)` for `c < d`.
-/

public section

open Finset

/-- If `c < d` coordinatewise on a finite index type, the differences sum to at least `1`. -/
theorem Finset.one_le_sum_sub_of_lt {β : Type*} [Fintype β] {c d : β → ℕ} (h : c < d) :
    1 ≤ ∑ i, ((d i : ℝ) - c i) := by
  obtain ⟨i₀, hi₀⟩ := Pi.lt_def.mp h |>.2
  calc (1 : ℝ) ≤ (d i₀ : ℝ) - c i₀ := by
        rw [le_sub_iff_add_le', ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
        omega
    _ ≤ ∑ i, ((d i : ℝ) - c i) :=
        single_le_sum (f := fun i => (d i : ℝ) - c i)
          (fun i _ => sub_nonneg.mpr (Nat.cast_le.mpr (h.le i))) (mem_univ i₀)
