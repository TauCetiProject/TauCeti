/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Fintype.BigOperators

/-!
# Sums of differences of natural-valued functions

If `c ≤ d` pointwise and `c ≠ d` (that is, `c < d` in the pointwise order) for functions from a
finite type to the natural numbers, then the differences `d i - c i`, computed in a linearly
ordered ring, sum to at least `1`.

## Main results

* `TauCeti.one_le_sum_sub_of_lt`: `1 ≤ ∑ i, ((d i : R) - c i)` for `c < d`.
-/

public section

namespace TauCeti

open Finset

/-- If `c ≤ d` pointwise and `c ≠ d` (that is, `c < d` in the pointwise order) on a finite index
type, the differences `d i - c i` sum to at least `1`. -/
theorem one_le_sum_sub_of_lt {R β : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype β] {c d : β → ℕ} (h : c < d) : 1 ≤ ∑ i, ((d i : R) - c i) := by
  obtain ⟨i₀, hi₀⟩ := Pi.lt_def.mp h |>.2
  calc (1 : R) ≤ (d i₀ : R) - c i₀ := by
        rw [le_sub_iff_add_le']
        exact_mod_cast hi₀
    _ ≤ ∑ i, ((d i : R) - c i) :=
        single_le_sum (f := fun i => (d i : R) - c i)
          (fun i _ => sub_nonneg.mpr (Nat.cast_le.mpr (h.le i))) (mem_univ i₀)

end TauCeti
