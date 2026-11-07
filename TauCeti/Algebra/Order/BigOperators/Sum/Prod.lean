/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Finite sums and products

The sum of nonnegative terms plus one is bounded by the product of those terms plus one.
-/

public section

namespace TauCeti

/-- A sum of nonnegative terms plus one is bounded by the product of those terms plus one. -/
theorem one_add_sum_le_prod {ι R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hf' : ∀ j ∈ s, 0 ≤ f j := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hs : 0 ≤ ∑ j ∈ s, f j := Finset.sum_nonneg hf'
    have hi0 : 0 ≤ f i := hf i (Finset.mem_insert_self i s)
    have ih' := ih hf'
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    calc
      _ ≤ (1 + f i) * (1 + ∑ j ∈ s, f j) := by
        have h : 1 + (f i + ∑ j ∈ s, f j) ≤
            1 + (f i + ∑ j ∈ s, f j) + f i * (∑ j ∈ s, f j) :=
          le_add_of_nonneg_right (mul_nonneg hi0 hs)
        convert h using 1; ring
      _ ≤ (1 + f i) * ∏ j ∈ s, (1 + f j) :=
        mul_le_mul_of_nonneg_left ih' (add_nonneg zero_le_one hi0)

end TauCeti
