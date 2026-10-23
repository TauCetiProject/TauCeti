/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.NatAntidiagonal
-- Proof-only: Gauss's summation formula.
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The pairs of natural numbers with bounded sum

The pairs `(i, j)` of natural numbers with `i + j < m` are the union of the antidiagonals
`i + j = s` for `s < m`, and there are `m (m + 1) / 2` of them.

## Main results

* `Finset.Nat.two_mul_card_biUnion_range_antidiagonal`: the union of the antidiagonals
  `i + j = s` for `s < m` has `m (m + 1) / 2` elements.
-/

public section

namespace Finset.Nat

/-- **There are `m (m + 1) / 2` pairs of natural numbers with sum less than `m`**: the union of
the antidiagonals `i + j = s` for `s < m` has `m (m + 1) / 2` elements. -/
theorem two_mul_card_biUnion_range_antidiagonal (m : ℕ) :
    2 * ((range m).biUnion antidiagonal).card = m * (m + 1) := by
  rw [card_biUnion fun a _ b _ hab ↦ disjoint_left.mpr fun p ha hb ↦
    hab ((mem_antidiagonal.mp ha).symm.trans (mem_antidiagonal.mp hb))]
  simp_rw [card_antidiagonal]
  have h := sum_range_id_mul_two (m + 1)
  rw [sum_range_succ'] at h
  simpa [mul_comm] using h

end Finset.Nat
