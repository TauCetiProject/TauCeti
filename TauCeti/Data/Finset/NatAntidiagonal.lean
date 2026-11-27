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
* `Finset.Nat.div_eq_zero_of_mem_antidiagonal`: both coordinates of any pair in `antidiagonal n`
  vanish upon Euclidean division by `d > n`.
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

/-- Both coordinates of a pair in `antidiagonal n` vanish upon division by any `d > n`. -/
theorem div_eq_zero_of_mem_antidiagonal {d n : ℕ} {ij : ℕ × ℕ}
    (hn : n < d) (hij : ij ∈ antidiagonal n) :
    ij.1 / d = 0 ∧ ij.2 / d = 0 :=
  ⟨Nat.div_eq_of_lt ((HasAntidiagonal.antidiagonal.fst_le hij).trans_lt hn),
   Nat.div_eq_of_lt ((HasAntidiagonal.antidiagonal.snd_le hij).trans_lt hn)⟩

end Finset.Nat
