/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Finite sums of truncations of natural numbers

For a finite family `c` of natural numbers, the truncated sums `∑ l, min k (c l)` count the boxes
in the first `k` columns of the Young diagram with rows `c l`. Their second differences count
the members of the family in a range: for `p < q`, the combination of the truncated sums at
`p + 1`, `q - 1`, `p` and `q` is the number of members strictly between `p` and `q`.
-/

public section

namespace Finset

variable {α : Type*}

/-- For `p < q`, the second differences of the truncated sums `∑ l, min k (c l)` at `p` and `q`
count the members of the family `c` strictly between `p` and `q`. -/
theorem sum_min_add_sum_min_eq (u : Finset α) (c : α → ℕ) {p q : ℕ} (hpq : p < q) :
    ∑ l ∈ u, min (p + 1) (c l) + ∑ l ∈ u, min (q - 1) (c l) =
      ∑ l ∈ u, min p (c l) + ∑ l ∈ u, min q (c l) + #{l ∈ u | p < c l ∧ c l < q} := by
  rw [card_filter, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun l _ => by split_ifs <;> omega

end Finset
