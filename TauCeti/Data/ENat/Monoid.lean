/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ENat.Monoid

/-!
# Successor bounds in extended natural numbers

Krull dimensions take values in `WithBot ℕ∞`, and a dimension formula often has the shape
`c + 1 = k` for a natural number `k`. In `WithBot ℕ∞` the inequality `c < c + 1` fails for
`c = ⊤`, but a successor equal to a natural number rules that case out, so `c < k`.

A successor bound in `ℕ∞` also gives a nonzero order after coercion to `WithTop ℕ∞`.

## Main results

* `ENat.coe_ne_zero_of_add_one_le`: a successor bound gives a nonzero extended order.
* `ENat.WithBot.lt_natCast_of_add_one_eq`: if `c + 1 = k` with `k : ℕ`, then `c < k`.
-/

public section

namespace ENat

/-- An extended order above a successor remains nonzero after adjoining a new top element. -/
theorem coe_ne_zero_of_add_one_le {n r : ℕ∞} (h : n + 1 ≤ r) : (r : WithTop ℕ∞) ≠ 0 := by
  have hr : (0 : ℕ∞) < r := (add_pos_of_right zero_lt_one n).trans_le h
  exact_mod_cast hr.ne'

end ENat

namespace ENat.WithBot

/-- In `WithBot ℕ∞`, an element whose successor is a natural number is smaller than it. -/
theorem lt_natCast_of_add_one_eq {c : WithBot ℕ∞} {k : ℕ} (h : c + 1 = k) : c < k :=
  (le_add_of_nonneg_right zero_le_one).trans_eq h |>.lt_of_ne (by rintro rfl; norm_cast at h; omega)

end ENat.WithBot
