/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ENat.Monoid
import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Successor bounds and cancellation in extended natural numbers

Krull dimensions take values in `WithBot ℕ∞`, and a dimension formula often has the shape
`c + 1 = k` for a natural number `k`. In `WithBot ℕ∞` the inequality `c < c + 1` fails for
`c = ⊤`, but a successor equal to a natural number rules that case out, so `c < k`.

A successor bound in `ℕ∞` also gives a nonzero order after coercion to `WithTop ℕ∞`.

Two dimension formulas `n + d = N` and `n' + d' = N` with the same finite nonnegative total can
be compared: a larger second summand forces a smaller natural-number first summand. Additive
cancellation fails in `WithBot ℕ∞` in general, because of `⊥` and `⊤`.

## Main results

* `ENat.coe_ne_zero_of_add_one_le`: a successor bound gives a nonzero extended order.
* `ENat.WithBot.lt_natCast_of_add_one_eq`: if `c + 1 = k` with `k : ℕ`, then `c < k`.
* `ENat.WithBot.natCast_le_natCast_of_add_eq_of_le`: if `n + d = N = n' + d'` with `d' ≤ d` and
  `0 ≤ N < ⊤`, then `n ≤ n'`.
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

/-- Cancellation in `WithBot ℕ∞`: if `n + d = N = n' + d'` with `d' ≤ d` and `N` finite and
nonnegative, then `n ≤ n'`. -/
theorem natCast_le_natCast_of_add_eq_of_le {n n' : ℕ} {d d' N : WithBot ℕ∞}
    (h : (n : WithBot ℕ∞) + d = N) (h' : (n' : WithBot ℕ∞) + d' = N) (hle : d' ≤ d)
    (hbot : 0 ≤ N) (htop : N < ⊤) : (n : WithBot ℕ∞) ≤ n' := by
  subst h
  induction d using WithBot.recBotCoe with
  | bot => simp at hbot
  | coe d =>
  induction d using ENat.recTopCoe with
  | top => simp at htop
  | coe d =>
  induction d' using WithBot.recBotCoe with
  | bot => norm_cast at h'
  | coe d' =>
  induction d' using ENat.recTopCoe with
  | top => norm_cast at h'
  | coe d' =>
  norm_cast at h' hle ⊢
  omega

end ENat.WithBot
