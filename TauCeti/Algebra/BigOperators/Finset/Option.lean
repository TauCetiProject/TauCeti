/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Option

/-!
# Big operators over finite sets of optional values

This file splits a product or sum over `Finset (Option α)` into the terms indexed by `some`
and the possible term indexed by `none`.

## Main results

* `Finset.prod_option`: split a product into its `some` terms and its possible `none` term.
* `Finset.sum_option`: additive version of `Finset.prod_option`.
-/

public section

namespace Finset

variable {α M : Type*} [DecidableEq α] [CommMonoid M]

/-- Split a product over optional values into its `some` terms and its possible `none` term. -/
@[to_additive /-- Split a sum over optional values into its `some` terms and its possible `none`
term. -/]
theorem prod_option (s : Finset (Option α)) (f : Option α → M) :
    ∏ x ∈ s, f x = (∏ x ∈ s.eraseNone, f (some x)) * if none ∈ s then f none else 1 := by
  by_cases h : none ∈ s
  · rw [ite_eq_left h, ← prod_erase_mul _ _ h, ← map_some_eraseNone, prod_map]
    simp only [Function.Embedding.some_apply]
  · conv_lhs => rw [← erase_eq_of_notMem h]
    rw [ite_eq_right h, mul_one, ← map_some_eraseNone, prod_map]
    simp only [Function.Embedding.some_apply]

end Finset
