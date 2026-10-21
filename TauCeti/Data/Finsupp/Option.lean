/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Option

/-!
# Weighted products over an extension to `Option`

For a finitely supported `f : α →₀ ℕ` extended by `n` at `none`, the weighted product
`∏ c i ^ (f.optionElim n) i` splits as `c none ^ n` times the weighted product of `f` with the
weights `c ∘ some`. This is the form of Mathlib's `Finsupp.prod_option_index` used to separate
one variable from the monomial weights of multivariate series.
-/

public section

namespace Finsupp

/-- The weighted product of `f.optionElim n` splits off the factor `c none ^ n`. -/
@[to_additive /-- The weighted sum of `f.optionElim n` splits off the summand `n • c none`. -/]
theorem prod_pow_optionElim {α N : Type*} [CommMonoid N] (c : Option α → N) (n : ℕ)
    (f : α →₀ ℕ) :
    (f.optionElim n).prod (c · ^ ·) = c none ^ n * f.prod (fun i k ↦ c (Option.some i) ^ k) := by
  rw [prod_option_index _ _ (fun _ ↦ pow_zero _) fun _ _ _ ↦ pow_add _ _ _,
    optionElim_apply_none, some_optionElim]

end Finsupp
