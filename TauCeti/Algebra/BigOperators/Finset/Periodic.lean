/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Periodic

import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# Products of periodic families over ranges

A product of an `l`-periodic family `f : ℕ → M` over `range (n₁ * l + n₀)` is the `n₁`-th power
of the product over one period times the product over `range n₀`. For instance, the generating
polynomials `∏_{j < n} (1 + q^(2j) X)` of the quantum binomial coefficients factor this way when
`q²` is a root of unity of order `l`, which proves the quantum Lucas theorem.

## Main results

* `Finset.prod_range_mul_add_of_periodic`, `Finset.sum_range_mul_add_of_periodic`: a product or
  sum of an `l`-periodic family over `range (n₁ * l + n₀)` in terms of one period and a remainder.
-/

public section

namespace Finset

/-- A product over `range (n₁ * l + n₀)` of an `l`-periodic family is the `n₁`-th power of the
product over one period times the product over `range n₀`. -/
@[to_additive sum_range_mul_add_of_periodic
  /-- A sum over `range (n₁ * l + n₀)` of an `l`-periodic family is `n₁` times the sum over one
  period plus the sum over `range n₀`. -/]
theorem prod_range_mul_add_of_periodic {M : Type*} [CommMonoid M] {f : ℕ → M} {l : ℕ}
    (hf : Function.Periodic f l) (n₁ n₀ : ℕ) :
    ∏ j ∈ range (n₁ * l + n₀), f j = (∏ j ∈ range l, f j) ^ n₁ * ∏ j ∈ range n₀, f j := by
  have h (j i : ℕ) : f (l * j + i) = f i := by simpa [mul_comm l, add_comm] using hf.nat_mul j i
  rw [prod_range_add, mul_comm n₁, prod_range_mul_eq_prod_prod]
  simp only [h, prod_const, card_range]

end Finset
