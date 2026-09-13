/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Splitting a finite product at a distinguished index

A product over a finite type can be split into the factor at a chosen index and the product over
the subtype of the remaining indices.

Mathlib's `Fintype.prod_eq_mul_prod_compl` splits off the factor at an index but leaves the rest
as a product over the `Finset` complement of a singleton. Indexing the remainder by the subtype
`{i // i ≠ i₀}` instead is what a construction that genuinely treats the remaining coordinates as
a separate carrier needs, such as a chart on a hyperplane that drops one coordinate.

## Main results

* `TauCeti.prod_eq_mul_prod_subtype_ne` and its additive version
  `TauCeti.sum_eq_add_sum_subtype_ne`.
-/

public section

namespace TauCeti

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]

/-- Split a product over a finite type into the factor at `i₀` and the product over the subtype of
the other indices. -/
@[to_additive /-- Split a sum over a finite type into the term at `i₀` and the sum over the
subtype of the other indices. -/]
theorem prod_eq_mul_prod_subtype_ne (i₀ : ι) (f : ι → M) :
    ∏ i, f i = f i₀ * ∏ j : {i // i ≠ i₀}, f j := by
  rw [Fintype.prod_eq_mul_prod_compl i₀ f]
  exact congrArg _ (Finset.prod_subtype (F := inferInstance) _ (by simp) f)

end TauCeti
