/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Dimension of a module from a basis

This file complements Mathlib's `Module.finrank_eq_card_basis` with basis-cardinality formulas for
`Module.finrank`, beginning with `Module.finrank_eq_two_mul_card_of_basis_sum` for a finite basis
indexed by a doubled index type `ι ⊕ ι`.
-/

public section

namespace Module

/-- A module with a finite basis indexed by `ι ⊕ ι` has `finrank` equal to
`2 * Fintype.card ι`. -/
theorem finrank_eq_two_mul_card_of_basis_sum {R M ι : Type*} [Semiring R]
    [StrongRankCondition R] [AddCommMonoid M] [Module R M] [Fintype ι]
    (b : Module.Basis (ι ⊕ ι) R M) :
    Module.finrank R M = 2 * Fintype.card ι := by
  rw [Module.finrank_eq_card_basis b, Fintype.card_sum, two_mul]

end Module
