/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Data.Fintype.Card

/-!
# An index type matching the dimension of an infinite-dimensional module

Since `Module.finrank` is `0` for a module that is not finite, a finite index type whose
cardinality equals the `finrank` of such a module is empty
(`Module.isEmpty_of_card_eq_finrank_of_not_finite`).
-/

public section

namespace Module

variable {R M ι : Type*} [Semiring R] [StrongRankCondition R] [AddCommMonoid M] [Module R M]
  [Module.Free R M] [Fintype ι]

/-- A finite index type whose cardinality equals the `finrank` of a module that is not finite is
empty, since `finrank` is `0` there. -/
theorem isEmpty_of_card_eq_finrank_of_not_finite
    (h : Fintype.card ι = finrank R M) (hM : ¬ Module.Finite R M) : IsEmpty ι :=
  Fintype.card_eq_zero_iff.1 (h.trans (Module.finrank_of_not_finite hM))

end Module
