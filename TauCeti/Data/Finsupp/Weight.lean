/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Weight

/-!
# Upper bounds for weights by the degree

If every variable has weight at most `c`, then the weight of a monomial `f : σ →₀ ℕ` is at most
`degree f • c`. With `c = -1` over `ℤ`, this says that a monomial all of whose variables have
negative weight has weight at most minus its total degree, which is how negatively graded
variables bound the degree of elements of powers of the ideal of the variables.

## Main results

* `Finsupp.weight_le_degree_nsmul`: if `w s ≤ c` for all `s`, then `weight w f ≤ degree f • c`.
-/

public section

namespace Finsupp

variable {σ M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]

/-- If every variable has weight at most `c`, then the weight of `f` is at most its degree times
`c`. -/
theorem weight_le_degree_nsmul (f : σ →₀ ℕ) {w : σ → M} {c : M} (hw : ∀ s, w s ≤ c) :
    weight w f ≤ degree f • c := by
  rw [weight_apply, degree_apply, Finsupp.sum, ← Finset.sum_nsmul_assoc]
  exact Finset.sum_le_sum fun s _ ↦ nsmul_le_nsmul_right (hw s) _

end Finsupp
