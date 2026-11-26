/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Weight
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Monotonicity and nonnegativity of `Finsupp.weight`

When every coordinate weight `w u` is nonnegative in an ordered additive commutative monoid,
`Finsupp.weight w` is monotone and nonnegative on `ι →₀ ℕ`.

## Main results

* `Finsupp.weight_mono_of_nonneg`: if `∀ u, 0 ≤ w u`, then `weight w : (ι →₀ ℕ) → M` is monotone.
* `Finsupp.weight_nonneg`: if `∀ u, 0 ≤ w u`, then `0 ≤ weight w α` for every `α : ι →₀ ℕ`.
-/

public section

namespace Finsupp

variable {ι M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftMono M]

/-- A weight with nonnegative coordinates is monotone on `ι →₀ ℕ`. -/
theorem weight_mono_of_nonneg {w : ι → M} (hw : ∀ u : ι, 0 ≤ w u) :
    Monotone (weight w : (ι →₀ ℕ) → M) := fun α β h_exp ↦ by
  classical
  rw [weight_apply, weight_apply,
    Finsupp.sum_of_support_subset α (Finsupp.support_mono h_exp) _ (by simp), Finsupp.sum]
  exact Finset.sum_le_sum fun u _ ↦ nsmul_le_nsmul_left (hw u) (h_exp u)

/-- A weight with nonnegative coordinates takes nonnegative values on `ι →₀ ℕ`. -/
theorem weight_nonneg {w : ι → M} (hw : ∀ u : ι, 0 ≤ w u) (α : ι →₀ ℕ) :
    0 ≤ weight w α := by
  simpa using weight_mono_of_nonneg hw (zero_le (a := α))

end Finsupp
