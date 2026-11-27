/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Products and sums over all permutations evaluated at a point

For `f : α → M` with `α` finite, the product `∏ σ : Perm α, f (σ a)` over all permutations does
not depend on the point `a` (`Equiv.Perm.prod_apply_eq_prod_apply`), and the product of these
products over all points `a` is `(∏ a, f a) ^ |Perm α|` (`Equiv.Perm.prod_prod_apply`). The
additive versions say that the coordinates of the symmetrization `∑ σ, f ∘ σ` are all equal, with
sum `|Perm α| • ∑ a, f a`.

## Main results

* `Equiv.Perm.prod_apply_eq_prod_apply`, `Equiv.Perm.sum_apply_eq_sum_apply`:
  `∏ σ, f (σ a) = ∏ σ, f (σ b)`.
* `Equiv.Perm.prod_prod_apply`, `Equiv.Perm.sum_sum_apply`:
  `∏ a, ∏ σ, f (σ a) = (∏ a, f a) ^ |Perm α|`.
-/

public section

namespace Equiv.Perm

variable {α M : Type*} [Fintype α] [DecidableEq α] [CommMonoid M]

/-- The product `∏ σ, f (σ a)` over all permutations `σ` does not depend on the point `a`. -/
@[to_additive /-- The sum `∑ σ, f (σ a)` over all permutations `σ` does not depend on the point
`a`. -/]
theorem prod_apply_eq_prod_apply (f : α → M) (a b : α) :
    ∏ σ : Perm α, f (σ a) = ∏ σ : Perm α, f (σ b) :=
  Fintype.prod_equiv (Equiv.mulRight (Equiv.swap a b)) _ _ fun σ ↦ by simp [mul_apply]

/-- The products `∏ σ, f (σ a)` over all permutations `σ` multiply, over all points `a`, to
`(∏ a, f a) ^ |Perm α|`. -/
@[to_additive /-- The sums `∑ σ, f (σ a)` over all permutations `σ` add up, over all points `a`,
to `|Perm α| • ∑ a, f a`. -/]
theorem prod_prod_apply (f : α → M) :
    ∏ a, ∏ σ : Perm α, f (σ a) = (∏ a, f a) ^ Fintype.card (Perm α) := by
  rw [Finset.prod_comm]
  simp [Equiv.prod_comp]

end Equiv.Perm
